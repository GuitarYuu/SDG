import Lean
import Lean.Util.CollectAxioms
import Lean.Elab.Command
import Lean.Elab.InfoTree

/-!
# SDG.NoChoice

元编程基础设施：自动确保本项目的每个声明都没有使用**选择公理**（`Classical.choice`）。

合成微分几何（SDG）采用构造性取向：Kock-Lawvere 公理、微线性等都建立在
「存在且唯一」的显式数据上（本仓库用子类型编码 `ExistsUnique'`），因此
证明中不应（也不需）使用选择公理。本模块复用了 `#print axioms` 的底层
`Lean.collectAxioms`，将「是否依赖 `Classical.choice`」的检查自动化。

本模块提供两层保护：

1. **自动 linter** `linter.noAxiomOfChoice`（默认开启）：注册后，对本文件
   之后每个声明的命令自动调用 `Lean.collectAxioms`，若该声明（传递地）依赖
   `Classical.choice` 则**报错**。
   * 在项目每个源文件顶部 `import SDG.NoChoice` 即自动生效；
   * 若某处确需临时放行，可用 `set_option linter.noAxiomOfChoice false` 包裹；
   * 也可在 `lakefile.toml` 的 `leanOptions` 中整体关闭。

2. **显式命令** `#assert_no_choice n₁ n₂ ⋯`：手动检查任意（含导入的）声明，
   违反则报错，通过则打印确认信息。

实现要点：

* `Lean.collectAxioms` 返回一个常量**传递**依赖的全部内核公理名
  （与 `#print axioms` 同源），因此对 `def`/`theorem`/`instance` 等的
  底层依赖也一并检查；
* 默认只禁止 `Classical.choice`（选择公理）。`propext` 与 `Quot.sound` 是
  Lean 逻辑本身的基础公理，不属于「选择公理」，故不在此列；
  如需更严格，可自行扩充 `forbiddenAxioms`；
* `by_cases`/`split_ifs` 在有 `DecidableEq` 实例时**不**引入选择公理，
  但 `fin_cases`、`simp` 展开含 `by_cases` 证明的定义、以及在无判定性命题上
  使用 `by_cases` 都会引入 `Classical.choice` —— 本 linter 会自动捕获这些情况。
-/

open Lean Elab Command Parser Linter

namespace SDG.NoChoice

/-- 视为「选择公理」的内核公理（默认仅 `Classical.choice`）。 -/
def forbiddenAxioms : Array Name := #[``Classical.choice]

/-- 若声明 `name`（传递地）依赖任一禁止公理，返回 `some <公理名>`；否则 `none`。 -/
def forbiddenAxiomUsed? (name : Name) : CommandElabM (Option Name) := do
  let axioms ← collectAxioms name
  return forbiddenAxioms.find? (fun ax ↦ axioms.contains ax)

/-- 从命令语法中提取刚声明的名字（短名，尚未按当前命名空间解析）。
支持 `def`/`theorem`/`lemma`/`abbrev`/`opaque`/`axiom`/`inductive`/`structure`/
`class` 以及具名 `instance`；`example` 与匿名 `instance` 返回 `none`。

**为什么需要显式处理 `lemma`**：`lemma` 是 Mathlib 在**根命名空间**引入的独立语法
（`syntax (name := lemma) ... : command`，宏展开为 `theorem`），其节点种类是裸名
`lemma`；而 linter 收到的是**宏展开前**的原始命令节点，故须显式识别 `lemma` 种类，
否则 `lemma` 声明会被静默跳过。 -/
def rawDeclName? (stx : Syntax) : Option Name :=
  -- 只处理标准声明命令（`declaration`）或 Mathlib 的 `lemma` 节点。
  -- 注意：`lemma` 由 Mathlib 在**根命名空间**声明为 `syntax (name := lemma)`，
  -- 其种类是裸名 `lemma`（而非 `Lean.Parser.Command.lemma`）；且本文件不导入
  -- Mathlib，故种类比较须用单反引号 Name 字面量（`` `foo ``），不能用双反引号。
  if !stx.isOfKind `Lean.Parser.Command.declaration &&
     !stx.isOfKind `lemma then
    none
  -- `example` 没有持久名字
  else if stx.isOfKind `Lean.Parser.Command.declaration &&
     stx[1].getKind == `Lean.Parser.Command.example then
    none
  else
    -- 声明名即语法树中第一个 `declId` 节点；`lemma` 的 `declId` 位于内层
    -- `group` 中，用 `find?` 可统一处理各种声明形态（匿名 `instance` 无
    -- `declId`，自然返回 `none`）。
    match stx.find? (·.isOfKind `Lean.Parser.Command.declId) with
    | some declId => some declId[0].getId.eraseMacroScopes
    | none        => none

/-- 开关：`linter.noAxiomOfChoice`（默认开启）。 -/
register_option linter.noAxiomOfChoice : Bool := {
  defValue := true
  descr := "error if a declaration (transitively) uses the axiom of choice (Classical.choice)"
}

/-- 递归检查单个命令语法：处理 `cmd₁ in cmd₂` 包裹后，对声明做选择公理检查。

`in`（如 `open X in cmd`、`set_option ... in cmd`）是宏，展开为 `section cmd₁ cmd₂ end`；
linter 只收到**展开前**的顶层 `in` 节点，内部声明不会单独经过 linter。
这里用 `withSetOptionIn` 先处理 `set_option ... in`（更新选项再递归内层），
再对其它 `in` 直接递归进 `cmd₂`，从而检查到被包裹的声明。 -/
partial def checkDecl : Syntax → CommandElabM Unit := withSetOptionIn fun stx ↦ do
  -- 通用 `cmd₁ in cmd₂`（如 `open X in`）：递归检查内部 `cmd₂`
  if stx.getKind == `Lean.Parser.Command.in then
    checkDecl stx[2]
    return
  unless getLinterValue linter.noAxiomOfChoice (← getLinterOptions) do
    return
  -- 命令本身有错误时（声明未成功加入环境）跳过，避免叠加噪音
  if (← get).messages.hasErrors then
    return
  let some shortName := rawDeclName? stx | return
  -- 解析到全局名字（处理当前命名空间 / `_root_` 等）；解析失败（如私有声明）则跳过
  let resolved? ←
    try
      pure (some (← liftCoreM <| realizeGlobalConstNoOverloadCore shortName))
    catch _ =>
      pure none
  let some name := resolved? | return
  if let some ax ← forbiddenAxiomUsed? name then
    throwErrorAt stx
      m!"declaration '{name}' (transitively) depends on the axiom of choice: {ax}. \
        To allow it, use `set_option linter.noAxiomOfChoice false` around this declaration."

/-- 自动 linter：每个新声明若（传递地）使用选择公理则报错。 -/
def noAxiomOfChoice : Linter where
  name := `linter.noAxiomOfChoice
  run := checkDecl

initialize addLinter noAxiomOfChoice

/-- 显式检查：`#assert_no_choice n₁ n₂ ⋯` 确保所列声明不使用选择公理。 -/
elab "#assert_no_choice " ids:ident+ : command => do
  for id in ids do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    if let some ax ← forbiddenAxiomUsed? name then
      throwErrorAt id
        m!"'{name}' (transitively) depends on the axiom of choice: {ax}"
    else
      logInfo m!"'{name}' does not use the axiom of choice"

end SDG.NoChoice
