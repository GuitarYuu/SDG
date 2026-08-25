import SDG.NoChoice
import Mathlib

/-!
# SDG.TestNoChoice

验证 `SDG.NoChoice` 的选择公理自动检查机制。

* 无选择公理的 `def`/`theorem`/`lemma`/`instance` 应通过 linter；
* `open X in ...` / `set_option ... in ...` 包裹内的声明也**会被**检查
  （linter 递归进 `in` 块）；
* `#assert_no_choice` 对无选择公理的声明打印确认信息；
* `set_option linter.noAxiomOfChoice false in` 可临时放行。

**故意使用 `Classical.choice` 的例子**：`demo_choice_allowed` 用
`set_option linter.noAxiomOfChoice false in` 包裹，故可构建。若把它改为
顶层无包裹的声明，linter 会报错——例如文末注释中的 `demo_choice_violation`
与 `open Rat in` 包裹的 `demo_choice_in_violation`，可自行取消注释验证。
-/

/-! ## 无选择公理的声明：应全部通过 linter -/

def clean_def : ℕ := 42

theorem clean_theorem : 0 + 0 = 0 := by
  rfl

lemma clean_lemma : 1 + 1 = 2 := by
  norm_num

instance instClean : Nonempty ℕ := ⟨0⟩

/-! ## 显式命令检查 -/

#assert_no_choice clean_def clean_theorem clean_lemma instClean

/-! ## `in` 块内的声明也应被检查（无选择公理时通过） -/

open Rat in
lemma clean_in : 1 + 1 = 2 := by
  norm_num

/-! ## 临时放行（`set_option ... in` 包裹，作用域内不检查） -/

set_option linter.noAxiomOfChoice false in
lemma demo_choice_allowed : Nonempty ℕ := ⟨Classical.choice ⟨0⟩⟩

open Rat in
set_option linter.noAxiomOfChoice false in
lemma demo_choice_in_allowed : Nonempty ℕ := ⟨Classical.choice ⟨0⟩⟩

/-!
下面两个（未放行的）版本若取消注释，会被 linter 报错：
```
lemma demo_choice_violation : Nonempty ℕ := ⟨Classical.choice ⟨0⟩⟩

open Rat in
lemma demo_choice_in_violation : Nonempty ℕ := ⟨Classical.choice ⟨0⟩⟩
```
-/
