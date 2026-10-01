# SDG：综合微分几何的 Lean 4 形式化

在 Lean 4 + Mathlib 中对**综合微分几何**（Synthetic Differential Geometry,
SDG）的核心内容做**构造性、无选择公理**的形式化。当前为 Kock《Synthetic
Differential Geometry of Manifolds》第 I 部分的微分形式—de Rham 复形链条。

## 约束（红线）

全部微分形式模块遵守 `SDG/NoChoice.lean` 的强制审计：

- 禁止 `sorry`、`admit`、裸 `axiom`、`Classical.choice`、`unsafe`；
- 禁止用 `noncomputable`/`opaque` 绕过证明；
- `d² = 0`、Stokes 等定理全部给出完整证明，不塞进 typeclass；
- 每条新声明可由 `#print axioms` 复核（当前全部为 `[propext, Quot.sound]`
  或更少）。

凡 Mathlib 中依赖选择公理的构造（如 `Finset.sum`、
`AlternatingMap.domCoprod`），均以 `Fin` 专用的构造性替身绕开
（`finSum`/`finProd`、显式 `precompose`、构造性置换编码 `FinPerm`）。

## 模块地图

| 模块 | 内容 |
|---|---|
| `SDG/NoChoice.lean` | 无选择公理的 linter 与 `#assert_no_choice` 审计机制 |
| `SDG/KockLawvereDkn.lean` | Kock–Lawvere 公理与 Dₙ 环 |
| `SDG/Infinitesimal.lean` | 无穷小对象与微线性（Microlinear） |
| `SDG/TangentBundle.lean` | 切丛、切纤维 `TangentFiber` 及其模结构 |
| `SDG/Derivative.lean` | 方向导数 |
| `SDG/DifferentialForms/Core.lean` | 严格逐点形式层 `FiberwiseDifferentialForm`（每基点一个 Mathlib `AlternatingMap`）、严格拉回、0-形式外微分 `d₀` 及 Leibniz |
| `SDG/DifferentialForms/Algebra.lean` | 形式代数主体（见下） |
| `SDG/DifferentialForms/Simplicial.lean` | 单纯形面映射 `faceMap i = i.succAbove` |
| `SDG/FinSumProd.lean` | 无选择 `finSum`/`finProd` 及其拆分/重排/配对引理 |

## 已完成的形式化内容

### 1. 严格逐点形式层（Core）

`FiberwiseDifferentialForm R X n := ∀ x, TangentFiber R X x [⋀^Fin n]→ₗ[R] R`
——每个基点给出一个真正的交错多线性映射，加法性/齐次性/交错性由类型
保证。配套：严格预合成（绕开 choice-dependent 的 `compLinearMap`）、
拉回的恒等/复合/线性定律、0-形式外微分 `d₀`（KL 方向导数）及其
加法/数乘/常值/Leibniz 律。

### 2. 构造性置换代数（Algebra, FinPerm 段）

归纳插入编码 `FinPerm n`、构造性逆与双射性、从单射自映射恢复编码
（枚举全部置换）、逆序数 `invCount` 与 `depth = invCount`、无选择置换
求和 `permSum`。

### 3. 相邻对换与求和重排（Algebra, SwapFinAdj 段）

构造性相邻对换 `swapFinAdj j`（交换 `j, j+1`）及其值公式、自逆性、
后继交换律；核心组合事实 **`finSum_swapFinAdj`**：无选择求和在任意
位置的相邻对换下不变。配套 `finSum_split_at`（任意位置拆出单项）、
`finSum_congr`、`finSum_neg`。

### 4. 楔积

- `1 ∧ 1` 楔积 `wedgeOneOne`：完整 `AlternatingMap` 打包 + 双线性/
  反对称/零/分次交换/拉回相容；
- `0 ∧ n` 楔积 `wedgeZeroLeft/Right`：单位/零/线性/拉回；
- **一般 `1 ∧ n` 楔积**（Kock I.14 公式 (14.7)）：展开项
  `wedgeOneAnyTerm i = (-1)ⁱ·ω(vᵢ)·η(v₀,…,v̂ᵢ,…,vₙ)`，交错性无选择证明：
  - 极化恒等式 `alternatingMap_swapFinAdj'`：交错形式在相邻对换下变号
    （构造性，目标只需 AddCommMonoid，对 char 2 亦成立）；
  - `removeNth` 与相邻对换的三种位置交换关系（左移/不变/吸收）；
  - `wedgeOneAnyFun_swapFinAdj`：相邻槽对换反号（逐项配对：η 的对换
    变号 + `(-1)ⁱ` 错位 + `finSum_swapFinAdj` 重排）；
  - `wedgeOneAnyFun_eq_zero_of_adjacent / _eq_zero_of_eq`：任意两槽
    代入相等向量则值为零（相邻情形 char-2 安全的直接配对消去 +
    冒泡归纳）。

### 5. 奇异上链与 de Rham 复形（Algebra, DeRham 段）

- n-上链 `Cochain R X n`、面删除 `coFace σ i = σ ∘ i.succAbove`；
- 余边界算子 `∂`（面删除的交错和，无选择）及其线性、拉回自然性；
- `∂² = 0` 于 0-上链（`coboundary_coboundary_one`，六条面组合恒等式
  `fcc1–fcc6` 成对消去）；
- `∂(cochainOfFun f) = d₀ f`：de Rham 微分与 KL 方向导数一致；
- cup 积 `cupProduct`（`cupLeft/cupRight` 分组指标）：双线性、零、
  拉回自然性、0-上链交换律；
- 常值函数闭（`∂c = 0`）、`d₀` 的 Leibniz/加法/数乘/常值律。

## 数学结论速览

形式化得到的核心定理（全部无选择公理、全构造性）：

1. **严格形式层良构**：求值对每槽加法/数乘线性和交错性成立；
2. **`finSum` 重排理论**：相邻对换不变、单项拆出、逐项相等/取负；
3. **`1 ∧ n` 楔积是交错的**：相邻反交换 + 任意槽相等消去；
4. **∂ 是复形微分**：`∂² = 0`（0-上链层）且与 `d₀` 相容。

## 后续路线图（未形式化部分）

按优先级：

1. **一般 n 的 `∂² = 0`**：单纯形恒等式
   `i.succAbove ∘ j.succAbove = j'.succAbove ∘ i'.succAbove`（case 分裂
   重参数化）+ 双和配对消去（基础设施已就绪：`finSum_swapFinAdj`、
   `finSum_split_at`）；
2. **`(p,q)` 一般楔积**：permSum + shuffle 符号加权（需任意对换 =
   相邻对换乘积的构造性分解）；
3. **任意阶外微分 `d : Ωⁿ → Ωⁿ⁺¹`**（Koszul 公式）与 `d² = 0`、
   分次 Leibniz、拉回自然性；
4. **参数化单形积分与 Stokes**（先 n=1, 2 再归纳）；
5. **构造性链与 currents**：`∂² = 0` 对偶、current-Stokes；
6. Čech 上同调、de Rham 同构的 SDG 版本。

## 构建

```bash
lake build          # 全量构建（首次会补建 Mathlib，约 8000+ 目标）
lake env lean SDG/TestNoChoice.lean   # 无选择公理审计自检
```

Lean 工具链：`leanprover/lean4:v4.34.0-rc1`，Mathlib `v4.34.0-rc1`。

## 分支与 PR

- 工作分支 `feature/differential-forms-core`，PR：
  <https://github.com/cao-jia-rong/SDG/pull/2>（自 fork
  [GuitarYuu/SDG](https://github.com/GuitarYuu/SDG) 发起）；
- 断点续作见 `RESUME.md`（含关键 Lean 工程配方与已验证的坑）。
