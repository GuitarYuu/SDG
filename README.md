# SDG：综合微分几何的 Lean 4 形式化

在 Lean 4 + Mathlib 中对**综合微分几何**（Synthetic Differential Geometry,
SDG）的核心内容做**构造性、无选择公理**的形式化。目标：完成 Kock
《Synthetic Differential Geometry of Manifolds》第 I 部分的微分形式—de Rham
复形链条（含电流层与场变元代数层）。**核心理论闭环已宣告**：de Rham 复形
正合性（d² = 0）在单纯层与场变元层两层完整证明。

## 项目背景与合作

本项目起源于 **2026 年上海交通大学 Lean 暑校**（无穷类型咖啡 · AI4Math
方向），由 **caojiarong** 与 **[GuitarYuu](https://github.com/GuitarYuu)**
在暑校期间合作搭建，完成了项目的基础设施与初步形式化（NoChoice 审计框架、
KL 公理、微线性、切丛、Core 逐点形式层、Algebra 的置换引擎与楔积基础、
Currents 电流层初始提交）。

暑校结束后，caojiarong 选择不再继续维护，本项目由
**[GuitarYuu](https://github.com/GuitarYuu)** 独立完成了剩余部分的
全部形式化工作，包括：Algebra.lean 的上闭链 de Rham 复形完整理论（∂²=0、
cup 积、分次 Leibniz、分次交换律）、Currents.lean 的电流层完整理论
（Hₙ/Hⁿ 同调群、Stokes 配对、Module R）、Integration.lean 积分层、
场变元代数层全新模块（AlgebraicForms.lean——李括号、Koszul 外微分、
d²=0 两层闭环、楔积与分次 Leibniz）、以及 AuditSweep.lean 的 111 条
核心声明批量 axiom 审计基建。

全部工作遵守项目红线：**构造性、零选择公理、零 sorry**。

## 约束（红线）

全部微分形式模块遵守 `SDG/NoChoice.lean` 的强制审计：

- 禁止 `sorry`、`admit`、裸 `axiom`、`Classical.choice`、`unsafe`；
- 禁止用 `noncomputable`/`opaque` 绕过证明；
- `d² = 0`、Stokes 等定理全部给出完整证明，不塞进 typeclass；
- 每条新声明可由 `#print axioms` 复核（当前 **111 条核心声明**全部为
  `[propext, Quot.sound]` 或更少，见 `SDG/AuditSweep.lean`）。

凡 Mathlib 中依赖选择公理的构造（如 `Finset.sum`、
`AlternatingMap.domCoprod`），均以 `Fin` 专用的构造性替身绕开
（`finSum`/`finProd`、显式 `precompose`、构造性置换编码 `FinPerm`）。

## 模块地图

| 模块 | 内容 |
|---|---|
| `SDG/NoChoice.lean` | 无选择公理的 linter 与 `#assert_no_choice` 审计机制 |
| `SDG/KockLawvereDkn.lean` | Kock–Lawvere 公理与 Dₙ 环（含全 schema） |
| `SDG/Infinitesimal.lean` | 无穷小对象与微线性（Microlinear）、D(2)/D(3) 基础设施 |
| `SDG/Microlinear.lean` | 微线性的 Π-保持、积保持、R 自身微线性 |
| `SDG/TangentBundle.lean` | 切丛、切纤维 `TangentFiber` 及其模结构（AddCommMonoid + Module R） |
| `SDG/Derivative.lean` | 方向导数（KL 公理） |
| `SDG/LieBracket.lean` | 李括号（Property W 因子化路线，Kock I.9） |
| `SDG/DifferentialForms/Core.lean` | 严格逐点形式层、严格拉回、0-形式外微分 `d₀` 及 Leibniz |
| `SDG/DifferentialForms/Algebra.lean` | 形式代数主体（置换引擎、楔积 E0-E3、上闭链 de Rham 复形、cup 积、分次 Leibniz、∂²=0） |
| `SDG/DifferentialForms/AlgebraicForms.lean` | **场变元代数层**：李括号配套、Koszul 外微分 algD0-D3、d²=0 两层闭环、楔积、分次 Leibniz |
| `SDG/DifferentialForms/Simplicial.lean` | 单纯形面映射 `faceMap i = i.succAbove` |
| `SDG/DifferentialForms/StokesCup.lean` | 分次 Leibniz（cup 层）、cochainLenCast、cupProduct_isCocycle |
| `SDG/DifferentialForms/CupAssoc.lean` | cupProduct 结合律（cupProduct_assoc） |
| `SDG/DifferentialForms/CupCohomology.lean` | Hⁿ 商层 cup（deRhamCup，双线性+结合律）、H-度数 transport |
| `SDG/DifferentialForms/CohomologyModule.lean` | 双侧 Module R 结构（ModuleCon 路线）、配对 R-双线性 |
| `SDG/DifferentialForms/Currents.lean` | 电流层：拓扑/紧支撑、电流空间、∂²=0、Stokes 配对、Hₙ |
| `SDG/DifferentialForms/Integration.lean` | 区间积分、FTC、原函数 |
| `SDG/FinSumProd.lean` | 无选择 `finSum`/`finProd` 及其拆分/重排/配对引理 |
| `SDG/AuditSweep.lean` | **111 条核心声明批量 `#print axioms` 审计** |

## 数学成果总览

### A. 单纯上闭链层（Algebra.lean，2026-09 ~ 10）

1. **构造性置换代数**：`FinPerm n` 编码、逆与双射性、逆序数、`permSum`
2. **相邻对换与求和重排**：`finSum_swapFinAdj`（无选择求和对换不变）
3. **楔积 E0-E3 全套**：`wedgeOneOne`/`wedgeOneAny` 交错性、分次交换律 `wedgeAny_grad_comm`
4. **上闭链 de Rham 复形**：`Cochain R X n`、`∂`（面删除交错和）、
   **`∂² = 0`**（`coboundary_coboundary`）、`∂(cochainOfFun f) = d₀ f`
5. **cup 积**：`cupProduct`（Alexander-Whitney 型）、双线性、**结合律**
   `cupProduct_assoc`、单位律 `cupProduct_unit_left/right`
6. **分次 Leibniz**：`coboundary_cup_product`（∂(c₁∪c₂) = (∂c₁)∪c₂ + (−1)^|c₁| c₁∪(∂c₂)）
7. **cup 上同调**：`cupProduct_isCocycle`（cup 保上闭链）

### B. 同调层（Currents.lean + CupCohomology.lean + CohomologyModule.lean）

1. **Hⁿ 商群**：`deRhamCon`（AddCon 路线）→ `deRhamCohomology`（AddCommGroup）
2. **Hₙ 电流同调**：`currentCon` → `currentHomology`（AddCommGroup）
3. **双侧 Module R**：`ModuleCon` 路线 → `instModuleDeRhamCohomology`/`instModuleCurrentHomology`
4. **商层 cup**：`deRhamCup`（双线性+结合律）、`deRhamCup_add/smul`
5. **H 层度数 transport**：`cocyclesCast`/`deRhamCohomologyCast`
6. **类层配对**：`deRhamPairing`（Hₙ × Hⁿ → R，R-双线性）
7. **Stokes 配对**：`chainCurrent_boundary_apply`、`currentBoundary_currentBoundary`（∂²=0）

### C. 积分层（Integration.lean + ScratchR.lean）

1. **区间积分**：`integralR`（线性/区间可加/基本恒等式/step/sderiv）
2. **FTC**：`integral_ftc_UI`（微积分基本定理 UnitInterval 版）
3. **分部积分**：`integral_I_mul_parts` + `integral_I_parts`（经典对称形）
4. **单形积分**：`simplexIntegral2`（n=2 叠代积分 + 加法/数乘）

### D. 场变元代数层（AlgebraicForms.lean + LieBracket.lean，2026-10-27 ~ 11-07）

1. **李括号**（Kock I.9 Property W 路线）：无穷小变换交换子经 Property W
   因子化得 `lieBracket`；**反对称性** `lieBracket_antisymm`、
   **交换子公式** `fieldDeriv_lieBracket`：`[ξ,η](f) = ξ(ηf) − η(ξf)`、
   **函数层 Jacobi** `fieldDeriv_jacobi`、**括号是导子**
   `fieldDeriv_lieBracket_mul`、**C∞(X)-线性**
   `fieldDeriv_lieBracket_smul_field`
2. **场导子**：`fieldDeriv`（KL 刻画）+ **线性性全套**
   （`fieldDeriv_add`/`smul`/`sub`/`neg`/`zero_fun`/`zero_field`）+
   **乘积法则** `fieldDeriv_mul` + **可加性突破**
   `directionalDeriv_tangentAdd`（Microlinear R R = KL 全 schema）
3. **Koszul 外微分**：`algD0`（0-形式）、`algD1`（1-形式 Koszul 公式）、
   `algD2`（2-形式三顶点）、`algD3`（3-形式 4-顶点）——对形式变元
   R-线性（`algD1/2/3_add/smul`）
4. **⭐ d² = 0（核心理论闭环）**：
   - **d²|₀**：`algD_d2_zero_form`——`d(d₀f) = 0`（交换子公式直推）
   - **d²|₁**：`algD_d2_one_form`——`d(dω) = 0` 对好形式 ω
     （场可加+零保持+三体折叠三假设 → Koszul 展开 → 函数层 Jacobi）
   - **精确链**：`algD_d2_exact`——`d²(d₀f) = 0` 零假设
   - **三阶链**：`algD_d3_exact`——`d³(d₀f) = 0`
5. **楔积与交错化**：`wedge11`（1×1 楔积）、`wedge21`/`wedge12`（2+1/1+2
   插入）、`algTens2`（张量积）、`alt2`（交错化算子）、
   **`wedge11_eq_alt2`**（楔积 = 交错化张量积）、`alt2_antisymm`、
   `alt2_idem`
6. **分次 Leibniz**：`algD1_algSMul_wedge`（d(f·ω) = f·dω + d₀f∧ω，
   核心情形）+ `d_wedge11`（d(α∧ω) = dα∧ω − α∧dω，完整 1×1）
7. **反对称重组**：`algForm2_regroup`（双重括号泛型重组）、
   `lieBracket_neg_smul_left`（括号对 (−1)-缩放齐次性）、
   `algForm1_neg_smul`（形式 −1-线性）、`field_add_neg_smul`（场层 (−1)·φ+φ = 0）
8. **congr-action**：`algForm1_congr_action`（ω 尊重函数作用相等）

### E. 审计基建（AuditSweep.lean）

**111 条核心声明**的批量 `#print axioms` 复核——全部
`[propext, Quot.sound]` 或更少，**零 `Classical.choice`、零 `sorryAx`**。
新增声明追加一行即可复验。

## 统计

| 指标 | 值 |
|---|---|
| 全量构建目标 | 8732 jobs |
| Lean 工具链 | v4.34.0-rc1 |
| Mathlib | v4.34.0-rc1 |
| 核心声明审计 | 111 条全干净 |
| 选择公理依赖 | 零 |
| sorry/admit | 零 |
| 主力模块 | Algebra.lean（~4700 行）、AlgebraicForms.lean（~1500 行） |
| Git 提交 | 60+ |

## 关键工程经验（RESUME.md 详录）

1. **KL 数据必须内联**（`have` 会丢 body 导致 defeq 断裂）
2. **rw 在 λ-绑定下实例化元变量失败**——一律先 rfl-桥统一 β-形
3. **omega 的蕴含假设泄漏 Classical.choice**——前置事实析取化
4. **Pi-层的 `sub_eq_add_neg` 非 defeq**——neg-原子需显式化
5. **结构实例缩进铁律**——字段缩进 = 内层 `{` 缩进 − 2
6. **单文件编译不更新 olean**——探针前必须 `lake build` 目标模块
7. **多会话并行纪律**——编辑前 git status + 读 RESUME 顶条

## 构建

```bash
lake build          # 全量构建（8732 目标）
lake env lean SDG/AuditSweep.lean   # 111 条核心声明 axiom 审计
lake env lean SDG/TestNoChoice.lean # 无选择公理自检
```

## 分支与 PR

- 工作分支 `feature/differential-forms-core`，PR：
  <https://github.com/cao-jia-rong/SDG/pull/2>（自 fork
  [GuitarYuu/SDG](https://github.com/GuitarYuu/SDG) 发起）
- 断点续作检查点：`RESUME.md`（含 62 个接力点的完整工程日志）

## 后续路线图

1. **d²|₂**（任意 2-形式 α 的 algD3 (algD2 α) = 0）——WIP 存档，
   hpair-架构 + 全部桥就绪，差 halt-桥精调
2. **场变元楔积一般 p×q 分次 Leibniz**——alt2-交错化模板已立
3. **current-Stokes 定理**——路径-电流模型
4. **参数化单形积分 n≥3** + Fubini
5. **商层分次交换律**（shuffle-cup）
6. **Čech 上同调、de Rham 同构**的 SDG 版本
