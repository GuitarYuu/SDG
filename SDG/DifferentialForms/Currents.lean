import SDG.DifferentialForms.Algebra
import SDG.Order
import SDG.Integration

/-!
# SDG.DifferentialForms.Currents

电流（currents）层：拓扑/紧支撑结构与电流空间。

本模块为 de Rham 型电流理论提供无选择公理的基础设施，分三部分：

* **拓扑/紧支撑结构**（section `Support`）：
  - `SupportsIn`：函数支撑含于一个谓词承载集（「在承载集外逐点为零」的
    构造性表述，无需闭包/补集运算）；
  - `CompactFamily`：抽象紧集族类——「紧」子集谓词 + 空集紧 + 有限并封闭，
    这是 currents 理论所需的全部拓扑公理；
  - `HasCompactSupport`：紧支撑函数，对加法/取负/数乘封闭，打包为
    `compactSupportedFuns` R-子模；严格形式层同样成立
    （`SupportsInForm`/`HasCompactSupportForm`/`compactSupportedForms`）；
  - `IsCompactOrder`：R 上紧性的具体化——预序的有向性（下有向/上有向）
    公理，由此得 `CompactFamily R` 实例、区间紧性 `compactFamily_Icc` 与
    紧支撑的区间刻画 `hasCompactSupport_iff_interval`。

* **电流主层**（section `Currents`）：电流 = 上链空间上的 R-线性泛函
  `Current R X n := Cochain R X n →ₗ[R] R`；对偶边界算子
  `currentBoundary T c = T (coboundary c)`（次数降一），其 ∂² = 0
  是里程碑 D2（`coboundary_coboundary`）的直接对偶推论；单纯形链电流
  `evalCochain σ`（在 σ 处求值）与加权单纯形族电流 `chainCurrent`，
  以及 Stokes 配对恒等式（Fubini 换序 `finSum_sum_comm`）。

* **积分电流**（section `IntegralCurrents`）：紧支撑「密度」连同其承载
  区间定义的积分电流 `f ↦ ∫ f·density`，对测试函数 f 线性；只依赖承载
  区间内的行为（`IntegralCurrent.apply_congr_on`）。区间捆绑进数据：
  SDG 预序下「紧支撑积分与承载区间选取无关」需单点质量为零的进一步
  论证，此处不作声称。

全部声明通过 `linter.noAxiomOfChoice` 审计（仅依赖 `[propext, Quot.sound]`）。
-/

namespace SDG.DifferentialForms

/-! ## 拓扑/紧支撑结构 -/

section Support

variable {R : Type u} [CommRing R] {X : Type u}

/-- **支撑含于承载集**：`f` 在 `S` 外逐点为零。
（构造性表述：对任意类型 `X` 有意义，不依赖拓扑结构。） -/
def SupportsIn (S : X → Prop) (f : X → R) : Prop := ∀ x : X, ¬ S x → f x = 0

/-- 承载集放大则支撑包含关系保持。 -/
theorem supportsIn_mono {S T : X → Prop} (hST : ∀ x, S x → T x) {f : X → R}
    (h : SupportsIn S f) : SupportsIn T f :=
  fun x hx => h x (fun hs => hx (hST x hs))

/-- 承载集为有限并时和函数的支撑估计。 -/
theorem supportsIn_add {S T : X → Prop} {f g : X → R}
    (hf : SupportsIn S f) (hg : SupportsIn T g) :
    SupportsIn (fun x => S x ∨ T x) (f + g) := by
  intro x hx
  have hfx : f x = 0 := hf x (fun hs => hx (Or.inl hs))
  have hgx : g x = 0 := hg x (fun ht => hx (Or.inr ht))
  rw [Pi.add_apply, hfx, hgx]
  exact zero_add 0

/-- 取负保持支撑。 -/
theorem supportsIn_neg {S : X → Prop} {f : X → R} (hf : SupportsIn S f) :
    SupportsIn S (-f) := by
  intro x hx
  rw [Pi.neg_apply, hf x hx]
  exact neg_zero

/-- 数乘保持支撑。 -/
theorem supportsIn_smul (a : R) {S : X → Prop} {f : X → R} (hf : SupportsIn S f) :
    SupportsIn S (a • f) := by
  intro x hx
  rw [Pi.smul_apply, hf x hx]
  exact smul_zero a

/-! ### 抽象紧集族 -/

/-- **抽象紧集族**：类型 `X` 上的「紧」子集谓词，具有 currents 理论所需的
最小封闭性质：空集紧、有限并紧。

这是本项目的拓扑层接口：不预设 `X` 上的拓扑结构，只要求「紧」这个谓词
对有限并封闭（紧支撑函数对加法封闭的唯一所需性质）。具体到光滑直线
`R`，见 `IsCompactOrder`。 -/
class CompactFamily (X : Type v) where
  Compact : (X → Prop) → Prop
  compact_empty : Compact (fun _ : X => False)
  compact_union : ∀ (S T : X → Prop), Compact S → Compact T → Compact (fun x => S x ∨ T x)

/-- **紧支撑**：支撑含于某个紧集。 -/
def HasCompactSupport [CompactFamily X] (f : X → R) : Prop :=
  ∃ S : X → Prop, CompactFamily.Compact S ∧ SupportsIn S f

/-- 紧支撑函数对加法封闭（有限并紧）。 -/
theorem HasCompactSupport.add [CompactFamily X] {f g : X → R}
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) : HasCompactSupport (f + g) := by
  obtain ⟨S, hS, hSf⟩ := hf
  obtain ⟨T, hT, hTg⟩ := hg
  exact ⟨fun x => S x ∨ T x, CompactFamily.compact_union S T hS hT, supportsIn_add hSf hTg⟩

/-- 零函数紧支撑。 -/
theorem HasCompactSupport.zero [CompactFamily X] : HasCompactSupport (0 : X → R) :=
  ⟨fun _ => False, CompactFamily.compact_empty, fun _ _ => rfl⟩

/-- 紧支撑函数对取负封闭。 -/
theorem HasCompactSupport.neg [CompactFamily X] {f : X → R}
    (hf : HasCompactSupport f) : HasCompactSupport (-f) := by
  obtain ⟨S, hS, hSf⟩ := hf
  exact ⟨S, hS, supportsIn_neg hSf⟩

/-- 紧支撑函数对数乘封闭。 -/
theorem HasCompactSupport.smul [CompactFamily X] (a : R) {f : X → R}
    (hf : HasCompactSupport f) : HasCompactSupport (a • f) := by
  obtain ⟨S, hS, hSf⟩ := hf
  exact ⟨S, hS, supportsIn_smul a hSf⟩

/-- 紧支撑函数构成的 `R`-子模。 -/
def compactSupportedFuns [CompactFamily X] : Submodule R (X → R) where
  carrier := {f | HasCompactSupport f}
  add_mem' hf hg := HasCompactSupport.add hf hg
  zero_mem' := HasCompactSupport.zero
  smul_mem' := by
    intro a x hf
    exact HasCompactSupport.smul a hf

/-! ### 严格形式层的紧支撑 -/

section SupportForms

variable [Microlinear R X] {n : ℕ}

/-- 形式的支撑含于承载集：基点在 `S` 外处，形式（作为该基点切空间上的
交错多线性形式）为零。 -/
def SupportsInForm (S : X → Prop) (ω : FiberwiseDifferentialForm R X n) : Prop :=
  ∀ x : X, ¬ S x → ω x = 0

/-- 承载集放大则形式的支撑包含关系保持。 -/
theorem supportsInForm_mono {S T : X → Prop} (hST : ∀ x, S x → T x)
    {ω : FiberwiseDifferentialForm R X n} (h : SupportsInForm S ω) : SupportsInForm T ω :=
  fun x hx => h x (fun hs => hx (hST x hs))

/-- 承载集为有限并时形式和的支撑估计。 -/
theorem supportsInForm_add {S T : X → Prop} {ω η : FiberwiseDifferentialForm R X n}
    (hω : SupportsInForm S ω) (hη : SupportsInForm T η) :
    SupportsInForm (fun x => S x ∨ T x) (ω + η) := by
  intro x hx
  have hωx : ω x = 0 := hω x (fun hs => hx (Or.inl hs))
  have hηx : η x = 0 := hη x (fun ht => hx (Or.inr ht))
  rw [Pi.add_apply, hωx, hηx]
  exact zero_add 0

/-- 取负保持形式的支撑。 -/
theorem supportsInForm_neg {S : X → Prop} {ω : FiberwiseDifferentialForm R X n}
    (hω : SupportsInForm S ω) : SupportsInForm S (-ω) := by
  intro x hx
  rw [Pi.neg_apply, hω x hx]
  exact neg_zero

/-- 数乘保持形式的支撑。 -/
theorem supportsInForm_smul (a : R) {S : X → Prop} {ω : FiberwiseDifferentialForm R X n}
    (hω : SupportsInForm S ω) : SupportsInForm S (a • ω) := by
  intro x hx
  rw [Pi.smul_apply, hω x hx]
  exact smul_zero a

/-- **形式紧支撑**：支撑含于某个紧集（严格形式层版本）。 -/
def HasCompactSupportForm [CompactFamily X] (ω : FiberwiseDifferentialForm R X n) : Prop :=
  ∃ S : X → Prop, CompactFamily.Compact S ∧ SupportsInForm S ω

/-- 形式紧支撑对加法封闭。 -/
theorem HasCompactSupportForm.add [CompactFamily X]
    {ω η : FiberwiseDifferentialForm R X n}
    (hω : HasCompactSupportForm ω) (hη : HasCompactSupportForm η) :
    HasCompactSupportForm (ω + η) := by
  obtain ⟨S, hS, hSω⟩ := hω
  obtain ⟨T, hT, hTη⟩ := hη
  exact ⟨fun x => S x ∨ T x, CompactFamily.compact_union S T hS hT,
    supportsInForm_add hSω hTη⟩

/-- 零形式紧支撑。 -/
theorem HasCompactSupportForm.zero [CompactFamily X] :
    HasCompactSupportForm (0 : FiberwiseDifferentialForm R X n) :=
  ⟨fun _ => False, CompactFamily.compact_empty, fun _ _ => rfl⟩

/-- 形式紧支撑对取负封闭。 -/
theorem HasCompactSupportForm.neg [CompactFamily X]
    {ω : FiberwiseDifferentialForm R X n} (hω : HasCompactSupportForm ω) :
    HasCompactSupportForm (-ω) := by
  obtain ⟨S, hS, hSω⟩ := hω
  exact ⟨S, hS, supportsInForm_neg hSω⟩

/-- 形式紧支撑对数乘封闭。 -/
theorem HasCompactSupportForm.smul [CompactFamily X] (a : R)
    {ω : FiberwiseDifferentialForm R X n} (hω : HasCompactSupportForm ω) :
    HasCompactSupportForm (a • ω) := by
  obtain ⟨S, hS, hSω⟩ := hω
  exact ⟨S, hS, supportsInForm_smul a hSω⟩

/-- 紧支撑形式构成的 `R`-子模（严格形式层）。 -/
def compactSupportedForms [CompactFamily X] (n : ℕ) :
    Submodule R (FiberwiseDifferentialForm R X n) where
  carrier := {ω | HasCompactSupportForm ω}
  add_mem' hω hη := HasCompactSupportForm.add hω hη
  zero_mem' := HasCompactSupportForm.zero
  smul_mem' := by
    intro a x hf
    exact HasCompactSupportForm.smul a hf

end SupportForms

/-! ### `R` 上紧性的具体化 -/

/-- **紧序公理**（在 `IsSDGOrder` 之上的温和加强）：预序**下有向**与
**上有向**——任意两元素有公共下界与公共上界。

在经典实直线上显然成立（取 min/max）；在 SDG 的预序（无反对称、无线性、
无格结构）中它是独立的温和假设。它使得「序有界集」构成紧集族，从而
支撑在闭区间内的函数成为紧支撑函数。 -/
class IsCompactOrder (R : Type u) extends SDG.Order.IsSDGOrder R where
  directedDown : ∀ x y : R, ∃ m : R, m ≤ x ∧ m ≤ y
  directedUp : ∀ x y : R, ∃ M : R, x ≤ M ∧ y ≤ M

/-- 有界集构成 `R` 的紧集族（由有向性合并界）。 -/
instance instCompactFamilyR {R : Type u} [IsCompactOrder R] : CompactFamily R where
  Compact S := ∃ a b : R, ∀ x : R, S x → a ≤ x ∧ x ≤ b
  compact_empty := ⟨0, 0, fun _ hx => hx.elim⟩
  compact_union S T hS hT := by
    obtain ⟨af, bf, hSb⟩ := hS
    obtain ⟨ag, bg, hTb⟩ := hT
    obtain ⟨A, hA1, hA2⟩ := IsCompactOrder.directedDown af ag
    obtain ⟨B, hB1, hB2⟩ := IsCompactOrder.directedUp bf bg
    refine ⟨A, B, fun x hx => ?_⟩
    rcases hx with hs | ht
    · obtain ⟨h1, h2⟩ := hSb x hs
      exact ⟨hA1.trans h1, h2.trans hB1⟩
    · obtain ⟨h1, h2⟩ := hTb x ht
      exact ⟨hA2.trans h1, h2.trans hB2⟩

/-- 闭区间 `[a, b]` 是紧集。 -/
theorem compactFamily_Icc {R : Type u} [IsCompactOrder R] (a b : R) :
    CompactFamily.Compact (Set.Icc a b) := ⟨a, b, fun _ hx => Set.mem_Icc.mp hx⟩

/-- `R` 上紧支撑的区间刻画：紧支撑当且仅当在某个闭区间外逐点为零。 -/
theorem hasCompactSupport_iff_interval {R : Type u} [IsCompactOrder R] (f : R → R) :
    HasCompactSupport f ↔ ∃ a b : R, ∀ x : R, ¬ (a ≤ x ∧ x ≤ b) → f x = 0 := by
  constructor
  · rintro ⟨S, ⟨a, b, hb⟩, hS⟩
    exact ⟨a, b, fun x hx => hS x (fun hs => hx (hb x hs))⟩
  · rintro ⟨a, b, h⟩
    exact ⟨Set.Icc a b, compactFamily_Icc a b,
      fun x hx => h x (fun hmem => hx (Set.mem_Icc.mpr hmem))⟩

end Support

/-! ## 电流主层 -/

section Currents

variable {R : Type u} [CommRing R] {X : Type u} {n : ℕ}

/-! ### 上边界的线性打包 -/

/-- `coboundary` 的线性打包：`Cochain R X n →ₗ[R] Cochain R X (n+1)`。 -/
def coboundaryLinear : Cochain R X n →ₗ[R] Cochain R X (n + 1) where
  toFun := coboundary
  map_add' := by
    intro a b
    funext σ
    have hpt : ∀ i : Fin (n + 2),
        (-1 : R) ^ (i : ℕ) * (a + b) (coFace σ i)
          = (-1 : R) ^ (i : ℕ) * (a (coFace σ i) + b (coFace σ i)) :=
      fun i => by
        rw [show (a + b) (coFace σ i) = a (coFace σ i) + b (coFace σ i) from rfl]
    have h : coboundary (a + b) σ
        = finSum R (n + 2) (fun i : Fin (n + 2) =>
            (-1 : R) ^ (i : ℕ) * (a (coFace σ i) + b (coFace σ i))) :=
      finSum_congr R hpt
    have h2 : finSum R (n + 2) (fun i : Fin (n + 2) =>
        (-1 : R) ^ (i : ℕ) * (a (coFace σ i) + b (coFace σ i)))
        = finSum R (n + 2) (fun i : Fin (n + 2) => (-1 : R) ^ (i : ℕ) * a (coFace σ i))
          + finSum R (n + 2) (fun i : Fin (n + 2) => (-1 : R) ^ (i : ℕ) * b (coFace σ i)) :=
      (finSum_congr R (fun i =>
        mul_add ((-1 : R) ^ (i : ℕ)) (a (coFace σ i)) (b (coFace σ i)))).trans
      (finSum_add R (n + 2) (fun i : Fin (n + 2) => (-1 : R) ^ (i : ℕ) * a (coFace σ i))
        (fun i : Fin (n + 2) => (-1 : R) ^ (i : ℕ) * b (coFace σ i)))
    rw [h, h2,
      show (coboundary a + coboundary b) σ = coboundary a σ + coboundary b σ from rfl,
      coboundary_apply, coboundary_apply]
  map_smul' := by
    intro r a
    funext σ
    have hpt : ∀ i : Fin (n + 2),
        (-1 : R) ^ (i : ℕ) * (r • a) (coFace σ i)
          = r * ((-1 : R) ^ (i : ℕ) * a (coFace σ i)) := by
      intro i
      rw [show (r • a) (coFace σ i) = r * a (coFace σ i) from by
        rw [Pi.smul_apply, smul_eq_mul], mul_left_comm]
    have h : coboundary (r • a) σ
        = finSum R (n + 2) (fun i : Fin (n + 2) =>
            r * ((-1 : R) ^ (i : ℕ) * a (coFace σ i))) :=
      finSum_congr R hpt
    rw [h, show ((RingHom.id R) r • coboundary a) σ = r * coboundary a σ from by
      simp [coboundary_apply, smul_eq_mul]]
    exact finSum_mul_left R (n + 2) r
      (fun i : Fin (n + 2) => (-1 : R) ^ (i : ℕ) * a (coFace σ i))

@[simp]
theorem coboundaryLinear_apply (c : Cochain R X n) :
    coboundaryLinear c = coboundary c := rfl

/-! ### 电流空间与对偶边界 -/

/-- **电流**：`n` 次上链空间上的 `R`-线性泛函（de Rham 型电流）。 -/
abbrev Current (R : Type u) [CommRing R] (X : Type u) (n : ℕ) : Type u :=
  Cochain R X n →ₗ[R] R

/-- **对偶边界**：`∂T(ω) := T(∂ω)`（次数降一；Stokes 配对公式）。 -/
def currentBoundary (T : Current R X (n + 1)) : Current R X n :=
  T.comp coboundaryLinear

@[simp]
theorem currentBoundary_apply (T : Current R X (n + 1)) (c : Cochain R X n) :
    currentBoundary T c = T (coboundary c) := rfl

theorem currentBoundary_zero : currentBoundary (0 : Current R X (n + 1)) = 0 := by
  ext c
  simp [currentBoundary_apply]

theorem currentBoundary_add (T S : Current R X (n + 1)) :
    currentBoundary (T + S) = currentBoundary T + currentBoundary S := by
  ext c
  simp [currentBoundary_apply]

theorem currentBoundary_smul (a : R) (T : Current R X (n + 1)) :
    currentBoundary (a • T) = a • currentBoundary T := by
  ext c
  simp [currentBoundary_apply]

/-- 对偶边界算子的线性打包。 -/
def currentBoundaryLinear :
    Current R X (n + 1) →ₗ[R] Current R X n where
  toFun := currentBoundary
  map_add' := currentBoundary_add
  map_smul' := currentBoundary_smul

/-- **电流的对偶边界满足 ∂² = 0**：里程碑 D2（`coboundary_coboundary`）的
直接对偶推论——`∂(∂T)(c) = T(∂∂c) = T(0) = 0`。 -/
theorem currentBoundary_currentBoundary (T : Current R X (n + 2)) :
    currentBoundary (currentBoundary T) = 0 := by
  ext c
  simp [currentBoundary_apply, coboundary_coboundary]

/-! ### 单纯形链电流 -/

/-- **初等链电流** `[σ]`：在单纯形 `σ` 处求值的电流。 -/
def evalCochain (σ : SimplexPts X n) : Current R X n where
  toFun := fun c => c σ
  map_add' := fun _a _b => rfl
  map_smul' := fun _r _a => rfl

@[simp]
theorem evalCochain_apply (σ : SimplexPts X n) (c : Cochain R X n) :
    evalCochain σ c = c σ := rfl

/-- **加权单纯形族电流**：`C = Σ_i w_i · [σs i]`。 -/
def chainCurrent {m : ℕ} (σs : Fin m → SimplexPts X n) (w : Fin m → R) :
    Current R X n where
  toFun := fun c => finSum R m (fun i => w i * c (σs i))
  map_add' := fun a b => by
    show finSum R m (fun i : Fin m => w i * (a + b) (σs i))
        = finSum R m (fun i : Fin m => w i * a (σs i))
          + finSum R m (fun i : Fin m => w i * b (σs i))
    have h : finSum R m (fun i : Fin m => w i * (a + b) (σs i))
        = finSum R m (fun i : Fin m => w i * a (σs i) + w i * b (σs i)) :=
      finSum_congr R (fun i => mul_add (w i) (a (σs i)) (b (σs i)))
    rw [h]
    exact finSum_add R m (fun i : Fin m => w i * a (σs i))
      (fun i : Fin m => w i * b (σs i))
  map_smul' := fun r a => by
    show finSum R m (fun i : Fin m => w i * (r • a) (σs i))
        = r • finSum R m (fun i : Fin m => w i * a (σs i))
    have h : finSum R m (fun i : Fin m => w i * (r • a) (σs i))
        = finSum R m (fun i : Fin m => r * (w i * a (σs i))) :=
      finSum_congr R (fun i => by rw [Pi.smul_apply, smul_eq_mul, mul_left_comm])
    rw [h, show (r • finSum R m (fun i : Fin m => w i * a (σs i)))
        = r * finSum R m (fun i : Fin m => w i * a (σs i)) from by rw [smul_eq_mul]]
    exact finSum_mul_left R m r (fun i : Fin m => w i * a (σs i))

@[simp]
theorem chainCurrent_apply {m : ℕ} (σs : Fin m → SimplexPts X n) (w : Fin m → R)
    (c : Cochain R X n) :
    chainCurrent σs w c = finSum R m (fun i => w i * c (σs i)) := rfl

/-- **Stokes 配对恒等式（Fubini 展开式）**：`⟨∂C, c⟩` 对链权与面指标的双和
可换序——换序引擎为 `finSum_sum_comm`。 -/
theorem chainCurrent_boundary_apply {m : ℕ}
    (σs : Fin m → SimplexPts X (n + 1)) (w : Fin m → R) (c : Cochain R X n) :
    currentBoundary (chainCurrent σs w) c
      = finSum R (n + 2) (fun j : Fin (n + 2) => (-1 : R) ^ (j : ℕ) *
          finSum R m (fun i => w i * c (coFace (σs i) j))) := by
  rw [currentBoundary_apply, chainCurrent_apply]
  have hstep : ∀ i : Fin m,
      w i * coboundary c (σs i)
        = w i * finSum R (n + 2) (fun j : Fin (n + 2) =>
            (-1 : R) ^ (j : ℕ) * c (coFace (σs i) j)) :=
    fun i => congrArg (fun x => w i * x) (coboundary_apply c (σs i))
  have h2 : finSum R m (fun i : Fin m => w i * coboundary c (σs i))
      = finSum R m (fun i : Fin m => w i * finSum R (n + 2) (fun j : Fin (n + 2) =>
          (-1 : R) ^ (j : ℕ) * c (coFace (σs i) j))) :=
    finSum_congr R hstep
  have h3 : finSum R m (fun i : Fin m => w i * finSum R (n + 2) (fun j : Fin (n + 2) =>
      (-1 : R) ^ (j : ℕ) * c (coFace (σs i) j)))
      = finSum R m (fun i : Fin m => finSum R (n + 2) (fun j : Fin (n + 2) =>
          w i * ((-1 : R) ^ (j : ℕ) * c (coFace (σs i) j)))) :=
    finSum_congr R (fun i =>
      (finSum_mul_left R (n + 2) (w i)
        (fun j : Fin (n + 2) => (-1 : R) ^ (j : ℕ) * c (coFace (σs i) j))).symm)
  have h4 : finSum R m (fun i : Fin m => finSum R (n + 2) (fun j : Fin (n + 2) =>
      w i * ((-1 : R) ^ (j : ℕ) * c (coFace (σs i) j))))
      = finSum R (n + 2) (fun j : Fin (n + 2) => finSum R m (fun i : Fin m =>
          w i * ((-1 : R) ^ (j : ℕ) * c (coFace (σs i) j)))) :=
    finSum_sum_comm R m (n + 2)
      (fun i j => w i * ((-1 : R) ^ (j : ℕ) * c (coFace (σs i) j)))
  rw [h2, h3, h4]
  have hring : ∀ (j : Fin (n + 2)) (i : Fin m),
      w i * ((-1 : R) ^ (j : ℕ) * c (coFace (σs i) j))
        = (-1 : R) ^ (j : ℕ) * (w i * c (coFace (σs i) j)) := by
    intro j i
    ring
  have h5 : ∀ j : Fin (n + 2),
      finSum R m (fun i : Fin m => w i * ((-1 : R) ^ (j : ℕ) * c (coFace (σs i) j)))
        = (-1 : R) ^ (j : ℕ) * finSum R m (fun i : Fin m => w i * c (coFace (σs i) j)) :=
    fun j => (finSum_congr R (hring j)).trans
      (finSum_mul_left R m ((-1 : R) ^ (j : ℕ))
        (fun i : Fin m => w i * c (coFace (σs i) j)))
  exact finSum_congr R h5

/-- 初等链电流的边界在单纯形 `σ` 上的求值 = 上边界的逐面和（rfl）。 -/
theorem evalCochain_boundary_apply (σ : SimplexPts X (n + 1)) (c : Cochain R X n) :
    currentBoundary (evalCochain σ) c
      = finSum R (n + 2) (fun i : Fin (n + 2) => (-1 : R) ^ (i : ℕ) * c (coFace σ i)) := by
  simp only [currentBoundary_apply, evalCochain_apply, coboundary_apply]

/-- **初等链的边界是加权面链**：`∂[σ] = Σ_i (-1)^i [∂_i σ]`（作为电流的等式）。 -/
theorem evalCochain_boundary_eq_family (σ : SimplexPts X (n + 1)) :
    currentBoundary (evalCochain σ)
      = chainCurrent (fun i : Fin (n + 2) => coFace σ i)
          (fun i : Fin (n + 2) => (-1 : R) ^ (i : ℕ)) := by
  ext c
  simp [currentBoundary_apply, evalCochain_apply, coboundary_apply, chainCurrent_apply]

/-- 链电流的 ∂² = 0（`currentBoundary_currentBoundary` 的特例）。 -/
theorem chainCurrent_boundary_boundary {m : ℕ}
    (σs : Fin m → SimplexPts X (n + 2)) (w : Fin m → R) :
    currentBoundary (currentBoundary (chainCurrent σs w)) = 0 :=
  currentBoundary_currentBoundary _

end Currents

/-! ## 同调层：循环/边缘与配对的适定性 -/

section Homology

variable {R : Type u} [CommRing R] {X : Type u} {n : ℕ}

/-- **链循环**：对偶边界为零的电流（电流链复形的闭链）。 -/
def IsChainCycle (T : Current R X (n + 1)) : Prop := currentBoundary T = 0

/-- **链边缘**：是某个电流的对偶边界（电流同调中的零类）。 -/
def IsChainBoundary (T : Current R X (n + 1)) : Prop :=
  ∃ S : Current R X (n + 2), currentBoundary S = T

/-- **上循环**：上边界为零的上链（de Rham 复形的闭形式链）。 -/
def IsCocycle (c : Cochain R X n) : Prop := coboundary c = 0

/-- **上边缘**：是某个上链的上边界（恰当形式链）。 -/
def IsCoboundary (c : Cochain R X (n + 1)) : Prop :=
  ∃ b : Cochain R X n, coboundary b = c

/-- 链边缘必是链循环：∂² = 0（电流侧）。 -/
theorem IsChainBoundary.isChainCycle {T : Current R X (n + 1)}
    (h : IsChainBoundary T) : IsChainCycle T := by
  obtain ⟨S, hS⟩ := h
  show currentBoundary T = 0
  rw [← hS]
  exact currentBoundary_currentBoundary S

/-- 上边缘必是上循环：∂² = 0（上链侧）。 -/
theorem IsCoboundary.isCocycle {c : Cochain R X (n + 1)}
    (h : IsCoboundary c) : IsCocycle c := by
  obtain ⟨b, hb⟩ := h
  show coboundary c = 0
  rw [← hb]
  exact coboundary_coboundary b

/-- **循环电流子模**：链循环对加法、零、数乘封闭。 -/
def chainCycles : Submodule R (Current R X (n + 1)) where
  carrier := {T | currentBoundary T = 0}
  add_mem' ha hb := by
    show currentBoundary (_ + _) = 0
    rw [currentBoundary_add, ha, hb, add_zero]
  zero_mem' := currentBoundary_zero
  smul_mem' := by
    intro r T h
    show currentBoundary (r • T) = 0
    rw [currentBoundary_smul, h, smul_zero]

/-- **上循环子模**：闭形式链对加法、零、数乘封闭。 -/
def cocycles : Submodule R (Cochain R X n) where
  carrier := {c | coboundary c = 0}
  add_mem' ha hb := by
    show coboundary (_ + _) = 0
    rw [← coboundaryLinear_apply, LinearMap.map_add, coboundaryLinear_apply,
      coboundaryLinear_apply, ha, hb, add_zero]
  zero_mem' := by
    show coboundary (0 : Cochain R X n) = 0
    rw [← coboundaryLinear_apply, LinearMap.map_zero]
  smul_mem' := by
    intro r c hc
    show coboundary (r • c) = 0
    rw [← coboundaryLinear_apply, LinearMap.map_smul, coboundaryLinear_apply, hc,
      smul_zero]

/-- **边缘电流与上循环的配对为零**：⟨∂S, c⟩ = S(∂c) = S(0) = 0——
边缘修改不改变配对（第一半）。 -/
theorem currentBoundary_pair_isCocycle (S : Current R X (n + 2))
    (c : Cochain R X (n + 1)) (hc : IsCocycle c) : currentBoundary S c = 0 := by
  rw [currentBoundary_apply, hc, map_zero]

/-- **循环电流与上边缘的配对为零**：⟨T, ∂b⟩ = ⟨∂T, b⟩ = 0——
上边缘修改不改变配对（第二半）。 -/
theorem isChainCycle_pair_coboundary (T : Current R X (n + 1)) (b : Cochain R X n)
    (hT : IsChainCycle T) : T (coboundary b) = 0 := by
  rw [← currentBoundary_apply, hT, LinearMap.zero_apply]

/-- **配对适定性（电流同调 × 上同调）**：循环电流对上循环的配对在
「电流加边缘」与「上链加上边缘」两类修改下不变：
⟨T + ∂S, c + ∂b⟩ = ⟨T, c⟩（T 循环、c 闭）。
这是电流理论的中央恒等式——配对良定义于 Hₙ(currents) × Hⁿ(cochains)。 -/
theorem pairing_cycle_cocycle_congr (T T' : Current R X (n + 1))
    (c c' : Cochain R X (n + 1))
    (hT : IsChainCycle T) (hc : IsCocycle c)
    (hTT' : ∃ S : Current R X (n + 2), T' = T + currentBoundary S)
    (hcc' : ∃ b : Cochain R X n, c' = c + coboundary b) :
    T' c' = T c := by
  obtain ⟨S, rfl⟩ := hTT'
  obtain ⟨b, rfl⟩ := hcc'
  have e1 : ∀ (U : Current R X (n + 1)) (d e : Cochain R X (n + 1)),
      U (d + e) = U d + U e := fun U d e => LinearMap.map_add U d e
  have e2 : ∀ (U V : Current R X (n + 1)) (d : Cochain R X (n + 1)),
      (U + V) d = U d + V d := fun U V d => LinearMap.add_apply U V d
  have hcob : ∀ (d e : Cochain R X (n + 1)),
      coboundary (d + e) = coboundary d + coboundary e := by
    intro d e
    show coboundaryLinear (d + e) = coboundaryLinear d + coboundaryLinear e
    rw [LinearMap.map_add, coboundaryLinear_apply, coboundaryLinear_apply]
  calc (T + currentBoundary S) (c + coboundary b)
      = T c + T (coboundary b)
          + (S (coboundary c) + S (coboundary (coboundary b))) := by
        rw [e2, e1, currentBoundary_apply, hcob, LinearMap.map_add S]
    _ = T c := by
        rw [isChainCycle_pair_coboundary T b hT, hc, map_zero S,
          coboundary_coboundary b, map_zero S]
        ring

end Homology

/-! ## 积分电流 -/

section IntegralCurrents

open SDG.Integration

variable {R : Type u} [IsIntegration R]

/-- 仿射路径含于区间：`a ≤ b` 时 `t ↦ a + t(b-a)`（`t ∈ [0,1]`）落在
`[a, b]` 内。由预序的有向乘法（`mul_nonneg`）与加法单调推出。 -/
theorem affine_path_mem_Icc {R : Type u} [SDG.Order.IsSDGOrder R] (a b : R) (hab : a ≤ b)
    (t : SDG.Order.UnitInterval R) :
    a ≤ a + (t : R) * (b - a) ∧ a + (t : R) * (b - a) ≤ b := by
  obtain ⟨ht1, ht2⟩ := t.2
  have hba : 0 ≤ b - a := by
    have h := SDG.Order.IsSDGOrder.add_le_add_left (R := R) hab (-a)
    have e0 : a + -a = 0 := by ring
    have e1 : b + -a = b - a := by ring
    rw [e0, e1] at h
    exact h
  have h01 : 0 ≤ (1 : R) - (t : R) := by
    have h := SDG.Order.IsSDGOrder.add_le_add_left (R := R) ht2 (-(t : R))
    have e0 : (t : R) + -(t : R) = 0 := by ring
    have e1 : (1 : R) + -(t : R) = (1 : R) - (t : R) := by ring
    rw [e0, e1] at h
    exact h
  have h1 : 0 ≤ (t : R) * (b - a) := SDG.Order.IsSDGOrder.mul_nonneg ht1 hba
  have h2 : 0 ≤ ((1 : R) - (t : R)) * (b - a) := SDG.Order.IsSDGOrder.mul_nonneg h01 hba
  constructor
  · have hge := SDG.Order.IsSDGOrder.add_le_add_left (R := R) h1 a
    rw [zero_add, add_comm] at hge
    exact hge
  · have hsum : ((1 : R) - (t : R)) * (b - a) + (a + (t : R) * (b - a)) = b := by ring
    have hle := SDG.Order.IsSDGOrder.add_le_add_left (R := R) h2 (a + (t : R) * (b - a))
    rw [zero_add, hsum] at hle
    exact hle

/-- **积分电流**：密度 `density` 连同其承载区间 `[left, right]`。

区间捆绑进数据是诚实的工程决策：SDG 预序（`IsSDGOrder` 无反对称/格结构）
下「紧支撑积分与承载区间选取无关」需单点质量为零的进一步论证，本层不作
声称；能严格交付的是——配对只依赖承载区间内的行为
（`IntegralCurrent.apply_congr_on`）。 -/
structure IntegralCurrent (R : Type u) [IsIntegration R] where
  density : R → R
  left : R
  right : R

/-- **配对**：测试函数 `g ↦ ∫_{left}^{right} density · g`（经 `integralR`
的仿射参数化，区间捆绑在数据里）。 -/
def IntegralCurrent.apply (T : IntegralCurrent R) (g : R → R) : R :=
  integralR (fun x => T.density x * g x) T.left T.right

/-- 配对对测试函数可加。 -/
theorem IntegralCurrent.apply_add (T : IntegralCurrent R) (g h : R → R) :
    T.apply (fun x => g x + h x) = T.apply g + T.apply h := by
  have hfun : (fun x : R => T.density x * (g x + h x))
      = (fun x : R => T.density x * g x + T.density x * h x) :=
    funext fun x => mul_add (T.density x) (g x) (h x)
  have hd : T.apply (fun x : R => g x + h x)
      = integralR (fun x : R => T.density x * (g x + h x)) T.left T.right := rfl
  have hg : T.apply g = integralR (fun x : R => T.density x * g x) T.left T.right := rfl
  have hh : T.apply h = integralR (fun x : R => T.density x * h x) T.left T.right := rfl
  rw [hd, hfun, hg, hh]
  exact integralR_add (fun x : R => T.density x * g x) (fun x : R => T.density x * h x)
    T.left T.right

/-- 配对对测试函数的数乘。 -/
theorem IntegralCurrent.apply_smul (T : IntegralCurrent R) (r : R) (g : R → R) :
    T.apply (fun x => r * g x) = r * T.apply g := by
  have hfun : (fun x : R => T.density x * (r * g x))
      = (fun x : R => r * (T.density x * g x)) :=
    funext fun x => mul_left_comm (T.density x) r (g x)
  have hd : T.apply (fun x : R => r * g x)
      = integralR (fun x : R => T.density x * (r * g x)) T.left T.right := rfl
  have hg : T.apply g = integralR (fun x : R => T.density x * g x) T.left T.right := rfl
  rw [hd, hfun, hg]
  exact integralR_smul r (fun x : R => T.density x * g x) T.left T.right

/-- **配对只依赖承载区间内的行为**：`left ≤ right` 且两测试函数在
`[left, right]` 上逐点相等，则配对相等。 -/
theorem IntegralCurrent.apply_congr_on (T : IntegralCurrent R) (g g' : R → R)
    (hab : T.left ≤ T.right)
    (h : ∀ x : R, T.left ≤ x ∧ x ≤ T.right → g x = g' x) :
    T.apply g = T.apply g' := by
  have hfun : (fun t : SDG.Order.UnitInterval R =>
        T.density (T.left + (t : R) * (T.right - T.left))
          * g (T.left + (t : R) * (T.right - T.left)))
      = (fun t : SDG.Order.UnitInterval R =>
        T.density (T.left + (t : R) * (T.right - T.left))
          * g' (T.left + (t : R) * (T.right - T.left))) := by
    funext t
    exact congrArg
      (fun x => T.density (T.left + (t : R) * (T.right - T.left)) * x)
      (h _ (affine_path_mem_Icc T.left T.right hab t))
  have hd : T.apply g = integralR (fun x : R => T.density x * g x) T.left T.right := rfl
  have hd' : T.apply g' = integralR (fun x : R => T.density x * g' x) T.left T.right := rfl
  have hint : integralR (fun x : R => T.density x * g x) T.left T.right
      = integralR (fun x : R => T.density x * g' x) T.left T.right := by
    unfold integralR
    rw [hfun]
  rw [hd, hint, hd']

/-- 配对只依赖密度的全局逐点值（密度的改写）。 -/
theorem IntegralCurrent.apply_congr_density (T : IntegralCurrent R) (f' : R → R)
    (h : ∀ x : R, T.density x = f' x) (g : R → R) :
    T.apply g = IntegralCurrent.apply ⟨f', T.left, T.right⟩ g := by
  have hd : T.apply g = integralR (fun x : R => T.density x * g x) T.left T.right := rfl
  have hd' : IntegralCurrent.apply ⟨f', T.left, T.right⟩ g
      = integralR (fun x : R => f' x * g x) T.left T.right := rfl
  have hfun : (fun x : R => T.density x * g x) = (fun x : R => f' x * g x) :=
    funext fun x => by rw [h x]
  rw [hd, hd', hfun]

/-- 密度在承载区间外为零则密度紧支撑——积分电流层与拓扑/紧支撑层的衔接点。 -/
theorem IntegralCurrent.hasCompactSupport [IsCompactOrder R] (T : IntegralCurrent R)
    (hout : ∀ x : R, ¬ (T.left ≤ x ∧ x ≤ T.right) → T.density x = 0) :
    HasCompactSupport T.density := by
  rw [hasCompactSupport_iff_interval]
  exact ⟨T.left, T.right, hout⟩

end IntegralCurrents

/-! ## 审计 -/

#print axioms SDG.DifferentialForms.HasCompactSupport
#print axioms SDG.DifferentialForms.compactSupportedFuns
#print axioms SDG.DifferentialForms.HasCompactSupportForm
#print axioms SDG.DifferentialForms.compactSupportedForms
#print axioms SDG.DifferentialForms.instCompactFamilyR
#print axioms SDG.DifferentialForms.compactFamily_Icc
#print axioms SDG.DifferentialForms.hasCompactSupport_iff_interval
#print axioms SDG.DifferentialForms.coboundaryLinear
#print axioms SDG.DifferentialForms.currentBoundary
#print axioms SDG.DifferentialForms.currentBoundaryLinear
#print axioms SDG.DifferentialForms.currentBoundary_currentBoundary
#print axioms SDG.DifferentialForms.evalCochain
#print axioms SDG.DifferentialForms.chainCurrent
#print axioms SDG.DifferentialForms.chainCurrent_boundary_apply
#print axioms SDG.DifferentialForms.evalCochain_boundary_eq_family
#print axioms SDG.DifferentialForms.chainCurrent_boundary_boundary
/-! ## de Rham 上同调群 -/

section Cohomology

variable {R : Type u} [CommRing R] {X : Type u}

/-- **上边缘子模**：`∂ : Cⁿ → Cⁿ⁺¹` 的像。手工构造——Mathlib 的
`LinearMap.range` 传递依赖 `Classical.choice`，为通过无选择审计自建。 -/
def coboundaries (n : ℕ) : Submodule R (Cochain R X (n + 1)) where
  carrier := {c | ∃ b : Cochain R X n, coboundary b = c}
  add_mem' := by
    rintro c₁ c₂ ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩
    refine ⟨b₁ + b₂, ?_⟩
    rw [← coboundaryLinear_apply, coboundaryLinear.map_add,
      show coboundaryLinear b₁ = coboundary b₁ from rfl,
      show coboundaryLinear b₂ = coboundary b₂ from rfl, hb₁, hb₂]
  zero_mem' := by
    refine ⟨0, ?_⟩
    rw [← coboundaryLinear_apply, coboundaryLinear.map_zero]
  smul_mem' := by
    rintro r c ⟨b, hb⟩
    refine ⟨r • b, ?_⟩
    rw [← coboundaryLinear_apply, coboundaryLinear.map_smul,
      show coboundaryLinear b = coboundary b from rfl, hb]

@[simp]
theorem mem_coboundaries {n : ℕ} {c : Cochain R X (n + 1)} :
    c ∈ coboundaries n ↔ ∃ b : Cochain R X n, coboundary b = c :=
  Iff.rfl

/-- 上边缘含于上循环：∂² = 0 的子模表述（`IsCoboundary.isCocycle`）。 -/
theorem coboundaries_le_cocycles {n : ℕ} :
    coboundaries (R := R) (X := X) n ≤ cocycles (R := R) (X := X) (n := n + 1) := by
  intro x hx
  rw [mem_coboundaries] at hx
  rcases hx with ⟨b, hb⟩
  exact IsCoboundary.isCocycle ⟨b, hb⟩

/-- 上同调的集合胚：`α ~ β ⟺ α - β ∈ Bⁿ`（差为上边缘）。自建——
`QuotientAddGroup.leftRel` 传递依赖 `Classical.choice`，过不了无选择
审计；纯子模性质的 Setoid 零选择。 -/
def deRhamSetoid (n : ℕ) : Setoid (cocycles (R := R) (X := X) (n := n + 1)) where
  r a b :=
    (a : Cochain R X (n + 1)) - (b : Cochain R X (n + 1)) ∈ coboundaries (R := R) (X := X) n
  iseqv := by
    constructor
    · intro a
      simpa using zero_mem (coboundaries (R := R) (X := X) n)
    · intro a b h
      simpa using neg_mem h
    · intro a b c h₁ h₂
      simpa using add_mem h₁ h₂

/-- 上同调的加法同余关系：`AddCon` 包装——商的加法交换群结构由
Mathlib 的 surjective 搬运 instance（`AddCon.commGroup` 加法版）现成
提供，零 choice。 -/
def deRhamCon (n : ℕ) : AddCon (cocycles (R := R) (X := X) (n := n + 1)) where
  toSetoid := deRhamSetoid (R := R) (X := X) n
  add' := by
    rintro a₁ b₁ a₂ b₂ h₁ h₂
    show (((a₁ + a₂ : Cochain R X (n + 1)) - (b₁ + b₂ : Cochain R X (n + 1))) :
            Cochain R X (n + 1)) ∈ coboundaries (R := R) (X := X) n
    have hab : ((a₁ + a₂ : Cochain R X (n + 1)) - (b₁ + b₂ : Cochain R X (n + 1)) :
            Cochain R X (n + 1))
        = ((a₁ : Cochain R X (n + 1)) - (b₁ : Cochain R X (n + 1)))
          + ((a₂ : Cochain R X (n + 1)) - (b₂ : Cochain R X (n + 1))) := by
      abel
    rw [hab]
    exact add_mem h₁ h₂

/-- **de Rham 上同调群** `Hⁿ := Zⁿ/Bⁿ`：加法同余的商（`AddCon` 商——
其 `AddCommGroup` 结构由底层的函数环加法交换群经商搬运现成提供）。 -/
def deRhamCohomology (n : ℕ) : Type u :=
  (deRhamCon (R := R) (X := X) n).Quotient

instance instAddCommGroupDeRhamCohomology :
    AddCommGroup (deRhamCohomology (R := R) (X := X) n) :=
  inferInstanceAs (AddCommGroup (deRhamCon (R := R) (X := X) n).Quotient)

/-- 上同调类投影：上循环 `α` 的类 `[α] ∈ Hⁿ`。 -/
def deRhamClass {n : ℕ} {α : Cochain R X (n + 1)} (hα : IsCocycle α) :
    deRhamCohomology (R := R) (X := X) n :=
  AddCon.toQuotient ⟨α, hα⟩

/-- 类的良定义：差为上边缘的两个上循环同类。 -/
theorem deRhamClass_eq {n : ℕ} {α β : Cochain R X (n + 1)} (hα : IsCocycle α)
    (hβ : IsCocycle β) (h : α - β ∈ coboundaries (R := R) (X := X) n) :
    deRhamClass hα = deRhamClass hβ :=
  Quotient.sound (by
    show (α - β : Cochain R X (n + 1)) ∈ coboundaries (R := R) (X := X) n
    exact h)

/-- **常值 1 的 0-上链是上循环**：`∂𝟙 = 0`——`[𝟙] ∈ H⁰` 良定义
（与 `CupAssoc.lean` 的 `cochainOne` 定义等价）。 -/
theorem cochainOfFun_one_isCocycle : IsCocycle (cochainOfFun (fun _ : X => (1 : R))) := by
  show coboundary (cochainOfFun (fun _ : X => (1 : R))) = 0
  funext σ
  rw [coboundary_apply]
  simp [cochainOfFun, finSum_two]

/-! ### 电流同调群与配对 -/

/-- 电流边缘子群（Current 层；手工构造——`LinearMap.range` 带
choice，过不了无选择审计）。 -/
theorem currentBoundaryLinear_eq {n : ℕ} (T : Current R X (n + 1)) :
    currentBoundaryLinear (R := R) (X := X) T = currentBoundary T := rfl

def currentBoundariesAdd (n : ℕ) : AddSubgroup (Current R X (n + 1)) where
  carrier := {S | ∃ T : Current R X (n + 2), currentBoundary T = S}
  add_mem' := by
    rintro S₁ S₂ ⟨T₁, hT₁⟩ ⟨T₂, hT₂⟩
    refine ⟨T₁ + T₂, ?_⟩
    rw [← currentBoundaryLinear_eq, currentBoundaryLinear.map_add,
      currentBoundaryLinear_eq, currentBoundaryLinear_eq, hT₁, hT₂]
  zero_mem' := by
    refine ⟨0, ?_⟩
    rw [← currentBoundaryLinear_eq, currentBoundaryLinear.map_zero]
  neg_mem' := by
    rintro S ⟨T, hT⟩
    refine ⟨-T, ?_⟩
    rw [← currentBoundaryLinear_eq, LinearMap.map_neg currentBoundaryLinear T,
      currentBoundaryLinear_eq, hT]

/-- **电流同调的集合胚**：`T ~ U ⟺ T - U ∈ Bₙ`（差为边缘电流）。
定义在循环电流底类型上（循环性由底类型自带）；与 `deRhamSetoid`
完全对偶。 -/
def currentSetoid (n : ℕ) : Setoid (chainCycles (R := R) (X := X) (n := n)) where
  r a b := Subtype.val a - Subtype.val b ∈ currentBoundariesAdd (R := R) (X := X) n
  iseqv := by
    constructor
    · intro a
      simpa using zero_mem (currentBoundariesAdd (R := R) (X := X) n)
    · intro a b h
      simpa using neg_mem h
    · intro a b c h₁ h₂
      simpa using add_mem h₁ h₂

/-- 循环电流的类投影：`[T] ∈ Hₙ`。 -/
def currentClass {n : ℕ} {T : Current R X (n + 1)} (hT : IsChainCycle T) :
    Quotient (currentSetoid (R := R) (X := X) n) :=
  Quotient.mk (currentSetoid (R := R) (X := X) (n := n)) ⟨T, hT⟩

/-- 类的良定义：差为边缘的两个循环电流同类。 -/
theorem currentClass_eq {n : ℕ} {T U : Current R X (n + 1)} (hT : IsChainCycle T)
    (hU : IsChainCycle U) (h : T - U ∈ currentBoundariesAdd (R := R) (X := X) n) :
    currentClass hT = currentClass hU :=
  Quotient.sound (by
    show (T - U : Current R X (n + 1)) ∈ currentBoundariesAdd (R := R) (X := X) n
    exact h)

/-- **配对的类层良定义**：循环电流类与上循环类的配对在代表元选取下
不变——`pairing_cycle_cocycle_congr` 的直接派生。这是 Currents 理论的
收官恒等式：配对 `⟨[T], [c]⟩ := T c` 良定义于 `Hₙ × Hⁿ`。 -/
theorem pairing_class_well_defined {n : ℕ} {T T' : Current R X (n + 1)}
    {c c' : Cochain R X (n + 1)} (_hT : IsChainCycle T) (_hT' : IsChainCycle T')
    (_hc : IsCocycle c) (_hc' : IsCocycle c')
    (hTT' : T - T' ∈ currentBoundariesAdd (R := R) (X := X) n)
    (hcc' : c - c' ∈ coboundaries (R := R) (X := X) n) :
    T' c' = T c := by
  obtain ⟨S, hS⟩ := hTT'
  obtain ⟨b, hb⟩ := hcc'
  refine pairing_cycle_cocycle_congr T T' c c' _hT _hc ⟨-S, ?_⟩ ⟨-b, ?_⟩
  · rw [← currentBoundaryLinear_eq, LinearMap.map_neg currentBoundaryLinear S,
      currentBoundaryLinear_eq, ← sub_eq_add_neg, hS, sub_sub_cancel]
  · rw [← coboundaryLinear_apply, LinearMap.map_neg, coboundaryLinear_apply, hb]
    abel

end Cohomology

#print axioms SDG.DifferentialForms.IsChainCycle
#print axioms SDG.DifferentialForms.IsChainBoundary
#print axioms SDG.DifferentialForms.IsCocycle
#print axioms SDG.DifferentialForms.IsCoboundary
#print axioms SDG.DifferentialForms.IsChainBoundary.isChainCycle
#print axioms SDG.DifferentialForms.IsCoboundary.isCocycle
#print axioms SDG.DifferentialForms.chainCycles
#print axioms SDG.DifferentialForms.cocycles
#print axioms SDG.DifferentialForms.currentBoundary_pair_isCocycle
#print axioms SDG.DifferentialForms.isChainCycle_pair_coboundary
#print axioms SDG.DifferentialForms.pairing_cycle_cocycle_congr
#print axioms SDG.DifferentialForms.affine_path_mem_Icc
#print axioms SDG.DifferentialForms.IntegralCurrent.apply
#print axioms SDG.DifferentialForms.IntegralCurrent.apply_add
#print axioms SDG.DifferentialForms.IntegralCurrent.apply_smul
#print axioms SDG.DifferentialForms.IntegralCurrent.apply_congr_on
#print axioms SDG.DifferentialForms.IntegralCurrent.apply_congr_density
#print axioms SDG.DifferentialForms.IntegralCurrent.hasCompactSupport

#print axioms SDG.DifferentialForms.coboundaries
#print axioms SDG.DifferentialForms.mem_coboundaries
#print axioms SDG.DifferentialForms.coboundaries_le_cocycles
#print axioms SDG.DifferentialForms.deRhamSetoid
#print axioms SDG.DifferentialForms.deRhamCohomology
#print axioms SDG.DifferentialForms.deRhamClass
#print axioms SDG.DifferentialForms.deRhamClass_eq
#print axioms SDG.DifferentialForms.cochainOfFun_one_isCocycle
#print axioms SDG.DifferentialForms.currentSetoid
#print axioms SDG.DifferentialForms.currentClass
#print axioms SDG.DifferentialForms.currentClass_eq
#print axioms SDG.DifferentialForms.pairing_class_well_defined

end SDG.DifferentialForms
