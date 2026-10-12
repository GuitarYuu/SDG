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
#print axioms SDG.DifferentialForms.affine_path_mem_Icc
#print axioms SDG.DifferentialForms.IntegralCurrent.apply
#print axioms SDG.DifferentialForms.IntegralCurrent.apply_add
#print axioms SDG.DifferentialForms.IntegralCurrent.apply_smul
#print axioms SDG.DifferentialForms.IntegralCurrent.apply_congr_on
#print axioms SDG.DifferentialForms.IntegralCurrent.apply_congr_density
#print axioms SDG.DifferentialForms.IntegralCurrent.hasCompactSupport

end SDG.DifferentialForms
