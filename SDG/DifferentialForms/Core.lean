import SDG.NoChoice
import SDG.TangentBundle
import SDG.Derivative
import Mathlib.LinearAlgebra.Alternating.Basic

/-!
# SDG.DifferentialForms

微分形式 (differential forms) 的核心定义。

本模块对应 Kock《Synthetic Differential Geometry》第二版第 I.14 节中
Definition 14.1 的「切向量组」版本：一个 $n$-形式把同基点的 $n$ 个切向量
送到 $R$ 中，并满足对每个变量的齐次性与交错性。本文件先形式化一个
PR 友好的核心骨架：切向量组、规范化/交错/齐次的形式、$0/1/2$-形式别名，
以及 $0$-形式的外微分 $d f$。

完整的单形形式、currents 与 Stokes 定理留给后续模块。 -/

universe u

namespace SDG.DifferentialForms

/-! ## 同基点切向量组 -/

/-- 同一基点处的 $n$ 个切向量。

这正是 Kock Definition 14.1 中 “an n-tuple of tangents with common base point”
的 Lean 编码：`basePoint` 是公共基点，`vector i` 是该点处的第 `i` 个切向量。 -/
structure TangentFrame (R : Type u) [CommRing R] (X : Type u) (n : ℕ) where
  basePoint : X
  vector : Fin n → TangentFiber R X basePoint

namespace TangentFrame

variable {R : Type u} [CommRing R] {X : Type u} {n : ℕ}

/-- 替换切向量组的第 `i` 个分量。 -/
def replace (F : TangentFrame R X n) (i : Fin n)
    (v : TangentFiber R X F.basePoint) : TangentFrame R X n where
  basePoint := F.basePoint
  vector := Function.update F.vector i v

@[simp]
lemma replace_basePoint (F : TangentFrame R X n) (i : Fin n)
    (v : TangentFiber R X F.basePoint) :
    (F.replace i v).basePoint = F.basePoint := rfl

@[simp]
lemma replace_vector_same (F : TangentFrame R X n) (i : Fin n)
    (v : TangentFiber R X F.basePoint) :
    (F.replace i v).vector i = v := by
  simp [replace]

@[simp]
lemma replace_vector_ne (F : TangentFrame R X n) (i j : Fin n)
    (v : TangentFiber R X F.basePoint) (h : j ≠ i) :
    (F.replace i v).vector j = F.vector j := by
  simp [replace, Function.update, h]

/-- 把第 `i` 个分量置为零切向量。 -/
def zeroAt (F : TangentFrame R X n) (i : Fin n) : TangentFrame R X n :=
  F.replace i 0

@[simp]
lemma zeroAt_basePoint (F : TangentFrame R X n) (i : Fin n) :
    (F.zeroAt i).basePoint = F.basePoint := rfl

@[simp]
lemma zeroAt_vector_same (F : TangentFrame R X n) (i : Fin n) :
    (F.zeroAt i).vector i = 0 :=
  F.replace_vector_same i 0

@[simp]
lemma zeroAt_vector_ne (F : TangentFrame R X n) (i j : Fin n) (h : j ≠ i) :
    (F.zeroAt i).vector j = F.vector j := by
  simp [zeroAt, h]

/-- 对第 `i` 个分量做标量乘法。 -/
def smulAt (F : TangentFrame R X n) (i : Fin n) (a : R) : TangentFrame R X n :=
  F.replace i (a • F.vector i)

@[simp]
lemma smulAt_basePoint (F : TangentFrame R X n) (i : Fin n) (a : R) :
    (F.smulAt i a).basePoint = F.basePoint := rfl

@[simp]
lemma smulAt_vector_same (F : TangentFrame R X n) (i : Fin n) (a : R) :
    (F.smulAt i a).vector i = a • F.vector i := by
  simp [smulAt]

@[simp]
lemma smulAt_vector_ne (F : TangentFrame R X n) (i j : Fin n) (a : R) (h : j ≠ i) :
    (F.smulAt i a).vector j = F.vector j := by
  simp [smulAt, h]

/-- 对第 `i` 个分量做切纤维内加法。 -/
def addAt (F : TangentFrame R X n) [Microlinear R X] (i : Fin n)
    (v : TangentFiber R X F.basePoint) : TangentFrame R X n :=
  F.replace i (F.vector i + v)

/-- 由单个切向量得到一元切向量组。 -/
def ofVector {x : X} (v : TangentFiber R X x) : TangentFrame R X 1 where
  basePoint := x
  vector := fun _ ↦ v

@[simp]
lemma ofVector_basePoint {x : X} (v : TangentFiber R X x) :
    (ofVector v).basePoint = x := rfl

@[simp]
lemma ofVector_vector {x : X} (v : TangentFiber R X x) (i : Fin 1) :
    (ofVector v).vector i = v := rfl

/-- 映射 `f` 对切向量的逐点作用。 -/
def mapVector {Y : Type u} (f : X → Y) {x : X} (v : TangentFiber R X x) :
    TangentFiber R Y (f x) where
  val d := f (v.1 d)
  property := by simp [v.2]

@[simp]
lemma mapVector_apply {Y : Type u} (f : X → Y) {x : X}
    (v : TangentFiber R X x) (d : D R) :
    (mapVector f v).1 d = f (v.1 d) := rfl

@[simp]
lemma mapVector_zero {Y : Type u} (f : X → Y) (x : X) :
    mapVector f (0 : TangentFiber R X x) = (0 : TangentFiber R Y (f x)) := by
  apply Subtype.ext
  rfl

@[simp]
lemma mapVector_smul {Y : Type u} (f : X → Y) {x : X}
    (v : TangentFiber R X x) (a : R) :
    mapVector f (a • v) = a • mapVector f v := by
  apply Subtype.ext
  rfl

/-- 映射 `f` 对同基点切向量组的逐点作用。 -/
def map {Y : Type u} (f : X → Y) (F : TangentFrame R X n) :
    TangentFrame R Y n where
  basePoint := f F.basePoint
  vector := fun i ↦ mapVector f (F.vector i)

@[simp]
lemma map_basePoint {Y : Type u} (f : X → Y) (F : TangentFrame R X n) :
    (F.map f).basePoint = f F.basePoint := rfl

@[simp]
lemma map_vector {Y : Type u} (f : X → Y) (F : TangentFrame R X n) (i : Fin n) :
    (F.map f).vector i = mapVector f (F.vector i) := rfl

lemma map_replace {Y : Type u} (f : X → Y) (F : TangentFrame R X n)
    (i : Fin n) (v : TangentFiber R X F.basePoint) :
    (F.replace i v).map f = (F.map f).replace i (mapVector f v) := by
  cases F with
  | mk x vector =>
      change
        ({ basePoint := f x
           vector := fun j ↦ mapVector f ((Function.update vector i v) j) } :
          TangentFrame R Y n) =
        { basePoint := f x
          vector := Function.update (fun j ↦ mapVector f (vector j)) i (mapVector f v) }
      apply congrArg (fun vector' : Fin n → TangentFiber R Y (f x) ↦
        ({ basePoint := f x, vector := vector' } : TangentFrame R Y n))
      funext j
      by_cases h : j = i
      · subst j
        simp [Function.update]
      · simp [Function.update, h]

lemma map_smulAt {Y : Type u} (f : X → Y) (F : TangentFrame R X n)
    (i : Fin n) (a : R) :
    (F.smulAt i a).map f = (F.map f).smulAt i a := by
  change (F.replace i (a • F.vector i)).map f =
    (F.map f).replace i (a • mapVector f (F.vector i))
  simpa [mapVector_smul] using
    (map_replace f F i (a • F.vector i))

lemma map_zeroAt {Y : Type u} (f : X → Y) (F : TangentFrame R X n)
    (i : Fin n) :
    (F.zeroAt i).map f = (F.map f).zeroAt i := by
  change (F.replace i (0 : TangentFiber R X F.basePoint)).map f =
    (F.map f).replace i (0 : TangentFiber R Y (f F.basePoint))
  simpa [mapVector_zero] using
    (map_replace f F i (0 : TangentFiber R X F.basePoint))

end TangentFrame

/-! ## 微分形式：齐次性、交错性与规范化 -/

/-- 原始的 $n$-余切量：从同基点切向量组到标量环 `R` 的函数。 -/
abbrev RawDifferentialForm (R : Type u) [CommRing R] (X : Type u) (n : ℕ) :=
  TangentFrame R X n → R

/-- Kock Definition 14.1 的齐次性条件 (14.1)：每个变量单独数乘时，形式值也相应数乘。 -/
def IsHomogeneous {R : Type u} [CommRing R] {X : Type u} {n : ℕ}
    (ω : RawDifferentialForm R X n) : Prop :=
  ∀ (F : TangentFrame R X n) (i : Fin n) (a : R),
    ω (F.smulAt i a) = a * ω F

/-- 交错性的重复向量版本：若两个不同槽位里的切向量相同，则形式值为零。

完整的置换符号公式 `ω(t_{σ(1)},…,t_{σ(n)}) = sign σ · ω(t_1,…,t_n)`
留给后续外代数基础设施；在核心版中先使用微分形式常用的 “zero on repeated
arguments” 形式。 -/
def IsAlternating {R : Type u} [CommRing R] {X : Type u} {n : ℕ}
    (ω : RawDifferentialForm R X n) : Prop :=
  ∀ (F : TangentFrame R X n) (i j : Fin n),
    i ≠ j → F.vector i = F.vector j → ω F = 0

/-- 规范化条件：任一槽位为零切向量时，形式值为零。 -/
def IsNormalized {R : Type u} [CommRing R] {X : Type u} {n : ℕ}
    (ω : RawDifferentialForm R X n) : Prop :=
  ∀ (F : TangentFrame R X n) (i : Fin n), ω (F.zeroAt i) = 0

/-- 逐槽加法性。该条件使用切纤维上的加法，因此需要 `Microlinear R X`。 -/
def IsAdditiveIn {R : Type u} [CommRing R] {X : Type u} {n : ℕ}
    [Microlinear R X] (ω : RawDifferentialForm R X n) : Prop :=
  ∀ (F : TangentFrame R X n) (i : Fin n)
    (v w : TangentFiber R X F.basePoint),
    ω (F.replace i (v + w)) = ω (F.replace i v) + ω (F.replace i w)

/-- 严格多线性：齐次性加逐槽加法性。 -/
def IsMultilinear {R : Type u} [CommRing R] {X : Type u} {n : ℕ}
    [Microlinear R X] (ω : RawDifferentialForm R X n) : Prop :=
  IsHomogeneous ω ∧ IsAdditiveIn ω

/-- $R$ 值的微分 $n$-形式：齐次、交错且规范化的同基点切向量组函数。 -/
structure DifferentialForm (R : Type u) [CommRing R] (X : Type u) (n : ℕ) where
  toFun : RawDifferentialForm R X n
  homogeneous : IsHomogeneous toFun
  alternating : IsAlternating toFun
  normalized : IsNormalized toFun

instance instCoeFunDifferentialForm {R : Type u} [CommRing R] {X : Type u} {n : ℕ} :
    CoeFun (DifferentialForm R X n) (fun _ ↦ TangentFrame R X n → R) where
  coe ω := ω.toFun

/-- $0$-形式就是函数 `X → R`。 -/
abbrev Differential0Form (R : Type u) [CommRing R] (X : Type u) := X → R

/-- $1$-形式。 -/
abbrev Differential1Form (R : Type u) [CommRing R] (X : Type u) := DifferentialForm R X 1

/-- $2$-形式。 -/
abbrev Differential2Form (R : Type u) [CommRing R] (X : Type u) := DifferentialForm R X 2

namespace DifferentialForm

variable {R : Type u} [CommRing R] {X : Type u} {n : ℕ}

@[simp]
lemma homogeneous_apply (ω : DifferentialForm R X n) (F : TangentFrame R X n)
    (i : Fin n) (a : R) :
    ω (F.smulAt i a) = a * ω F :=
  ω.homogeneous F i a

@[simp]
lemma alternating_apply (ω : DifferentialForm R X n) (F : TangentFrame R X n)
    (i j : Fin n) (hij : i ≠ j) (hEq : F.vector i = F.vector j) :
    ω F = 0 :=
  ω.alternating F i j hij hEq

@[simp]
lemma normalized_apply (ω : DifferentialForm R X n) (F : TangentFrame R X n)
    (i : Fin n) :
    ω (F.zeroAt i) = 0 :=
  ω.normalized F i

/-- 零形式。 -/
instance instZero : Zero (DifferentialForm R X n) where
  zero :=
    { toFun := fun _ ↦ 0
      homogeneous := by intro F i a; simp
      alternating := by intro F i j hij hEq; simp
      normalized := by intro F i; simp }

@[simp]
lemma zero_apply (F : TangentFrame R X n) :
    (0 : DifferentialForm R X n) F = 0 := rfl

/-- 微分形式的逐点加法。 -/
instance instAdd : Add (DifferentialForm R X n) where
  add ω η :=
    { toFun := fun F ↦ ω F + η F
      homogeneous := by
        intro F i a
        change ω.toFun (F.smulAt i a) + η.toFun (F.smulAt i a) =
          a * (ω.toFun F + η.toFun F)
        rw [ω.homogeneous F i a, η.homogeneous F i a]
        ring
      alternating := by
        intro F i j hij hEq
        change ω.toFun F + η.toFun F = 0
        rw [ω.alternating F i j hij hEq, η.alternating F i j hij hEq]
        ring
      normalized := by
        intro F i
        change ω.toFun (F.zeroAt i) + η.toFun (F.zeroAt i) = 0
        rw [ω.normalized F i, η.normalized F i]
        ring }

@[simp]
lemma add_apply (ω η : DifferentialForm R X n) (F : TangentFrame R X n) :
    (ω + η) F = ω F + η F := rfl

/-- 微分形式的逐点取负。 -/
instance instNeg : Neg (DifferentialForm R X n) where
  neg ω :=
    { toFun := fun F ↦ -ω F
      homogeneous := by
        intro F i a
        change -(ω.toFun (F.smulAt i a)) = a * (-(ω.toFun F))
        rw [ω.homogeneous F i a]
        ring
      alternating := by
        intro F i j hij hEq
        change -(ω.toFun F) = 0
        rw [ω.alternating F i j hij hEq]
        ring
      normalized := by
        intro F i
        change -(ω.toFun (F.zeroAt i)) = 0
        rw [ω.normalized F i]
        ring }

@[simp]
lemma neg_apply (ω : DifferentialForm R X n) (F : TangentFrame R X n) :
    (-ω) F = -ω F := rfl

/-- 微分形式的逐点减法。 -/
instance instSub : Sub (DifferentialForm R X n) where
  sub ω η := ω + (-η)

@[simp]
lemma sub_apply (ω η : DifferentialForm R X n) (F : TangentFrame R X n) :
    (ω - η) F = ω F - η F := by
  change ω.toFun F + (-(η.toFun F)) = ω.toFun F - η.toFun F
  rw [sub_eq_add_neg]

/-- 微分形式的标量乘法。 -/
instance instSMul : SMul R (DifferentialForm R X n) where
  smul c ω :=
    { toFun := fun F ↦ c * ω F
      homogeneous := by
        intro F i a
        change c * ω.toFun (F.smulAt i a) = a * (c * ω.toFun F)
        rw [ω.homogeneous F i a]
        ring
      alternating := by
        intro F i j hij hEq
        change c * ω.toFun F = 0
        rw [ω.alternating F i j hij hEq]
        ring
      normalized := by
        intro F i
        change c * ω.toFun (F.zeroAt i) = 0
        rw [ω.normalized F i]
        ring }

@[simp]
lemma smul_apply (c : R) (ω : DifferentialForm R X n) (F : TangentFrame R X n) :
    (c • ω) F = c * ω F := rfl

/-- 把函数看作 $0$-形式。 -/
def ofFunction (f : Differential0Form R X) : DifferentialForm R X 0 where
  toFun := fun F ↦ f F.basePoint
  homogeneous := by intro F i a; exact Fin.elim0 i
  alternating := by intro F i j hij hEq; exact Fin.elim0 i
  normalized := by intro F i; exact Fin.elim0 i

@[simp]
lemma ofFunction_apply (f : Differential0Form R X) (F : TangentFrame R X 0) :
    ofFunction f F = f F.basePoint := rfl

/-- 从 $0$-形式取回普通函数。 -/
def toFunction (ω : DifferentialForm R X 0) : Differential0Form R X :=
  fun x ↦ ω { basePoint := x, vector := fun i ↦ Fin.elim0 i }

@[simp]
lemma toFunction_ofFunction (f : Differential0Form R X) :
    toFunction (ofFunction f) = f := by
  funext x
  rfl

/-- 任意映射沿切向量组逐点拉回形式。 -/
def pullback {Y : Type u} (f : X → Y) (ω : DifferentialForm R Y n) :
    DifferentialForm R X n where
  toFun := fun F ↦ ω (F.map f)
  homogeneous := by
    intro F i a
    change ω.toFun ((F.smulAt i a).map f) = a * ω.toFun (F.map f)
    rw [TangentFrame.map_smulAt]
    exact ω.homogeneous (F.map f) i a
  alternating := by
    intro F i j hij hEq
    apply ω.alternating (F.map f) i j hij
    simp [hEq]
  normalized := by
    intro F i
    change ω.toFun ((F.zeroAt i).map f) = 0
    rw [TangentFrame.map_zeroAt]
    exact ω.normalized (F.map f) i

@[simp]
lemma pullback_apply {Y : Type u} (f : X → Y) (ω : DifferentialForm R Y n)
    (F : TangentFrame R X n) :
    pullback f ω F = ω (F.map f) := rfl

/-- 零形式对任意次数形式的左乘。 -/
def wedgeZeroLeft (f : Differential0Form R X) (ω : DifferentialForm R X n) :
    DifferentialForm R X n where
  toFun := fun F ↦ f F.basePoint * ω F
  homogeneous := by
    intro F i a
    change f F.basePoint * ω.toFun (F.smulAt i a) =
      a * (f F.basePoint * ω.toFun F)
    rw [ω.homogeneous F i a]
    ring
  alternating := by
    intro F i j hij hEq
    change f F.basePoint * ω.toFun F = 0
    rw [ω.alternating F i j hij hEq]
    ring
  normalized := by
    intro F i
    change f F.basePoint * ω.toFun (F.zeroAt i) = 0
    rw [ω.normalized F i]
    ring

@[simp]
lemma wedgeZeroLeft_apply (f : Differential0Form R X)
    (ω : DifferentialForm R X n) (F : TangentFrame R X n) :
    wedgeZeroLeft f ω F = f F.basePoint * ω F := rfl

/-- 零形式对任意次数形式的右乘。 -/
def wedgeZeroRight (ω : DifferentialForm R X n) (f : Differential0Form R X) :
    DifferentialForm R X n :=
  wedgeZeroLeft f ω

@[simp]
lemma wedgeZeroRight_apply (ω : DifferentialForm R X n)
    (f : Differential0Form R X) (F : TangentFrame R X n) :
    wedgeZeroRight ω f F = ω F * f F.basePoint := by
  change f F.basePoint * ω F = ω F * f F.basePoint
  exact mul_comm _ _

end DifferentialForm

/-! ## $0$-形式的外微分 -/

/-- 函数 `f : X → R` 沿切向量 `v` 的方向导数。 -/
def directionalDerivative {R : Type u} {X : Type u} [IsKockLawvere_one R]
    (f : X → R) {x : X} (v : TangentFiber R X x) : R :=
  (IsKockLawvere_one.isKockLawvere_one (fun d : D R ↦ f (v.1 d))).1

/-- 方向导数的 KL 刻画。 -/
theorem directionalDerivative_spec {R : Type u} {X : Type u} [IsKockLawvere_one R]
    (f : X → R) {x : X} (v : TangentFiber R X x) (d : D R) :
    f (v.1 d) = f x + directionalDerivative f (x := x) v * (d : R) := by
  unfold directionalDerivative
  simpa [v.2] using
    (IsKockLawvere_one.isKockLawvere_one (fun d : D R ↦ f (v.1 d))).2.1 d

/-- 零切向量上的方向导数为零。 -/
theorem directionalDerivative_zero {R : Type u} {X : Type u} [IsKockLawvere_one R]
    (f : X → R) (x : X) :
    directionalDerivative f (x := x) (0 : TangentFiber R X x) = 0 := by
  unfold directionalDerivative
  symm
  apply (IsKockLawvere_one.isKockLawvere_one
    (fun d : D R ↦ f ((0 : TangentFiber R X x).1 d))).2.2 0
  intro d
  change f x = f x + 0 * (d : R)
  simp

/-- 方向导数对切向量数乘齐次。 -/
theorem directionalDerivative_smul {R : Type u} {X : Type u} [IsKockLawvere_one R]
    (f : X → R) {x : X} (a : R) (v : TangentFiber R X x) :
    directionalDerivative f (x := x) (a • v) = a * directionalDerivative f (x := x) v := by
  let b : R := directionalDerivative f (x := x) v
  have hspec : ∀ d : D R, f (v.1 d) = f x + b * (d : R) := by
    intro d
    dsimp [b]
    exact directionalDerivative_spec f (x := x) v d
  unfold directionalDerivative
  symm
  apply (IsKockLawvere_one.isKockLawvere_one
    (fun d : D R ↦ f ((a • v).1 d))).2.2 (a * b)
  intro d
  have hv := hspec (a • d)
  have h0 : f ((a • v).1 0) = f x := by
    rw [(a • v).2]
  rw [h0]
  change f (v.1 (a • d)) = f x + (a * b) * (d : R)
  rw [hv]
  change f x + b * (a * (d : R)) = f x + (a * b) * (d : R)
  ring

/-- 方向导数对函数加法满足线性律。 -/
theorem directionalDerivative_add {R : Type u} {X : Type u} [IsKockLawvere_one R]
    (f g : X → R) {x : X} (v : TangentFiber R X x) :
    directionalDerivative (fun y ↦ f y + g y) (x := x) v =
      directionalDerivative f (x := x) v + directionalDerivative g (x := x) v := by
  let b : R := directionalDerivative f (x := x) v
  let c : R := directionalDerivative g (x := x) v
  have hf : ∀ d : D R, f (v.1 d) = f x + b * (d : R) := by
    intro d
    dsimp [b]
    exact directionalDerivative_spec f (x := x) v d
  have hg : ∀ d : D R, g (v.1 d) = g x + c * (d : R) := by
    intro d
    dsimp [c]
    exact directionalDerivative_spec g (x := x) v d
  unfold directionalDerivative
  symm
  apply (IsKockLawvere_one.isKockLawvere_one
    (fun d : D R ↦ f (v.1 d) + g (v.1 d))).2.2 (b + c)
  intro d
  have hfx0 : f (v.1 0) = f x := by rw [v.2]
  have hgx0 : g (v.1 0) = g x := by rw [v.2]
  rw [hf d, hg d, hfx0, hgx0]
  ring

/-- 方向导数对函数标量乘法满足线性律。 -/
theorem directionalDerivative_fun_smul {R : Type u} {X : Type u} [IsKockLawvere_one R]
    (c : R) (f : X → R) {x : X} (v : TangentFiber R X x) :
    directionalDerivative (fun y ↦ c * f y) (x := x) v =
      c * directionalDerivative f (x := x) v := by
  let b : R := directionalDerivative f (x := x) v
  have hf : ∀ d : D R, f (v.1 d) = f x + b * (d : R) := by
    intro d
    dsimp [b]
    exact directionalDerivative_spec f (x := x) v d
  unfold directionalDerivative
  symm
  apply (IsKockLawvere_one.isKockLawvere_one
    (fun d : D R ↦ c * f (v.1 d))).2.2 (c * b)
  intro d
  have hfx0 : f (v.1 0) = f x := by rw [v.2]
  rw [hf d, hfx0]
  ring

/-- 常值函数的方向导数为零。 -/
theorem directionalDerivative_const {R : Type u} {X : Type u} [IsKockLawvere_one R]
    (c : R) {x : X} (v : TangentFiber R X x) :
    directionalDerivative (fun _ : X ↦ c) (x := x) v = 0 := by
  unfold directionalDerivative
  symm
  apply (IsKockLawvere_one.isKockLawvere_one (fun _ : D R ↦ c)).2.2 0
  intro d
  simp

/-- $0$-形式的外微分：`d f` 是一形式，其值为沿给定切向量的方向导数。 -/
def exteriorDerivative0 {R : Type u} {X : Type u} [IsKockLawvere_one R]
    (f : Differential0Form R X) : Differential1Form R X where
  toFun := fun F ↦ directionalDerivative f (x := F.basePoint) (F.vector 0)
  homogeneous := by
    intro F i a
    have hi : i = 0 := Subsingleton.elim i 0
    subst i
    simpa using directionalDerivative_smul f (x := F.basePoint) a (F.vector 0)
  alternating := by
    intro F i j hij hEq
    exact False.elim (hij (Subsingleton.elim i j))
  normalized := by
    intro F i
    have hi : i = 0 := Subsingleton.elim i 0
    subst i
    change directionalDerivative f (x := F.basePoint) ((F.zeroAt 0).vector 0) = 0
    rw [TangentFrame.zeroAt_vector_same]
    exact directionalDerivative_zero f F.basePoint

@[simp]
theorem exteriorDerivative0_apply {R : Type u} {X : Type u} [IsKockLawvere_one R]
    (f : Differential0Form R X) (F : TangentFrame R X 1) :
    exteriorDerivative0 f F = directionalDerivative f (x := F.basePoint) (F.vector 0) := rfl

/-- `d f` 在单个切向量上的值。 -/
theorem exteriorDerivative0_ofVector {R : Type u} {X : Type u} [IsKockLawvere_one R]
    (f : Differential0Form R X) {x : X} (v : TangentFiber R X x) :
    exteriorDerivative0 f (TangentFrame.ofVector v) = directionalDerivative f (x := x) v := by
  rfl

@[simp]
theorem exteriorDerivative0_add_apply {R : Type u} {X : Type u} [IsKockLawvere_one R]
    (f g : Differential0Form R X) (F : TangentFrame R X 1) :
    exteriorDerivative0 (fun x ↦ f x + g x) F =
      exteriorDerivative0 f F + exteriorDerivative0 g F := by
  change directionalDerivative (fun x ↦ f x + g x) (x := F.basePoint) (F.vector 0) = _
  rw [directionalDerivative_add]
  rfl

@[simp]
theorem exteriorDerivative0_smul_apply {R : Type u} {X : Type u} [IsKockLawvere_one R]
    (c : R) (f : Differential0Form R X) (F : TangentFrame R X 1) :
    exteriorDerivative0 (fun x ↦ c * f x) F =
      c * exteriorDerivative0 f F := by
  change directionalDerivative (fun x ↦ c * f x) (x := F.basePoint) (F.vector 0) = _
  rw [directionalDerivative_fun_smul]
  rfl

@[simp]
theorem exteriorDerivative0_const_apply {R : Type u} {X : Type u} [IsKockLawvere_one R]
    (c : R) (F : TangentFrame R X 1) :
    exteriorDerivative0 (fun _ : X ↦ c) F = 0 := by
  change directionalDerivative (fun _ : X ↦ c) (x := F.basePoint) (F.vector 0) = 0
  exact directionalDerivative_const c (F.vector 0)

/-! ## 严格逐点交错多线性形式

`DifferentialForm` 保留了 PR #2 的切向量组 API。下面的
`FiberwiseDifferentialForm` 是完整版形式代数使用的规范层：在每个基点给出
一个 Mathlib `AlternatingMap`。因此加法性、齐次性和交错性都由类型本身保证，
不再依赖额外的命题字段。
-/

/-- 在每个基点给出的严格交错多线性 `n`-形式。 -/
abbrev FiberwiseDifferentialForm (R : Type u) [CommRing R] (X : Type u)
    [Microlinear R X] (n : ℕ) :=
  ∀ x : X, TangentFiber R X x [⋀^Fin n]→ₗ[R] R

/-- `FiberwiseDifferentialForm` 的规范名称。 -/
abbrev StrictDifferentialForm (R : Type u) [CommRing R] (X : Type u)
    [Microlinear R X] (n : ℕ) := FiberwiseDifferentialForm R X n

/-- 严格的零、一、二阶形式别名。 -/
abbrev StrictDifferential0Form (R : Type u) [CommRing R] (X : Type u)
    [Microlinear R X] := StrictDifferentialForm R X 0

abbrev StrictDifferential1Form (R : Type u) [CommRing R] (X : Type u)
    [Microlinear R X] := StrictDifferentialForm R X 1

abbrev StrictDifferential2Form (R : Type u) [CommRing R] (X : Type u)
    [Microlinear R X] := StrictDifferentialForm R X 2

namespace FiberwiseDifferentialForm

variable {R : Type u} [CommRing R] {X : Type u} [Microlinear R X] {n : ℕ}

/-- 严格形式在同基点切向量组上的求值。 -/
def eval (ω : FiberwiseDifferentialForm R X n) (F : TangentFrame R X n) : R :=
  ω F.basePoint F.vector

@[simp]
lemma eval_apply (ω : FiberwiseDifferentialForm R X n) (F : TangentFrame R X n) :
    eval ω F = ω F.basePoint F.vector := rfl

/-- 严格形式在某个映射下的切向量组变换。 -/
def mapFrame {Y : Type u} [Microlinear R Y] (f : X → Y)
    (F : TangentFrame R X n) : TangentFrame R Y n where
  basePoint := f F.basePoint
  vector := fun i ↦ tangentMapAt R f (F.vector i)

@[simp]
lemma mapFrame_basePoint {Y : Type u} [Microlinear R Y] (f : X → Y)
    (F : TangentFrame R X n) :
    (mapFrame f F).basePoint = f F.basePoint := rfl

@[simp]
lemma mapFrame_vector {Y : Type u} [Microlinear R Y] (f : X → Y)
    (F : TangentFrame R X n) (i : Fin n) :
    (mapFrame f F).vector i = tangentMapAt R f (F.vector i) := rfl

/-- 严格形式在每个槽位为零时消失。 -/
lemma eval_zeroAt (ω : FiberwiseDifferentialForm R X n)
    (F : TangentFrame R X n) (i : Fin n) :
    eval ω (F.zeroAt i) = 0 := by
  change ω F.basePoint (Function.update F.vector i (0 : TangentFiber R X F.basePoint)) = 0
  have h := (ω F.basePoint).map_update_smul F.vector i 0 (F.vector i)
  have hself : Function.update F.vector i (F.vector i) = F.vector := by
    funext j
    by_cases h : j = i
    · subst j
      exact Function.update_self i (F.vector i) F.vector
    · exact Function.update_of_ne h (F.vector i) F.vector
  rw [hself, zero_smul] at h
  calc
    ω F.basePoint (Function.update F.vector i 0) =
        0 • ω F.basePoint F.vector := h
    _ = 0 := zero_smul R (ω F.basePoint F.vector)

/-- 严格形式对同一基点切向量组的数乘公式。 -/
lemma eval_smulAt (ω : FiberwiseDifferentialForm R X n)
    (F : TangentFrame R X n) (i : Fin n) (a : R) :
    eval ω (F.smulAt i a) = a * eval ω F := by
  change ω F.basePoint (Function.update F.vector i (a • F.vector i)) =
    a * ω F.basePoint F.vector
  have h := (ω F.basePoint).map_update_smul F.vector i a (F.vector i)
  have hself : Function.update F.vector i (F.vector i) = F.vector := by
    funext j
    by_cases h : j = i
    · subst j
      exact Function.update_self i (F.vector i) F.vector
    · exact Function.update_of_ne h (F.vector i) F.vector
  rw [hself] at h
  change ω F.basePoint (Function.update F.vector i (a • F.vector i)) =
    a • ω F.basePoint F.vector
  change ω F.basePoint (Function.update F.vector i (a • F.vector i)) =
    a • ω F.basePoint F.vector
  exact h

/-- 把普通函数看作严格的零形式。 -/
def ofFunction (f : X → R) : FiberwiseDifferentialForm R X 0 :=
  fun x ↦ AlternatingMap.constOfIsEmpty R (TangentFiber R X x) (Fin 0) (f x)

/-- 从严格零形式取回普通函数。 -/
def toFunction (ω : FiberwiseDifferentialForm R X 0) : X → R :=
  fun x ↦ ω x (fun i ↦ Fin.elim0 i)

@[simp]
lemma toFunction_ofFunction (f : X → R) : toFunction (ofFunction f) = f := by
  funext x
  change (AlternatingMap.constOfIsEmpty R (TangentFiber R X x) (Fin 0) (f x))
      (fun i ↦ Fin.elim0 i) = f x
  rw [AlternatingMap.constOfIsEmpty_apply]
  rfl

lemma ofFunction_toFunction (ω : FiberwiseDifferentialForm R X 0) :
    ofFunction (toFunction ω) = ω := by
  funext x
  apply AlternatingMap.ext
  intro v
  have hv : v = (fun i ↦ Fin.elim0 i) := by
    funext i
    exact Fin.elim0 i
  rw [hv]
  change ω x (fun i ↦ Fin.elim0 i) = ω x (fun i ↦ Fin.elim0 i)
  rfl

/-- 交错映射沿同一个线性映射逐槽预合成。

这个构造显式给出多线性与交错性证明，避免直接调用 Mathlib
`AlternatingMap.compLinearMap` 时引入选择公理。 -/
def precompose {M M₂ : Type u} [AddCommMonoid M] [AddCommMonoid M₂]
    [Module R M] [Module R M₂] {ι : Type*}
    (ω : M [⋀^ι]→ₗ[R] R) (g : M₂ →ₗ[R] M) : M₂ [⋀^ι]→ₗ[R] R :=
  { toMultilinearMap :=
      { toFun := fun v ↦ ω (fun i ↦ g (v i))
        map_update_add' := by
          intro _ v i x y
          have hxy : (fun k ↦ g ((Function.update v i (x + y)) k)) =
              Function.update (fun k ↦ g (v k)) i (g x + g y) := by
            funext k
            by_cases h : k = i
            · subst k
              simp
            · simp [Function.update, h]
          have hx : (fun k ↦ g ((Function.update v i x) k)) =
              Function.update (fun k ↦ g (v k)) i (g x) := by
            funext k
            by_cases h : k = i
            · subst k
              simp
            · simp [Function.update, h]
          have hy : (fun k ↦ g ((Function.update v i y) k)) =
              Function.update (fun k ↦ g (v k)) i (g y) := by
            funext k
            by_cases h : k = i
            · subst k
              simp
            · simp [Function.update, h]
          rw [hxy, hx, hy, ω.map_update_add]
        map_update_smul' := by
          intro _ v i c x
          have hcx : (fun k ↦ g ((Function.update v i (c • x)) k)) =
              Function.update (fun k ↦ g (v k)) i (c • g x) := by
            funext k
            by_cases h : k = i
            · subst k
              simp
            · simp [Function.update, h]
          have hx : (fun k ↦ g ((Function.update v i x) k)) =
              Function.update (fun k ↦ g (v k)) i (g x) := by
            funext k
            by_cases h : k = i
            · subst k
              simp
            · simp [Function.update, h]
          rw [hcx, hx, ω.map_update_smul] }
    map_eq_zero_of_eq' := by
      intro v i j h hij
      apply ω.map_eq_zero_of_eq (fun k ↦ g (v k))
      · exact congrArg g h
      · exact hij }

/-- 严格形式的拉回。 -/
def pullback {Y : Type u} [Microlinear R Y] (f : X → Y)
    (ω : FiberwiseDifferentialForm R Y n) :
    FiberwiseDifferentialForm R X n :=
  fun x ↦ precompose (R := R) (ι := Fin n) (ω (f x)) (tangentMapAtLinear R f)

@[simp]
lemma pullback_apply {Y : Type u} [Microlinear R Y] (f : X → Y)
    (ω : FiberwiseDifferentialForm R Y n) (x : X)
    (v : Fin n → TangentFiber R X x) :
    pullback f ω x v = ω (f x) (fun i ↦ tangentMapAtLinear R f (v i)) := by
  change ω (f x) (fun i ↦ tangentMapAtLinear R f (v i)) = _
  rfl

@[simp]
lemma eval_pullback {Y : Type u} [Microlinear R Y] (f : X → Y)
    (ω : FiberwiseDifferentialForm R Y n) (F : TangentFrame R X n) :
    eval (pullback f ω) F = eval ω (mapFrame f F) := by
  change ω (f F.basePoint) (fun i ↦ tangentMapAtLinear R f (F.vector i)) = _
  rfl

lemma pullback_id (ω : FiberwiseDifferentialForm R X n) :
    pullback id ω = ω := by
  funext x
  apply AlternatingMap.ext
  intro v
  change ω (id x) (fun i ↦ tangentMapAtLinear R id (v i)) = ω x v
  have hv : (fun i ↦ tangentMapAtLinear R id (v i)) = v := by
    funext i
    apply Subtype.ext
    rfl
  have hval := congrArg (fun w ↦ ω x w) hv
  exact hval

lemma pullback_comp {Y Z : Type u} [Microlinear R Y] [Microlinear R Z]
    (f : X → Y) (g : Y → Z) (ω : FiberwiseDifferentialForm R Z n) :
    pullback f (pullback g ω) = pullback (g ∘ f) ω := by
  funext x
  apply AlternatingMap.ext
  intro v
  rfl

lemma pullback_zero {Y : Type u} [Microlinear R Y] (f : X → Y) :
    pullback f (0 : FiberwiseDifferentialForm R Y n) = 0 := by
  funext x
  ext v
  simp

lemma pullback_add {Y : Type u} [Microlinear R Y] (f : X → Y)
    (ω η : FiberwiseDifferentialForm R Y n) :
    pullback f (ω + η) = pullback f ω + pullback f η := by
  funext x
  ext v
  rfl

lemma pullback_smul {Y : Type u} [Microlinear R Y] (c : R) (f : X → Y)
    (ω : FiberwiseDifferentialForm R Y n) :
    pullback f (c • ω) = c • pullback f ω := by
  funext x
  ext v
  rfl

end FiberwiseDifferentialForm

end SDG.DifferentialForms
