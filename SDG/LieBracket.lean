import SDG.TangentBundle

/-!
# SDG.LieBracket

李括号 (Lie bracket)：无穷小变换的群论交换子。

本模块对应 Kock《Synthetic Differential Geometry》第二版第 I.9 节：若微线性对象
`X` 还满足 Property W，则两个向量场 `ξ`、`η` 的无穷小变换
`ξ_d, η_e : X → X` 可以先取群论交换子

`η_{-e} ∘ ξ_{-d} ∘ η_e ∘ ξ_d`,

再由 Property W 把这个依赖 `(d,e) : D × D` 的二阶无穷小变换唯一地因子化为
一个依赖 `d * e : D` 的一阶无穷小变换。这一因子化得到的向量场就是
`lieBracket ξ η`。
-/

universe u v w

/-! ## Property W 与 `D × D → D` 的乘积 -/

/-- 两个一阶无穷小量的乘积仍是一阶无穷小量。 -/
def D.mul (R : Type u) [CommRing R] (d e : D R) : D R :=
  D.ofMul R ((d : R) * (e : R)) (by
    calc
      ((d : R) * (e : R)) * ((d : R) * (e : R))
          = ((d : R) * (d : R)) * ((e : R) * (e : R)) := by ring
      _ = 0 := by
        rw [D.mul_eq_zero R d, D.mul_eq_zero R e]
        simp)

@[simp]
theorem D.coe_mul (R : Type u) [CommRing R] (d e : D R) :
    ((D.mul R d e : D R) : R) = (d : R) * (e : R) := rfl

@[simp]
lemma D.mul_zero_left (R : Type u) [CommRing R] (d : D R) :
    D.mul R 0 d = 0 := by
  apply Subtype.ext
  simp [D.mul]

@[simp]
lemma D.mul_zero_right (R : Type u) [CommRing R] (d : D R) :
    D.mul R d 0 = 0 := by
  apply Subtype.ext
  simp [D.mul]

@[simp]
lemma D.mul_zero_zero (R : Type u) [CommRing R] :
    D.mul R (0 : D R) (0 : D R) = 0 := by
  simp

lemma D.mul_comm (R : Type u) [CommRing R] (d e : D R) :
    D.mul R d e = D.mul R e d := by
  apply Subtype.ext
  rw [D.coe_mul, D.coe_mul]
  ring

/-- $D$ 中的 $-0 = 0$（项目自带的 `Zero` 实例，故不能直接用 `neg_zero`）。 -/
lemma D.neg_zero (R : Type u) [CommRing R] :
    (-(0 : D R)) = 0 := by
  apply Subtype.ext
  show (-(0 : R)) = (0 : R)
  ring

lemma D.neg_one_smul (R : Type u) [CommRing R] (d : D R) :
    ((-1 : R) • d) = -d := by
  apply Subtype.ext
  change (-1 : R) * (d : R) = -(d : R)
  ring

lemma D.neg_one_smul_mul_comm (R : Type u) [CommRing R] (d₁ d₂ : D R) :
    ((-1 : R) • D.mul R d₁ d₂) = -(D.mul R d₂ d₁) := by
  apply Subtype.ext
  change (-1 : R) * ((d₁ : R) * (d₂ : R)) = -((d₂ : R) * (d₁ : R))
  ring

/-- **Property W**（Kock 第 I.9 节的 Condition W）。

若 `τ : D × D → M` 在两条坐标轴上都退化到同一个值 `τ 0 0`，则 `τ` 唯一地
只依赖乘积 `d₁ * d₂`：存在唯一 `t : D → M` 使
` t (d₁ * d₂) = τ d₁ d₂`。

这里用 `D.mul R d₁ d₂` 表示乘积 `d₁ * d₂` 作为 `D` 中的元素。 -/
class PropertyW (R : Type u) [CommRing R] (M : Type v) : Type (max u v) where
  propertyW (τ : D R → D R → M)
      (hRightAxis : ∀ d₁ : D R, τ d₁ 0 = τ 0 0)
      (hLeftAxis : ∀ d₂ : D R, τ 0 d₂ = τ 0 0) :
    ExistsUnique' fun t : D R → M ↦
      ∀ d₁ d₂ : D R, t (D.mul R d₁ d₂) = τ d₁ d₂

/-- Property W 对任意 Π-类型逐点成立。

特别地，若 `M` 满足 Property W，则函数空间 `X → M` 也满足 Property W；
这正是第 I.9 节中把 `M` 的 Property W 用到 `M^M` 上的步骤。 -/
instance instPropertyWPi (R : Type u) [CommRing R] {I : Type v} {Y : I → Type w}
    [hY : ∀ i, PropertyW R (Y i)] : PropertyW R ((i : I) → Y i) where
  propertyW τ hRightAxis hLeftAxis := by
    let τAt : (i : I) → D R → D R → Y i := fun i d₁ d₂ ↦ τ d₁ d₂ i
    have hRightAt : ∀ i : I, ∀ d₁ : D R, τAt i d₁ 0 = τAt i 0 0 := by
      intro i d₁
      exact congrFun (hRightAxis d₁) i
    have hLeftAt : ∀ i : I, ∀ d₂ : D R, τAt i 0 d₂ = τAt i 0 0 := by
      intro i d₂
      exact congrFun (hLeftAxis d₂) i
    let tAt : (i : I) → D R → Y i :=
      fun i ↦ (PropertyW.propertyW (R := R) (M := Y i) (τAt i) (hRightAt i) (hLeftAt i)).1
    let t : D R → (i : I) → Y i := fun d i ↦ tAt i d
    refine ⟨t, ?_, ?_⟩
    · intro d₁ d₂
      funext i
      exact (PropertyW.propertyW (R := R) (M := Y i) (τAt i) (hRightAt i) (hLeftAt i)).2.1 d₁ d₂
    · intro y hy
      funext d
      funext i
      have hyi : ∀ d₁ d₂ : D R, (fun d ↦ y d i) (D.mul R d₁ d₂) = τAt i d₁ d₂ := by
        intro d₁ d₂
        exact congrFun (hy d₁ d₂) i
      have huniq : (fun d ↦ y d i) = tAt i :=
        (PropertyW.propertyW (R := R) (M := Y i) (τAt i) (hRightAt i) (hLeftAt i)).2.2
          (fun d ↦ y d i) hyi
      exact congrFun huniq d

namespace TangentVectorField

/-! ## 无穷小变换与交换子 -/

/-- 向量场 `ξ` 在无穷小时间 `d` 给出的无穷小变换 `ξ_d : X → X`。 -/
def infTranslation {R X} [CommRing R] (ξ : TangentVectorField R X) (d : D R) : X → X :=
  fun x ↦ ξ.1 x d

@[simp]
lemma infTranslation_apply {R X} [CommRing R] (ξ : TangentVectorField R X) (d : D R) (x : X) :
    infTranslation ξ d x = ξ.1 x d := rfl

/-- 零无穷小时间给出恒等变换。 -/
@[simp]
lemma infTranslation_zero {R X} [CommRing R] (ξ : TangentVectorField R X) :
    infTranslation ξ 0 = id := by
  funext x
  exact ξ.2 x

/-- 无穷小变换 `ξ_d` 的显式逆为 `ξ_{-d}`。 -/
theorem infTranslation_leftInverse {R X} [CommRing R] [Microlinear R X]
    (ξ : TangentVectorField R X) (d : D R) :
    Function.LeftInverse (infTranslation ξ (-d)) (infTranslation ξ d) := by
  exact (infTranslation_invertible ξ d).1

/-- 无穷小变换 `ξ_d` 的显式逆为 `ξ_{-d}`。 -/
theorem infTranslation_rightInverse {R X} [CommRing R] [Microlinear R X]
    (ξ : TangentVectorField R X) (d : D R) :
    Function.RightInverse (infTranslation ξ (-d)) (infTranslation ξ d) := by
  exact (infTranslation_invertible ξ d).2

/-- 两个向量场无穷小变换的群论交换子：
`η_{-d₂} ∘ ξ_{-d₁} ∘ η_{d₂} ∘ ξ_{d₁}`。 -/
def transformationCommutator {R X} [CommRing R]
    (ξ η : TangentVectorField R X) (d₁ d₂ : D R) : X → X :=
  fun x ↦ η.1 (ξ.1 (η.1 (ξ.1 x d₁) d₂) (-d₁)) (-d₂)

lemma transformationCommutator_apply {R X} [CommRing R]
    (ξ η : TangentVectorField R X) (d₁ d₂ : D R) (x : X) :
    transformationCommutator ξ η d₁ d₂ x =
      η.1 (ξ.1 (η.1 (ξ.1 x d₁) d₂) (-d₁)) (-d₂) := rfl

/-- 交换子在第一坐标为零时退化为恒等变换。 -/
lemma transformationCommutator_zero_left {R X} [CommRing R] [Microlinear R X]
    (ξ η : TangentVectorField R X) (d₂ : D R) :
    transformationCommutator ξ η 0 d₂ = id := by
  funext x
  simp only [transformationCommutator_apply, D.neg_zero R, ξ.2]
  exact (infTranslation_leftInverse η d₂) x

/-- 交换子在第二坐标为零时退化为恒等变换。 -/
lemma transformationCommutator_zero_right {R X} [CommRing R] [Microlinear R X]
    (ξ η : TangentVectorField R X) (d₁ : D R) :
    transformationCommutator ξ η d₁ 0 = id := by
  funext x
  simp only [transformationCommutator_apply, D.neg_zero R, η.2]
  exact (infTranslation_leftInverse ξ d₁) x

@[simp]
lemma transformationCommutator_zero_zero {R X} [CommRing R] [Microlinear R X]
    (ξ η : TangentVectorField R X) :
    transformationCommutator ξ η 0 0 = id :=
  transformationCommutator_zero_right ξ η 0

lemma transformationCommutator_rightAxis {R X} [CommRing R] [Microlinear R X]
    (ξ η : TangentVectorField R X) (d₁ : D R) :
    transformationCommutator ξ η d₁ 0 = transformationCommutator ξ η 0 0 := by
  calc
    transformationCommutator ξ η d₁ 0 = id := transformationCommutator_zero_right ξ η d₁
    _ = transformationCommutator ξ η 0 0 := (transformationCommutator_zero_zero ξ η).symm

lemma transformationCommutator_leftAxis {R X} [CommRing R] [Microlinear R X]
    (ξ η : TangentVectorField R X) (d₂ : D R) :
    transformationCommutator ξ η 0 d₂ = transformationCommutator ξ η 0 0 := by
  calc
    transformationCommutator ξ η 0 d₂ = id := transformationCommutator_zero_left ξ η d₂
    _ = transformationCommutator ξ η 0 0 := (transformationCommutator_zero_zero ξ η).symm

/-! ## 李括号 -/

/-- Property W 给出的交换子唯一因子化数据。 -/
def lieBracketData {R X} [CommRing R] [Microlinear R X] [PropertyW R X]
    (ξ η : TangentVectorField R X) :
    ExistsUnique' fun t : D R → X → X ↦
      ∀ d₁ d₂ : D R, t (D.mul R d₁ d₂) = transformationCommutator ξ η d₁ d₂ :=
  PropertyW.propertyW (R := R) (M := X → X) (transformationCommutator ξ η)
    (transformationCommutator_rightAxis ξ η)
    (transformationCommutator_leftAxis ξ η)

/-- 李括号对应的一参数无穷小变换。 -/
def lieBracketTransform {R X} [CommRing R] [Microlinear R X] [PropertyW R X]
    (ξ η : TangentVectorField R X) : D R → X → X :=
  (lieBracketData ξ η).1

/-- 李括号变换由交换子的二阶无穷小量乘积刻画。 -/
theorem lieBracketTransform_spec {R X} [CommRing R] [Microlinear R X] [PropertyW R X]
    (ξ η : TangentVectorField R X) (d₁ d₂ : D R) :
    lieBracketTransform ξ η (D.mul R d₁ d₂) = transformationCommutator ξ η d₁ d₂ :=
  (lieBracketData ξ η).2.1 d₁ d₂

/-- **李括号** `[ξ, η]`：由无穷小变换交换子经 Property W 因子化得到的向量场。 -/
def lieBracket {R X} [CommRing R] [Microlinear R X] [PropertyW R X]
    (ξ η : TangentVectorField R X) : TangentVectorField R X :=
  ⟨fun x d ↦ lieBracketTransform ξ η d x, by
    intro x
    show lieBracketTransform ξ η 0 x = x
    have hspec := lieBracketTransform_spec ξ η (0 : D R) (0 : D R)
    rw [D.mul_zero_zero] at hspec
    calc
      lieBracketTransform ξ η 0 x = transformationCommutator ξ η 0 0 x :=
        congrFun hspec x
      _ = x := congrFun (transformationCommutator_zero_zero ξ η) x⟩

/-- Kock 第 I.9 节公式 (9.3) 的 Lean 形式：
`[ξ,η]_{d₁d₂}` 等于 `η_{-d₂} ∘ ξ_{-d₁} ∘ η_{d₂} ∘ ξ_{d₁}`。 -/
theorem lieBracket_spec {R X} [CommRing R] [Microlinear R X] [PropertyW R X]
    (ξ η : TangentVectorField R X) (x : X) (d₁ d₂ : D R) :
    (lieBracket ξ η).1 x (D.mul R d₁ d₂) =
      η.1 (ξ.1 (η.1 (ξ.1 x d₁) d₂) (-d₁)) (-d₂) := by
  change lieBracketTransform ξ η (D.mul R d₁ d₂) x =
    η.1 (ξ.1 (η.1 (ξ.1 x d₁) d₂) (-d₁)) (-d₂)
  exact congrFun (lieBracketTransform_spec ξ η d₁ d₂) x

/-- 李括号在 `0` 处的基点条件。 -/
@[simp]
lemma lieBracket_basePoint {R X} [CommRing R] [Microlinear R X] [PropertyW R X]
    (ξ η : TangentVectorField R X) (x : X) :
    (lieBracket ξ η).1 x 0 = x :=
  (lieBracket ξ η).2 x

end TangentVectorField
