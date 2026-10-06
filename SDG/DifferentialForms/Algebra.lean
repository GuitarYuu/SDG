import SDG.NoChoice
import SDG.DifferentialForms.Core
import SDG.FinSumProd

/-!
# SDG.DifferentialForms.Algebra

形式代数的第一阶段基础设施。所有新增构造都保持项目的无选择公理约束：
不调用 Mathlib 中 choice-dependent 的 `AlternatingMap.domCoprod` 或
`domDomCongr`。当前先提供显式的 `1 ∧ 1` 楔积，作为一般 shuffle 楔积的
低阶回归实现；更高次数将在同一构造性接口上递进扩展。
-/

universe u

namespace SDG.DifferentialForms

namespace TangentFrame

variable {R : Type u} [CommRing R] {X : Type u}

/-- 按有限指标等价重排切向量组。 -/
def reindex {m n : ℕ} (F : TangentFrame R X m) (e : Fin n ≃ Fin m) :
    TangentFrame R X n where
  basePoint := F.basePoint
  vector := fun i ↦ F.vector (e i)

@[simp]
lemma reindex_basePoint {m n : ℕ} (F : TangentFrame R X m) (e : Fin n ≃ Fin m) :
    (F.reindex e).basePoint = F.basePoint := rfl

@[simp]
lemma reindex_vector {m n : ℕ} (F : TangentFrame R X m) (e : Fin n ≃ Fin m)
    (i : Fin n) :
    (F.reindex e).vector i = F.vector (e i) := rfl

lemma reindex_refl {n : ℕ} (F : TangentFrame R X n) :
    F.reindex (Equiv.refl (Fin n)) = F := by
  rfl

lemma reindex_trans {l m n : ℕ} (F : TangentFrame R X l)
    (e₁ : Fin m ≃ Fin l) (e₂ : Fin n ≃ Fin m) :
    (F.reindex e₁).reindex e₂ = F.reindex (e₂.trans e₁) := by
  rfl

end TangentFrame

/-! ### `Fin 2` 上的函数更新引理 -/

/-- 更新 `Fin 2` 向量的第 `0` 槽后，第 `0` 坐标就是新值。 -/
lemma update_fin2_zero_left {α : Type u} [DecidableEq (Fin 2)]
    (v : Fin 2 → α) (w : α) :
    Function.update v 0 w 0 = w :=
  Function.update_self 0 w v

/-- 更新 `Fin 2` 向量的第 `0` 槽后，第 `1` 坐标不变。 -/
lemma update_fin2_zero_right {α : Type u} [DecidableEq (Fin 2)]
    (v : Fin 2 → α) (w : α) :
    Function.update v 0 w 1 = v 1 :=
  Function.update_of_ne (by omega) w v

/-- 更新 `Fin 2` 向量的第 `1` 槽后，第 `0` 坐标不变。 -/
lemma update_fin2_one_left {α : Type u} [DecidableEq (Fin 2)]
    (v : Fin 2 → α) (w : α) :
    Function.update v 1 w 0 = v 0 :=
  Function.update_of_ne (by omega) w v

/-- 更新 `Fin 2` 向量的第 `1` 槽后，第 `1` 坐标就是新值。 -/
lemma update_fin2_one_right {α : Type u} [DecidableEq (Fin 2)]
    (v : Fin 2 → α) (w : α) :
    Function.update v 1 w 1 = w :=
  Function.update_self 1 w v

namespace FiberwiseDifferentialForm

variable {R : Type u} [CommRing R] {X : Type u} [Microlinear R X]

/-- 把一阶严格形式看作固定基点切纤维上的线性泛函。 -/
def oneArg {x : X} (ω : TangentFiber R X x [⋀^Fin 1]→ₗ[R] R) :
    TangentFiber R X x →ₗ[R] R where
  toFun v := ω (fun _ ↦ v)
  map_add' v w := by
    have h := ω.map_update_add (fun _ : Fin 1 ↦ v) 0 v w
    have h₁ : Function.update (fun _ : Fin 1 ↦ v) 0 (v + w) =
        (fun _ : Fin 1 ↦ v + w) := by
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst i
      simp
    have h₂ : Function.update (fun _ : Fin 1 ↦ v) 0 v =
        (fun _ : Fin 1 ↦ v) := by
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst i
      exact Function.update_self 0 v (fun _ : Fin 1 ↦ v)
    have h₃ : Function.update (fun _ : Fin 1 ↦ v) 0 w =
        (fun _ : Fin 1 ↦ w) := by
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst i
      exact Function.update_self 0 w (fun _ : Fin 1 ↦ v)
    rw [h₁, h₂, h₃] at h
    exact h
  map_smul' c v := by
    have h := ω.map_update_smul (fun _ : Fin 1 ↦ v) 0 c v
    have h₁ : Function.update (fun _ : Fin 1 ↦ v) 0 (c • v) =
        (fun _ : Fin 1 ↦ c • v) := by
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst i
      exact Function.update_self 0 (c • v) (fun _ : Fin 1 ↦ v)
    have h₂ : Function.update (fun _ : Fin 1 ↦ v) 0 v =
        (fun _ : Fin 1 ↦ v) := by
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst i
      exact Function.update_self 0 v (fun _ : Fin 1 ↦ v)
    rw [h₁, h₂] at h
    exact h

@[simp]
lemma oneArg_apply {x : X} (ω : TangentFiber R X x [⋀^Fin 1]→ₗ[R] R)
    (v : TangentFiber R X x) :
    oneArg ω v = ω (fun _ ↦ v) := rfl

/-- 固定基点处 `1 ∧ 1` 楔积的数值函数：
`ω(v₀)η(v₁) - ω(v₁)η(v₀)`。 -/
def wedgeOneOneFun {x : X} (ω η : TangentFiber R X x [⋀^Fin 1]→ₗ[R] R)
    (v : Fin 2 → TangentFiber R X x) : R :=
  oneArg ω (v 0) * oneArg η (v 1) - oneArg ω (v 1) * oneArg η (v 0)

lemma wedgeOneOneFun_update_zero_add {x : X}
    (ω η : TangentFiber R X x [⋀^Fin 1]→ₗ[R] R)
    (v : Fin 2 → TangentFiber R X x) (p q : TangentFiber R X x) :
    wedgeOneOneFun ω η (Function.update v 0 (p + q)) =
      wedgeOneOneFun ω η (Function.update v 0 p) +
      wedgeOneOneFun ω η (Function.update v 0 q) := by
  simp only [wedgeOneOneFun, update_fin2_zero_left, update_fin2_zero_right, map_add]
  ring

lemma wedgeOneOneFun_update_one_add {x : X}
    (ω η : TangentFiber R X x [⋀^Fin 1]→ₗ[R] R)
    (v : Fin 2 → TangentFiber R X x) (p q : TangentFiber R X x) :
    wedgeOneOneFun ω η (Function.update v 1 (p + q)) =
      wedgeOneOneFun ω η (Function.update v 1 p) +
      wedgeOneOneFun ω η (Function.update v 1 q) := by
  simp only [wedgeOneOneFun, update_fin2_one_left, update_fin2_one_right, map_add]
  ring

lemma wedgeOneOneFun_update_zero_smul {x : X}
    (ω η : TangentFiber R X x [⋀^Fin 1]→ₗ[R] R)
    (v : Fin 2 → TangentFiber R X x) (c : R) (p : TangentFiber R X x) :
    wedgeOneOneFun ω η (Function.update v 0 (c • p)) =
      c • wedgeOneOneFun ω η (Function.update v 0 p) := by
  simp only [wedgeOneOneFun, update_fin2_zero_left, update_fin2_zero_right,
    map_smul, smul_eq_mul]
  ring

lemma wedgeOneOneFun_update_one_smul {x : X}
    (ω η : TangentFiber R X x [⋀^Fin 1]→ₗ[R] R)
    (v : Fin 2 → TangentFiber R X x) (c : R) (p : TangentFiber R X x) :
    wedgeOneOneFun ω η (Function.update v 1 (c • p)) =
      c • wedgeOneOneFun ω η (Function.update v 1 p) := by
  simp only [wedgeOneOneFun, update_fin2_one_left, update_fin2_one_right,
    map_smul, smul_eq_mul]
  ring

lemma wedgeOneOneFun_eq_zero_of_zero_one {x : X}
    (ω η : TangentFiber R X x [⋀^Fin 1]→ₗ[R] R)
    (v : Fin 2 → TangentFiber R X x) (h : v 0 = v 1) :
    wedgeOneOneFun ω η v = 0 := by
  simp only [wedgeOneOneFun]
  rw [h]
  ring

lemma wedgeOneOneFun_eq_zero_of_one_zero {x : X}
    (ω η : TangentFiber R X x [⋀^Fin 1]→ₗ[R] R)
    (v : Fin 2 → TangentFiber R X x) (h : v 1 = v 0) :
    wedgeOneOneFun ω η v = 0 := by
  simp only [wedgeOneOneFun]
  rw [h]
  ring

/-- 两个严格一形式的显式楔积。

公式为 `ω(v₀)η(v₁) - ω(v₁)η(v₀)`；它是一般 shuffle 楔积在
`1 ∧ 1` 情形的无选择实现。 -/
def wedgeOneOne (ω η : FiberwiseDifferentialForm R X 1) :
    FiberwiseDifferentialForm R X 2 := by
  intro x
  exact
    { toMultilinearMap :=
        { toFun := wedgeOneOneFun (ω x) (η x)
          map_update_add' := by
            intro _ v i p q
            have hi : i = 0 ∨ i = 1 := by
              by_cases h : i = 0
              · exact Or.inl h
              · exact Or.inr (fin_two_eq_one_of_ne_zero h)
            rcases hi with rfl | rfl
            · simp only [wedgeOneOneFun, update_fin2_zero_left,
                update_fin2_zero_right, map_add]
              ring
            · simp only [wedgeOneOneFun, update_fin2_one_left,
                update_fin2_one_right, map_add]
              ring
          map_update_smul' := by
            intro _ v i c p
            have hi : i = 0 ∨ i = 1 := by
              by_cases h : i = 0
              · exact Or.inl h
              · exact Or.inr (fin_two_eq_one_of_ne_zero h)
            rcases hi with rfl | rfl
            · simp only [wedgeOneOneFun, update_fin2_zero_left,
                update_fin2_zero_right, map_smul, smul_eq_mul]
              ring
            · simp only [wedgeOneOneFun, update_fin2_one_left,
                update_fin2_one_right, map_smul, smul_eq_mul]
              ring }
      map_eq_zero_of_eq' := by
        intro v i j h hij
        have hi : i = 0 ∨ i = 1 := by
          by_cases hi : i = 0
          · exact Or.inl hi
          · exact Or.inr (fin_two_eq_one_of_ne_zero hi)
        have hj : j = 0 ∨ j = 1 := by
          by_cases hj : j = 0
          · exact Or.inl hj
          · exact Or.inr (fin_two_eq_one_of_ne_zero hj)
        rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
        · exact False.elim (hij rfl)
        · simp only [wedgeOneOneFun]
          rw [h]
          ring
        · simp only [wedgeOneOneFun]
          rw [h]
          ring
        · exact False.elim (hij rfl) }

@[simp]
lemma wedgeOneOne_apply (ω η : FiberwiseDifferentialForm R X 1)
    (x : X) (v : Fin 2 → TangentFiber R X x) :
    wedgeOneOne ω η x v = wedgeOneOneFun (ω x) (η x) v := rfl

/-! ### `1 ∧ 1` 楔积的代数定律 -/

lemma oneArg_add {x : X} (ω₁ ω₂ : TangentFiber R X x [⋀^Fin 1]→ₗ[R] R)
    (v : TangentFiber R X x) :
    oneArg (ω₁ + ω₂) v = oneArg ω₁ v + oneArg ω₂ v := rfl

lemma oneArg_smul {x : X} (c : R) (ω : TangentFiber R X x [⋀^Fin 1]→ₗ[R] R)
    (v : TangentFiber R X x) :
    oneArg (c • ω) v = c * oneArg ω v := rfl

lemma oneArg_zero {x : X} (v : TangentFiber R X x) :
    oneArg (0 : TangentFiber R X x [⋀^Fin 1]→ₗ[R] R) v = 0 := rfl

lemma wedgeOneOneFun_add_left {x : X}
    (ω₁ ω₂ η : TangentFiber R X x [⋀^Fin 1]→ₗ[R] R)
    (v : Fin 2 → TangentFiber R X x) :
    wedgeOneOneFun (ω₁ + ω₂) η v =
      wedgeOneOneFun ω₁ η v + wedgeOneOneFun ω₂ η v := by
  simp only [wedgeOneOneFun, oneArg_add]
  ring

lemma wedgeOneOneFun_add_right {x : X}
    (ω η₁ η₂ : TangentFiber R X x [⋀^Fin 1]→ₗ[R] R)
    (v : Fin 2 → TangentFiber R X x) :
    wedgeOneOneFun ω (η₁ + η₂) v =
      wedgeOneOneFun ω η₁ v + wedgeOneOneFun ω η₂ v := by
  simp only [wedgeOneOneFun, oneArg_add]
  ring

lemma wedgeOneOneFun_smul_left {x : X}
    (c : R) (ω η : TangentFiber R X x [⋀^Fin 1]→ₗ[R] R)
    (v : Fin 2 → TangentFiber R X x) :
    wedgeOneOneFun (c • ω) η v = c * wedgeOneOneFun ω η v := by
  simp only [wedgeOneOneFun, oneArg_smul]
  ring

lemma wedgeOneOneFun_smul_right {x : X}
    (c : R) (ω η : TangentFiber R X x [⋀^Fin 1]→ₗ[R] R)
    (v : Fin 2 → TangentFiber R X x) :
    wedgeOneOneFun ω (c • η) v = c * wedgeOneOneFun ω η v := by
  simp only [wedgeOneOneFun, oneArg_smul]
  ring

lemma wedgeOneOneFun_zero_left {x : X}
    (η : TangentFiber R X x [⋀^Fin 1]→ₗ[R] R)
    (v : Fin 2 → TangentFiber R X x) :
    wedgeOneOneFun (0 : TangentFiber R X x [⋀^Fin 1]→ₗ[R] R) η v = 0 := by
  simp only [wedgeOneOneFun, oneArg_zero]
  ring

lemma wedgeOneOneFun_zero_right {x : X}
    (ω : TangentFiber R X x [⋀^Fin 1]→ₗ[R] R)
    (v : Fin 2 → TangentFiber R X x) :
    wedgeOneOneFun ω (0 : TangentFiber R X x [⋀^Fin 1]→ₗ[R] R) v = 0 := by
  simp only [wedgeOneOneFun, oneArg_zero]
  ring

/-- `1 ∧ 1` 楔积对第一个因子加法。 -/
lemma wedgeOneOne_add_left (ω₁ ω₂ η : FiberwiseDifferentialForm R X 1) :
    wedgeOneOne (ω₁ + ω₂) η = wedgeOneOne ω₁ η + wedgeOneOne ω₂ η := by
  funext x
  apply AlternatingMap.ext
  intro v
  simp only [wedgeOneOne_apply, AlternatingMap.add_apply, Pi.add_apply,
    wedgeOneOneFun_add_left]

/-- `1 ∧ 1` 楔积对第二个因子加法。 -/
lemma wedgeOneOne_add_right (ω η₁ η₂ : FiberwiseDifferentialForm R X 1) :
    wedgeOneOne ω (η₁ + η₂) = wedgeOneOne ω η₁ + wedgeOneOne ω η₂ := by
  funext x
  apply AlternatingMap.ext
  intro v
  simp only [wedgeOneOne_apply, AlternatingMap.add_apply, Pi.add_apply,
    wedgeOneOneFun_add_right]

/-- `1 ∧ 1` 楔积对第一个因子数乘。 -/
lemma wedgeOneOne_smul_left (c : R) (ω η : FiberwiseDifferentialForm R X 1) :
    wedgeOneOne (c • ω) η = c • wedgeOneOne ω η := by
  funext x
  apply AlternatingMap.ext
  intro v
  simp only [wedgeOneOne_apply, Pi.smul_apply, AlternatingMap.smul_apply,
    wedgeOneOneFun_smul_left, smul_eq_mul]

/-- `1 ∧ 1` 楔积对第二个因子数乘。 -/
lemma wedgeOneOne_smul_right (c : R) (ω η : FiberwiseDifferentialForm R X 1) :
    wedgeOneOne ω (c • η) = c • wedgeOneOne ω η := by
  funext x
  apply AlternatingMap.ext
  intro v
  simp only [wedgeOneOne_apply, Pi.smul_apply, AlternatingMap.smul_apply,
    wedgeOneOneFun_smul_right, smul_eq_mul]

/-- `1 ∧ 1` 楔积对左零形式为零。 -/
lemma wedgeOneOne_zero_left (η : FiberwiseDifferentialForm R X 1) :
    wedgeOneOne (0 : FiberwiseDifferentialForm R X 1) η = 0 := by
  funext x
  apply AlternatingMap.ext
  intro v
  simp only [wedgeOneOne_apply, Pi.zero_apply, AlternatingMap.zero_apply,
    wedgeOneOneFun_zero_left]

/-- `1 ∧ 1` 楔积对右零形式为零。 -/
lemma wedgeOneOne_zero_right (ω : FiberwiseDifferentialForm R X 1) :
    wedgeOneOne ω (0 : FiberwiseDifferentialForm R X 1) = 0 := by
  funext x
  apply AlternatingMap.ext
  intro v
  simp only [wedgeOneOne_apply, Pi.zero_apply, AlternatingMap.zero_apply,
    wedgeOneOneFun_zero_right]

/-- `1 ∧ 1` 楔积的分次交换律：交换因子差一个负号。 -/
lemma wedgeOneOne_anticomm (ω η : FiberwiseDifferentialForm R X 1) :
    wedgeOneOne η ω = -wedgeOneOne ω η := by
  funext x
  apply AlternatingMap.ext
  intro v
  simp only [wedgeOneOne_apply, Pi.neg_apply, AlternatingMap.neg_apply,
    wedgeOneOneFun]
  ring

/-- `1 ∧ 1` 楔积在同基点切向量组上的求值公式。 -/
lemma eval_wedgeOneOne (ω η : FiberwiseDifferentialForm R X 1)
    (F : TangentFrame R X 2) :
    eval (wedgeOneOne ω η) F =
      ω F.basePoint (fun _ : Fin 1 ↦ F.vector 0) *
        η F.basePoint (fun _ : Fin 1 ↦ F.vector 1) -
      ω F.basePoint (fun _ : Fin 1 ↦ F.vector 1) *
        η F.basePoint (fun _ : Fin 1 ↦ F.vector 0) := by
  rfl

/-- 严格形式拉回保持 `1 ∧ 1` 楔积。 -/
lemma wedgeOneOne_pullback {Y : Type u} [Microlinear R Y] (f : X → Y)
    (ω η : FiberwiseDifferentialForm R Y 1) :
    pullback f (wedgeOneOne ω η) = wedgeOneOne (pullback f ω) (pullback f η) := by
  funext x
  apply AlternatingMap.ext
  intro v
  show wedgeOneOneFun (ω (f x)) (η (f x))
      (fun i ↦ tangentMapAtLinear R f (v i)) =
    wedgeOneOneFun (pullback f ω x) (pullback f η x) v
  rfl

/-! ### 严格零形式与任意次数形式的楔积 -/

/-- 严格零形式从左作用在任意次数严格形式上。 -/
def wedgeZeroLeft {n : ℕ} (f : FiberwiseDifferentialForm R X 0)
    (ω : FiberwiseDifferentialForm R X n) : FiberwiseDifferentialForm R X n :=
  fun x ↦ toFunction f x • ω x

@[simp]
lemma wedgeZeroLeft_apply {n : ℕ} (f : FiberwiseDifferentialForm R X 0)
    (ω : FiberwiseDifferentialForm R X n) (x : X)
    (v : Fin n → TangentFiber R X x) :
    wedgeZeroLeft f ω x v = toFunction f x * ω x v := rfl

/-- 在交换系数环上，严格零形式的右作用使用同一逐点乘法。 -/
def wedgeZeroRight {n : ℕ} (ω : FiberwiseDifferentialForm R X n)
    (f : FiberwiseDifferentialForm R X 0) : FiberwiseDifferentialForm R X n :=
  wedgeZeroLeft f ω

@[simp]
lemma wedgeZeroRight_apply {n : ℕ} (ω : FiberwiseDifferentialForm R X n)
    (f : FiberwiseDifferentialForm R X 0) (x : X)
    (v : Fin n → TangentFiber R X x) :
    wedgeZeroRight ω f x v = ω x v * toFunction f x := by
  rw [wedgeZeroRight, wedgeZeroLeft_apply, mul_comm]

/-- 常值函数 `1` 对应的严格零形式。 -/
def oneZeroForm : FiberwiseDifferentialForm R X 0 := ofFunction (fun _ ↦ 1)

@[simp]
lemma toFunction_oneZeroForm : toFunction (oneZeroForm : FiberwiseDifferentialForm R X 0) =
    (fun _ ↦ 1) := by
  exact toFunction_ofFunction (fun _ ↦ 1)

lemma wedgeZeroLeft_one {n : ℕ} (ω : FiberwiseDifferentialForm R X n) :
    wedgeZeroLeft oneZeroForm ω = ω := by
  funext x
  apply AlternatingMap.ext
  intro v
  simp only [wedgeZeroLeft_apply, toFunction_oneZeroForm, one_mul]

lemma wedgeZeroRight_one {n : ℕ} (ω : FiberwiseDifferentialForm R X n) :
    wedgeZeroRight ω oneZeroForm = ω := by
  funext x
  apply AlternatingMap.ext
  intro v
  simp only [wedgeZeroRight_apply, toFunction_oneZeroForm, mul_one]

lemma wedgeZeroLeft_zero {n : ℕ} (ω : FiberwiseDifferentialForm R X n) :
    wedgeZeroLeft (0 : FiberwiseDifferentialForm R X 0) ω = 0 := by
  funext x
  apply AlternatingMap.ext
  intro v
  simp only [wedgeZeroLeft_apply, toFunction, Pi.zero_apply, AlternatingMap.zero_apply,
    zero_mul]

lemma wedgeZeroRight_zero {n : ℕ} (f : FiberwiseDifferentialForm R X 0) :
    wedgeZeroRight (0 : FiberwiseDifferentialForm R X n) f = 0 := by
  funext x
  apply AlternatingMap.ext
  intro v
  simp only [wedgeZeroRight_apply, Pi.zero_apply, AlternatingMap.zero_apply, zero_mul]

lemma wedgeZeroLeft_add_left {n : ℕ} (f g : FiberwiseDifferentialForm R X 0)
    (ω : FiberwiseDifferentialForm R X n) :
    wedgeZeroLeft (f + g) ω = wedgeZeroLeft f ω + wedgeZeroLeft g ω := by
  funext x
  apply AlternatingMap.ext
  intro v
  simp only [wedgeZeroLeft_apply, toFunction, Pi.add_apply, AlternatingMap.add_apply]
  ring

lemma wedgeZeroLeft_add_right {n : ℕ} (f : FiberwiseDifferentialForm R X 0)
    (ω η : FiberwiseDifferentialForm R X n) :
    wedgeZeroLeft f (ω + η) = wedgeZeroLeft f ω + wedgeZeroLeft f η := by
  funext x
  apply AlternatingMap.ext
  intro v
  simp only [wedgeZeroLeft_apply, Pi.add_apply, AlternatingMap.add_apply]
  ring

lemma wedgeZeroLeft_smul_left {n : ℕ} (c : R)
    (f : FiberwiseDifferentialForm R X 0) (ω : FiberwiseDifferentialForm R X n) :
    wedgeZeroLeft (c • f) ω = c • wedgeZeroLeft f ω := by
  funext x
  apply AlternatingMap.ext
  intro v
  simp only [wedgeZeroLeft_apply, toFunction, Pi.smul_apply, AlternatingMap.smul_apply,
    smul_eq_mul]
  ring

lemma wedgeZeroLeft_smul_right {n : ℕ} (c : R)
    (f : FiberwiseDifferentialForm R X 0) (ω : FiberwiseDifferentialForm R X n) :
    wedgeZeroLeft f (c • ω) = c • wedgeZeroLeft f ω := by
  funext x
  apply AlternatingMap.ext
  intro v
  simp only [wedgeZeroLeft_apply, Pi.smul_apply, AlternatingMap.smul_apply, smul_eq_mul]
  ring

lemma toFunction_pullback {Y : Type u} [Microlinear R Y] (h : X → Y)
    (f : FiberwiseDifferentialForm R Y 0) :
    toFunction (pullback h f) = toFunction f ∘ h := by
  funext x
  unfold toFunction
  change f (h x) (fun i ↦ tangentMapAtLinear R h (Fin.elim0 i)) =
    f (h x) (fun i ↦ Fin.elim0 i)
  congr 1
  funext i
  exact Fin.elim0 i

lemma wedgeZeroLeft_pullback {Y : Type u} [Microlinear R Y] (h : X → Y)
    {n : ℕ} (f : FiberwiseDifferentialForm R Y 0)
    (ω : FiberwiseDifferentialForm R Y n) :
    pullback h (wedgeZeroLeft f ω) =
      wedgeZeroLeft (pullback h f) (pullback h ω) := by
  funext x
  apply AlternatingMap.ext
  intro v
  change toFunction f (h x) * ω (h x) (fun i ↦ tangentMapAtLinear R h (v i)) =
    toFunction (pullback h f) x * pullback h ω x v
  rw [congrFun (toFunction_pullback h f) x]
  rfl

end FiberwiseDifferentialForm

/-! ## 构造性有限置换

Mathlib 的 `Equiv.Perm` 有限指标实例与 `List.permutations` 均传递依赖
`Classical.choice`；这里给出 `Fin n` 置换的构造性归纳编码，用于后续
一般次数 shuffle 楔积，全程通过 no-choice linter。

编码方式：`cons σ i` 表示由 `Fin n` 的置换 `σ` 扩张出的 `Fin (n+1)` 置换，
其中新增元素（编码为坐标 `0`）落在第 `i` 个位置，其余分量经 Mathlib
无选择的 `Fin.succAbove` 嵌入并跳过 `i`。 -/

/-- 交换 `Fin n` 中两个坐标的自映射（构造性定义，无选择公理）。 -/
def swapFin {n : ℕ} (i j : Fin n) : Fin n → Fin n :=
  fun k => if k = i then j else if k = j then i else k

lemma swapFin_self_left {n : ℕ} (i j : Fin n) :
    swapFin i j i = j := by
  simp [swapFin]

lemma swapFin_self_right {n : ℕ} (i j : Fin n) :
    swapFin i j j = i := by
  by_cases h : j = i
  · unfold swapFin
    rw [if_pos h]
    exact h
  · unfold swapFin
    rw [if_neg h]
    simp

lemma swapFin_of_ne {n : ℕ} {i j k : Fin n} (h1 : k ≠ i) (h2 : k ≠ j) :
    swapFin i j k = k := by
  simp only [swapFin, if_neg h1, if_neg h2]

lemma swapFin_leftInverse {n : ℕ} (i j : Fin n) :
    Function.LeftInverse (swapFin j i) (swapFin i j) := by
  intro k
  by_cases h1 : k = i
  · subst k
    rw [swapFin_self_left, swapFin_self_left]
  · by_cases h2 : k = j
    · subst k
      rw [swapFin_self_right, swapFin_self_right]
    · rw [swapFin_of_ne h1 h2, swapFin_of_ne h2 h1]

lemma swapFin_injective {n : ℕ} (i j : Fin n) :
    Function.Injective (swapFin i j) :=
  Function.LeftInverse.injective (swapFin_leftInverse i j)

inductive FinPerm : ℕ → Type where
  | nil : FinPerm 0
  | cons {n : ℕ} (σ : FinPerm n) (i : Fin (n + 1)) : FinPerm (n + 1)

namespace FinPerm

/-- 把 `k : Fin n` 插入 `Fin (n+1)` 并跳过位置 `i`（纯 ℕ 比较，无选择公理）。 -/
def insertAt {n : ℕ} (i : Fin (n + 1)) (k : Fin n) : Fin (n + 1) :=
  if (k : ℕ) < (i : ℕ) then ⟨(k : ℕ), by have := k.isLt; omega⟩
  else ⟨(k : ℕ) + 1, by have := k.isLt; omega⟩

lemma insertAt_ne {n : ℕ} (i : Fin (n + 1)) (k : Fin n) :
    insertAt i k ≠ i := by
  have h1 := k.isLt
  have hi := i.isLt
  by_cases hl : (k : ℕ) < (i : ℕ)
  · intro hEq
    rw [insertAt, if_pos hl] at hEq
    have hv : (k : ℕ) = (i : ℕ) := congrArg Fin.val hEq
    omega
  · intro hEq
    rw [insertAt, if_neg hl] at hEq
    have hv : (k : ℕ) + 1 = (i : ℕ) := congrArg Fin.val hEq
    omega

lemma insertAt_injective {n : ℕ} (i : Fin (n + 1)) :
    Function.Injective (insertAt i) := by
  intro k₁ k₂ hEq
  have h1 := k₁.isLt
  have h2 := k₂.isLt
  have hi := i.isLt
  by_cases hl₁ : (k₁ : ℕ) < (i : ℕ) <;> by_cases hl₂ : (k₂ : ℕ) < (i : ℕ)
  · rw [insertAt, if_pos hl₁, insertAt, if_pos hl₂] at hEq
    exact Fin.ext (by simpa using congrArg Fin.val hEq)
  · rw [insertAt, if_pos hl₁, insertAt, if_neg hl₂] at hEq
    have hv : (k₁ : ℕ) = (k₂ : ℕ) + 1 := by
      simpa using congrArg Fin.val hEq
    omega
  · rw [insertAt, if_neg hl₁, insertAt, if_pos hl₂] at hEq
    have hv : (k₁ : ℕ) + 1 = (k₂ : ℕ) := by
      simpa using congrArg Fin.val hEq
    omega
  · rw [insertAt, if_neg hl₁, insertAt, if_neg hl₂] at hEq
    exact Fin.ext (by simpa using congrArg Fin.val hEq)

/-- 置换在 `Fin n` 上的作用：`0 ↦ i`，后继分量经 `insertAt` 嵌入。 -/
def toFun {n : ℕ} : FinPerm n → Fin n → Fin n
  | .nil, j => j
  | .cons σ i, j => Fin.cases i (fun k ↦ insertAt i (σ.toFun k)) j

lemma toFun_nil (j : Fin 0) :
    toFun (FinPerm.nil : FinPerm 0) j = j := rfl

lemma toFun_cons_zero {n : ℕ} (σ : FinPerm n) (i : Fin (n + 1)) :
    toFun (cons σ i) 0 = i := rfl

lemma toFun_cons_succ {n : ℕ} (σ : FinPerm n) (i : Fin (n + 1)) (k : Fin n) :
    toFun (cons σ i) k.succ = insertAt i (σ.toFun k) := rfl

/-- 置换作用是单射（归纳于编码）。 -/
lemma toFun_injective : ∀ {n : ℕ} (π : FinPerm n), Function.Injective π.toFun := by
  intro n π
  induction π with
  | nil =>
      intro j₁ j₂ h
      simpa only [toFun] using h
  | cons σ i ih =>
      intro a b hab
      cases a using Fin.cases with
      | zero =>
          cases b using Fin.cases with
          | zero => rfl
          | succ b' =>
              rw [toFun_cons_zero, toFun_cons_succ] at hab
              exact absurd hab.symm (insertAt_ne i (σ.toFun b'))
      | succ a' =>
          cases b using Fin.cases with
          | zero =>
              rw [toFun_cons_succ, toFun_cons_zero] at hab
              exact absurd hab (insertAt_ne i (σ.toFun a'))
          | succ b' =>
              rw [toFun_cons_succ, toFun_cons_succ] at hab
              exact congrArg Fin.succ (ih (insertAt_injective i hab))

/-- 逆序数：插入到第 `i` 位贡献 `i` 个逆序。 -/
def depth : FinPerm n → ℕ
  | .nil => 0
  | .cons σ i => depth σ + (i : ℕ)

lemma depth_nil : depth (FinPerm.nil : FinPerm 0) = 0 := rfl

lemma depth_cons {n : ℕ} (σ : FinPerm n) (i : Fin (n + 1)) :
    depth (cons σ i) = depth σ + (i : ℕ) := rfl

/-- 置换符号：`-1` 的逆序数次幂。 -/
def sign (R : Type u) [CommRing R] {n : ℕ} (π : FinPerm n) : R :=
  (-1 : R) ^ (depth π)

lemma sign_nil (R : Type u) [CommRing R] :
    sign R (FinPerm.nil : FinPerm 0) = 1 := by
  show (-1 : R) ^ (depth (FinPerm.nil : FinPerm 0)) = 1
  rw [depth_nil, pow_zero]

lemma sign_cons (R : Type u) [CommRing R] {n : ℕ} (σ : FinPerm n) (i : Fin (n + 1)) :
    sign R (cons σ i) = sign R σ * (-1 : R) ^ (i : ℕ) := by
  rw [sign, sign, depth_cons, pow_add]

lemma sign_cons_zero (R : Type u) [CommRing R] {n : ℕ} (σ : FinPerm n) :
    sign R (cons σ 0) = sign R σ := by
  rw [sign_cons]
  simp

/-- `finSum` 对常值函数求和等于数乘。 -/
lemma finSum_const (R : Type u) [AddCommMonoid R] (k : ℕ) (x : R) :
    finSum R k (fun _ : Fin k ↦ x) = k • x := by
  induction k with
  | zero => rw [finSum_zero, zero_smul]
  | succ k ih =>
      rw [finSum_succ, ih, succ_nsmul']

/-- 对所有 `Fin n` 置换求和（无选择公理：递归展开为项目的 `finSum`）。 -/
def permSum (R : Type u) [AddCommMonoid R] : {n : ℕ} → (FinPerm n → R) → R
  | 0, f => f .nil
  | n + 1, f => finSum R (n + 1) (fun i ↦ permSum R (fun σ : FinPerm n ↦ f (.cons σ i)))

lemma permSum_zero (R : Type u) [AddCommMonoid R] (f : FinPerm 0 → R) :
    permSum R f = f .nil := rfl

lemma permSum_succ (R : Type u) [AddCommMonoid R] (n : ℕ)
    (f : FinPerm (n + 1) → R) :
    permSum R f =
      finSum R (n + 1) (fun i ↦ permSum R (fun σ : FinPerm n ↦ f (.cons σ i))) := rfl

/-- 置换和关于函数加法可分配。 -/
lemma permSum_add (R : Type u) [AddCommMonoid R] {n : ℕ}
    (f g : FinPerm n → R) :
    permSum R (fun π ↦ f π + g π) = permSum R f + permSum R g := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [permSum_succ, ih, finSum_add]

/-- 常值置换和：`n!` 项之和。 -/
lemma permSum_const (R : Type u) [AddCommMonoid R] (n : ℕ) (c : R) :
    permSum R (fun _ : FinPerm n ↦ c) = Nat.factorial n • c := by
  induction n with
  | zero => simp [permSum_zero]
  | succ n ih =>
      rw [permSum_succ]
      have hterm : (fun _i : Fin (n + 1) ↦
          permSum R (fun σ : FinPerm n ↦ (fun _p : FinPerm (n + 1) ↦ c) (.cons σ _i))) =
          (fun _i : Fin (n + 1) ↦ Nat.factorial n • c) := by
        funext i
        exact ih
      rw [hterm, finSum_const, Nat.factorial_succ, smul_smul]

/-! ### 从单射函数恢复置换编码

`insertAt` 与 `unshift` 互逆，从而任何单射自映射（即 `Fin n` 的置换）
都由插入编码给出。这是「编码枚举全部置换」的构造性证明，也是
swap 配对消去论证的基础。 -/

/-- `insertAt i` 的右逆方向辅助：把 `w ≠ i` 压回 `Fin n`
（大于 `i` 的坐标减一，小于 `i` 的坐标不变）。 -/
def unshift {n : ℕ} (i : Fin (n + 1)) (w : Fin (n + 1)) (hw : w ≠ i) : Fin n :=
  dite ((i : ℕ) < (w : ℕ))
    (fun hlt => ⟨(w : ℕ) - 1, by have := w.isLt; have := i.isLt; omega⟩)
    (fun hge => ⟨(w : ℕ), by
      have := w.isLt
      have := i.isLt
      have hne : (w : ℕ) ≠ (i : ℕ) := by
        intro hc
        exact hw (Fin.ext hc)
      omega⟩)

lemma insertAt_unshift {n : ℕ} (i : Fin (n + 1)) (w : Fin (n + 1)) (hw : w ≠ i) :
    insertAt i (unshift i w hw) = w := by
  have hi := i.isLt
  have hw2 := w.isLt
  have hne : (i : ℕ) ≠ (w : ℕ) := by
    intro hc
    exact hw (Fin.ext hc).symm
  unfold insertAt unshift
  by_cases hlt : (i : ℕ) < (w : ℕ)
  · rw [dif_pos hlt]
    by_cases h2 : ((w : ℕ) - 1 : ℕ) < (i : ℕ)
    · exfalso
      omega
    · rw [if_neg h2]
      have hsum : (w : ℕ) - 1 + 1 = (w : ℕ) := by omega
      exact Fin.ext (by simpa using hsum)
  · rw [dif_neg hlt]
    by_cases h2 : ((w : ℕ) : ℕ) < (i : ℕ)
    · rw [if_pos h2]
    · exact absurd (Fin.ext (by omega)) hw

lemma unshift_injective {n : ℕ} (i : Fin (n + 1)) {w₁ w₂ : Fin (n + 1)}
    (hw₁ : w₁ ≠ i) (hw₂ : w₂ ≠ i) (hEq : unshift i w₁ hw₁ = unshift i w₂ hw₂) :
    w₁ = w₂ := by
  have hi := i.isLt
  have h1 := w₁.isLt
  have h2 := w₂.isLt
  have hne₁ : (w₁ : ℕ) ≠ (i : ℕ) := by
    intro hc
    exact hw₁ (Fin.ext hc)
  have hne₂ : (w₂ : ℕ) ≠ (i : ℕ) := by
    intro hc
    exact hw₂ (Fin.ext hc)
  unfold unshift at hEq
  by_cases hlt₁ : (i : ℕ) < (w₁ : ℕ) <;> by_cases hlt₂ : (i : ℕ) < (w₂ : ℕ)
  · rw [dif_pos hlt₁, dif_pos hlt₂] at hEq
    have hv : (w₁ : ℕ) - 1 = (w₂ : ℕ) - 1 := by
      simpa using congrArg Fin.val hEq
    exact Fin.ext (by omega)
  · rw [dif_pos hlt₁, dif_neg hlt₂] at hEq
    have hv : (w₁ : ℕ) - 1 = (w₂ : ℕ) := by
      simpa using congrArg Fin.val hEq
    exact absurd (Fin.ext (by omega)) hw₂
  · rw [dif_neg hlt₁, dif_pos hlt₂] at hEq
    have hv : (w₁ : ℕ) = (w₂ : ℕ) - 1 := by
      simpa using congrArg Fin.val hEq
    exact absurd (Fin.ext (by omega)) hw₁
  · rw [dif_neg hlt₁, dif_neg hlt₂] at hEq
    exact Fin.ext (by simpa using congrArg Fin.val hEq)

/-- 从单射自映射恢复插入编码：`FinPerm` 枚举全部单射自映射。 -/
def encode : {n : ℕ} → (f : Fin n → Fin n) → Function.Injective f → FinPerm n
  | 0, _f, _hf => .nil
  | n + 1, f, hf =>
      have hsucc : Function.Injective (fun k : Fin n ↦ f k.succ) :=
        hf.comp (Fin.succ_injective n)
      have hne : ∀ k : Fin n, f k.succ ≠ f 0 := by
        intro k hEq
        exact Fin.succ_ne_zero k (hf hEq)
      have hg : Function.Injective
          (fun k : Fin n ↦ unshift (f 0) (f k.succ) (hne k)) := by
        intro k₁ k₂ hEq
        exact Fin.succ_injective n
          (hf (unshift_injective (f 0) (hne k₁) (hne k₂) hEq))
      .cons (encode (fun k : Fin n ↦ unshift (f 0) (f k.succ) (hne k)) hg) (f 0)

lemma toFun_encode : ∀ {n : ℕ} (f : Fin n → Fin n) (hf : Function.Injective f),
    (encode f hf).toFun = f := by
  intro n f hf
  induction n with
  | zero =>
      funext j
      exact Fin.elim0 j
  | succ n ih =>
      have hsucc : Function.Injective (fun k : Fin n ↦ f k.succ) :=
        hf.comp (Fin.succ_injective n)
      have hne : ∀ k : Fin n, f k.succ ≠ f 0 := by
        intro k hEq
        exact Fin.succ_ne_zero k (hf hEq)
      have hg : Function.Injective
          (fun k : Fin n ↦ unshift (f 0) (f k.succ) (hne k)) := by
        intro k₁ k₂ hEq
        exact Fin.succ_injective n
          (hf (unshift_injective (f 0) (hne k₁) (hne k₂) hEq))
      have henc := ih (fun k : Fin n ↦ unshift (f 0) (f k.succ) (hne k)) hg
      have hcons : (encode f hf).toFun =
          (FinPerm.cons
            (encode (fun k : Fin n ↦ unshift (f 0) (f k.succ) (hne k)) hg) (f 0)).toFun := rfl
      funext j
      cases j using Fin.cases with
      | zero => rfl
      | succ k =>
          rw [hcons, toFun_cons_succ, henc]
          exact insertAt_unshift (f 0) (f k.succ) (hne k)

/-- 置换作用的构造性逆映射。 -/
def inv : {n : ℕ} → FinPerm n → Fin n → Fin n
  | 0, .nil => fun w => w
  | n + 1, .cons σ i => fun w =>
      dite (w = i) (fun _ => 0) (fun hw => Fin.succ (inv σ (unshift i w hw)))

/-- 逆映射是右逆：`π.toFun (π.inv w) = w`。 -/
lemma map_inv : ∀ {n : ℕ} (π : FinPerm n) (w : Fin n), π.toFun (π.inv w) = w := by
  intro n
  induction n with
  | zero =>
      intro π w
      cases π
      exact Fin.elim0 w
  | succ n ih =>
      intro π w
      cases π with
      | cons σ i =>
          simp only [inv]
          by_cases hw : w = i
          · rw [dif_pos hw, hw, toFun_cons_zero]
          · rw [dif_neg hw, toFun_cons_succ]
            have hun := ih σ (unshift i w hw)
            rw [hun]
            exact insertAt_unshift i w hw

/-- 置换作用是双射。 -/
lemma toFun_bijective {n : ℕ} (π : FinPerm n) : Function.Bijective π.toFun := by
  constructor
  · exact π.toFun_injective
  · intro w
    exact ⟨π.inv w, π.map_inv w⟩

lemma ext_toFun : ∀ {n : ℕ} (π₁ π₂ : FinPerm n), π₁.toFun = π₂.toFun → π₁ = π₂ := by
  intro n
  induction n with
  | zero =>
      intro π₁ π₂ _h
      cases π₁ <;> cases π₂ <;> rfl
  | succ n ih =>
      intro π₁ π₂ h
      cases π₁ with
      | cons σ₁ i₁ =>
          cases π₂ with
          | cons σ₂ i₂ =>
              have h0 : i₁ = i₂ := by
                have h1 := congrFun h 0
                rw [toFun_cons_zero, toFun_cons_zero] at h1
                exact h1
              have hs : σ₁.toFun = σ₂.toFun := by
                funext k
                have hk := congrFun h k.succ
                rw [toFun_cons_succ, toFun_cons_succ, h0] at hk
                exact insertAt_injective i₂ hk
              rw [ih σ₁ σ₂ hs, h0]

/-! ### 坐标交换的编码表示 -/

lemma swapFin_comm {n : ℕ} (i j k : Fin n) :
    swapFin i j k = swapFin j i k := by
  unfold swapFin
  by_cases h1 : k = i <;> by_cases h2 : k = j
  · rw [if_pos h1, if_pos h2]
    exact (h1.symm.trans h2).symm
  · rw [if_pos h1, if_neg h2, if_pos h1]
  · rw [if_neg h1, if_pos h2, if_pos h2]
  · rw [if_neg h1, if_neg h2, if_neg h2, if_neg h1]

lemma swapFin_involutive {n : ℕ} (i j : Fin n) (k : Fin n) :
    swapFin i j (swapFin i j k) = k := by
  rw [swapFin_comm i j (swapFin i j k)]
  exact swapFin_leftInverse i j k

/-- 置换编码经坐标交换的左复合表示。 -/
def compSwap {n : ℕ} (i j : Fin n) (π : FinPerm n) : FinPerm n :=
  encode (fun k ↦ π.toFun (swapFin i j k))
    (π.toFun_injective.comp (swapFin_injective i j))

lemma toFun_compSwap {n : ℕ} (i j : Fin n) (π : FinPerm n) :
    (π.compSwap i j).toFun = fun k ↦ π.toFun (swapFin i j k) :=
  toFun_encode _ _

lemma compSwap_involutive {n : ℕ} (i j : Fin n) (π : FinPerm n) :
    (π.compSwap i j).compSwap i j = π := by
  have hX : ((π.compSwap i j).compSwap i j).toFun = π.toFun := by
    rw [toFun_compSwap, toFun_compSwap]
    funext k
    change π.toFun (swapFin i j (swapFin i j k)) = π.toFun k
    rw [swapFin_involutive]
  exact ext_toFun _ _ hX

/-! ### 构造性置换的复合代数 -/

/-- 恒等置换的构造性编码。 -/
def identity {n : ℕ} : FinPerm n :=
  encode id Function.injective_id

lemma toFun_identity {n : ℕ} :
    (identity : FinPerm n).toFun = id :=
  toFun_encode _ _

/-- 两个构造性置换的复合。 -/
def compose {n : ℕ} (π₁ π₂ : FinPerm n) : FinPerm n :=
  encode (fun k ↦ π₁.toFun (π₂.toFun k))
    (π₁.toFun_injective.comp π₂.toFun_injective)

lemma toFun_compose {n : ℕ} (π₁ π₂ : FinPerm n) :
    (compose π₁ π₂).toFun = fun k ↦ π₁.toFun (π₂.toFun k) :=
  toFun_encode _ _

lemma compose_identity_left {n : ℕ} (π : FinPerm n) :
    compose identity π = π := by
  apply ext_toFun _ _
  rw [toFun_compose, toFun_identity]
  funext k
  rfl

lemma compose_identity_right {n : ℕ} (π : FinPerm n) :
    compose π identity = π := by
  apply ext_toFun _ _
  rw [toFun_compose, toFun_identity]
  funext k
  rfl

lemma compose_assoc {n : ℕ} (π₁ π₂ π₃ : FinPerm n) :
    compose (compose π₁ π₂) π₃ = compose π₁ (compose π₂ π₃) := by
  apply ext_toFun _ _
  rw [toFun_compose, toFun_compose, toFun_compose, toFun_compose]

/-- 交换两个 `Fin n` 坐标的构造性置换。 -/
def swapPerm {n : ℕ} (i j : Fin n) : FinPerm n :=
  encode (swapFin i j) (swapFin_injective i j)

lemma toFun_swapPerm {n : ℕ} (i j : Fin n) :
    (swapPerm i j).toFun = swapFin i j :=
  toFun_encode _ _

lemma swapPerm_involutive {n : ℕ} (i j : Fin n) :
    compose (swapPerm i j) (swapPerm i j) = identity := by
  apply ext_toFun _ _
  rw [toFun_compose, toFun_identity]
  simp only [toFun_swapPerm, id_eq]
  funext k
  change swapFin i j (swapFin i j k) = k
  rw [swapFin_involutive]

lemma compSwap_eq_compose_swapPerm {n : ℕ} (i j : Fin n) (π : FinPerm n) :
    π.compSwap i j = compose π (swapPerm i j) := by
  apply ext_toFun _ _
  rw [toFun_compSwap, toFun_compose, toFun_swapPerm]

/-! ### 单射自映射的计数 -/

/-- 单射自映射是满射。 -/
lemma surjective_of_injective_self {n : ℕ} {f : Fin n → Fin n}
    (hf : Function.Injective f) : Function.Surjective f := by
  have hb := (FinPerm.encode f hf).toFun_bijective
  have hEq : f = (FinPerm.encode f hf).toFun := (FinPerm.toFun_encode f hf).symm
  rw [hEq]
  exact hb.2

/-- 单射自映射下，取值等于 `c` 的指标恰有一个。 -/
lemma finSum_indicator_eq_one {n : ℕ} {f : Fin n → Fin n}
    (hf : Function.Injective f) (c : Fin n) :
    finSum ℕ n (fun k ↦ if f k = c then 1 else 0) = 1 := by
  obtain ⟨k₀, hk₀⟩ := surjective_of_injective_self hf c
  have heq : (fun k : Fin n ↦ if f k = c then (1:ℕ) else 0) =
      (fun k : Fin n ↦ if k = k₀ then (1:ℕ) else 0) := by
    funext k
    by_cases h : k = k₀
    · subst k
      simp [hk₀]
    · have hne : f k ≠ c := by
        intro hc
        exact h (hf (hc.trans hk₀.symm))
      simp [hne, h]
  rw [heq]
  exact finSum_eq_single ℕ k₀ 1

/-- 单射自映射下，取值小于 `i` 的指标恰有 `i` 个。 -/
lemma finSum_count_lt {n : ℕ} {f : Fin n → Fin n} (hf : Function.Injective f) :
    ∀ (m : ℕ), m ≤ n →
      finSum ℕ n (fun k ↦ if (f k : ℕ) < m then (1:ℕ) else 0) = m := by
  intro m
  induction m with
  | zero =>
      intro _
      rw [finSum_eq_zero]
      intro k
      simp
  | succ m ih =>
      intro hm
      have hmn : m < n := by omega
      have hsplit : (fun k : Fin n ↦ if (f k : ℕ) < m + 1 then (1:ℕ) else 0) =
          (fun k : Fin n ↦ (if (f k : ℕ) < m then (1:ℕ) else 0) +
            (if (f k : ℕ) = m then 1 else 0)) := by
        funext k
        by_cases h : (f k : ℕ) < m
        · rw [if_pos (by omega : (f k : ℕ) < m + 1), if_pos h,
            if_neg (by omega : ¬((f k : ℕ) = m))]
        · by_cases h2 : (f k : ℕ) = m
          · rw [if_pos (by omega : (f k : ℕ) < m + 1), if_neg h, if_pos h2]
          · rw [if_neg (by omega : ¬((f k : ℕ) < m + 1)), if_neg h, if_neg h2]
      have hval : (fun k : Fin n ↦ if (f k : ℕ) = m then (1:ℕ) else 0) =
          (fun k : Fin n ↦ if f k = (⟨m, hmn⟩ : Fin n) then 1 else 0) := by
        funext k
        by_cases h2 : (f k : ℕ) = m
        · have heq : f k = (⟨m, hmn⟩ : Fin n) := Fin.ext (by simpa using h2)
          simp [heq]
        · have hne : f k ≠ (⟨m, hmn⟩ : Fin n) := by
            intro hc
            exact h2 (congrArg Fin.val hc)
          simp [h2, hne]
      rw [hsplit, finSum_add, hval,
        finSum_indicator_eq_one hf (⟨m, hmn⟩ : Fin n), ih (by omega)]

/-! ### `insertAt` 的序性质（逆序数分析用） -/

/-- `insertAt i k` 的数值展开。 -/
lemma insertAt_val {n : ℕ} (i : Fin (n + 1)) (k : Fin n) :
    ((insertAt i k : Fin (n + 1)) : ℕ) =
      if (k : ℕ) < (i : ℕ) then (k : ℕ) else (k : ℕ) + 1 := by
  unfold insertAt
  split <;> rfl

/-- `insertAt` 保持严格序。 -/
lemma insertAt_lt_iff {n : ℕ} (i : Fin (n + 1)) (k k' : Fin n) :
    ((insertAt i k : Fin (n + 1)) : ℕ) < ((insertAt i k' : Fin (n + 1)) : ℕ) ↔
      (k : ℕ) < (k' : ℕ) := by
  rw [insertAt_val, insertAt_val]
  by_cases h1 : (k : ℕ) < (i : ℕ) <;> by_cases h2 : (k' : ℕ) < (i : ℕ)
  · rw [if_pos h1, if_pos h2]
  · rw [if_pos h1, if_neg h2]
    exact ⟨fun h => by omega, fun h => by omega⟩
  · rw [if_neg h1, if_pos h2]
    exact ⟨fun h => by omega, fun h => by omega⟩
  · rw [if_neg h1, if_neg h2]
    exact ⟨fun h => by omega, fun h => by omega⟩

/-- 插入值落在枢轴之前当且仅当原值在枢轴之前。 -/
lemma insertAt_lt_pivot_iff {n : ℕ} (i : Fin (n + 1)) (k : Fin n) :
    ((insertAt i k : Fin (n + 1)) : ℕ) < (i : ℕ) ↔ (k : ℕ) < (i : ℕ) := by
  rw [insertAt_val]
  by_cases h : (k : ℕ) < (i : ℕ)
  · rw [if_pos h]
  · rw [if_neg h]
    exact ⟨fun hc => by omega, fun hc => by omega⟩

/-- 插入值落在枢轴之后当且仅当原值不小于枢轴。 -/
lemma insertAt_gt_pivot_iff {n : ℕ} (i : Fin (n + 1)) (k : Fin n) :
    (i : ℕ) < ((insertAt i k : Fin (n + 1)) : ℕ) ↔ (i : ℕ) ≤ (k : ℕ) := by
  rw [insertAt_val]
  split
  · exact ⟨fun h => by omega, fun h => by omega⟩
  · exact ⟨fun h => by omega, fun h => by omega⟩

/-- 标准逆序计数：数所有满足 `a < j` 且 `π a > π j` 的对（无选择公理）。 -/
def invCount (π : FinPerm n) : ℕ :=
  finSum ℕ n (fun j : Fin n ↦
    finSum ℕ n (fun a : Fin n ↦
      if (a : ℕ) < (j : ℕ) then
        if (π.toFun a : ℕ) > (π.toFun j : ℕ) then 1 else 0
      else 0))

lemma invCount_zero : invCount (FinPerm.nil : FinPerm 0) = 0 := by
  rfl

lemma nat_gt_iff_lt {x y : ℕ} : x > y ↔ y < x := Iff.rfl

/-- 归纳步骤：插入编码的逆序数 = 剩余部分逆序数 + 插入位置贡献。

所有 toForm 重写都在具体点（`finSum_succ` 分离出的字面量与逐点 `funext`）
上进行，函数级替换一律经 `congrArg` 传递，避免 ite 的 `Decidable`
实例在 lambda 内不同步的问题。 -/
lemma invCount_cons {n : ℕ} (σ : FinPerm n) (i : Fin (n + 1)) :
    invCount (cons σ i) = invCount σ + (i : ℕ) := by
  unfold invCount
  rw [finSum_succ (R := ℕ) (n := n) (f := fun j : Fin (n + 1) ↦
      finSum ℕ (n + 1) (fun a : Fin (n + 1) ↦
        if (a : ℕ) < (j : ℕ) then
          if ((cons σ i).toFun a : ℕ) > ((cons σ i).toFun j : ℕ) then 1 else 0
        else 0))]
  have h0 : (finSum ℕ (n + 1) (fun a : Fin (n + 1) ↦
      if (a : ℕ) < ((0 : Fin (n + 1)) : ℕ) then
        if ((cons σ i).toFun a : ℕ) > ((cons σ i).toFun 0 : ℕ) then 1 else 0
      else 0) : ℕ) = 0 := by
    rw [finSum_eq_zero]
    intro a
    simp
  rw [h0, zero_add]
  have hstep : ∀ j' : Fin n,
      (finSum ℕ (n + 1) (fun a : Fin (n + 1) ↦
          if (a : ℕ) < ((j'.succ : Fin (n + 1)) : ℕ) then
            if ((cons σ i).toFun a : ℕ) >
              ((cons σ i).toFun (j'.succ : Fin (n + 1)) : ℕ) then 1 else 0
          else 0) : ℕ) =
        (if (σ.toFun j' : ℕ) < (i : ℕ) then (1 : ℕ) else 0) +
        (finSum ℕ n (fun a' : Fin n ↦
          if (a' : ℕ) < (j' : ℕ) then
            if (σ.toFun a' : ℕ) > (σ.toFun j' : ℕ) then 1 else 0
          else 0) : ℕ) := by
    intro j'
    rw [finSum_succ (R := ℕ) (n := n) (f := fun a : Fin (n + 1) ↦
        if (a : ℕ) < ((j'.succ : Fin (n + 1)) : ℕ) then
          if ((cons σ i).toFun a : ℕ) >
            ((cons σ i).toFun (j'.succ : Fin (n + 1)) : ℕ) then 1 else 0
        else 0)]
    have hzp : (0 : ℕ) < ((j'.succ : Fin (n + 1)) : ℕ) := by
      show 0 < (j' : ℕ) + 1
      omega
    rw [Fin.val_zero, if_pos hzp, toFun_cons_zero, toFun_cons_succ]
    have hcond0 : ((i : ℕ) > ((insertAt i (σ.toFun j') : Fin (n + 1)) : ℕ)) ↔
        ((σ.toFun j' : ℕ) < (i : ℕ)) := by
      rw [nat_gt_iff_lt, insertAt_lt_pivot_iff]
    simp only [hcond0]
    have hin' : ∀ a' : Fin n,
        (if ((a'.succ : Fin (n + 1)) : ℕ) < ((j'.succ : Fin (n + 1)) : ℕ) then
            if ((cons σ i).toFun (a'.succ : Fin (n + 1)) : ℕ) >
              ((cons σ i).toFun (j'.succ : Fin (n + 1)) : ℕ) then 1 else 0
          else 0) =
        (if (a' : ℕ) < (j' : ℕ) then
            if (σ.toFun a' : ℕ) > (σ.toFun j' : ℕ) then 1 else 0
          else 0) := by
      intro a'
      simp only [toFun_cons_succ, Fin.val_succ, Nat.succ_lt_succ_iff,
        nat_gt_iff_lt, insertAt_lt_iff]
    exact congrArg (fun x : ℕ ↦ (if (σ.toFun j' : ℕ) < (i : ℕ) then (1 : ℕ) else 0) + x)
      (congrArg (finSum ℕ n) (funext hin'))
  simp only [hstep]
  rw [finSum_add]
  have hcount : (finSum ℕ n (fun j' : Fin n ↦
      if (σ.toFun j' : ℕ) < (i : ℕ) then (1 : ℕ) else 0) : ℕ) = (i : ℕ) :=
    finSum_count_lt σ.toFun_injective (i : ℕ) (Nat.lt_succ_iff.mp i.isLt)
  rw [hcount]
  omega

/-- 插入深度与标准逆序计数一致。 -/
lemma depth_eq_invCount {n : ℕ} (π : FinPerm n) : depth π = invCount π := by
  induction π with
  | nil => rfl
  | cons σ i ih => rw [depth_cons, ih, invCount_cons]

/-! ### finSum 在相邻交换下的重参数化 -/

/-- `swapFin 0 1` 的三个求值性质（`Fin (n+2)` 上 0 和 1 总可用）。 -/
lemma swap01_zero {n : ℕ} :
    swapFin (0 : Fin (n + 2)) (1 : Fin (n + 2)) (0 : Fin (n + 2)) = (1 : Fin (n + 2)) := by
  simp [swapFin]

lemma swap01_one {n : ℕ} :
    swapFin (0 : Fin (n + 2)) (1 : Fin (n + 2)) (1 : Fin (n + 2)) = (0 : Fin (n + 2)) := by
  simp [swapFin]

lemma swap01_rest {n : ℕ} (k : Fin (n + 2)) (hk : (k : ℕ) ≥ 2) :
    swapFin (0 : Fin (n + 2)) (1 : Fin (n + 2)) k = k := by
  have hk0 : (k : Fin (n + 2)) ≠ (0 : Fin (n + 2)) := by
    intro hc
    have hv : (k : ℕ) = 0 := by simpa using congrArg Fin.val hc
    omega
  have hk1 : (k : Fin (n + 2)) ≠ (1 : Fin (n + 2)) := by
    intro hc
    have hv : (k : ℕ) = 1 := by simpa using congrArg Fin.val hc
    omega
  simp only [swapFin, if_neg hk0, if_neg hk1]

/-- `finSum` 在交换前两个位置的相邻对换下不变。

这是 sign 变号的核心基础设施。当前证明需要 finSum 重参数化理论，
暂留为后续工作；d² = 0 的证明通过面算子恒等式绕开此引理。 -/
lemma finSum_swap01 {n : ℕ} (f : Fin (n + 2) → ℕ) (hn : 2 ≤ n) :
    finSum ℕ (n + 2) f =
    finSum ℕ (n + 2) (fun a ↦ f (swapFin (0 : Fin (n + 2)) (1 : Fin (n + 2)) a)) := by
  -- 外层分离
  rw [finSum_succ (R := ℕ) (n := n + 1) (f := f)]
  rw [finSum_succ (R := ℕ) (n := n + 1)
    (f := fun a : Fin (n + 2) ↦ f (swapFin (0 : Fin (n + 2)) (1 : Fin (n + 2)) a))]
  -- 首项：swap 0 = 1
  rw [swap01_zero]
  -- 内层分离
  rw [finSum_succ (R := ℕ) (n := n) (f := fun i : Fin (n + 1) ↦ f i.succ)]
  rw [finSum_succ (R := ℕ) (n := n) (f := fun i : Fin (n + 1) ↦
    f (swapFin (0 : Fin (n + 2)) (1 : Fin (n + 2)) i.succ))]
  -- 内层尾部
  have hrest : ∀ j : Fin n,
      swapFin (0 : Fin (n + 2)) (1 : Fin (n + 2)) j.succ.succ = j.succ.succ := by
    intro j
    apply swap01_rest
    have hv : ((j.succ.succ : Fin (n+2)) : ℕ) = (j : ℕ) + 2 := rfl
    omega
  simp only [hrest]
  -- 归一化并处理所有 swapFin 残余
  have heq : (Fin.succ (0 : Fin (n + 1)) : Fin (n + 2)) = (1 : Fin (n + 2)) := rfl
  rw [heq]
  rw [swap01_one]
  abel

end FinPerm

/-! ### 相邻对换基础设施

`swapFinAdj j` 交换 `Fin (n+2)` 中位置 `j` 与 `j+1`（按值比较构造，无选择公理）。
核心组合事实：无选择求和 `finSum` 在任意位置的相邻对换下不变。
这是把 `1 ∧ n` 楔积展开式的「逐项配对消去」论证落到 `finSum` 上的重排基础。 -/

section SwapFinAdj

variable {R : Type u} [AddCommMonoid R]

/-- 交换 `Fin (n+2)` 中位置 `j` 与 `j+1` 的构造性自映射。 -/
def swapFinAdj {n : ℕ} (j : Fin n) (a : Fin (n + 1)) : Fin (n + 1) :=
  if (a : ℕ) = (j : ℕ) then ⟨(j : ℕ) + 1, by have := j.isLt; omega⟩
  else if (a : ℕ) = (j : ℕ) + 1 then ⟨(j : ℕ), by have := j.isLt; omega⟩
  else a

lemma swapFinAdj_eq {n : ℕ} {j : Fin n} {a : Fin (n + 1)} (h : (a : ℕ) = (j : ℕ)) :
    swapFinAdj j a = ⟨(j : ℕ) + 1, by have := j.isLt; omega⟩ := if_pos h

lemma swapFinAdj_eq_one {n : ℕ} {j : Fin n} {a : Fin (n + 1)}
    (h : (a : ℕ) = (j : ℕ) + 1) :
    swapFinAdj j a = ⟨(j : ℕ), by have := j.isLt; omega⟩ := by
  rw [swapFinAdj, if_neg (show (a : ℕ) ≠ (j : ℕ) by omega), if_pos h]

lemma swapFinAdj_of_ne {n : ℕ} {j : Fin n} {a : Fin (n + 1)}
    (h₁ : (a : ℕ) ≠ (j : ℕ)) (h₂ : (a : ℕ) ≠ (j : ℕ) + 1) :
    swapFinAdj j a = a := by
  rw [swapFinAdj, if_neg h₁, if_neg h₂]

lemma swapFinAdj_of_lt {n : ℕ} {j : Fin n} {a : Fin (n + 1)}
    (h : (a : ℕ) < (j : ℕ)) : swapFinAdj j a = a :=
  swapFinAdj_of_ne (by omega) (by omega)

lemma swapFinAdj_of_gt {n : ℕ} {j : Fin n} {a : Fin (n + 1)}
    (h : (a : ℕ) > (j : ℕ) + 1) : swapFinAdj j a = a :=
  swapFinAdj_of_ne (by omega) (by omega)

lemma swapFinAdj_val {n : ℕ} (j : Fin n) (a : Fin (n + 1)) :
    ((swapFinAdj j a : Fin (n + 1)) : ℕ) =
      if (a : ℕ) = (j : ℕ) then (j : ℕ) + 1
      else if (a : ℕ) = (j : ℕ) + 1 then (j : ℕ) else (a : ℕ) := by
  by_cases h₁ : (a : ℕ) = (j : ℕ)
  · rw [swapFinAdj_eq h₁, if_pos h₁]
  · by_cases h₂ : (a : ℕ) = (j : ℕ) + 1
    · rw [swapFinAdj_eq_one h₂, if_neg h₁, if_pos h₂]
    · rw [swapFinAdj_of_ne h₁ h₂, if_neg h₁, if_neg h₂]

lemma swapFinAdj_self {n : ℕ} (j : Fin n) (a : Fin (n + 1)) :
    swapFinAdj j (swapFinAdj j a) = a := by
  apply Fin.ext
  by_cases h₁ : (a : ℕ) = (j : ℕ)
  · have hval : ((swapFinAdj j a : Fin (n + 1)) : ℕ) = (j : ℕ) + 1 := by
      rw [swapFinAdj_val, if_pos h₁]
    rw [swapFinAdj_val, hval, if_neg (by omega), if_pos rfl]
    omega
  · by_cases h₂ : (a : ℕ) = (j : ℕ) + 1
    · have hval : ((swapFinAdj j a : Fin (n + 1)) : ℕ) = (j : ℕ) := by
        rw [swapFinAdj_val, if_neg h₁, if_pos h₂]
      rw [swapFinAdj_val, hval, if_pos (by omega)]
      omega
    · have hval : ((swapFinAdj j a : Fin (n + 1)) : ℕ) = (a : ℕ) := by
        rw [swapFinAdj_val, if_neg h₁, if_neg h₂]
      rw [swapFinAdj_val, hval, if_neg (by omega), if_neg (by omega)]

/-- 相邻对换与后继交换：在 `Fin (n+2)` 中对换位置 `j+1, j+2`，等价于先在
`Fin (n+1)` 中对换 `j, j+1` 再整体后移一格。 -/
lemma swapFinAdj_succ {n : ℕ} (j : Fin n) (i : Fin (n + 1)) :
    swapFinAdj (j.succ) (i.succ) = (swapFinAdj j i).succ := by
  apply Fin.ext
  have hjv : ((j.succ : Fin (n + 1)) : ℕ) = (j : ℕ) + 1 := rfl
  have hiv : ((i.succ : Fin (n + 2)) : ℕ) = (i : ℕ) + 1 := rfl
  have hs : (((swapFinAdj j i).succ : Fin (n + 2)) : ℕ)
      = ((swapFinAdj j i : Fin (n + 1)) : ℕ) + 1 := rfl
  rw [swapFinAdj_val, hiv, hjv, hs, swapFinAdj_val]
  by_cases h₁ : (i : ℕ) = (j : ℕ)
  · rw [h₁, if_pos rfl, if_pos rfl]
  · by_cases h₂ : (i : ℕ) = (j : ℕ) + 1
    · rw [h₂, if_neg (by omega), if_pos rfl, if_neg (by omega), if_pos rfl]
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- 位置 `0, 1` 的相邻对换：基点情形。 -/
lemma finSum_swapFinAdj_zero {n : ℕ} (f : Fin (n + 2) → R) :
    finSum R (n + 2) f =
    finSum R (n + 2) (fun a ↦ f (swapFinAdj (0 : Fin (n + 1)) a)) := by
  rw [finSum_succ (R := R) (n := n + 1) (f := f)]
  rw [finSum_succ (R := R) (n := n + 1)
    (f := fun a : Fin (n + 2) ↦ f (swapFinAdj (0 : Fin (n + 1)) a))]
  rw [swapFinAdj_eq rfl]
  rw [finSum_succ (R := R) (n := n) (f := fun i : Fin (n + 1) ↦ f i.succ)]
  rw [finSum_succ (R := R) (n := n) (f := fun i : Fin (n + 1) ↦
    f (swapFinAdj (0 : Fin (n + 1)) i.succ))]
  have hrest : ∀ j : Fin n,
      swapFinAdj (0 : Fin (n + 1)) j.succ.succ = j.succ.succ := by
    intro j
    exact swapFinAdj_of_gt (by
      show ((j.succ.succ : Fin (n + 2)) : ℕ) > (0 : ℕ) + 1
      have hv : ((j.succ.succ : Fin (n + 2)) : ℕ) = (j : ℕ) + 2 := rfl
      omega)
  simp only [hrest]
  have heq : (Fin.succ (0 : Fin (n + 1)) : Fin (n + 2)) = (1 : Fin (n + 2)) := rfl
  rw [heq]
  rw [swapFinAdj_eq_one rfl]
  show f (0 : Fin (n + 2)) + (f (1 : Fin (n + 2)) + finSum R n (fun i ↦ f i.succ.succ)) =
    f (1 : Fin (n + 2)) + (f (0 : Fin (n + 2)) + finSum R n (fun i ↦ f i.succ.succ))
  abel

/-- **`finSum` 在相邻对换下不变**：对任意位置 `j`（交换 `j, j+1` 两项），
无选择求和保持不变。 -/
lemma finSum_swapFinAdj : ∀ (n : ℕ) (f : Fin (n + 1) → R) (j : Fin n),
    finSum R (n + 1) f = finSum R (n + 1) (fun a ↦ f (swapFinAdj j a))
  | 0, f, j => j.elim0
  | n + 1, f, j => by
      by_cases h0 : (j : ℕ) = 0
      · have hfun : swapFinAdj j = swapFinAdj (0 : Fin (n + 1)) := by
          funext a
          apply Fin.ext
          rw [swapFinAdj_val, swapFinAdj_val]
          have hv0 : ((0 : Fin (n + 1)) : ℕ) = 0 := rfl
          rw [hv0, h0]
        rw [hfun]
        exact finSum_swapFinAdj_zero f
      · obtain ⟨j', rfl⟩ : ∃ k : Fin n, j = k.succ :=
            ⟨⟨(j : ℕ) - 1, by have := j.isLt; omega⟩, by
              apply Fin.ext
              simp only [Fin.val_succ]
              omega⟩
        have hhead : swapFinAdj j'.succ (0 : Fin (n + 2)) = (0 : Fin (n + 2)) :=
          swapFinAdj_of_ne (by simp only [Fin.val_zero, Fin.val_succ]; omega)
            (by simp only [Fin.val_zero, Fin.val_succ]; omega)
        rw [finSum_succ (R := R) (n := n + 1) (f := f),
            finSum_succ (R := R) (n := n + 1)
              (f := fun a : Fin (n + 2) ↦ f (swapFinAdj j'.succ a)),
            hhead,
            show (fun i : Fin (n + 1) ↦ f (swapFinAdj j'.succ i.succ)) =
              (fun i : Fin (n + 1) ↦ f ((swapFinAdj j' i).succ)) from by
              funext i
              exact congrArg f (swapFinAdj_succ j' i),
            finSum_swapFinAdj n (fun i : Fin (n + 1) ↦ f i.succ) j']

end SwapFinAdj

/-! ### 任意双射的求和重排（(p,q) 楔积的地基）

README 路线图条目 2 的前置引理「任意对换 = 相邻对换乘积的构造性分解」
在此落为 `finSum` 层面的重排不变性：有限集的任何单射自映射（构造性双射）
都不改变 `finSum`。全部构造性，无选择公理。 -/

section FinSumReindex

/-- 非零有限值的「去 0 归一」：减 1 落回 `Fin m`。 -/
private def predNZ {m : ℕ} (x : Fin (m + 1)) (hx : (x : ℕ) ≠ 0) : Fin m :=
  ⟨(x : ℕ) - 1, by have := x.isLt; have := hx; omega⟩

lemma val_predNZ_add {m : ℕ} (x : Fin (m + 1)) (hx : (x : ℕ) ≠ 0) :
    ((predNZ x hx : Fin m) : ℕ) + 1 = (x : ℕ) := by
  simp only [predNZ]
  have := x.isLt
  omega

/-- 相邻位置的对换 `swapFin ⟨k⟩ ⟨k+1⟩` 不改变 `finSum`
（归一到 `finSum_swapFinAdj`）。 -/
lemma finSum_reindex_swapFin_adj (R : Type u) [AddCommMonoid R] {m : ℕ}
    (k : ℕ) (hk : k + 1 < m) (f : Fin m → R) :
    finSum R m (fun a => f (swapFin (⟨k, by have := hk; omega⟩ : Fin m) (⟨k + 1, by have := hk; omega⟩ : Fin m) a))
      = finSum R m f := by
  obtain ⟨d, rfl⟩ : ∃ d, m = d + 1 := ⟨m - 1, by omega⟩
  have hkd : k < d := by omega
  have heq : swapFin (⟨k, by omega⟩ : Fin (d + 1)) (⟨k + 1, by have := hk; omega⟩ : Fin (d + 1))
      = swapFinAdj (⟨k, hkd⟩ : Fin d) := by
    funext a
    apply Fin.ext
    by_cases h1 : (a : ℕ) = k
    · have ha : a = (⟨k, by omega⟩ : Fin (d + 1)) := Fin.ext h1
      rw [ha, swapFin_self_left, swapFinAdj_eq rfl]
    · by_cases h2 : (a : ℕ) = k + 1
      · have ha : a = (⟨k + 1, by have := hk; omega⟩ : Fin (d + 1)) := Fin.ext h2
        rw [ha, swapFin_self_right, swapFinAdj_eq_one rfl]
      · rw [swapFin_of_ne (fun hh => h1 (by rw [hh]))
          (fun hh => h2 (by rw [hh])),
        swapFinAdj_of_ne (fun hh => h1 (by rw [hh]))
          (fun hh => h2 (by rw [hh]))]
  rw [heq]
  exact (finSum_swapFinAdj d f ⟨k, hkd⟩).symm

/-- 对换 `(0 k)` 不改变 `finSum`：`k = 0` 为恒等，`k = 1` 为相邻对换，
`k → k+1` 用共轭恒等式 `(0 (k+1)) = (k (k+1)) ∘ (0 k) ∘ (k (k+1))`（`k ≥ 1`）。 -/
lemma finSum_reindex_swapFin0 (R : Type u) [AddCommMonoid R] : ∀ (n : ℕ) (k : ℕ) (hk : k < n),
    ∀ (f : Fin n → R),
    finSum R n (fun a => f (swapFin (⟨0, by omega⟩ : Fin n)
      (⟨k, by have := hk; omega⟩ : Fin n) a)) = finSum R n f := by
  intro n k
  induction k with
  | zero =>
      intro hk f
      have hid : swapFin (⟨0, hk⟩ : Fin n) (⟨0, hk⟩ : Fin n) = id := by
        funext a
        by_cases h : (a : ℕ) = 0
        · have ha : a = (⟨0, hk⟩ : Fin n) := Fin.ext h
          rw [ha, swapFin_self_left, id_eq]
        · rw [swapFin_of_ne (fun hh => h (by rw [hh]))
            (fun hh => h (by rw [hh])), id_eq]
      rw [hid]
      exact finSum_congr R (fun a : Fin n => rfl)
  | succ k ih =>
      intro hk f
      by_cases hk0 : k = 0
      · subst hk0
        rw [finSum_reindex_swapFin_adj R 0 hk f]
      · -- k ≥ 1：共轭恒等式 (0 (k+1)) = s_k ∘ (0 k) ∘ s_k
        have hne1 : (⟨0, by omega⟩ : Fin n)
            ≠ (⟨k, by have := hk; omega⟩ : Fin n) := fun hh => by
          have := congrArg Fin.val hh
          simp only [Fin.val_mk] at this
          omega
        have hne2 : (⟨0, by omega⟩ : Fin n)
            ≠ (⟨k + 1, by have := hk; omega⟩ : Fin n) := fun hh => by
          have := congrArg Fin.val hh
          simp only [Fin.val_mk] at this
          omega
        have hτ : ∀ a : Fin n, swapFin (⟨0, by omega⟩ : Fin n)
              (⟨k + 1, by have := hk; omega⟩ : Fin n) a
            = swapFin (⟨k, by have := hk; omega⟩ : Fin n) (⟨k + 1, by have := hk; omega⟩ : Fin n)
                (swapFin (⟨0, by omega⟩ : Fin n) (⟨k, by have := hk; omega⟩ : Fin n)
                  (swapFin (⟨k, by have := hk; omega⟩ : Fin n) (⟨k + 1, by have := hk; omega⟩ : Fin n) a)) := by
          intro a
          apply Fin.ext
          by_cases ha0 : (a : ℕ) = 0
          · have ha : a = (⟨0, by omega⟩ : Fin n) := Fin.ext ha0
            rw [ha, swapFin_self_left, swapFin_of_ne hne1 hne2, swapFin_self_left,
              swapFin_self_left]
          · by_cases hak : (a : ℕ) = k
            · have ha : a = (⟨k, by have := hk; omega⟩ : Fin n) := Fin.ext hak
              have hne3 : (⟨k, by have := hk; omega⟩ : Fin n) ≠ (⟨0, by omega⟩ : Fin n) :=
                Ne.symm hne1
              have hne4 : (⟨k, by have := hk; omega⟩ : Fin n) ≠ (⟨k + 1, by have := hk; omega⟩ : Fin n) := fun hh => by
                have := congrArg Fin.val hh
                simp only [Fin.val_mk] at this
                omega
              have hne5 : (⟨k + 1, by have := hk; omega⟩ : Fin n)
                  ≠ (⟨0, by omega⟩ : Fin n) := Ne.symm hne2
              rw [ha, swapFin_of_ne hne3 hne4, swapFin_self_left,
                swapFin_of_ne hne5 (Ne.symm hne4), swapFin_self_right]
            · by_cases hak1 : (a : ℕ) = k + 1
              · have ha : a = (⟨k + 1, by have := hk; omega⟩ : Fin n) := Fin.ext hak1
                rw [ha, swapFin_self_right, swapFin_self_right, swapFin_self_right,
                  swapFin_of_ne hne1 hne2]
              · have ha0' : (a : Fin n) ≠ (⟨0, by omega⟩ : Fin n) :=
                  fun hh => by rw [hh] at ha0; exact ha0 rfl
                have hak' : (a : Fin n) ≠ (⟨k, by have := hk; omega⟩ : Fin n) := fun hh => by
                  rw [hh] at hak; exact hak rfl
                have hak1' : (a : Fin n) ≠ (⟨k + 1, by have := hk; omega⟩ : Fin n) := fun hh => by
                  rw [hh] at hak1; exact hak1 rfl
                have hs0 : swapFin (⟨0, by omega⟩ : Fin n)
                    (⟨k + 1, by have := hk; omega⟩ : Fin n) a = a :=
                  swapFin_of_ne ha0' hak1'
                have hs1 : swapFin (⟨k, by have := hk; omega⟩ : Fin n)
                    (⟨k + 1, by have := hk; omega⟩ : Fin n) a = a :=
                  swapFin_of_ne hak' hak1'
                have hs2 : swapFin (⟨0, by omega⟩ : Fin n)
                    (⟨k, by have := hk; omega⟩ : Fin n) a = a :=
                  swapFin_of_ne ha0' hak'
                simp only [hs0, hs1, hs2]
        rw [finSum_congr R (fun a => congrArg f (hτ a))]
        rw [finSum_reindex_swapFin_adj R k hk
          (f := fun c => f (swapFin (⟨k, by have := hk; omega⟩ : Fin n) (⟨k + 1, by have := hk; omega⟩ : Fin n)
            (swapFin (⟨0, by omega⟩ : Fin n) (⟨k, by have := hk; omega⟩ : Fin n) c)))]
        rw [ih (by have := hk; omega)
          (f := fun b => f (swapFin (⟨k, by have := hk; omega⟩ : Fin n)
            (⟨k + 1, by have := hk; omega⟩ : Fin n) b))]
        rw [finSum_reindex_swapFin_adj R k hk (f := f)]

/-- **重排主引理**：有限集的任何单射自映射（构造性双射）不改变 `finSum`。

证明：取 `0` 的原像 `k`（`FinPerm.surjective_of_injective_self`，构造性），先用
对换 `(0 k)` 把它换到首位（对换不改变和），再用 `finSum_succ` 分离首项 `f 0`，
尾部经「去 0 归一」映射 `predNZ`（值非零，减 1 落回 `Fin n`，仍单射）归纳。 -/
lemma finSum_reindex (R : Type u) [AddCommMonoid R] : ∀ (n : ℕ) (u : Fin n → Fin n),
    Function.Injective u → ∀ (f : Fin n → R),
    finSum R n (fun a => f (u a)) = finSum R n f := by
  intro n
  induction n with
  | zero =>
      intro u _ f
      rw [finSum_zero, finSum_zero]
  | succ n ih =>
      intro u hu f
      obtain ⟨k, hk⟩ : ∃ k : Fin (n + 1), u k = 0 :=
        FinPerm.surjective_of_injective_self hu 0
      -- 第一步：用对换 (0 k) 把 0 的原像换到首位
      rw [← finSum_reindex_swapFin0 R (n + 1) (k : ℕ) k.isLt
        (f := fun b => f (u b))]
      have hv0 : f (u (swapFin (⟨0, by omega⟩ : Fin (n + 1)) k (0 : Fin (n + 1)))) = f 0 := by
        show f (u (swapFin (⟨0, by omega⟩ : Fin (n + 1)) k
          (⟨0, by omega⟩ : Fin (n + 1)))) = f 0
        rw [swapFin_self_left, hk]
      rw [finSum_succ (R := R) (n := n)
        (f := fun a : Fin (n + 1) => f (u (swapFin (⟨0, by omega⟩ : Fin (n + 1)) k a))), hv0]
      rw [finSum_succ (R := R) (n := n) (f := f)]
      congr 1
      -- 尾部：值非零 → predNZ 归一 → 归纳
      have hnz : ∀ i : Fin n, (u (swapFin (⟨0, by omega⟩ : Fin (n + 1)) k i.succ) : ℕ) ≠ 0 := by
        intro i hcon
        have hX : u (swapFin (⟨0, by omega⟩ : Fin (n + 1)) k i.succ) = (0 : Fin (n + 1)) :=
          Fin.ext hcon
        rw [← hk] at hX
        have h2 := hu hX
        have h4 : swapFin k (⟨0, by omega⟩ : Fin (n + 1))
            (swapFin (⟨0, by omega⟩ : Fin (n + 1)) k i.succ)
            = swapFin k (⟨0, by omega⟩ : Fin (n + 1)) k :=
          congrArg (swapFin k (⟨0, by omega⟩ : Fin (n + 1))) h2
        have h5 : swapFin k (⟨0, by omega⟩ : Fin (n + 1))
            (swapFin (⟨0, by omega⟩ : Fin (n + 1)) k i.succ) = i.succ :=
          swapFin_leftInverse (⟨0, by omega⟩ : Fin (n + 1)) k _
        rw [h4, swapFin_self_left] at h5
        have := congrArg Fin.val h5
        simp only [Fin.val_mk, Fin.val_zero, Fin.val_succ] at this
        omega
      have hu''inj : Function.Injective (fun i : Fin n => predNZ
          (u (swapFin (⟨0, by omega⟩ : Fin (n + 1)) k i.succ)) (hnz i)) := by
        intro i i' hii
        have h0 := hnz i
        have h0' := hnz i'
        have e1 : (u (swapFin (⟨0, by omega⟩ : Fin (n + 1)) k i.succ) : ℕ)
            = (u (swapFin (⟨0, by omega⟩ : Fin (n + 1)) k i'.succ) : ℕ) := by
          have := congrArg Fin.val hii
          simp only [predNZ, Fin.val_mk] at this
          omega
        have e2 : u (swapFin (⟨0, by omega⟩ : Fin (n + 1)) k i.succ)
            = u (swapFin (⟨0, by omega⟩ : Fin (n + 1)) k i'.succ) := Fin.ext e1
        have e3 : swapFin (⟨0, by omega⟩ : Fin (n + 1)) k i.succ
            = swapFin (⟨0, by omega⟩ : Fin (n + 1)) k i'.succ := hu e2
        have e4 := swapFin_injective (⟨0, by omega⟩ : Fin (n + 1)) k e3
        exact Fin.ext (by
          have := congrArg Fin.val e4
          simp only [Fin.val_succ] at this
          omega)
      have hbridge : ∀ i : Fin n, f (u (swapFin (⟨0, by omega⟩ : Fin (n + 1)) k i.succ))
          = f (⟨((predNZ (u (swapFin (⟨0, by omega⟩ : Fin (n + 1)) k i.succ))
              (hnz i) : Fin n) : ℕ) + 1, (by have := i.isLt; omega)⟩ : Fin (n + 1)) := by
        intro i
        have he : (⟨((predNZ (u (swapFin (⟨0, by omega⟩ : Fin (n + 1)) k i.succ))
              (hnz i) : Fin n) : ℕ) + 1, (by have := i.isLt; omega)⟩ : Fin (n + 1))
            = (u (swapFin (⟨0, by omega⟩ : Fin (n + 1)) k i.succ)) := by
          have hval := val_predNZ_add (u (swapFin (⟨0, by omega⟩ : Fin (n + 1)) k i.succ))
            (hnz i)
          exact Fin.ext (by simp only [Fin.val_mk]; omega)
        rw [congrArg f he]
      rw [finSum_congr R hbridge]
      rw [ih (fun i : Fin n => predNZ (u (swapFin (⟨0, by omega⟩ : Fin (n + 1)) k i.succ))
          (hnz i)) hu''inj
        (fun x : Fin n => f (Fin.mk ((x : ℕ) + 1) (by have := x.isLt; omega)))]
      exact finSum_congr R (fun a => rfl)

end FinSumReindex

section PermSumReindex

variable {R : Type u} [AddCommMonoid R]

/-! ### permSum 的重排不变性（(p,q) 楔积的地基）

`(p,q)` 楔积将定义为对全部置换的 `permSum` 加权和；其交错性证明需要
「求和变量经置换复合重排后 permSum 不变」。本节给出两条重排引理：

* `permSum_reindex_encode`（编码级）：单射自映射 `ρ` 复合到 `π.toFun`
  上不改变 permSum——头部经 `finSum_reindex`（E0）重排，尾部递归；
* `permSum_reindex_compose`（复合级）：左复合固定置换不改变 permSum。

关键分解（`encode_compose_cons`）：单射函数作用于 cons-置换的编码
`= cons (限制编码) (ρ i)`，其中限制编码的域函数
`k ↦ unshift (ρ i) (ρ (insertAt i (σ.toFun k)))` 是与 σ 无关的
`permRestr ρ hρ i` 与 `σ.toFun` 的复合——这正是归纳假设得以应用的形状。 -/

/-- 逐点相等的两个函数 permSum 相等。 -/
lemma permSum_congr {n : ℕ} {f g : FinPerm n → R} (h : ∀ π, f π = g π) :
    FinPerm.permSum R f = FinPerm.permSum R g := by
  induction n with
  | zero => simp only [FinPerm.permSum_zero]; exact h _
  | succ n ih =>
      simp only [FinPerm.permSum_succ]
      exact finSum_congr R (fun i => ih (fun σ => h (FinPerm.cons σ i)))

/-- 头部 `i` 处的限制重排：`ρ` 作用后挖去 `ρ i` 再压缩回 `Fin n`。 -/
def permRestr {n : ℕ} (ρ : Fin (n + 1) → Fin (n + 1)) (hρ : Function.Injective ρ)
    (i : Fin (n + 1)) (k : Fin n) : Fin n :=
  FinPerm.unshift (ρ i) (ρ (FinPerm.insertAt i k))
    (fun hc => FinPerm.insertAt_ne i k (hρ hc))

lemma permRestr_injective {n : ℕ} (ρ : Fin (n + 1) → Fin (n + 1)) (hρ : Function.Injective ρ)
    (i : Fin (n + 1)) :
    Function.Injective (permRestr ρ hρ i) := by
  intro k₁ k₂ hEq
  have h2 := FinPerm.unshift_injective (ρ i)
    (fun hc => FinPerm.insertAt_ne i k₁ (hρ hc))
    (fun hc => FinPerm.insertAt_ne i k₂ (hρ hc)) hEq
  exact FinPerm.insertAt_injective i (hρ h2)

/-- 共享分解：单射函数作用于 cons-置换的编码。 -/
lemma encode_compose_cons {n : ℕ} (σ : FinPerm n) (i : Fin (n + 1))
    (ρ : Fin (n + 1) → Fin (n + 1)) (hρ : Function.Injective ρ) :
    FinPerm.encode (fun k => ρ ((FinPerm.cons σ i).toFun k))
        (hρ.comp (FinPerm.cons σ i).toFun_injective)
      = FinPerm.cons (FinPerm.encode (fun k => permRestr ρ hρ i (σ.toFun k))
          (show Function.Injective fun k => permRestr ρ hρ i (σ.toFun k) from
            (permRestr_injective ρ hρ i).comp σ.toFun_injective)) (ρ i) := by
  apply FinPerm.ext_toFun _ _
  have hEnc := FinPerm.toFun_encode (fun k => ρ ((FinPerm.cons σ i).toFun k))
    (hρ.comp (FinPerm.cons σ i).toFun_injective)
  have hTail := FinPerm.toFun_encode (fun k => permRestr ρ hρ i (σ.toFun k))
    ((permRestr_injective ρ hρ i).comp σ.toFun_injective)
  funext j
  cases j using Fin.cases with
  | zero => simp only [hEnc, FinPerm.toFun_cons_zero]
  | succ k =>
      simp only [hEnc, FinPerm.toFun_cons_succ, hTail]
      simp only [permRestr, FinPerm.insertAt_unshift]

/-- **编码级重排**：单射自映射复合到 `π.toFun` 上不改变 permSum。 -/
lemma permSum_reindex_encode : ∀ (n : ℕ) (ρ : Fin n → Fin n) (hρ : Function.Injective ρ)
    (g : FinPerm n → R),
    FinPerm.permSum R (fun σ => g (FinPerm.encode (fun k => ρ (σ.toFun k))
      (hρ.comp σ.toFun_injective))) = FinPerm.permSum R g := by
  intro n
  induction n with
  | zero =>
      intro ρ hρ g
      simp only [FinPerm.permSum_zero]
      have hnil : FinPerm.encode (fun k => ρ ((FinPerm.nil : FinPerm 0).toFun k))
          (hρ.comp FinPerm.nil.toFun_injective) = FinPerm.nil := by
        apply FinPerm.ext_toFun _ _
        funext j
        exact j.elim0
      rw [hnil]
  | succ n ih =>
      intro ρ hρ g
      simp only [FinPerm.permSum_succ]
      have hstep1 : ∀ i : Fin (n + 1),
          FinPerm.permSum R (fun σ => g (FinPerm.encode (fun k =>
              ρ ((FinPerm.cons σ i).toFun k)) (hρ.comp (FinPerm.cons σ i).toFun_injective)))
            = FinPerm.permSum R (fun σ' => g (FinPerm.cons σ' (ρ i))) := by
        intro i
        rw [permSum_congr (fun σ => congrArg g (encode_compose_cons σ i ρ hρ)),
          ih (permRestr ρ hρ i) (permRestr_injective ρ hρ i)
            (fun σ' => g (FinPerm.cons σ' (ρ i)))]
      rw [finSum_congr R hstep1]
      exact finSum_reindex R (n + 1) ρ hρ
        (fun j => FinPerm.permSum R (fun σ' => g (FinPerm.cons σ' j)))

/-- **复合级重排**：左复合固定置换不改变 permSum。 -/
lemma permSum_reindex_compose : ∀ (n : ℕ) (τ : FinPerm n) (f : FinPerm n → R),
    FinPerm.permSum R (fun π => f (FinPerm.compose τ π)) = FinPerm.permSum R f := by
  intro n
  induction n with
  | zero =>
      intro τ f
      cases τ
      simp only [FinPerm.permSum_zero]
      apply congrArg f
      apply FinPerm.ext_toFun _ _
      rw [FinPerm.toFun_compose]
      funext j
      exact j.elim0
  | succ n ih =>
      intro τ f
      simp only [FinPerm.permSum_succ]
      have hcomp : ∀ (i : Fin (n + 1)) (σ : FinPerm n),
          FinPerm.compose τ (FinPerm.cons σ i)
            = FinPerm.encode (fun k => τ.toFun ((FinPerm.cons σ i).toFun k))
                (show Function.Injective fun k => τ.toFun ((FinPerm.cons σ i).toFun k) from
                  τ.toFun_injective.comp (FinPerm.cons σ i).toFun_injective) := by
        intro i σ
        apply FinPerm.ext_toFun _ _
        rw [FinPerm.toFun_compose, FinPerm.toFun_encode]
      have hstep1 : ∀ i : Fin (n + 1),
          FinPerm.permSum R (fun σ => f (FinPerm.compose τ (FinPerm.cons σ i)))
            = FinPerm.permSum R (fun σ' => f (FinPerm.cons σ' (τ.toFun i))) := by
        intro i
        rw [permSum_congr (fun σ => congrArg f (hcomp i σ)),
          permSum_congr (fun σ => congrArg f
            (encode_compose_cons σ i τ.toFun τ.toFun_injective)),
          permSum_reindex_encode n (permRestr τ.toFun τ.toFun_injective i)
            (permRestr_injective τ.toFun τ.toFun_injective i)
            (fun σ' => f (FinPerm.cons σ' (τ.toFun i)))]
      rw [finSum_congr R hstep1]
      exact finSum_reindex R (n + 1) τ.toFun τ.toFun_injective
        (fun j => FinPerm.permSum R (fun σ' => f (FinPerm.cons σ' j)))

end PermSumReindex

section PermSumLin

variable {R : Type u} [CommRing R]

/-- permSum 对常量数乘可提出。 -/
lemma permSum_mul_left {n : ℕ} (a : R) (f : FinPerm n → R) :
    FinPerm.permSum R (fun π => a * f π) = a * FinPerm.permSum R f := by
  induction n with
  | zero => simp only [FinPerm.permSum_zero]
  | succ n ih =>
      simp only [FinPerm.permSum_succ, ih, finSum_mul_left]

end PermSumLin

section WedgeAny

variable {R : Type u} [CommRing R] {X : Type u} [Microlinear R X]

/-- 一般 `(p,q)` 楔积的展开函数（交替化定义）：对全部 `(p+q)`-置换的
符号加权求和，`ω` 取置换像的前 `p` 个槽位、`η` 取后 `q` 个槽位。

与 `1 ∧ n` 情形（`wedgeOneAnyFun` 的位置求和）不同，这里用
`FinPerm.permSum`（全置换枚举，无选择公理），其重排基础设施
（`permSum_reindex_compose` 等）是交错性证明的关键。 -/
def wedgeAnyFun {p q : ℕ} {x : X}
    (ω : TangentFiber R X x [⋀^Fin p]→ₗ[R] R)
    (η : TangentFiber R X x [⋀^Fin q]→ₗ[R] R)
    (v : Fin (p + q) → TangentFiber R X x) : R :=
  FinPerm.permSum R (fun π : FinPerm (p + q) =>
    FinPerm.sign R π * (ω (fun i : Fin p => v (π.toFun (Fin.castAdd q i))) *
    η (fun j : Fin q => v (π.toFun (Fin.natAdd p j)))))

lemma wedgeAnyFun_apply {p q : ℕ} {x : X}
    (ω : TangentFiber R X x [⋀^Fin p]→ₗ[R] R)
    (η : TangentFiber R X x [⋀^Fin q]→ₗ[R] R)
    (v : Fin (p + q) → TangentFiber R X x) :
    wedgeAnyFun ω η v = FinPerm.permSum R (fun π : FinPerm (p + q) =>
    FinPerm.sign R π * (ω (fun i : Fin p => v (π.toFun (Fin.castAdd q i))) *
    η (fun j : Fin q => v (π.toFun (Fin.natAdd p j))))) := rfl

/-- `(p,q)` 楔积对第一个因子的加法。 -/
lemma wedgeAnyFun_add_left {p q : ℕ} {x : X}
    (ω₁ ω₂ : TangentFiber R X x [⋀^Fin p]→ₗ[R] R)
    (η : TangentFiber R X x [⋀^Fin q]→ₗ[R] R)
    (v : Fin (p + q) → TangentFiber R X x) :
    wedgeAnyFun (ω₁ + ω₂) η v = wedgeAnyFun ω₁ η v + wedgeAnyFun ω₂ η v := by
  unfold wedgeAnyFun
  have hpoint : ∀ π : FinPerm (p + q),
      FinPerm.sign R π * ((ω₁ + ω₂) (fun i : Fin p => v (π.toFun (Fin.castAdd q i))) *
        η (fun j : Fin q => v (π.toFun (Fin.natAdd p j))))
      = FinPerm.sign R π * (ω₁ (fun i : Fin p => v (π.toFun (Fin.castAdd q i))) *
        η (fun j : Fin q => v (π.toFun (Fin.natAdd p j)))) +
        FinPerm.sign R π * (ω₂ (fun i : Fin p => v (π.toFun (Fin.castAdd q i))) *
        η (fun j : Fin q => v (π.toFun (Fin.natAdd p j)))) := by
    intro π
    rw [show ((ω₁ + ω₂) (fun i : Fin p => v (π.toFun (Fin.castAdd q i))))
        = ω₁ (fun i : Fin p => v (π.toFun (Fin.castAdd q i)))
          + ω₂ (fun i : Fin p => v (π.toFun (Fin.castAdd q i))) from rfl]
    ring
  rw [permSum_congr hpoint, FinPerm.permSum_add]

/-- `(p,q)` 楔积对第二个因子的加法。 -/
lemma wedgeAnyFun_add_right {p q : ℕ} {x : X}
    (ω : TangentFiber R X x [⋀^Fin p]→ₗ[R] R)
    (η₁ η₂ : TangentFiber R X x [⋀^Fin q]→ₗ[R] R)
    (v : Fin (p + q) → TangentFiber R X x) :
    wedgeAnyFun ω (η₁ + η₂) v = wedgeAnyFun ω η₁ v + wedgeAnyFun ω η₂ v := by
  unfold wedgeAnyFun
  have hpoint : ∀ π : FinPerm (p + q),
      FinPerm.sign R π * (ω (fun i : Fin p => v (π.toFun (Fin.castAdd q i))) *
        (η₁ + η₂) (fun j : Fin q => v (π.toFun (Fin.natAdd p j))))
      = FinPerm.sign R π * (ω (fun i : Fin p => v (π.toFun (Fin.castAdd q i))) *
        η₁ (fun j : Fin q => v (π.toFun (Fin.natAdd p j)))) +
        FinPerm.sign R π * (ω (fun i : Fin p => v (π.toFun (Fin.castAdd q i))) *
        η₂ (fun j : Fin q => v (π.toFun (Fin.natAdd p j)))) := by
    intro π
    rw [show ((η₁ + η₂) (fun j : Fin q => v (π.toFun (Fin.natAdd p j))))
        = η₁ (fun j : Fin q => v (π.toFun (Fin.natAdd p j)))
          + η₂ (fun j : Fin q => v (π.toFun (Fin.natAdd p j))) from rfl]
    ring
  rw [permSum_congr hpoint, FinPerm.permSum_add]

/-- `(p,q)` 楔积对第一个因子的数乘。 -/
lemma wedgeAnyFun_smul_left {p q : ℕ} {x : X}
    (a : R) (ω : TangentFiber R X x [⋀^Fin p]→ₗ[R] R)
    (η : TangentFiber R X x [⋀^Fin q]→ₗ[R] R)
    (v : Fin (p + q) → TangentFiber R X x) :
    wedgeAnyFun (a • ω) η v = a • wedgeAnyFun ω η v := by
  unfold wedgeAnyFun
  have hpoint : ∀ π : FinPerm (p + q),
      FinPerm.sign R π * ((a • ω) (fun i : Fin p => v (π.toFun (Fin.castAdd q i))) *
        η (fun j : Fin q => v (π.toFun (Fin.natAdd p j))))
      = a * (FinPerm.sign R π * (ω (fun i : Fin p => v (π.toFun (Fin.castAdd q i))) *
        η (fun j : Fin q => v (π.toFun (Fin.natAdd p j))))) := by
    intro π
    rw [show ((a • ω) (fun i : Fin p => v (π.toFun (Fin.castAdd q i))))
        = a * ω (fun i : Fin p => v (π.toFun (Fin.castAdd q i))) from rfl]
    ring
  rw [permSum_congr hpoint, permSum_mul_left, smul_eq_mul]

/-- `(p,q)` 楔积对第二个因子的数乘。 -/
lemma wedgeAnyFun_smul_right {p q : ℕ} {x : X}
    (a : R) (ω : TangentFiber R X x [⋀^Fin p]→ₗ[R] R)
    (η : TangentFiber R X x [⋀^Fin q]→ₗ[R] R)
    (v : Fin (p + q) → TangentFiber R X x) :
    wedgeAnyFun ω (a • η) v = a • wedgeAnyFun ω η v := by
  unfold wedgeAnyFun
  have hpoint : ∀ π : FinPerm (p + q),
      FinPerm.sign R π * (ω (fun i : Fin p => v (π.toFun (Fin.castAdd q i))) *
        (a • η) (fun j : Fin q => v (π.toFun (Fin.natAdd p j))))
      = a * (FinPerm.sign R π * (ω (fun i : Fin p => v (π.toFun (Fin.castAdd q i))) *
        η (fun j : Fin q => v (π.toFun (Fin.natAdd p j))))) := by
    intro π
    rw [show ((a • η) (fun j : Fin q => v (π.toFun (Fin.natAdd p j))))
        = a * η (fun j : Fin q => v (π.toFun (Fin.natAdd p j))) from rfl]
    ring
  rw [permSum_congr hpoint, permSum_mul_left, smul_eq_mul]

end WedgeAny





/-! ### `1 ∧ n` 楔积的原始函数公式 -/

section WedgeOneAny

variable {R : Type u} [CommRing R] {X : Type u} [Microlinear R X]

/-- `1 ∧ n` 楔积展开式的第 `i` 项：`(-1)ⁱ · ω(vᵢ) · η(v₀,…,v̂ᵢ,…,vₙ)`。 -/
def wedgeOneAnyTerm {n : ℕ} {x : X}
    (ω : TangentFiber R X x [⋀^Fin 1]→ₗ[R] R)
    (η : TangentFiber R X x [⋀^Fin n]→ₗ[R] R)
    (v : Fin (n + 1) → TangentFiber R X x) (i : Fin (n + 1)) : R :=
  (-1 : R) ^ (i : ℕ) * FiberwiseDifferentialForm.oneArg ω (v i) * η (i.removeNth v)

@[simp]
lemma wedgeOneAnyTerm_apply {n : ℕ} {x : X}
    (ω : TangentFiber R X x [⋀^Fin 1]→ₗ[R] R)
    (η : TangentFiber R X x [⋀^Fin n]→ₗ[R] R)
    (v : Fin (n + 1) → TangentFiber R X x) (i : Fin (n + 1)) :
    wedgeOneAnyTerm ω η v i =
      (-1 : R) ^ (i : ℕ) * FiberwiseDifferentialForm.oneArg ω (v i) * η (i.removeNth v) := rfl

/-- `1 ∧ n` 楔积的原始函数。

Kock I.14 (14.7) 公式：
`(ω ∧ η)(v₀,…,vₙ) = Σᵢ₌₀ⁿ (-1)ⁱ · ω(vᵢ) · η(v₀,…,v̂ᵢ,…,vₙ)`

其中 `v̂ᵢ` 表示用 `Fin.removeNth` 删除第 `i` 个分量。 -/
def wedgeOneAnyFun {n : ℕ} {x : X}
    (ω : TangentFiber R X x [⋀^Fin 1]→ₗ[R] R)
    (η : TangentFiber R X x [⋀^Fin n]→ₗ[R] R)
    (v : Fin (n + 1) → TangentFiber R X x) : R :=
  finSum R (n + 1) (wedgeOneAnyTerm ω η v)

lemma wedgeOneAnyFun_eq {n : ℕ} {x : X}
    (ω : TangentFiber R X x [⋀^Fin 1]→ₗ[R] R)
    (η : TangentFiber R X x [⋀^Fin n]→ₗ[R] R)
    (v : Fin (n + 1) → TangentFiber R X x) :
    wedgeOneAnyFun ω η v = finSum R (n + 1) (wedgeOneAnyTerm ω η v) := rfl

end WedgeOneAny

/-! ## 一般 `1 ∧ n` 楔积：交错性的无选择证明

方法：`1 ∧ n` 展开式的逐项配对。相邻对换反交换中，`i ∉ {j, j+1}` 的项由
η 的对换变号承担（自证极化恒等式，避开 Mathlib `map_swap` 的经典依赖），
`i ∈ {j, j+1}` 的项由 `(-1)ⁱ` 的错位承担；求和经 `finSum_swapFinAdj` 重排。
任意两槽相等的消去经冒泡归纳化归到相邻情形，配对消去对任意特征成立。 -/

section WedgeOneAnyGen

variable {R : Type u} [CommRing R] {X : Type u} [Microlinear R X]

/-! ### ℕ-下标的相邻对换与交错形式的变号 -/

/-- 交换 `Fin L` 中位置 `t` 与 `t+1`（ℕ-下标版，`t+1 < L`）。 -/
def swapFinAdj' (L t : ℕ) (ht : t + 1 < L) : Fin L → Fin L :=
  fun a => if (a : ℕ) = t then ⟨t + 1, by omega⟩
    else if (a : ℕ) = t + 1 then ⟨t, by omega⟩ else a

lemma swapFinAdj'_val {L t : ℕ} (ht : t + 1 < L) (a : Fin L) :
    ((swapFinAdj' L t ht a : Fin L) : ℕ) =
      if (a : ℕ) = t then t + 1 else if (a : ℕ) = t + 1 then t else (a : ℕ) := by
  by_cases h₁ : (a : ℕ) = t
  · rw [swapFinAdj', if_pos h₁, if_pos h₁]
  · by_cases h₂ : (a : ℕ) = t + 1
    · rw [swapFinAdj', if_neg h₁, if_pos h₂, if_neg h₁, if_pos h₂]
    · rw [swapFinAdj', if_neg h₁, if_neg h₂, if_neg h₁, if_neg h₂]

lemma swapFinAdj'_of_ne {L t : ℕ} (ht : t + 1 < L) {a : Fin L} (h₁ : (a : ℕ) ≠ t)
    (h₂ : (a : ℕ) ≠ t + 1) : swapFinAdj' L t ht a = a := by
  rw [swapFinAdj', if_neg h₁, if_neg h₂]

/-- 交错形式的相邻对换变号（极化恒等式，构造性，无选择公理）：
`η` 在位置 `t, t+1` 的对换下变号。对半幺环 `M` 即可（无需减法）。 -/
lemma alternatingMap_swapFinAdj' {R : Type u} [CommRing R] {M : Type u} [AddCommMonoid M]
    [Module R M] {L : ℕ} (η : M [⋀^Fin L]→ₗ[R] R) (t : ℕ) (ht : t + 1 < L)
    (w : Fin L → M) :
    η (w ∘ swapFinAdj' L t ht) = -η w := by
  set p : Fin L := ⟨t, by have := ht; omega⟩ with hp_def
  set q : Fin L := ⟨t + 1, by have := ht; omega⟩ with hq_def
  have hpv : (p : ℕ) = t := rfl
  have hqv : (q : ℕ) = t + 1 := rfl
  have hpq : p ≠ q := by
    intro hh
    have hval : (p : ℕ) = (q : ℕ) := by rw [hh]
    omega
  have hswap_p : swapFinAdj' L t ht p = q := by rw [swapFinAdj', if_pos rfl]
  have hswap_q : swapFinAdj' L t ht q = p := by rw [swapFinAdj', if_neg (by omega), if_pos rfl]
  set S : M := w p + w q with hS
  set u : Fin L → M := Function.update (Function.update w q S) p S with hu
  have hup : u p = S := Function.update_self ..
  have huq : u q = S := by
    rw [hu, Function.update_of_ne (show (q : Fin L) ≠ p by
      intro hh; exact hpq hh.symm), Function.update_self]
  have h0 : η u = 0 := η.map_eq_zero_of_eq u (by rw [hup, huq]) hpq
  -- 在槽 q 拆分
  have huq' : u = Function.update u q S := by
    funext k
    by_cases hk : k = q
    · subst hk; rw [huq, Function.update_self]
    · rw [Function.update_of_ne hk]
  have hid : ∀ Y : M, Function.update (Function.update u q (w p + w q)) q Y
      = Function.update u q Y := by
    intro Y
    funext k
    rw [hu]
    simp only [Function.update_apply]
    by_cases hk : k = q
    · subst hk; simp
    · simp [hk]
  have huq'' : η u = η (Function.update u q (w p)) + η (Function.update u q (w q)) := by
    rw [huq', hS, η.map_update_add, congrArg η (hid (w p)), congrArg η (hid (w q))]
  -- 两个半向量在槽 p 拆分（函数等式逐点验证，避免 rw 全局替换污染右侧）
  have heqP : Function.update u q (w p) = Function.update
      (Function.update u q (w p)) p (w p + w q) := by
    funext k
    by_cases hk : k = p
    · subst hk
      rw [Function.update_of_ne hpq, hup, hS, Function.update_self]
    · by_cases hk2 : k = q
      · subst hk2
        rw [Function.update_self, Function.update_of_ne hpq.symm, Function.update_self]
      · rw [Function.update_of_ne hk2, Function.update_of_ne hk,
          Function.update_of_ne hk2]
  have heqQ : Function.update u q (w q) = Function.update
      (Function.update u q (w q)) p (w p + w q) := by
    funext k
    by_cases hk : k = p
    · subst hk
      rw [Function.update_of_ne hpq, hup, hS, Function.update_self]
    · by_cases hk2 : k = q
      · subst hk2
        rw [Function.update_self, Function.update_of_ne hpq.symm, Function.update_self]
      · rw [Function.update_of_ne hk2, Function.update_of_ne hk,
          Function.update_of_ne hk2]
  have hPsplit : η (Function.update u q (w p))
      = η (Function.update (Function.update u q (w p)) p (w p))
      + η (Function.update (Function.update u q (w p)) p (w q)) := by
    conv_lhs => rw [heqP]
    rw [η.map_update_add]
  have hQsplit : η (Function.update u q (w q))
      = η (Function.update (Function.update u q (w q)) p (w p))
      + η (Function.update (Function.update u q (w q)) p (w q)) := by
    conv_lhs => rw [heqQ]
    rw [η.map_update_add]
  -- 对角块为零（p, q 两槽同值）
  have hdiag1 : η (Function.update (Function.update u q (w p)) p (w p)) = 0 := by
    refine η.map_eq_zero_of_eq _ ?_ hpq
    rw [Function.update_self, Function.update_of_ne hpq.symm, Function.update_self]
  have hdiag2 : η (Function.update (Function.update u q (w q)) p (w q)) = 0 := by
    refine η.map_eq_zero_of_eq _ ?_ hpq
    rw [Function.update_self, Function.update_of_ne hpq.symm, Function.update_self]
  -- 识别两个非对角块：交换后的 w 与 w 本身
  have hident_swap : Function.update (Function.update u q (w p)) p (w q)
      = w ∘ swapFinAdj' L t ht := by
    funext k
    rw [Function.comp_apply]
    by_cases hk : k = p
    · subst hk
      rw [Function.update_self, hswap_p]
    · by_cases hk2 : k = q
      · subst hk2
        rw [Function.update_of_ne hpq.symm, Function.update_self, hswap_q]
      · rw [Function.update_of_ne hk, Function.update_of_ne hk2, hu,
          Function.update_of_ne hk, Function.update_of_ne hk2,
          swapFinAdj'_of_ne ht (show (k : ℕ) ≠ t by
            intro hval; exact hk (Fin.ext (by have := hpv; omega))) (show (k : ℕ) ≠ t + 1 by
            intro hval; exact hk2 (Fin.ext (by have := hqv; omega)))]
  have hident_w : Function.update (Function.update u q (w q)) p (w p) = w := by
    funext k
    by_cases hk : k = p
    · subst hk; rw [Function.update_self]
    · by_cases hk2 : k = q
      · subst hk2
        rw [Function.update_of_ne hpq.symm, Function.update_self]
      · rw [Function.update_of_ne hk, Function.update_of_ne hk2, hu,
          Function.update_of_ne hk, Function.update_of_ne hk2]
  -- 汇总：0 = ηu = (0 + ηswap) + (ηw + 0)
  have e1 : η u = η (Function.update u q (w p)) + η (Function.update u q (w q)) := huq''
  have e2 : η (Function.update u q (w p))
      = η (w ∘ swapFinAdj' L t ht) := by rw [hPsplit, hdiag1, zero_add, hident_swap]
  have e3 : η (Function.update u q (w q)) = η w := by
    rw [hQsplit, hdiag2, add_zero, hident_w]
  have e5 : (0 : R) = η (w ∘ swapFinAdj' L t ht) + η w := by
    rw [← h0, e1, e2, e3]
  exact eq_neg_of_add_eq_zero_left e5.symm

/-! ### `removeNth` 与相邻对换的交换关系 -/

/-- `Fin.succAbove` 的值公式。 -/
lemma succAbove_val {n : ℕ} (i : Fin (n + 1)) (b : Fin n) :
    ((i.succAbove b : Fin (n + 1)) : ℕ) =
      if (b : ℕ) < (i : ℕ) then (b : ℕ) else (b : ℕ) + 1 := by
  rw [Fin.succAbove]
  by_cases h : (Fin.castSucc b : Fin (n + 1)) < i
  · rw [if_pos h, if_pos (by rw [Fin.lt_def, Fin.val_castSucc] at h; exact h),
      Fin.val_castSucc]
  · rw [if_neg h, if_neg (by rw [Fin.lt_def, Fin.val_castSucc] at h; omega),
      Fin.val_succ]

/-- `a.succAbove` 的逆向：`x ≠ a` 时存在原像。 -/
lemma exists_succAbove_eq {n : ℕ} {a x : Fin (n + 1)} (h : x ≠ a) :
    ∃ p : Fin n, a.succAbove p = x := by
  rcases Nat.lt_or_ge ((x : ℕ)) ((a : ℕ)) with hlt | hge
  · refine ⟨⟨(x : ℕ), by have := x.isLt; omega⟩, ?_⟩
    rw [Fin.succAbove, if_pos (by rw [Fin.lt_def, Fin.val_castSucc]; exact hlt)]
    exact Fin.ext rfl
  · refine ⟨⟨(x : ℕ) - 1, by have := x.isLt; have := a.isLt; omega⟩, ?_⟩
    rw [Fin.succAbove, if_neg (by
      rw [Fin.lt_def, Fin.val_castSucc]
      have hval : ((⟨(x : ℕ) - 1, by have := x.isLt; have := a.isLt; omega⟩ : Fin n) : ℕ)
          = (x : ℕ) - 1 := rfl
      rw [hval]
      omega)]
    exact Fin.ext (by show (x : ℕ) - 1 + 1 = (x : ℕ); omega)

/-- `i < j`：删除第 `i` 个分量后，`Fin (n+1)` 上的相邻对换 `swapFinAdj j`
左移为 `Fin n` 上的 `swapFinAdj' n (j-1)`。 -/
lemma removeNth_swapFinAdj_lt {n : ℕ} {T : Type u} {i : Fin (n + 1)} {j : Fin n}
    (h : (i : ℕ) < (j : ℕ)) (v : Fin (n + 1) → T) :
    i.removeNth (fun a : Fin (n + 1) ↦ v (swapFinAdj j a)) =
      (i.removeNth v) ∘ swapFinAdj' n (j - 1) (by have := j.isLt; omega) := by
  have hj : (j : ℕ) - 1 + 1 < n := by have := j.isLt; omega
  funext b
  simp only [Fin.removeNth_apply, Function.comp_apply]
  have hfin : swapFinAdj j (i.succAbove b) = i.succAbove (swapFinAdj' n (j - 1) hj b) := by
    apply Fin.ext
    have q1 : ((swapFinAdj j (i.succAbove b) : Fin (n + 1)) : ℕ)
        = if (if (b : ℕ) < (i : ℕ) then (b : ℕ) else (b : ℕ) + 1) = (j : ℕ) then (j : ℕ) + 1
          else if (if (b : ℕ) < (i : ℕ) then (b : ℕ) else (b : ℕ) + 1) = (j : ℕ) + 1
          then (j : ℕ)
          else if (b : ℕ) < (i : ℕ) then (b : ℕ) else (b : ℕ) + 1 := by
      rw [swapFinAdj_val, succAbove_val]
    have q3 : ((i.succAbove (swapFinAdj' n (j - 1) hj b) : Fin (n + 1)) : ℕ) =
        if (if (b : ℕ) = (j : ℕ) - 1 then (j : ℕ) - 1 + 1
            else if (b : ℕ) = (j : ℕ) - 1 + 1 then (j : ℕ) - 1 else (b : ℕ)) < (i : ℕ) then
          (if (b : ℕ) = (j : ℕ) - 1 then (j : ℕ) - 1 + 1
            else if (b : ℕ) = (j : ℕ) - 1 + 1 then (j : ℕ) - 1 else (b : ℕ))
        else (if (b : ℕ) = (j : ℕ) - 1 then (j : ℕ) - 1 + 1
            else if (b : ℕ) = (j : ℕ) - 1 + 1 then (j : ℕ) - 1 else (b : ℕ)) + 1 := by
      rw [succAbove_val, swapFinAdj'_val hj]
    rw [q1, q3]
    split_ifs <;> omega
  rw [hfin]

/-- `i > j + 1`：删除第 `i` 个分量后，相邻对换 `swapFinAdj j` 不移位，
仍为 `Fin n` 上的 `swapFinAdj' n j`。 -/
lemma removeNth_swapFinAdj_gt {n : ℕ} {T : Type u} {i : Fin (n + 1)} {j : Fin n}
    (h : (i : ℕ) > (j : ℕ) + 1) (v : Fin (n + 1) → T) :
    i.removeNth (fun a : Fin (n + 1) ↦ v (swapFinAdj j a)) =
      (i.removeNth v) ∘ swapFinAdj' n j (by have := j.isLt; omega) := by
  have hj : (j : ℕ) + 1 < n := by have := j.isLt; have := i.isLt; omega
  funext b
  simp only [Fin.removeNth_apply, Function.comp_apply]
  have hfin : swapFinAdj j (i.succAbove b) = i.succAbove (swapFinAdj' n j hj b) := by
    apply Fin.ext
    have q1 : ((swapFinAdj j (i.succAbove b) : Fin (n + 1)) : ℕ)
        = if (if (b : ℕ) < (i : ℕ) then (b : ℕ) else (b : ℕ) + 1) = (j : ℕ) then (j : ℕ) + 1
          else if (if (b : ℕ) < (i : ℕ) then (b : ℕ) else (b : ℕ) + 1) = (j : ℕ) + 1
          then (j : ℕ)
          else if (b : ℕ) < (i : ℕ) then (b : ℕ) else (b : ℕ) + 1 := by
      rw [swapFinAdj_val, succAbove_val]
    have q3 : ((i.succAbove (swapFinAdj' n j hj b) : Fin (n + 1)) : ℕ) =
        if (if (b : ℕ) = (j : ℕ) then (j : ℕ) + 1
            else if (b : ℕ) = (j : ℕ) + 1 then (j : ℕ) else (b : ℕ)) < (i : ℕ) then
          (if (b : ℕ) = (j : ℕ) then (j : ℕ) + 1
            else if (b : ℕ) = (j : ℕ) + 1 then (j : ℕ) else (b : ℕ))
        else (if (b : ℕ) = (j : ℕ) then (j : ℕ) + 1
            else if (b : ℕ) = (j : ℕ) + 1 then (j : ℕ) else (b : ℕ)) + 1 := by
      rw [succAbove_val, swapFinAdj'_val hj]
    rw [q1, q3]
    split_ifs <;> omega
  rw [hfin]

/-- `i ∈ {j, j+1}`：删除被对换的分量后，相邻对换被完全吸收：
`i.removeNth (v ∘ swapFinAdj j) = (swapFinAdj j i).removeNth v`。 -/
lemma removeNth_swapFinAdj_pivot {n : ℕ} {T : Type u} {i : Fin (n + 1)} {j : Fin n}
    (h : (i : ℕ) = (j : ℕ) ∨ (i : ℕ) = (j : ℕ) + 1) (v : Fin (n + 1) → T) :
    i.removeNth (fun a : Fin (n + 1) ↦ v (swapFinAdj j a)) =
      (swapFinAdj j i).removeNth v := by
  funext b
  simp only [Fin.removeNth_apply]
  rcases h with h | h
  · have hv : ((swapFinAdj j i : Fin (n + 1)) : ℕ) = (j : ℕ) + 1 := by
      rw [swapFinAdj_val, if_pos h]
    have hfin : swapFinAdj j (i.succAbove b) = (swapFinAdj j i).succAbove b := by
      apply Fin.ext
      have q1 : ((swapFinAdj j (i.succAbove b) : Fin (n + 1)) : ℕ)
          = if (if (b : ℕ) < (i : ℕ) then (b : ℕ) else (b : ℕ) + 1) = (j : ℕ)
            then (j : ℕ) + 1
            else if (if (b : ℕ) < (i : ℕ) then (b : ℕ) else (b : ℕ) + 1) = (j : ℕ) + 1
            then (j : ℕ)
            else if (b : ℕ) < (i : ℕ) then (b : ℕ) else (b : ℕ) + 1 := by
        rw [swapFinAdj_val, succAbove_val]
      have q3 : (((swapFinAdj j i).succAbove b : Fin (n + 1)) : ℕ) =
          if (b : ℕ) < (j : ℕ) + 1 then (b : ℕ) else (b : ℕ) + 1 := by
        rw [succAbove_val, hv]
      rw [q1, q3]
      split_ifs <;> omega
    rw [hfin]
  · have hv : ((swapFinAdj j i : Fin (n + 1)) : ℕ) = (j : ℕ) := by
      rw [swapFinAdj_val, if_neg (by omega : (i : ℕ) ≠ (j : ℕ)), if_pos h]
    have hfin : swapFinAdj j (i.succAbove b) = (swapFinAdj j i).succAbove b := by
      apply Fin.ext
      have q1 : ((swapFinAdj j (i.succAbove b) : Fin (n + 1)) : ℕ)
          = if (if (b : ℕ) < (i : ℕ) then (b : ℕ) else (b : ℕ) + 1) = (j : ℕ)
            then (j : ℕ) + 1
            else if (if (b : ℕ) < (i : ℕ) then (b : ℕ) else (b : ℕ) + 1) = (j : ℕ) + 1
            then (j : ℕ)
            else if (b : ℕ) < (i : ℕ) then (b : ℕ) else (b : ℕ) + 1 := by
        rw [swapFinAdj_val, succAbove_val]
      have q3 : (((swapFinAdj j i).succAbove b : Fin (n + 1)) : ℕ) =
          if (b : ℕ) < (j : ℕ) then (b : ℕ) else (b : ℕ) + 1 := by
        rw [succAbove_val, hv]
      rw [q1, q3]
      split_ifs <;> omega
    rw [hfin]

/-! ### 相邻对换的反交换 -/

/-- **`1 ∧ n` 楔积的相邻对换反交换**：交换第 `j, j+1` 两个槽位，值变号。
证明为逐项配对：`i ∉ {j, j+1}` 的项由 η 的对换变号承担，
`i ∈ {j, j+1}` 的项由 `(-1)ⁱ` 的错位承担。 -/
lemma wedgeOneAnyFun_swapFinAdj {n : ℕ} {x : X}
    (ω : TangentFiber R X x [⋀^Fin 1]→ₗ[R] R)
    (η : TangentFiber R X x [⋀^Fin n]→ₗ[R] R)
    (j : Fin n) (v : Fin (n + 1) → TangentFiber R X x) :
    wedgeOneAnyFun ω η (fun a ↦ v (swapFinAdj j a)) = -(wedgeOneAnyFun ω η v) := by
  have he1 : swapFinAdj j j.succ = j.castSucc := Eq.trans (swapFinAdj_eq_one rfl) rfl
  have he2 : swapFinAdj j j.castSucc = j.succ := Eq.trans (swapFinAdj_eq rfl) rfl
  have key : ∀ i : Fin (n + 1),
      wedgeOneAnyTerm ω η (fun a ↦ v (swapFinAdj j a)) i =
        -wedgeOneAnyTerm ω η v (swapFinAdj j i) := by
    intro i
    show (-1 : R) ^ (i : ℕ) * FiberwiseDifferentialForm.oneArg ω (v (swapFinAdj j i)) *
        η (i.removeNth (fun a : Fin (n + 1) ↦ v (swapFinAdj j a))) =
      -((-1 : R) ^ ((swapFinAdj j i : Fin (n + 1)) : ℕ) *
        FiberwiseDifferentialForm.oneArg ω (v (swapFinAdj j i)) *
        η ((swapFinAdj j i).removeNth v))
    rcases Nat.lt_trichotomy ((i : ℕ)) ((j : ℕ)) with hlt | he | hgt
    · rw [swapFinAdj_of_lt hlt]
      have hη : η ((i : Fin (n + 1)).removeNth (fun a : Fin (n + 1) ↦ v (swapFinAdj j a)))
          = -η ((i : Fin (n + 1)).removeNth v) := by
        rw [removeNth_swapFinAdj_lt hlt v]
        exact alternatingMap_swapFinAdj' η (j - 1) (by have := j.isLt; omega)
          ((i : Fin (n + 1)).removeNth v)
      rw [hη]
      ring
    · -- i = j（对换的对：(-1)ⁱ 错位承担变号）
      have hi : i = j.castSucc := Fin.ext he
      subst hi
      have hη : η (j.castSucc.removeNth (fun a : Fin (n + 1) ↦ v (swapFinAdj j a)))
          = η (j.succ.removeNth v) := by
        rw [removeNth_swapFinAdj_pivot (Or.inl rfl) v, he2]
      rw [hη, he2]
      have hvs : ((j.succ : Fin (n + 1)) : ℕ) = (j : ℕ) + 1 := rfl
      have hvc : ((j.castSucc : Fin (n + 1)) : ℕ) = (j : ℕ) := rfl
      simp only [hvs, hvc]
      rw [pow_succ]
      ring
    · by_cases h₂ : (i : ℕ) = (j : ℕ) + 1
      · -- i = j + 1
        have hi : i = j.succ := Fin.ext h₂
        subst hi
        have hη : η (j.succ.removeNth (fun a : Fin (n + 1) ↦ v (swapFinAdj j a)))
            = η (j.castSucc.removeNth v) := by
          rw [removeNth_swapFinAdj_pivot (Or.inr rfl) v, he1]
        rw [hη, he1]
        have hvs : ((j.succ : Fin (n + 1)) : ℕ) = (j : ℕ) + 1 := rfl
        have hvc : ((j.castSucc : Fin (n + 1)) : ℕ) = (j : ℕ) := rfl
        simp only [hvs, hvc]
        rw [pow_succ]
        ring
      · -- i > j + 1
        rw [swapFinAdj_of_gt (by omega)]
        have hη : η ((i : Fin (n + 1)).removeNth (fun a : Fin (n + 1) ↦ v (swapFinAdj j a)))
            = -η ((i : Fin (n + 1)).removeNth v) := by
          rw [removeNth_swapFinAdj_gt (by omega) v]
          exact alternatingMap_swapFinAdj' η j (by have := j.isLt; have := i.isLt; omega)
            ((i : Fin (n + 1)).removeNth v)
        rw [hη]
        ring
  calc wedgeOneAnyFun ω η (fun a ↦ v (swapFinAdj j a))
      = finSum R (n + 1) (fun i ↦ -wedgeOneAnyTerm ω η v (swapFinAdj j i)) := by
        rw [wedgeOneAnyFun_eq]
        exact finSum_congr R key
    _ = -finSum R (n + 1) (fun i ↦ wedgeOneAnyTerm ω η v (swapFinAdj j i)) := by
        rw [finSum_neg]
    _ = -finSum R (n + 1) (wedgeOneAnyTerm ω η v) := by
        rw [finSum_swapFinAdj n (wedgeOneAnyTerm ω η v) j]
    _ = -(wedgeOneAnyFun ω η v) := by
        rw [wedgeOneAnyFun_eq]

/-! ### 任意两槽相等则为零 -/

/-- `a.succAbove` 单射。 -/
lemma succAbove_right_injective' {n : ℕ} (a : Fin (n + 1)) :
    Function.Injective a.succAbove := Fin.succAbove_right_injective

/-- 相邻两槽相等则 `1 ∧ n` 楔积的原始函数为零（任意特征：非对换位置的项
由尾部含相等分量逐项为零，对换位置的两项直接配对相消）。 -/
lemma wedgeOneAnyFun_eq_zero_of_adjacent {n : ℕ} {x : X}
    (ω : TangentFiber R X x [⋀^Fin 1]→ₗ[R] R)
    (η : TangentFiber R X x [⋀^Fin n]→ₗ[R] R)
    (j : Fin n) (v : Fin (n + 1) → TangentFiber R X x)
    (h : v j.castSucc = v j.succ) :
    wedgeOneAnyFun ω η v = 0 := by
  -- 其余位置的项：η 的尾部同时含相等分量，逐项为零
  have hrest : ∀ a : Fin (n + 1), a ≠ j.castSucc → a ≠ j.succ →
      wedgeOneAnyTerm ω η v a = 0 := by
    intro a ha1 ha2
    obtain ⟨p₁, hp₁⟩ := exists_succAbove_eq (Ne.symm ha1)
    obtain ⟨p₂, hp₂⟩ := exists_succAbove_eq (Ne.symm ha2)
    have hne : (a.removeNth v) p₁ = (a.removeNth v) p₂ := by
      rw [Fin.removeNth_apply, Fin.removeNth_apply, hp₁, hp₂, h]
    have hpne : p₁ ≠ p₂ := by
      intro hh
      rw [← hh] at hp₂
      have hcon : (j.castSucc : Fin (n + 1)) = j.succ := hp₁.symm.trans hp₂
      have hv1 : ((j.castSucc : Fin (n + 1)) : ℕ) = (j : ℕ) := rfl
      have hv2 : ((j.succ : Fin (n + 1)) : ℕ) = (j : ℕ) + 1 := rfl
      rw [hcon] at hv1
      omega
    have hη0 : η (a.removeNth v) = 0 :=
      η.map_eq_zero_of_eq _ hne hpne
    rw [wedgeOneAnyTerm_apply, hη0, mul_zero]
  -- 拆出 j.castSucc 与 j.succ 两项
  have hsx : (j.succ : Fin (n + 1)) ≠ j.castSucc := by
    intro hh
    have hv1 : ((j.castSucc : Fin (n + 1)) : ℕ) = (j : ℕ) := rfl
    have hv2 : ((j.succ : Fin (n + 1)) : ℕ) = (j : ℕ) + 1 := rfl
    rw [hh] at hv2
    omega
  have hrem : ∀ k : Fin (n + 1),
      Function.update (Function.update (wedgeOneAnyTerm ω η v) j.castSucc 0) j.succ 0 k = 0 := by
    intro k
    by_cases h1 : k = j.castSucc
    · rw [h1, Function.update_of_ne hsx.symm, Function.update_self]
    · by_cases h2 : k = j.succ
      · rw [h2, Function.update_self]
      · rw [Function.update_of_ne h2, Function.update_of_ne h1, hrest k h1 h2]
  rw [wedgeOneAnyFun_eq,
    finSum_split_at R (wedgeOneAnyTerm ω η v) j.castSucc,
    finSum_split_at R (Function.update (wedgeOneAnyTerm ω η v) j.castSucc 0) j.succ,
    Function.update_of_ne hsx,
    finSum_eq_zero R hrem, wedgeOneAnyTerm_apply, wedgeOneAnyTerm_apply, add_zero]
  -- 尾部一致 + 配对相消（任意特征）
  have htail : j.castSucc.removeNth v = j.succ.removeNth v := by
    funext b
    rw [Fin.removeNth_apply, Fin.removeNth_apply]
    have hv1 : ((j.castSucc : Fin (n + 1)) : ℕ) = (j : ℕ) := rfl
    have hv2 : ((j.succ : Fin (n + 1)) : ℕ) = (j : ℕ) + 1 := rfl
    by_cases hb : (b : ℕ) < (j : ℕ)
    · have e1 : j.castSucc.succAbove b = ⟨(b : ℕ), by have := b.isLt; omega⟩ :=
        Fin.ext (by rw [succAbove_val, hv1, if_pos hb])
      have e2 : j.succ.succAbove b = ⟨(b : ℕ), by have := b.isLt; omega⟩ :=
        Fin.ext (by rw [succAbove_val, hv2, if_pos (by have := b.isLt; omega)])
      rw [e1, e2]
    · by_cases hb2 : (b : ℕ) = (j : ℕ)
      · have e1 : j.castSucc.succAbove b = j.succ := by
          apply Fin.ext
          rw [succAbove_val, hv1, if_neg (by omega), hv2]
          omega
        have e2 : j.succ.succAbove b = j.castSucc := by
          apply Fin.ext
          rw [succAbove_val, hv2, if_pos (by omega), hv1]
          omega
        rw [e1, e2, h.symm]
      · have e1 : j.castSucc.succAbove b = ⟨(b : ℕ) + 1, by
          have := b.isLt; have := j.isLt; omega⟩ :=
          Fin.ext (by rw [succAbove_val, hv1, if_neg (by have := b.isLt; omega)])
        have e2 : j.succ.succAbove b = ⟨(b : ℕ) + 1, by
          have := b.isLt; have := j.isLt; omega⟩ :=
          Fin.ext (by rw [succAbove_val, hv2, if_neg (by have := b.isLt; omega)])
        rw [e1, e2]
  rw [htail, h]
  have hv1 : ((j.castSucc : Fin (n + 1)) : ℕ) = (j : ℕ) := rfl
  have hv2 : ((j.succ : Fin (n + 1)) : ℕ) = (j : ℕ) + 1 := rfl
  rw [hv1, hv2, pow_succ]
  ring

/-- **`1 ∧ n` 楔积交错性**：任取两个不同槽位代入相同的切向量，值为零。
冒泡归纳化归到相邻情形。 -/
lemma wedgeOneAnyFun_eq_zero_of_eq {n : ℕ} {x : X}
    (ω : TangentFiber R X x [⋀^Fin 1]→ₗ[R] R)
    (η : TangentFiber R X x [⋀^Fin n]→ₗ[R] R)
    {i j : Fin (n + 1)} (v : Fin (n + 1) → TangentFiber R X x)
    (h : v i = v j) (hij : i ≠ j) :
    wedgeOneAnyFun ω η v = 0 := by
  have aux : ∀ d : ℕ, ∀ w : Fin (n + 1) → TangentFiber R X x, ∀ i j : Fin (n + 1),
      (j : ℕ) = (i : ℕ) + (d + 1) → w i = w j → wedgeOneAnyFun ω η w = 0 := by
    intro d
    induction d with
    | zero =>
        intro w i j hd he
        obtain ⟨k, rfl⟩ : ∃ k : Fin n, i = k.castSucc :=
          ⟨⟨(i : ℕ), by have := i.isLt; have := j.isLt; omega⟩, rfl⟩
        have hcv : ((k.castSucc : Fin (n + 1)) : ℕ) = (k : ℕ) := rfl
        have hjk : j = k.succ := Fin.ext (by
          have hkv : ((k.succ : Fin (n + 1)) : ℕ) = (k : ℕ) + 1 := rfl
          have := j.isLt
          omega)
        subst hjk
        exact wedgeOneAnyFun_eq_zero_of_adjacent ω η k w he
    | succ d ih =>
        intro w i j hd he
        have hin : (i : ℕ) < n := by have := i.isLt; have := j.isLt; omega
        set t : Fin n := ⟨(j : ℕ) - 1, by have := j.isLt; omega⟩ with ht
        have htv : (t : ℕ) = (j : ℕ) - 1 := rfl
        have hmove : wedgeOneAnyFun ω η w
            = -(wedgeOneAnyFun ω η (fun a ↦ w (swapFinAdj t a))) := by
          rw [wedgeOneAnyFun_swapFinAdj ω η t w, neg_neg]
        rw [hmove, neg_eq_zero]
        have hwj : (fun a ↦ w (swapFinAdj t a)) i = w i := by
          show w (swapFinAdj t i) = w i
          rw [swapFinAdj_of_lt (show (i : ℕ) < (t : ℕ) by omega)]
        have hwit : (fun a ↦ w (swapFinAdj t a))
            (⟨(t : ℕ), by have := t.isLt; omega⟩ : Fin (n + 1)) = w j := by
          have hp : (Fin.mk ((t : ℕ) + 1) (by have := t.isLt; omega)) = j := by
            apply Fin.ext
            show (t : ℕ) + 1 = (j : ℕ)
            omega
          show w (swapFinAdj t (⟨(t : ℕ), by have := t.isLt; omega⟩ : Fin (n + 1))) = w j
          rw [swapFinAdj_eq rfl, hp]
        exact ih (fun a ↦ w (swapFinAdj t a)) i
          (⟨(t : ℕ), by have := t.isLt; omega⟩ : Fin (n + 1))
          (show (t : ℕ) = (i : ℕ) + (d + 1) by omega)
          (hwj.trans (he.trans hwit.symm))
  rcases Nat.lt_trichotomy ((j : ℕ)) ((i : ℕ)) with hlt | heq | hgt
  · exact aux (i - j - 1) v j i (by omega) h.symm
  · exact absurd (Fin.ext heq) (Ne.symm hij)
  · exact aux (j - i - 1) v i j (by omega) h

end WedgeOneAnyGen

/-! ## `1 ∧ n` 楔积的严格形式打包

把 `wedgeOneAnyFun` 打包为纤维层 `AlternatingMap`：交错性由
`wedgeOneAnyFun_eq_zero_of_eq` 保证，逐槽加法/数乘由 η 的
`map_update_add/smul`（经 `k.succAbove m = i` 的原像）与 ω 的线性承担。 -/

section WedgeOneAnyPack

variable {R : Type u} [CommRing R] {X : Type u} [Microlinear R X]
variable [DecidableEq (Fin (n + 1))]

/-- `succAbove` 的像不含 `k` 本身（构造性，替代 Mathlib choice 版）。 -/
lemma succAbove_ne' {n : ℕ} (k : Fin (n + 1)) (r : Fin n) : k.succAbove r ≠ k := by
  rw [Fin.succAbove]
  by_cases h : (Fin.castSucc r : Fin (n + 1)) < k
  · rw [if_pos h]
    intro hh
    have hv : ((Fin.castSucc r : Fin (n + 1)) : ℕ) = (k : ℕ) := by rw [hh]
    rw [Fin.val_castSucc] at hv
    rw [Fin.lt_def, Fin.val_castSucc] at h
    omega
  · rw [if_neg h]
    intro hh
    have hv : ((Fin.succ r : Fin (n + 1)) : ℕ) = (k : ℕ) := by rw [hh]
    rw [Fin.val_succ] at hv
    rw [Fin.lt_def, Fin.val_castSucc] at h
    omega

/-- 更新第 `i` 槽后，第 `k ≠ i` 项的 η 尾部：删除第 `k` 槽恰在原像 `m` 处
看到更新。 -/
lemma removeNth_update_of_succAbove {n : ℕ} [DecidableEq (Fin (n + 1))] {T : Type u}
    {k : Fin (n + 1)} {i : Fin (n + 1)} (hk : i ≠ k) (v : Fin (n + 1) → T)
    (m : Fin n) (hm : k.succAbove m = i) (x : T) :
    k.removeNth (Function.update v i x) = Function.update (k.removeNth v) m x := by
  funext r
  by_cases hr : r = m
  · subst hr
    rw [Fin.removeNth_apply]
    simp [hm]
  · rw [Fin.removeNth_apply, Function.update_of_ne (by
      intro hh
      exact hr (Fin.succAbove_right_injective (hh.trans hm.symm)))]
    rw [Function.update_apply, Fin.removeNth_apply, if_neg hr]

/-- `1 ∧ n` 楔积对第 `i` 槽加法。 -/
lemma wedgeOneAnyFun_update_add {n : ℕ} [DecidableEq (Fin (n + 1))] {x : X}
    (ω : TangentFiber R X x [⋀^Fin 1]→ₗ[R] R)
    (η : TangentFiber R X x [⋀^Fin n]→ₗ[R] R)
    (v : Fin (n + 1) → TangentFiber R X x) (i : Fin (n + 1))
    (p q : TangentFiber R X x) :
    wedgeOneAnyFun ω η (Function.update v i (p + q)) =
      wedgeOneAnyFun ω η (Function.update v i p) +
      wedgeOneAnyFun ω η (Function.update v i q) := by
  rw [wedgeOneAnyFun_eq, wedgeOneAnyFun_eq, wedgeOneAnyFun_eq, ← finSum_add]
  refine finSum_congr R (fun k => ?_)
  have habs : ∀ X : TangentFiber R X x,
      k.removeNth (Function.update v k X) = k.removeNth v := by
    intro X
    funext r
    rw [Fin.removeNth_apply, Function.update_of_ne (succAbove_ne' k r),
      Fin.removeNth_apply]
  by_cases hk : k = i
  · subst hk
    rw [wedgeOneAnyTerm_apply, wedgeOneAnyTerm_apply, wedgeOneAnyTerm_apply,
      habs (p + q), habs p, habs q]
    simp only [Function.update_self]
    rw [map_add]
    ring
  · have hik : i ≠ k := fun hh => hk hh.symm
    obtain ⟨m, hm⟩ := exists_succAbove_eq hik
    rw [wedgeOneAnyTerm_apply, wedgeOneAnyTerm_apply, wedgeOneAnyTerm_apply,
      Function.update_of_ne hk, Function.update_of_ne hk, Function.update_of_ne hk,
      removeNth_update_of_succAbove hik v m hm (p + q),
      removeNth_update_of_succAbove hik v m hm p,
      removeNth_update_of_succAbove hik v m hm q,
      η.map_update_add]
    ring

/-- `1 ∧ n` 楔积对第 `i` 槽数乘。 -/
lemma wedgeOneAnyFun_update_smul {n : ℕ} [DecidableEq (Fin (n + 1))] {x : X}
    (ω : TangentFiber R X x [⋀^Fin 1]→ₗ[R] R)
    (η : TangentFiber R X x [⋀^Fin n]→ₗ[R] R)
    (v : Fin (n + 1) → TangentFiber R X x) (i : Fin (n + 1))
    (c : R) (p : TangentFiber R X x) :
    wedgeOneAnyFun ω η (Function.update v i (c • p)) =
      c • wedgeOneAnyFun ω η (Function.update v i p) := by
  rw [wedgeOneAnyFun_eq, wedgeOneAnyFun_eq]
  show finSum R (n + 1) (wedgeOneAnyTerm ω η (Function.update v i (c • p)))
    = c * finSum R (n + 1) (wedgeOneAnyTerm ω η (Function.update v i p))
  rw [← finSum_mul_left]
  refine finSum_congr R (fun k => ?_)
  have habs : ∀ X : TangentFiber R X x,
      k.removeNth (Function.update v k X) = k.removeNth v := by
    intro X
    funext r
    rw [Fin.removeNth_apply, Function.update_of_ne (succAbove_ne' k r),
      Fin.removeNth_apply]
  by_cases hk : k = i
  · subst hk
    rw [wedgeOneAnyTerm_apply, wedgeOneAnyTerm_apply, habs (c • p), habs p]
    simp only [Function.update_self]
    rw [map_smul, smul_eq_mul]
    ring
  · have hik : i ≠ k := fun hh => hk hh.symm
    obtain ⟨m, hm⟩ := exists_succAbove_eq hik
    rw [wedgeOneAnyTerm_apply, wedgeOneAnyTerm_apply,
      Function.update_of_ne hk, Function.update_of_ne hk,
      removeNth_update_of_succAbove hik v m hm (c • p),
      removeNth_update_of_succAbove hik v m hm p,
      η.map_update_smul, smul_eq_mul]
    ring

/-- **一般 `1 ∧ n` 楔积**：Kock I.14 (14.7) 展开的严格交错多线性形式。 -/
def wedgeOneAny {n : ℕ} (ω : FiberwiseDifferentialForm R X 1)
    (η : FiberwiseDifferentialForm R X n) :
    FiberwiseDifferentialForm R X (n + 1) := by
  intro x
  exact
    { toMultilinearMap :=
        { toFun := wedgeOneAnyFun (ω x) (η x)
          map_update_add' := by
            intro _ v i p q
            exact wedgeOneAnyFun_update_add (ω x) (η x) v i p q
          map_update_smul' := by
            intro _ v i c p
            exact wedgeOneAnyFun_update_smul (ω x) (η x) v i c p }
      map_eq_zero_of_eq' := by
        intro v i j h hij
        exact wedgeOneAnyFun_eq_zero_of_eq (ω x) (η x) v h hij }

@[simp]
lemma wedgeOneAny_apply {n : ℕ} (ω : FiberwiseDifferentialForm R X 1)
    (η : FiberwiseDifferentialForm R X n) (x : X)
    (v : Fin (n + 1) → TangentFiber R X x) :
    wedgeOneAny ω η x v = wedgeOneAnyFun (ω x) (η x) v := rfl

/-- 楔积对第一因子的加法。 -/
lemma wedgeOneAny_add_left {n : ℕ} (ω₁ ω₂ : FiberwiseDifferentialForm R X 1)
    (η : FiberwiseDifferentialForm R X n) :
    wedgeOneAny (ω₁ + ω₂) η = wedgeOneAny ω₁ η + wedgeOneAny ω₂ η := by
  funext x
  apply AlternatingMap.ext
  intro v
  show wedgeOneAnyFun ((ω₁ + ω₂) x) (η x) v =
    wedgeOneAnyFun (ω₁ x) (η x) v + wedgeOneAnyFun (ω₂ x) (η x) v
  rw [Pi.add_apply, wedgeOneAnyFun_eq, wedgeOneAnyFun_eq, wedgeOneAnyFun_eq,
    ← finSum_add]
  refine finSum_congr R (fun k => ?_)
  rw [wedgeOneAnyTerm_apply, wedgeOneAnyTerm_apply, wedgeOneAnyTerm_apply,
    FiberwiseDifferentialForm.oneArg_add]
  ring

/-- 楔积对第二因子的加法。 -/
lemma wedgeOneAny_add_right {n : ℕ} (ω : FiberwiseDifferentialForm R X 1)
    (η₁ η₂ : FiberwiseDifferentialForm R X n) :
    wedgeOneAny ω (η₁ + η₂) = wedgeOneAny ω η₁ + wedgeOneAny ω η₂ := by
  funext x
  apply AlternatingMap.ext
  intro v
  show wedgeOneAnyFun (ω x) ((η₁ + η₂) x) v =
    wedgeOneAnyFun (ω x) (η₁ x) v + wedgeOneAnyFun (ω x) (η₂ x) v
  rw [Pi.add_apply, wedgeOneAnyFun_eq, wedgeOneAnyFun_eq,
    wedgeOneAnyFun_eq, ← finSum_add]
  refine finSum_congr R (fun k => ?_)
  rw [wedgeOneAnyTerm_apply, wedgeOneAnyTerm_apply, wedgeOneAnyTerm_apply,
    AlternatingMap.add_apply]
  ring

/-- 楔积对第一因子的数乘。 -/
lemma wedgeOneAny_smul_left {n : ℕ} (c : R) (ω : FiberwiseDifferentialForm R X 1)
    (η : FiberwiseDifferentialForm R X n) :
    wedgeOneAny (c • ω) η = c • wedgeOneAny ω η := by
  funext x
  apply AlternatingMap.ext
  intro v
  show wedgeOneAnyFun ((c • ω) x) (η x) v = c • wedgeOneAnyFun (ω x) (η x) v
  rw [Pi.smul_apply]
  show wedgeOneAnyFun (c • ω x) (η x) v = c * wedgeOneAnyFun (ω x) (η x) v
  rw [wedgeOneAnyFun_eq, wedgeOneAnyFun_eq, ← finSum_mul_left]
  refine finSum_congr R (fun k => ?_)
  rw [wedgeOneAnyTerm_apply, wedgeOneAnyTerm_apply,
    FiberwiseDifferentialForm.oneArg_smul]
  ring

/-- 楔积对第二因子的数乘。 -/
lemma wedgeOneAny_smul_right {n : ℕ} (c : R) (ω : FiberwiseDifferentialForm R X 1)
    (η : FiberwiseDifferentialForm R X n) :
    wedgeOneAny ω (c • η) = c • wedgeOneAny ω η := by
  funext x
  apply AlternatingMap.ext
  intro v
  show wedgeOneAnyFun (ω x) ((c • η) x) v = c • wedgeOneAnyFun (ω x) (η x) v
  rw [Pi.smul_apply]
  show wedgeOneAnyFun (ω x) (c • η x) v = c * wedgeOneAnyFun (ω x) (η x) v
  rw [wedgeOneAnyFun_eq, wedgeOneAnyFun_eq, ← finSum_mul_left]
  refine finSum_congr R (fun k => ?_)
  rw [wedgeOneAnyTerm_apply, wedgeOneAnyTerm_apply, AlternatingMap.smul_apply,
    smul_eq_mul]
  ring

end WedgeOneAnyPack

/-! ## 奇异上链与 de Rham 复形

在单纯形方法中，n-上链是从 (n+1)-点组到 R 的函数。
余边界算子 ∂ 通过面删除的交错和定义：∂c 的值 = Σ(-1)ⁱ c(删除第 i 个顶点)。
∂² = 0 是纯组合恒等式（成对消去），不需要切向量传输。 -/

section DeRham

variable {R : Type u} [CommRing R] {X : Type u}

/-- n-单纯形的 (n+1) 个顶点。 -/
abbrev SimplexPts (X : Type u) (n : ℕ) := Fin (n + 1) → X

/-- n-上链：从 n-单纯形到 R 的函数。 -/
abbrev Cochain (R : Type u) [CommRing R] (X : Type u) (n : ℕ) :=
  SimplexPts X n → R

/-- 第 i 个面：从 (n+1)-单纯形中删除第 i 个顶点，得到 n-单纯形。 -/
def coFace {X : Type u} {n : ℕ} (σ : SimplexPts X (n + 1)) (i : Fin (n + 2)) :
    SimplexPts X n :=
  fun k ↦ σ (i.succAbove k)

/-- 余边界算子 ∂ : Cⁿ → Cⁿ⁺¹。 -/
def coboundary {R : Type u} [CommRing R] {X : Type u} {n : ℕ}
    (c : Cochain R X n) : Cochain R X (n + 1) :=
  fun σ ↦ finSum R (n + 2) (fun i : Fin (n + 2) ↦
    (-1 : R) ^ (i : ℕ) * c (coFace σ i))

lemma coboundary_apply {R : Type u} [CommRing R] {X : Type u} {n : ℕ}
    (c : Cochain R X n) (σ : SimplexPts X (n + 1)) :
    coboundary c σ = finSum R (n + 2) (fun i : Fin (n + 2) ↦
      (-1 : R) ^ (i : ℕ) * c (coFace σ i)) := rfl

/-! ### 0-形式的余边界 -/

/-- 0-形式 `f : X → R` 的余边界：`df(x₀,x₁) = f(x₁) - f(x₀)`。 -/
def d0 {R : Type u} [CommRing R] {X : Type u} (f : X → R) :
    Cochain R X 1 :=
  fun σ ↦ f (σ 1) - f (σ 0)

lemma d0_apply {R : Type u} [CommRing R] {X : Type u} (f : X → R)
    (σ : SimplexPts X 1) :
    d0 f σ = f (σ 1) - f (σ 0) := rfl

/-- `finSum R 3` 的显式展开（关键辅助引理：避免 `Fin.succ` 索引问题）。 -/
lemma finSum_three (R : Type u) [AddCommMonoid R] (g : Fin 3 → R) :
    finSum R 3 g = g 0 + (g 1 + (g 2 + 0)) := rfl

/-- `finSum R 4` 的显式展开。 -/
lemma finSum_four (R : Type u) [AddCommMonoid R] (g : Fin 4 → R) :
    finSum R 4 g = g 0 + (g 1 + (g 2 + (g 3 + 0))) := rfl

/- **∂² = 0 对 1-上链**：对 `c : Cochain X 1`，`∂(∂c)(σ) = 0`。

数学证明：展开 4×3=12 项双重求和，6 对面复合恒等式使每一对正负抵消。
6 对面复合等式已在下方证明（`fcc1` 至 `fcc6`）；完整的 12 项代数配对
消去需要 `finSum` 展开后 `simp` 能评估 Fin 系数幂运算，当前 tactic
基础设施暂不支持。后续可通过专用 `norm_num` 扩展或手工展开解决。 -/

/-- 面复合等式 1：`F(0,0) = F(1,0)`。 -/
lemma fcc1 {X : Type u} (σ : Fin 4 → X) :
    (fun k : Fin 2 ↦ σ ((0:Fin 4).succAbove ((0:Fin 3).succAbove k)))
    = (fun k : Fin 2 ↦ σ ((1:Fin 4).succAbove ((0:Fin 3).succAbove k))) := by
  funext k
  have h : ((0:Fin 4).succAbove ((0:Fin 3).succAbove k) : Fin 4) =
           ((1:Fin 4).succAbove ((0:Fin 3).succAbove k) : Fin 4) := by
    cases k using Fin.cases with
    | zero => decide
    | succ m => cases m using Fin.cases with
      | zero => decide
      | succ m => exact Fin.elim0 m
  rw [h]

/-- 面复合等式 2：`F(0,1) = F(2,0)`。 -/
lemma fcc2 {X : Type u} (σ : Fin 4 → X) :
    (fun k : Fin 2 ↦ σ ((0:Fin 4).succAbove ((1:Fin 3).succAbove k)))
    = (fun k : Fin 2 ↦ σ ((2:Fin 4).succAbove ((0:Fin 3).succAbove k))) := by
  funext k
  have h : ((0:Fin 4).succAbove ((1:Fin 3).succAbove k) : Fin 4) =
           ((2:Fin 4).succAbove ((0:Fin 3).succAbove k) : Fin 4) := by
    cases k using Fin.cases with
    | zero => decide
    | succ m => cases m using Fin.cases with
      | zero => decide
      | succ m => exact Fin.elim0 m
  rw [h]

/-- 面复合等式 3：`F(0,2) = F(3,0)`。 -/
lemma fcc3 {X : Type u} (σ : Fin 4 → X) :
    (fun k : Fin 2 ↦ σ ((0:Fin 4).succAbove ((2:Fin 3).succAbove k)))
    = (fun k : Fin 2 ↦ σ ((3:Fin 4).succAbove ((0:Fin 3).succAbove k))) := by
  funext k
  have h : ((0:Fin 4).succAbove ((2:Fin 3).succAbove k) : Fin 4) =
           ((3:Fin 4).succAbove ((0:Fin 3).succAbove k) : Fin 4) := by
    cases k using Fin.cases with
    | zero => decide
    | succ m => cases m using Fin.cases with
      | zero => decide
      | succ m => exact Fin.elim0 m
  rw [h]

/-- 面复合等式 4：`F(1,1) = F(2,1)`。 -/
lemma fcc4 {X : Type u} (σ : Fin 4 → X) :
    (fun k : Fin 2 ↦ σ ((1:Fin 4).succAbove ((1:Fin 3).succAbove k)))
    = (fun k : Fin 2 ↦ σ ((2:Fin 4).succAbove ((1:Fin 3).succAbove k))) := by
  funext k
  have h : ((1:Fin 4).succAbove ((1:Fin 3).succAbove k) : Fin 4) =
           ((2:Fin 4).succAbove ((1:Fin 3).succAbove k) : Fin 4) := by
    cases k using Fin.cases with
    | zero => decide
    | succ m => cases m using Fin.cases with
      | zero => decide
      | succ m => exact Fin.elim0 m
  rw [h]

/-- 面复合等式 5：`F(1,2) = F(3,1)`。 -/
lemma fcc5 {X : Type u} (σ : Fin 4 → X) :
    (fun k : Fin 2 ↦ σ ((1:Fin 4).succAbove ((2:Fin 3).succAbove k)))
    = (fun k : Fin 2 ↦ σ ((3:Fin 4).succAbove ((1:Fin 3).succAbove k))) := by
  funext k
  have h : ((1:Fin 4).succAbove ((2:Fin 3).succAbove k) : Fin 4) =
           ((3:Fin 4).succAbove ((1:Fin 3).succAbove k) : Fin 4) := by
    cases k using Fin.cases with
    | zero => decide
    | succ m => cases m using Fin.cases with
      | zero => decide
      | succ m => exact Fin.elim0 m
  rw [h]

/-- 面复合等式 6：`F(2,2) = F(3,2)`。 -/
lemma fcc6 {X : Type u} (σ : Fin 4 → X) :
    (fun k : Fin 2 ↦ σ ((2:Fin 4).succAbove ((2:Fin 3).succAbove k)))
    = (fun k : Fin 2 ↦ σ ((3:Fin 4).succAbove ((2:Fin 3).succAbove k))) := by
  funext k
  have h : ((2:Fin 4).succAbove ((2:Fin 3).succAbove k) : Fin 4) =
           ((3:Fin 4).succAbove ((2:Fin 3).succAbove k) : Fin 4) := by
    cases k using Fin.cases with
    | zero => decide
    | succ m => cases m using Fin.cases with
      | zero => decide
      | succ m => exact Fin.elim0 m
  rw [h]

/-- **∂² = 0 对 1-上链**：对 `c : Cochain X 1`，`∂(∂c)(σ) = 0`。

展开 4×3=12 项双重求和，用 `fcc1`-`fcc6` 配对面复合，
`norm_num` 评估 Fin 系数幂，`ring` 关闭。 -/
theorem coboundary_coboundary_one {R : Type u} [CommRing R] {X : Type u}
    (c : Cochain R X 1) (σ : SimplexPts X 3) :
    coboundary (coboundary c) σ = 0 := by
  unfold coboundary coFace
  rw [finSum_four]
  repeat rw [finSum_three]
  simp only [fcc1, fcc2, fcc3, fcc4, fcc5, fcc6]
  have c0 : (((0 : Fin 4) : ℕ)) = 0 := rfl
  have c1 : (((1 : Fin 4) : ℕ)) = 1 := rfl
  have c2 : (((2 : Fin 4) : ℕ)) = 2 := rfl
  have c3 : (((3 : Fin 4) : ℕ)) = 3 := rfl
  have d0' : (((0 : Fin 3) : ℕ)) = 0 := rfl
  have d1' : (((1 : Fin 3) : ℕ)) = 1 := rfl
  have d2' : (((2 : Fin 3) : ℕ)) = 2 := rfl
  simp only [c0, c1, c2, c3, d0', d1', d2']
  simp only [pow_zero, pow_one, pow_two]
  simp only [neg_mul, add_zero]
  ring

/-- **d² = 0 对 0-形式**：`(∂(d₀f))(x₀,x₁,x₂) = 0`。

纯代数恒等式：`[f(x₂)-f(x₁)] - [f(x₂)-f(x₀)] + [f(x₁)-f(x₀)] = 0`。 -/
theorem coboundary_d0 {R : Type u} [CommRing R] {X : Type u}
    (f : X → R) (σ : SimplexPts X 2) :
    coboundary (d0 f) σ = 0 := by
  unfold coboundary
  rw [finSum_three]
  simp only [d0, coFace]
  have e00 : ((0:Fin 3).succAbove (0:Fin 2) : Fin 3) = 1 := by decide
  have e01 : ((0:Fin 3).succAbove (1:Fin 2) : Fin 3) = 2 := by decide
  have e10 : ((1:Fin 3).succAbove (0:Fin 2) : Fin 3) = 0 := by decide
  have e11 : ((1:Fin 3).succAbove (1:Fin 2) : Fin 3) = 2 := by decide
  have e20 : ((2:Fin 3).succAbove (0:Fin 2) : Fin 3) = 0 := by decide
  have e21 : ((2:Fin 3).succAbove (1:Fin 2) : Fin 3) = 1 := by decide
  simp only [e00, e01, e10, e11, e20, e21]
  have c0 : ((0:Fin 3):ℕ) = 0 := rfl
  have c1 : ((1:Fin 3):ℕ) = 1 := rfl
  have c2 : ((2:Fin 3):ℕ) = 2 := rfl
  simp only [c0, c1, c2]
  simp only [pow_zero, pow_one, pow_two]
  simp only [neg_mul, add_zero]
  ring

/-! ### 一般 n 的 ∂² = 0（无选择公理）

策略：把双和整体提升到 ℕ-指标守卫项函数 `ddTerm`，用
`finSum_rect_eq_tri`（矩形和 = 三角和，逐点配对）一次性完成指标重排，
再用 δδ 复合恒等式 + 符号相消收尾。不出现 `Finset`，全程无选择公理。 -/

/-- δδ 复合恒等式：先删第 `a` 个面再删第 `b` 个面（`a ≤ b`），
等于先删第 `b+1` 个面再删第 `a` 个面。 -/
lemma coFace_comp_coFace {n : ℕ} (σ : Fin (n + 3) → X) {a : Fin (n + 3)} {b : Fin (n + 2)}
    (hab : (a : ℕ) ≤ (b : ℕ)) :
    coFace (coFace σ a) b
      = coFace (coFace σ ⟨(b : ℕ) + 1, by have := b.isLt; omega⟩)
          (⟨(a : ℕ), by have := b.isLt; have := hab; omega⟩ : Fin (n + 2)) := by
  funext k
  show σ (a.succAbove (b.succAbove k)) = σ ((⟨(b : ℕ) + 1, by have := b.isLt; omega⟩ : Fin (n + 3)).succAbove
    ((⟨(a : ℕ), by have := b.isLt; have := hab; omega⟩ : Fin (n + 2)).succAbove k))
  apply congrArg σ
  apply Fin.ext
  have q2 : ((b.succAbove k : Fin (n + 2)) : ℕ) =
      if (k : ℕ) < (b : ℕ) then (k : ℕ) else (k : ℕ) + 1 := succAbove_val b k
  have q1 : ((a.succAbove (b.succAbove k) : Fin (n + 3)) : ℕ) =
      (if (if (k : ℕ) < (b : ℕ) then (k : ℕ) else (k : ℕ) + 1) < (a : ℕ)
        then (if (k : ℕ) < (b : ℕ) then (k : ℕ) else (k : ℕ) + 1)
        else (if (k : ℕ) < (b : ℕ) then (k : ℕ) else (k : ℕ) + 1) + 1) := by
    rw [succAbove_val, q2]
  have q4 : (((⟨(a : ℕ), by have := b.isLt; have := hab; omega⟩ : Fin (n + 2)).succAbove k :
      Fin (n + 2)) : ℕ) =
      if (k : ℕ) < (a : ℕ) then (k : ℕ) else (k : ℕ) + 1 := succAbove_val _ k
  have q3 : (((⟨(b : ℕ) + 1, by have := b.isLt; omega⟩ : Fin (n + 3)).succAbove
      ((⟨(a : ℕ), by have := b.isLt; have := hab; omega⟩ : Fin (n + 2)).succAbove k)) : ℕ) =
      (if (if (k : ℕ) < (a : ℕ) then (k : ℕ) else (k : ℕ) + 1) < (b : ℕ) + 1
        then (if (k : ℕ) < (a : ℕ) then (k : ℕ) else (k : ℕ) + 1)
        else (if (k : ℕ) < (a : ℕ) then (k : ℕ) else (k : ℕ) + 1) + 1) := by
    rw [succAbove_val, q4]
  rw [q1, q3]
  by_cases h1 : (k : ℕ) < (b : ℕ)
  · by_cases h2 : (k : ℕ) < (a : ℕ)
    · rw [if_pos h1, if_pos h2, if_pos (by omega : (k : ℕ) < (b : ℕ) + 1)]
    · rw [if_pos h1, if_neg h2, if_pos (by omega : (k : ℕ) + 1 < (b : ℕ) + 1)]
  · by_cases h2 : (k : ℕ) < (a : ℕ)
    · exfalso; omega
    · rw [if_neg h1, if_neg h2, if_neg (show ¬((k : ℕ) + 1 < (a : ℕ)) by omega),
        if_neg (show ¬((k : ℕ) + 1 < (b : ℕ) + 1) by omega)]

/-- δδ 项的 ℕ-指标守卫版本：界内取真实项，界外取 0。

把双和提升到全 ℕ-指标，是规避 `Fin` 依赖类型下指标重排时
mk-证明项断裂问题的关键步骤。 -/
def ddTerm (R : Type u) [CommRing R] {X : Type u} {n : ℕ} (c : Cochain R X n)
    (σ : SimplexPts X (n + 2)) (a b : ℕ) : R :=
  if h : a < n + 3 ∧ b < n + 2 then
    (-1 : R) ^ (a + b) * c (coFace (coFace σ ⟨a, h.1⟩) ⟨b, h.2⟩)
  else 0

/-- **一般 n 的 ∂² = 0**

`∂(∂c) = 0`：双重余边界为零。证明：矩形双和 = 三角配对和
（`finSum_rect_eq_tri`），每个配对 `ddTerm i j + ddTerm j (i-1)` 中
两面经 δδ 复合恒等式（`coFace_comp_coFace`）相同，而符号
`(-1)^{i+j} + (-1)^{j+i-1} = 0`（`j < i` 保证 `i+j ≥ 1`），逐对相消。

纯组合恒等式，构造性证明；`#print axioms` 仅 `[propext, Quot.sound]`。 -/
theorem coboundary_coboundary {n : ℕ} (c : Cochain R X n) :
    coboundary (coboundary c) = 0 := by
  funext σ
  show finSum R (n + 3) (fun i : Fin (n + 3) => (-1 : R) ^ ((i : ℕ)) *
    finSum R (n + 2) (fun j : Fin (n + 2) => (-1 : R) ^ ((j : ℕ)) *
      c (coFace (coFace σ i) j))) = (0 : R)
  -- 提升到 ℕ-指标守卫项函数
  have hA : finSum R (n + 3) (fun i : Fin (n + 3) => (-1 : R) ^ ((i : ℕ)) *
      finSum R (n + 2) (fun j : Fin (n + 2) => (-1 : R) ^ ((j : ℕ)) *
        c (coFace (coFace σ i) j)))
      = finSum R (n + 3) (fun i : Fin (n + 3) => finSum R (n + 2) (fun j : Fin (n + 2) =>
          ddTerm R c σ ((i : ℕ)) ((j : ℕ)))) := by
    apply finSum_congr R
    intro i
    rw [← finSum_mul_left (R := R) (n := n + 2) (a := (-1 : R) ^ ((i : ℕ)))
      (f := fun j : Fin (n + 2) => (-1 : R) ^ ((j : ℕ)) * c (coFace (coFace σ i) j))]
    apply finSum_congr R
    intro j
    have hp : (i : ℕ) < n + 3 ∧ (j : ℕ) < n + 2 := ⟨i.isLt, j.isLt⟩
    simp only [ddTerm]
    rw [dif_pos hp]
    have q1 : (Fin.mk (i : ℕ) hp.1 : Fin (n + 3)) = i := Fin.ext rfl
    have q2 : (Fin.mk (j : ℕ) hp.2 : Fin (n + 2)) = j := Fin.ext rfl
    rw [q1, q2, pow_add]
    ring
  -- 矩形 = 三角
  have hB : finSum R (n + 3) (fun i : Fin (n + 3) => finSum R (n + 2) (fun j : Fin (n + 2) =>
      ddTerm R c σ ((i : ℕ)) ((j : ℕ))))
      = finSum R (n + 3) (fun i : Fin (n + 3) => finSum R ((i : ℕ)) (fun j : Fin ((i : ℕ)) =>
          ddTerm R c σ ((i : ℕ)) ((j : ℕ)) + ddTerm R c σ ((j : ℕ)) (((i : ℕ)) - 1))) :=
    finSum_rect_eq_tri (R := R) (W := n + 2) (fun a b => ddTerm R c σ a b)
  rw [hA, hB]
  apply finSum_eq_zero R
  intro i
  apply finSum_eq_zero R
  intro j
  -- 逐点相消：ddTerm i j + ddTerm j (i-1) = 0
  have hij : (j : ℕ) < (i : ℕ) := j.isLt
  have hib : (i : ℕ) < n + 3 := i.isLt
  have g1 : (i : ℕ) < n + 3 ∧ (j : ℕ) < n + 2 := ⟨hib, by omega⟩
  have g2 : (j : ℕ) < n + 3 ∧ ((i : ℕ) - 1) < n + 2 := ⟨by omega, by omega⟩
  simp only [ddTerm, dif_pos g1, dif_pos g2]
  -- 第二项的面经 δδ 恒等式改写为与第一项相同的面
  have hface : coFace (coFace σ (Fin.mk (j : ℕ) g2.1)) (Fin.mk ((i : ℕ) - 1) g2.2)
      = coFace (coFace σ (Fin.mk (i : ℕ) hib)) (Fin.mk (j : ℕ) g1.2) := by
    have vJ : ((Fin.mk (j : ℕ) g2.1 : Fin (n + 3)) : ℕ) = (j : ℕ) := rfl
    have vK : ((Fin.mk ((i : ℕ) - 1) g2.2 : Fin (n + 2)) : ℕ) = (i : ℕ) - 1 := rfl
    calc coFace (coFace σ (Fin.mk (j : ℕ) g2.1)) (Fin.mk ((i : ℕ) - 1) g2.2)
        = coFace (coFace σ (Fin.mk ((i : ℕ) - 1 + 1)
            (by have hb := (Fin.mk ((i : ℕ) - 1) g2.2).isLt; omega)))
            (Fin.mk (j : ℕ) (by have := (Fin.mk (j : ℕ) g2.1).isLt; omega)) :=
          coFace_comp_coFace (σ := σ) (a := (Fin.mk (j : ℕ) g2.1 : Fin (n + 3)))
            (b := (Fin.mk ((i : ℕ) - 1) g2.2 : Fin (n + 2))) (by omega)
      _ = coFace (coFace σ (Fin.mk (i : ℕ) hib)) (Fin.mk (j : ℕ) g1.2) := by
          have eA : (Fin.mk ((i : ℕ) - 1 + 1)
              (by have hb := (Fin.mk ((i : ℕ) - 1) g2.2).isLt; omega) : Fin (n + 3))
              = (Fin.mk (i : ℕ) hib : Fin (n + 3)) :=
            Fin.ext (by simp only [Fin.val_mk]; omega)
          rw [eA]
  rw [hface]
  -- 桥接第一项的外层 mk 证明项
  have q1 : (Fin.mk (i : ℕ) g1.1 : Fin (n + 3)) = (Fin.mk (i : ℕ) hib : Fin (n + 3)) := Fin.ext rfl
  rw [q1]
  -- 符号相消：(-1)^{i+j} + (-1)^{j+i-1} = 0（因 j < i 保证 i+j ≥ 1）
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (i : ℕ) + (j : ℕ) = m + 1 := ⟨(i : ℕ) + (j : ℕ) - 1, by omega⟩
  have hm2 : (j : ℕ) + ((i : ℕ) - 1) = m := by omega
  rw [hm, hm2, pow_succ]
  ring

/-! ## 余边界的加法与数乘线性 -/

/-- 余边界是加法同态。 -/
lemma coboundary_add {R : Type u} [CommRing R] {X : Type u} {n : ℕ}
    (c₁ c₂ : Cochain R X n) :
    coboundary (c₁ + c₂) = coboundary c₁ + coboundary c₂ := by
  funext σ
  show finSum R (n + 2) (fun i ↦ (-1:R)^(i:ℕ) * ((c₁ + c₂) (coFace σ i))) = _
  simp only [Pi.add_apply, mul_add]
  exact finSum_add R _ _ _

/-- 余边界是数乘同态。 -/
lemma coboundary_smul {R : Type u} [CommRing R] {X : Type u} {n : ℕ}
    (a : R) (c : Cochain R X n) :
    coboundary (a • c) = a • coboundary c := by
  funext σ
  show finSum R (n + 2) (fun i ↦ (-1:R)^(i:ℕ) * ((a • c) (coFace σ i))) = _
  simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm]
  exact finSum_mul_left R _ _ _

/-- 余边界的取负。 -/
lemma coboundary_neg {R : Type u} [CommRing R] {X : Type u} {n : ℕ}
    (c : Cochain R X n) :
    coboundary (-c) = -coboundary c := by
  have h : (-c : Cochain R X n) = (-1 : R) • c := by
    funext x; simp [neg_smul, one_smul]
  rw [h, coboundary_smul]
  simp [neg_smul, one_smul]

/-- 映射 `f : X → Y` 对上链的拉回。 -/
def cochainPullback {R : Type u} [CommRing R] {X Y : Type u} {n : ℕ}
    (h : X → Y) (c : Cochain R Y n) : Cochain R X n :=
  fun σ ↦ c (fun k ↦ h (σ k))

/-- **拉回自然性**：`∂(f⁎c) = f⁎(∂c)`。 -/
theorem coboundary_pullback {R : Type u} [CommRing R] {X Y : Type u} {n : ℕ}
    (h : X → Y) (c : Cochain R Y n) :
    coboundary (cochainPullback h c) = cochainPullback h (coboundary c) := by
  funext σ
  unfold coboundary cochainPullback
  rfl

end DeRham

/-! ## 上积（cup product）与分次 Leibniz 法则

上积是 de Rham 复形上链代数的乘法结构：
`(c₁ ∪ c₂)(σ₀,…,σ_{p+q}) = c₁(σ₀,…,σ_p) · c₂(σ_p,…,σ_{p+q})`。

分次 Leibniz：`∂(c₁ ∪ c₂) = ∂c₁ ∪ c₂ + (-1)^p c₁ ∪ ∂c₂`。 -/

section CupProduct

variable {R : Type u} [CommRing R] {X : Type u}

/-- 上积左嵌入：取前 `p+1` 个点。 -/
def cupLeft (p q : ℕ) : Fin (p + 1) → Fin (p + q + 1) :=
  fun k ↦ Fin.cast (by omega) (Fin.castAdd q k)

/-- 上积右嵌入：取后 `q+1` 个点。 -/
def cupRight (p q : ℕ) : Fin (q + 1) → Fin (p + q + 1) :=
  fun k ↦ Fin.cast (by omega) (Fin.natAdd p k)

/-- 上积：`(c₁ ∪ c₂)(σ₀,…,σ_{p+q}) = c₁(σ₀,…,σ_p) · c₂(σ_p,…,σ_{p+q})`。 -/
def cupProduct {p q : ℕ} (c₁ : Cochain R X p) (c₂ : Cochain R X q) :
    Cochain R X (p + q) :=
  fun σ ↦ c₁ (fun k : Fin (p + 1) ↦ σ (cupLeft p q k)) *
         c₂ (fun k : Fin (q + 1) ↦ σ (cupRight p q k))

lemma cupProduct_apply {p q : ℕ} (c₁ : Cochain R X p) (c₂ : Cochain R X q)
    (σ : SimplexPts X (p + q)) :
    cupProduct c₁ c₂ σ =
      c₁ (fun k : Fin (p + 1) ↦ σ (cupLeft p q k)) *
      c₂ (fun k : Fin (q + 1) ↦ σ (cupRight p q k)) := rfl

/-- 上积对第一个因子加法。 -/
lemma cup_add_left {p q : ℕ} (c₁ c₂ : Cochain R X p) (η : Cochain R X q) :
    cupProduct (c₁ + c₂) η = cupProduct c₁ η + cupProduct c₂ η := by
  funext σ
  unfold cupProduct
  simp only [Pi.add_apply]
  ring

/-- 上积对第二个因子加法。 -/
lemma cup_add_right {p q : ℕ} (c₁ : Cochain R X p) (η₁ η₂ : Cochain R X q) :
    cupProduct c₁ (η₁ + η₂) = cupProduct c₁ η₁ + cupProduct c₁ η₂ := by
  funext σ
  unfold cupProduct
  simp only [Pi.add_apply]
  ring

/-- 上积对第一个因子数乘。 -/
lemma cup_smul_left {p q : ℕ} (a : R) (c₁ : Cochain R X p) (η : Cochain R X q) :
    cupProduct (a • c₁) η = a • cupProduct c₁ η := by
  funext σ
  unfold cupProduct
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- 上积对第二个因子数乘。 -/
lemma cup_smul_right {p q : ℕ} (a : R) (c₁ : Cochain R X p) (η : Cochain R X q) :
    cupProduct c₁ (a • η) = a • cupProduct c₁ η := by
  funext σ
  unfold cupProduct
  simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm]

/-- 上积左零。 -/
lemma cup_zero_left {p q : ℕ} (η : Cochain R X q) :
    cupProduct (0 : Cochain R X p) η = 0 := by
  funext σ
  unfold cupProduct
  simp

/-- 上积右零。 -/
lemma cup_zero_right {p q : ℕ} (c₁ : Cochain R X p) :
    cupProduct c₁ (0 : Cochain R X q) = 0 := by
  funext σ
  unfold cupProduct
  simp

/- **分次 Leibniz 法则**：`∂(c₁ ∪ c₂) = ∂c₁ ∪ c₂ + (-1)^{p+1} c₁ ∪ ∂c₂`。

证明：展开 ∂ 的交错和，利用面复合恒等式将各项分为三组：
1. 内部面（同时在前 p+1 和后 q+1 中）——成对消去
2. 前 p+1 面——恰好组成 ∂c₁ ∪ c₂
3. 后 q+1 面——符号配对后组成 (-1)^{p+1} c₁ ∪ ∂c₂

当前 Lean 证明需要 `finSum` 重参数化的一般理论（任意相邻交换），
暂留为后续工作；0-形式情形（p=0）已由 `coboundary_d0` 间接覆盖。 -/
-- theorem coboundary_cup_product ... (deferred)

end CupProduct

/-! ## 余边界与 0-形式微分的相容性 -/

section CochainOfFun

variable {R : Type u} [CommRing R] {X : Type u}

/-- 将函数 `f : X → R` 嵌入为 0-上链。 -/
def cochainOfFun (f : X → R) : Cochain R X 0 :=
  fun σ ↦ f (σ 0)

/-- `finSum R 2` 的显式展开。 -/
lemma finSum_two (R : Type u) [AddCommMonoid R] (g : Fin 2 → R) :
    finSum R 2 g = g 0 + (g 1 + 0) := rfl

/-- **余边界在 0-上链上退化为 d₀**：`∂(cochainOfFun f) = d₀ f`。 -/
theorem coboundary_eq_d0 (f : X → R) (σ : SimplexPts X 1) :
    coboundary (cochainOfFun f) σ = d0 f σ := by
  unfold coboundary d0 coFace cochainOfFun
  rw [finSum_two]
  simp only [pow_zero, pow_one, add_zero]
  have h0 : (((0 : Fin 2).succAbove (0 : Fin 1) : Fin 2)) = 1 := by decide
  have h1 : (((1 : Fin 2).succAbove (0 : Fin 1) : Fin 2)) = 0 := by decide
  rw [h0, h1]
  have c0 : (((0 : Fin 2) : ℕ)) = 0 := rfl
  have c1 : (((1 : Fin 2) : ℕ)) = 1 := rfl
  rw [c0, c1]
  simp only [pow_zero, pow_one, add_zero]
  ring

/-- 0-上链的余边界满足 ∂² = 0。 -/
lemma coboundary_zero_of_cochainOfFun (f : X → R) (σ : SimplexPts X 2) :
    coboundary (coboundary (cochainOfFun f)) σ = 0 := by
  have h : coboundary (cochainOfFun f) = d0 f := by
    funext τ
    exact coboundary_eq_d0 f τ
  rw [h]
  exact coboundary_d0 f σ

/-- **常值函数的余边界为零**：∂c = 0 对常值函数 c。

这是 de Rham 复形中「常值函数是闭形式」的形式化。 -/
theorem coboundary_const {R : Type u} [CommRing R] {X : Type u}
    (c : R) :
    coboundary (cochainOfFun (fun _ : X ↦ c)) = 0 := by
  have h : coboundary (cochainOfFun (fun _ : X ↦ c)) = d0 (fun _ : X ↦ c) := by
    funext τ
    exact coboundary_eq_d0 (fun _ : X ↦ c) τ
  rw [h]
  funext σ
  unfold d0
  simp

end CochainOfFun

/-! ## 上积的单位律

注：`cupRight 0 q k = k` 和 `cupLeft 0 q 0 = 0` 在数学上成立，但
`0 + q` 和 `q` 在 Lean 4 中不是 syntactic 相等（需要 `Nat.zero_add`），
导致类型层面的不匹配。这些引理需要通过 `Fin.cast` 显式转换后证明，
留作后续工作。 -/

/-- **上积与拉回交换（函子性质）**：`h⁎(c₁ ∪ c₂) = h⁎c₁ ∪ h⁎c₂`。

由定义直接可得（`rfl`）：两边都计算为
`c₁(h ∘ σ ∘ cupLeft) · c₂(h ∘ σ ∘ cupRight)`。 -/
theorem cup_pullback {R : Type u} [CommRing R] {X Y : Type u} {p q : ℕ}
    (h : X → Y) (c₁ : Cochain R Y p) (c₂ : Cochain R Y q) :
    cochainPullback h (cupProduct c₁ c₂) =
    cupProduct (cochainPullback h c₁) (cochainPullback h c₂) := rfl

/-! ### 0-上链的上积：退化为逐点乘法 -/

section CupZeroZero

variable {R : Type u} [CommRing R] {X : Type u}

/-- `cupLeft 0 0` 是恒等嵌入。 -/
lemma cupLeft_00 : cupLeft 0 0 = id := by
  funext k
  unfold cupLeft
  simp

/-- `cupRight 0 0` 是恒等嵌入。 -/
lemma cupRight_00 : cupRight 0 0 = id := by
  funext k
  unfold cupRight
  simp

/-- 0-上链的上积是逐点乘法。 -/
lemma cupProduct_zero_zero (f g : Cochain R X 0) :
    cupProduct f g = fun σ ↦ f σ * g σ := by
  unfold cupProduct
  simp only [cupLeft_00, cupRight_00]
  rfl

end CupZeroZero

/-! ### 0-上链上积的代数性质 -/

section CupZeroAlgebra

variable {R : Type u} [CommRing R] {X : Type u}

/-- 0-上链的上积是交换的。 -/
lemma cupProduct_comm (f g : Cochain R X 0) :
    cupProduct f g = cupProduct g f := by
  rw [cupProduct_zero_zero, cupProduct_zero_zero]
  funext σ
  ring

end CupZeroAlgebra

/- **分次 Leibniz 对 0-上链**：`∂(f·g) = ∂f·g + f·∂g`。

这是 de Rham 复形作为微分分次代数（DG algebra）的基础。
数学证明：对于 0-上链，上积退化为逐点乘法（`cupProduct_zero_zero`），
展开 ∂f 和 ∂g 后 `ring` 关闭。完整 Lean 证明需要 cupProduct
与不同次数的 cupProduct 交互展开。 -/
-- theorem coboundary_mul_zero ... (deferred)

/-! ## d₀ 算子的导子性质 -/

/-- **d₀ 是逐点乘法的导子**：`d₀(f·g) = g·d₀f + f(σ₀)·d₀g`。

这是 de Rham 复形在 0-层面的 Leibniz 法则。 -/
theorem d0_mul {R : Type u} [CommRing R] {X : Type u}
    (f g : X → R) (σ : SimplexPts X 1) :
    d0 (fun x ↦ f x * g x) σ =
      g (σ 1) * d0 f σ + f (σ 0) * d0 g σ := by
  unfold d0
  ring

/-- **d₀ 消灭常值函数**：`d₀c = 0`。 -/
theorem d0_const {R : Type u} [CommRing R] {X : Type u}
    (c : R) :
    d0 (fun _ : X ↦ c) = 0 := by
  funext σ
  unfold d0
  simp only [Pi.zero_apply]
  ring

/-- **d₀ 的加法性**：`d₀(f+g) = d₀f + d₀g`。 -/
theorem d0_add {R : Type u} [CommRing R] {X : Type u}
    (f g : X → R) :
    d0 (fun x ↦ f x + g x) = d0 f + d0 g := by
  funext σ
  unfold d0
  simp only [Pi.add_apply]
  abel

/-- **d₀ 的数乘性**：`d₀(a·f) = a·d₀f`。 -/
theorem d0_smul {R : Type u} [CommRing R] {X : Type u}
    (a : R) (f : X → R) :
    d0 (fun x ↦ a * f x) = a • d0 f := by
  funext σ
  unfold d0
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-!
## 相邻对换的符号翻转（E2b）

`swapPerm a b`（`b = a + 1`）左复合任一置换使 sign 反号；推论：相邻对换自身
符号为 `-1`。证明依赖：`insertAt_eq_unshift_iff`、`unshift_insertAt`、`encode_toFun_self`、
`encode_compose_cons_ex`、Helper 1a/1b/2（`permRestr_swapFin_left/right/ne`）与
`unshift` 值公式。
-/

variable {R : Type u} [CommRing R]

section SignFlip

/-- `insertAt w k = x`（`x ≠ w`）当且仅当 `k = unshift w x`。 -/
lemma insertAt_eq_unshift_iff {n : ℕ} (w : Fin (n + 1)) {k : Fin n} {x : Fin (n + 1)}
    (hx : x ≠ w) : (FinPerm.insertAt w k = x) ↔ (k = FinPerm.unshift w x hx) := by
  constructor
  · intro hEq
    have hxval : (x : ℕ) = if (k : ℕ) < (w : ℕ) then (k : ℕ) else (k : ℕ) + 1 := by
      rw [← hEq, FinPerm.insertAt_val]
    by_cases hkw : (k : ℕ) < (w : ℕ)
    · have hx2 : (x : ℕ) = (k : ℕ) := by rw [hxval, if_pos hkw]
      have hx3 : ¬((w : ℕ) < (x : ℕ)) := by omega
      apply Fin.ext
      unfold FinPerm.unshift
      rw [dif_neg hx3]
      simp only [Fin.val_mk]
      omega
    · have hx2 : (x : ℕ) = (k : ℕ) + 1 := by rw [hxval, if_neg hkw]
      have hx3 : (w : ℕ) < (x : ℕ) := by omega
      apply Fin.ext
      unfold FinPerm.unshift
      rw [dif_pos hx3]
      simp only [Fin.val_mk]
      omega
  · intro hEq
    rw [hEq, FinPerm.insertAt_unshift]

/-- 删除第 `w` 个输入位置后压缩：`unshift w (insertAt w k) = k`。 -/
lemma unshift_insertAt {n : ℕ} (w : Fin (n + 1)) (k : Fin n) :
    FinPerm.unshift w (FinPerm.insertAt w k)
      (fun hc => FinPerm.insertAt_ne w k hc) = k := by
  unfold FinPerm.unshift
  have hin := FinPerm.insertAt_val w k
  by_cases hkw : (k : ℕ) < (w : ℕ)
  · have hval : (FinPerm.insertAt w k : ℕ) = (k : ℕ) := by rw [hin, if_pos hkw]
    have hcmp : ¬((w : ℕ) < (FinPerm.insertAt w k : ℕ)) := by rw [hval]; omega
    rw [dif_neg hcmp]
    exact Fin.ext hval
  · have hval : (FinPerm.insertAt w k : ℕ) = (k : ℕ) + 1 := by rw [hin, if_neg hkw]
    have hcmp : (w : ℕ) < (FinPerm.insertAt w k : ℕ) := by rw [hval]; omega
    rw [dif_pos hcmp]
    apply Fin.ext
    simp only [Fin.val_mk]
    omega

/-- encode σ.toFun = σ：提取型编码的还原。 -/
lemma encode_toFun_self {m : ℕ} (σ : FinPerm m) :
    FinPerm.encode (fun k : Fin m => σ.toFun k) σ.toFun_injective = σ := by
  apply FinPerm.ext_toFun _ _
  rw [FinPerm.toFun_encode]

/-- (D) 的显式 hΦ 变体：尾编码的单射性作为假设传入，
使重写实例完全确定（避免元变量证明参数阻断动机）。 -/
lemma encode_compose_cons_ex {n : ℕ} (σ : FinPerm n) (i : Fin (n + 1))
    (ρ : Fin (n + 1) → Fin (n + 1)) (hρ : Function.Injective ρ)
    (hΦ : Function.Injective fun k : Fin n => permRestr ρ hρ i (σ.toFun k)) :
    FinPerm.encode (fun k => ρ ((FinPerm.cons σ i).toFun k))
        (hρ.comp (FinPerm.cons σ i).toFun_injective)
      = FinPerm.cons (FinPerm.encode (fun k => permRestr ρ hρ i (σ.toFun k)) hΦ) (ρ i) := by
  apply FinPerm.ext_toFun _ _
  have hEnc := FinPerm.toFun_encode (fun k => ρ ((FinPerm.cons σ i).toFun k))
    (hρ.comp (FinPerm.cons σ i).toFun_injective)
  have hTail := FinPerm.toFun_encode (fun k => permRestr ρ hρ i (σ.toFun k)) hΦ
  funext j
  cases j using Fin.cases with
  | zero => simp only [hEnc, FinPerm.toFun_cons_zero]
  | succ k =>
      simp only [hEnc, FinPerm.toFun_cons_succ, hTail]
      simp only [permRestr, FinPerm.insertAt_unshift]

/-- Helper 1a：`w` 为对换的第一点时限制重排为恒等。 -/
lemma permRestr_swapFin_left {n : ℕ} (a b : Fin (n + 1)) (h : (a : ℕ) + 1 = (b : ℕ))
    (hinj : Function.Injective (swapFin a b)) :
    permRestr (swapFin a b) hinj a = id := by
  funext x
  rw [id_eq]
  unfold permRestr
  have hxlt := x.isLt
  have hins0 : (FinPerm.insertAt a x : ℕ) =
      if (x : ℕ) < (a : ℕ) then (x : ℕ) else (x : ℕ) + 1 := FinPerm.insertAt_val a x
  have hsw1 : (swapFin a b a : ℕ) = (b : ℕ) := by rw [swapFin_self_left]
  by_cases hxa : (x : ℕ) < (a : ℕ)
  · have hneB : FinPerm.insertAt a x ≠ b := by
      intro hc
      have hval := congrArg Fin.val hc
      rw [hins0, if_pos hxa] at hval
      have := hxlt
      have := h
      omega
    have hswx : (swapFin a b (FinPerm.insertAt a x) : ℕ) = (x : ℕ) := by
      rw [swapFin, if_neg (FinPerm.insertAt_ne a x), if_neg hneB, hins0, if_pos hxa]
    have hcmp : ¬((swapFin a b a : ℕ) < (swapFin a b (FinPerm.insertAt a x) : ℕ)) := by
      rw [hsw1, hswx]
      omega
    unfold FinPerm.unshift
    rw [dif_neg hcmp]
    apply Fin.ext
    simp only [Fin.val_mk, hswx]
  · by_cases hxa2 : (x : ℕ) = (a : ℕ)
    · have hinsB : FinPerm.insertAt a x = b := by
        apply Fin.ext
        rw [hins0, if_neg hxa, hxa2, h]
      have hswx : (swapFin a b (FinPerm.insertAt a x) : ℕ) = (a : ℕ) := by
        rw [hinsB, swapFin_self_right]
      have hcmp : ¬((swapFin a b a : ℕ) < (swapFin a b (FinPerm.insertAt a x) : ℕ)) := by
        rw [hsw1, hswx, ← h]
        omega
      unfold FinPerm.unshift
      rw [dif_neg hcmp]
      apply Fin.ext
      simp only [Fin.val_mk, hswx, hxa2]
    · have hneA : FinPerm.insertAt a x ≠ a := by
        intro hc
        have hval := congrArg Fin.val hc
        rw [hins0, if_neg hxa] at hval
        have := hxlt
        have := h
        omega
      have hneB : FinPerm.insertAt a x ≠ b := by
        intro hc
        have hval := congrArg Fin.val hc
        rw [hins0, if_neg hxa] at hval
        rw [← h] at hval
        have := hxlt
        omega
      have hswx : (swapFin a b (FinPerm.insertAt a x) : ℕ) = (x : ℕ) + 1 := by
        rw [swapFin, if_neg hneA, if_neg hneB, hins0, if_neg hxa]
      have hcmp : (swapFin a b a : ℕ) < (swapFin a b (FinPerm.insertAt a x) : ℕ) := by
        rw [hsw1, hswx, ← h]
        have := a.isLt
        omega
      unfold FinPerm.unshift
      rw [dif_pos hcmp]
      apply Fin.ext
      simp only [Fin.val_mk, hswx]
      omega

/-- Helper 1b：`w` 为对换的第二点时限制重排为恒等。 -/
lemma permRestr_swapFin_right {n : ℕ} (a b : Fin (n + 1)) (h : (a : ℕ) + 1 = (b : ℕ))
    (hinj : Function.Injective (swapFin a b)) :
    permRestr (swapFin a b) hinj b = id := by
  funext x
  rw [id_eq]
  unfold permRestr
  have hxlt := x.isLt
  have hins0 : (FinPerm.insertAt b x : ℕ) =
      if (x : ℕ) < (b : ℕ) then (x : ℕ) else (x : ℕ) + 1 := FinPerm.insertAt_val b x
  have hsw1 : (swapFin a b b : ℕ) = (a : ℕ) := by rw [swapFin_self_right]
  by_cases hxb : (x : ℕ) < (b : ℕ)
  · by_cases hxa : (x : ℕ) = (a : ℕ)
    · have hinsA : FinPerm.insertAt b x = a := by
        apply Fin.ext
        rw [hins0, if_pos hxb, hxa]
      have hswx : (swapFin a b (FinPerm.insertAt b x) : ℕ) = (b : ℕ) := by
        rw [hinsA, swapFin_self_left]
      have hcmp : (swapFin a b b : ℕ) < (swapFin a b (FinPerm.insertAt b x) : ℕ) := by
        rw [hsw1, hswx]
        omega
      unfold FinPerm.unshift
      rw [dif_pos hcmp]
      apply Fin.ext
      simp only [Fin.val_mk, hswx]
      omega
    · have hneA : FinPerm.insertAt b x ≠ a := by
        intro hc
        have hval := congrArg Fin.val hc
        rw [hins0, if_pos hxb] at hval
        have := hxlt
        have := h
        omega
      have hswx : (swapFin a b (FinPerm.insertAt b x) : ℕ) = (x : ℕ) := by
        rw [swapFin, if_neg (FinPerm.insertAt_ne b x), if_neg hneA, hins0, if_pos hxb]
      have hcmp : ¬((swapFin a b b : ℕ) < (swapFin a b (FinPerm.insertAt b x) : ℕ)) := by
        rw [hsw1, hswx]
        have := h
        omega
      unfold FinPerm.unshift
      rw [dif_neg hcmp]
      apply Fin.ext
      simp only [Fin.val_mk, hswx]
  · have hneA : FinPerm.insertAt b x ≠ a := by
      intro hc
      have hval := congrArg Fin.val hc
      rw [hins0, if_neg hxb] at hval
      have := hxlt
      have := h
      omega
    have hneB : FinPerm.insertAt b x ≠ b := by
      intro hc
      have hval := congrArg Fin.val hc
      rw [hins0, if_neg hxb] at hval
      have := hxlt
      omega
    have hswx : (swapFin a b (FinPerm.insertAt b x) : ℕ) = (x : ℕ) + 1 := by
      rw [swapFin, if_neg hneA, if_neg hneB, hins0, if_neg hxb]
    have hcmp : (swapFin a b b : ℕ) < (swapFin a b (FinPerm.insertAt b x) : ℕ) := by
      rw [hsw1, hswx]
      have := hxlt
      omega
    unfold FinPerm.unshift
    rw [dif_pos hcmp]
    apply Fin.ext
    simp only [Fin.val_mk, hswx]
    omega

/-- unshift 的值计算：无嵌套 Fin 项参与，供 omega 直接使用。 -/
lemma unshift_val_eq {n : ℕ} (i x : Fin (n + 1)) (hx : x ≠ i) :
    (FinPerm.unshift i x hx : ℕ)
      = if (i : ℕ) < (x : ℕ) then (x : ℕ) - 1 else (x : ℕ) := by
  unfold FinPerm.unshift
  split <;> simp only [Fin.val_mk] <;> omega

/-- `unshift` 的值公式（小于分支）：`i < w` 时压缩为 `w - 1`。 -/
lemma FinPerm.unshift_val_lt {n : ℕ} (i w : Fin (n + 1)) (hw : w ≠ i)
    (hlt : (i : ℕ) < (w : ℕ)) : ((FinPerm.unshift i w hw : Fin n) : ℕ) = (w : ℕ) - 1 := by
  rw [FinPerm.unshift, dif_pos hlt]

/-- `unshift` 的值公式（不小于分支）：`¬ i < w` 时压缩为 `w`。 -/
lemma FinPerm.unshift_val_ge {n : ℕ} (i w : Fin (n + 1)) (hw : w ≠ i)
    (hge : ¬((i : ℕ) < (w : ℕ))) : ((FinPerm.unshift i w hw : Fin n) : ℕ) = (w : ℕ) := by
  rw [FinPerm.unshift, dif_neg hge]

/-- Helper 2：`w` 不为对换两点时限制重排为压缩后的相邻对换。 -/
lemma permRestr_swapFin_ne {n : ℕ} (a b w : Fin (n + 1)) (h : (a : ℕ) + 1 = (b : ℕ))
    (hinj : Function.Injective (swapFin a b)) (hwa : w ≠ a) (hwb : w ≠ b) :
    permRestr (swapFin a b) hinj w
      = swapFin (FinPerm.unshift w a (Ne.symm hwa)) (FinPerm.unshift w b (Ne.symm hwb)) := by
  funext k
  unfold permRestr
  apply Fin.ext
  have ha' := (FinPerm.unshift w a (Ne.symm hwa)).isLt
  have hkw := k.isLt
  have hw := w.isLt
  have hpair : (FinPerm.unshift w a (Ne.symm hwa) : ℕ) + 1 = (FinPerm.unshift w b (Ne.symm hwb) : ℕ) := by
    unfold FinPerm.unshift
    split <;> split <;> simp only [Fin.val_mk] <;> omega
  have hinsa : FinPerm.insertAt w (FinPerm.unshift w a (Ne.symm hwa)) = a :=
    FinPerm.insertAt_unshift w a (Ne.symm hwa)
  have hinsb : FinPerm.insertAt w (FinPerm.unshift w b (Ne.symm hwb)) = b :=
    FinPerm.insertAt_unshift w b (Ne.symm hwb)
  have hvw2 : swapFin a b w = w := swapFin_of_ne hwa hwb
  have hvw2v : (swapFin a b w : ℕ) = (w : ℕ) := congrArg Fin.val hvw2
  have hval : (swapFin a b (FinPerm.insertAt w k) : ℕ)
      = (FinPerm.insertAt w (swapFin (FinPerm.unshift w a (Ne.symm hwa))
          (FinPerm.unshift w b (Ne.symm hwb)) k) : ℕ) := by
    rw [swapFin]
    by_cases hEq1 : FinPerm.insertAt w k = a
    · have hk : k = FinPerm.unshift w a (Ne.symm hwa) :=
        (insertAt_eq_unshift_iff w (Ne.symm hwa)).mp hEq1
      rw [if_pos hEq1, hk, swapFin_self_left, hinsb]
    · by_cases hEq2 : FinPerm.insertAt w k = b
      · have hk : k = FinPerm.unshift w b (Ne.symm hwb) :=
          (insertAt_eq_unshift_iff w (Ne.symm hwb)).mp hEq2
        rw [if_neg hEq1, if_pos hEq2, hk, swapFin_self_right, hinsa]
      · have hk1 : k ≠ FinPerm.unshift w a (Ne.symm hwa) := by
          intro hc
          rw [hc, hinsa] at hEq1
          exact hEq1 rfl
        have hk2 : k ≠ FinPerm.unshift w b (Ne.symm hwb) := by
          intro hc
          rw [hc, hinsb] at hEq2
          exact hEq2 rfl
        rw [if_neg hEq1, if_neg hEq2, swapFin_of_ne hk1 hk2]
  have hYins : (FinPerm.insertAt w (swapFin (FinPerm.unshift w a (Ne.symm hwa))
      (FinPerm.unshift w b (Ne.symm hwb)) k) : ℕ)
      = if (swapFin (FinPerm.unshift w a (Ne.symm hwa))
          (FinPerm.unshift w b (Ne.symm hwb)) k : ℕ) < (w : ℕ)
        then (swapFin (FinPerm.unshift w a (Ne.symm hwa))
          (FinPerm.unshift w b (Ne.symm hwb)) k : ℕ)
        else (swapFin (FinPerm.unshift w a (Ne.symm hwa))
          (FinPerm.unshift w b (Ne.symm hwb)) k : ℕ) + 1 :=
    FinPerm.insertAt_val w (swapFin (FinPerm.unshift w a (Ne.symm hwa))
      (FinPerm.unshift w b (Ne.symm hwb)) k)
  -- 主目标保持 unshift 不透明；左右两侧的值分别用值公式与 hval/hYins 化为同一组原子。
  by_cases hWX : (w : ℕ) < (swapFin a b (FinPerm.insertAt w k) : ℕ)
  · have hWX' : (swapFin a b w : ℕ) < (swapFin a b (FinPerm.insertAt w k) : ℕ) := by
      rw [hvw2v]
      exact hWX
    rw [FinPerm.unshift_val_lt _ _ _ hWX']
    by_cases hCX : (swapFin (FinPerm.unshift w a (Ne.symm hwa))
        (FinPerm.unshift w b (Ne.symm hwb)) k : ℕ) < (w : ℕ)
    · have hXe : (swapFin a b (FinPerm.insertAt w k) : ℕ)
          = (swapFin (FinPerm.unshift w a (Ne.symm hwa))
            (FinPerm.unshift w b (Ne.symm hwb)) k : ℕ) := by
        rw [hval, hYins, if_pos hCX]
      omega
    · have hXe : (swapFin a b (FinPerm.insertAt w k) : ℕ)
          = (swapFin (FinPerm.unshift w a (Ne.symm hwa))
            (FinPerm.unshift w b (Ne.symm hwb)) k : ℕ) + 1 := by
        rw [hval, hYins, if_neg hCX]
      omega
  · have hWX' : ¬((swapFin a b w : ℕ) < (swapFin a b (FinPerm.insertAt w k) : ℕ)) := by
      intro hc
      rw [hvw2v] at hc
      exact hWX hc
    rw [FinPerm.unshift_val_ge _ _ _ hWX']
    by_cases hCX : (swapFin (FinPerm.unshift w a (Ne.symm hwa))
        (FinPerm.unshift w b (Ne.symm hwb)) k : ℕ) < (w : ℕ)
    · have hXe : (swapFin a b (FinPerm.insertAt w k) : ℕ)
          = (swapFin (FinPerm.unshift w a (Ne.symm hwa))
            (FinPerm.unshift w b (Ne.symm hwb)) k : ℕ) := by
        rw [hval, hYins, if_pos hCX]
      exact hXe
    · have hXe : (swapFin a b (FinPerm.insertAt w k) : ℕ)
          = (swapFin (FinPerm.unshift w a (Ne.symm hwa))
            (FinPerm.unshift w b (Ne.symm hwb)) k : ℕ) + 1 := by
        rw [hval, hYins, if_neg hCX]
      omega

/-- **相邻对换的符号翻转**：左复合相邻对换 `swapPerm a b`（`b = a+1`）
使 sign 反号（对 π 的树结构归纳）。

情形分析：`w = a` 或 `w = b` 时，限制重排退化为恒等而头值恰好互换；
否则限制重排是压缩后的相邻对换 `swapFin a' b'（`a' = unshift w a`，
`b' = unshift w b`，仍有 `b' = a'+1`），交给归纳假设。 -/
lemma sign_compose_swapPerm_adj : ∀ {m : ℕ} (π : FinPerm m),
    ∀ (a b : Fin m), (a : ℕ) + 1 = (b : ℕ) →
    FinPerm.sign R (FinPerm.compose (FinPerm.swapPerm a b) π) = -FinPerm.sign R π := by
  intro m π
  induction π with
  | nil =>
      intro a b h
      exfalso
      have := a.isLt
      have := b.isLt
      omega
  | cons σ w ih =>
      intro a b h
      have hsFun : (FinPerm.swapPerm a b).toFun = swapFin a b := FinPerm.toFun_swapPerm _ _
      have hinj : Function.Injective (swapFin a b) := swapFin_injective _ _
      have hcomp : FinPerm.compose (FinPerm.swapPerm a b) (FinPerm.cons σ w)
          = FinPerm.encode (fun k => swapFin a b ((FinPerm.cons σ w).toFun k))
              (hinj.comp (FinPerm.cons σ w).toFun_injective) := by
        apply FinPerm.ext_toFun _ _
        rw [FinPerm.toFun_compose, FinPerm.toFun_encode, hsFun]
      have hΦinst : Function.Injective fun k =>
          permRestr (swapFin a b) hinj w (σ.toFun k) :=
        Function.Injective.comp (permRestr_injective (swapFin a b) hinj w)
          σ.toFun_injective
      rw [hcomp]
      by_cases hj0 : (w : ℕ) = (a : ℕ)
      · -- w = a：限制重排为恒等，头值 b
        have hw : w = a := Fin.ext hj0
        have hcons : FinPerm.encode (fun k => swapFin a b ((FinPerm.cons σ w).toFun k))
            (hinj.comp (FinPerm.cons σ w).toFun_injective)
            = FinPerm.cons (FinPerm.encode (fun k => σ.toFun k)
              σ.toFun_injective) (swapFin a b w) := by
          rw [encode_compose_cons_ex σ w (swapFin a b) hinj hΦinst]
          apply congrArg (fun X => FinPerm.cons X (swapFin a b w))
          apply FinPerm.ext_toFun _ _
          rw [FinPerm.toFun_encode, FinPerm.toFun_encode]
          funext k
          rw [hw, permRestr_swapFin_left a b h hinj, id_eq]
        have hvw : (swapFin a b w : ℕ) = (b : ℕ) := by
          rw [hw, swapFin_self_left]
        rw [hcons, encode_toFun_self, FinPerm.sign_cons, hvw, FinPerm.sign_cons, hw,
          ← h, pow_succ]
        ring
      · by_cases hj1 : (w : ℕ) = (b : ℕ)
        · -- w = b：限制重排为恒等，头值 a
          have hw : w = b := Fin.ext hj1
          have hcons : FinPerm.encode (fun k => swapFin a b ((FinPerm.cons σ w).toFun k))
              (hinj.comp (FinPerm.cons σ w).toFun_injective)
              = FinPerm.cons (FinPerm.encode (fun k => σ.toFun k)
                σ.toFun_injective) (swapFin a b w) := by
            rw [encode_compose_cons_ex σ w (swapFin a b) hinj hΦinst]
            apply congrArg (fun X => FinPerm.cons X (swapFin a b w))
            apply FinPerm.ext_toFun _ _
            rw [FinPerm.toFun_encode, FinPerm.toFun_encode]
            funext k
            rw [hw, permRestr_swapFin_right a b h hinj, id_eq]
          have hvw : (swapFin a b w : ℕ) = (a : ℕ) := by
            rw [hw, swapFin_self_right]
          rw [hcons, encode_toFun_self, FinPerm.sign_cons, hvw, FinPerm.sign_cons, hw,
            ← h, pow_succ]
          ring
        · -- 一般情形：限制重排 = 压缩后的相邻对换，交给归纳假设
          have hjw : a ≠ w := fun hc => hj0 (congrArg Fin.val hc).symm
          have hjw' : b ≠ w := fun hc => hj1 (congrArg Fin.val hc).symm
          have ha'val : ((FinPerm.unshift w a hjw) : ℕ) + 1
              = ((FinPerm.unshift w b hjw') : ℕ) := by
            unfold FinPerm.unshift
            by_cases h1 : (w : ℕ) < (a : ℕ)
            · rw [dif_pos h1, dif_pos (by have := h; omega)]
              simp only [Fin.val_mk]
              have := a.isLt
              omega
            · by_cases h2 : (w : ℕ) < (b : ℕ)
              · rw [dif_neg h1, dif_pos h2]
                simp only [Fin.val_mk]
                have := a.isLt
                have := h
                omega
              · rw [dif_neg h1, dif_neg h2]
                simp only [Fin.val_mk]
                exact h
          have hcons : FinPerm.encode (fun k => swapFin a b ((FinPerm.cons σ w).toFun k))
              (hinj.comp (FinPerm.cons σ w).toFun_injective)
              = FinPerm.cons (FinPerm.encode (fun k =>
                  swapFin (FinPerm.unshift w a hjw)
                  (FinPerm.unshift w b hjw') (σ.toFun k))
                (Function.Injective.comp (swapFin_injective (FinPerm.unshift w a hjw)
                  (FinPerm.unshift w b hjw')) σ.toFun_injective)) (swapFin a b w) := by
            rw [encode_compose_cons_ex σ w (swapFin a b) hinj hΦinst]
            apply congrArg (fun X => FinPerm.cons X (swapFin a b w))
            apply FinPerm.ext_toFun _ _
            rw [FinPerm.toFun_encode, FinPerm.toFun_encode]
            funext k
            exact congrFun (permRestr_swapFin_ne a b w h hinj (Ne.symm hjw)
              (Ne.symm hjw')) (σ.toFun k)
          have hEnc : FinPerm.encode (fun k => swapFin (FinPerm.unshift w a hjw)
                (FinPerm.unshift w b hjw') (σ.toFun k))
              (Function.Injective.comp (swapFin_injective (FinPerm.unshift w a hjw)
                (FinPerm.unshift w b hjw')) σ.toFun_injective)
              = FinPerm.compose (FinPerm.swapPerm (FinPerm.unshift w a hjw)
                (FinPerm.unshift w b hjw')) σ := by
            apply FinPerm.ext_toFun _ _
            rw [FinPerm.toFun_compose, FinPerm.toFun_swapPerm, FinPerm.toFun_encode]
          have hvw : (swapFin a b w : ℕ) = (w : ℕ) := by
            rw [swapFin_of_ne (Ne.symm hjw) (Ne.symm hjw')]
          rw [hcons, FinPerm.sign_cons, hvw, hEnc,
            ih (FinPerm.unshift w a hjw) (FinPerm.unshift w b hjw') ha'val,
            FinPerm.sign_cons]
          ring

/-- 恒等置换的符号为 `1`（对 n 归纳：identity 在后继层显式拆出
`cons (encode (fun k ↦ unshift 0 (succ k)) _) 0`，尾部编码的 toFun 逐点等于 id）。 -/
lemma FinPerm.sign_identity (R : Type u) [CommRing R] :
    ∀ (n : ℕ), FinPerm.sign R (FinPerm.identity : FinPerm n) = 1 := by
  intro n
  induction n with
  | zero => exact FinPerm.sign_nil R
  | succ n ih =>
      have hinj : Function.Injective fun k : Fin n ↦ FinPerm.unshift 0 (Fin.succ k)
          (Fin.succ_ne_zero k) := by
        intro k₁ k₂ hEq2
        exact Fin.succ_injective n
          (FinPerm.unshift_injective 0 (Fin.succ_ne_zero k₁) (Fin.succ_ne_zero k₂) hEq2)
      show FinPerm.sign R (FinPerm.cons (FinPerm.encode
            (fun k : Fin n ↦ FinPerm.unshift 0 (Fin.succ k) (Fin.succ_ne_zero k)) hinj)
          (0 : Fin (n + 1))) = 1
      rw [FinPerm.sign_cons_zero]
      have hEq : (FinPerm.encode (fun k : Fin n ↦ FinPerm.unshift 0 (Fin.succ k)
              (Fin.succ_ne_zero k)) hinj)
          = (FinPerm.identity : FinPerm n) := by
        apply FinPerm.ext_toFun _ _
        rw [FinPerm.toFun_encode, FinPerm.toFun_identity]
        funext k
        have hlt : ((0 : Fin (n + 1)) : ℕ) < (Fin.succ k : ℕ) := by
          show (0 : ℕ) < (k : ℕ) + 1
          omega
        rw [FinPerm.unshift, dif_pos hlt, id_eq]
        exact Fin.ext (by
          have hv : ((Fin.succ k : Fin (n + 1)) : ℕ) = (k : ℕ) + 1 := rfl
          simp only [hv, Fin.val_mk]
          omega)
      rw [hEq]
      exact ih

/-- 相邻对换自身的符号为 `-1`（与恒等置换复合后用翻转引理）。 -/
lemma sign_swapPerm_adj {m : ℕ} {a b : Fin m} (h : (a : ℕ) + 1 = (b : ℕ)) :
    FinPerm.sign R (FinPerm.swapPerm a b) = -1 := by
  have h1 := sign_compose_swapPerm_adj (R := R) (FinPerm.identity : FinPerm m) a b h
  rw [FinPerm.compose_identity_right, FinPerm.sign_identity R] at h1
  exact h1

end SignFlip

section WedgeAdjacent

variable {R : Type u} [CommRing R] {X : Type u} [Microlinear R X]

/-- **相邻反交换**：把第 `a`、`a+1 = b` 两个输入槽位对调（经相邻对换
`swapPerm a b` 作用于参数向量），`(p,q)` 楔积展开函数反号。

证明：点态恒等式 `sign π * W'(π) = -u(compose s π)`（FLIP 翻转符号、
`toFun_compose` 吸收对换），再经 `permSum_mul_left` 提出 `-1`、
`permSum_reindex_compose`（(P) 重排）吸收 `s∘s = id`。 -/
lemma wedgeAnyFun_swap_adj {p q : ℕ} {x : X}
    (ω : TangentFiber R X x [⋀^Fin p]→ₗ[R] R)
    (η : TangentFiber R X x [⋀^Fin q]→ₗ[R] R)
    (a b : Fin (p + q)) (h : (a : ℕ) + 1 = (b : ℕ))
    (v : Fin (p + q) → TangentFiber R X x) :
    wedgeAnyFun ω η (fun t => v ((FinPerm.swapPerm a b).toFun t))
      = -wedgeAnyFun ω η v := by
  unfold wedgeAnyFun
  have hpoint : ∀ π : FinPerm (p + q),
      FinPerm.sign R π * (ω (fun i : Fin p =>
          v ((FinPerm.swapPerm a b).toFun (π.toFun (Fin.castAdd q i)))) *
        η (fun j : Fin q =>
          v ((FinPerm.swapPerm a b).toFun (π.toFun (Fin.natAdd p j)))))
      = (-1 : R) * (FinPerm.sign R (FinPerm.compose (FinPerm.swapPerm a b) π) *
        (ω (fun i : Fin p =>
          v ((FinPerm.compose (FinPerm.swapPerm a b) π).toFun (Fin.castAdd q i))) *
        η (fun j : Fin q =>
          v ((FinPerm.compose (FinPerm.swapPerm a b) π).toFun (Fin.natAdd p j))))) := by
    intro π
    rw [FinPerm.toFun_compose, sign_compose_swapPerm_adj π a b h]
    simp only [Function.comp_apply]
    ring
  rw [permSum_congr hpoint, permSum_mul_left,
    permSum_reindex_compose (p + q) (FinPerm.swapPerm a b)
      (fun π' : FinPerm (p + q) => FinPerm.sign R π' *
        (ω (fun i : Fin p => v (π'.toFun (Fin.castAdd q i))) *
        η (fun j : Fin q => v (π'.toFun (Fin.natAdd p j)))))]
  ring

end WedgeAdjacent

/-! ### 任意对换的反号与等值消零（冒泡分解）

任意两槽对换经「三重相邻对换恒等式 `(a b) = (a c)∘(c b)∘(a c)`」冒泡分解；
两个输入槽位相等时展开函数等于自身取负，2 可逆下即为零——这是打包为
`AlternatingMap` 所需的 `map_eq_zero_of_eq'` 字段。 -/

section WedgeAlternating

variable {R : Type u} [CommRing R] {X : Type u} [Microlinear R X]

/-- 三重相邻对换恒等式（向量槽位冒泡分解）：`(a b) = (a c)∘(c b)∘(a c)`，
其中 `c = a + 1 < b`。 -/
lemma swapFin_triple {n : ℕ} {a b : Fin n} {c : Fin n}
    (hac : (a : ℕ) + 1 = (c : ℕ)) (hlt : (c : ℕ) < (b : ℕ)) :
    swapFin a b = (swapFin a c) ∘ ((swapFin c b) ∘ (swapFin a c)) := by
  funext t
  simp only [Function.comp_apply]
  have hca : (a : ℕ) ≠ (c : ℕ) := by omega
  have hcb : (c : ℕ) ≠ (b : ℕ) := by omega
  have hab : (a : ℕ) ≠ (b : ℕ) := by omega
  by_cases h1 : t = a
  · rw [h1, swapFin_self_left, swapFin_self_left, swapFin_self_left,
      swapFin_of_ne (fun hc => hab (congrArg Fin.val hc).symm)
        (fun hc => hcb (congrArg Fin.val hc).symm)]
  · by_cases h2 : t = b
    · rw [h2, swapFin_self_right,
        swapFin_of_ne (fun hc => hab (congrArg Fin.val hc).symm)
          (fun hc => hcb (congrArg Fin.val hc).symm),
        swapFin_self_right, swapFin_self_right]
    · by_cases h3 : t = c
      · rw [h3, swapFin_of_ne (fun hc => hca (congrArg Fin.val hc).symm)
          (fun hc => hcb (congrArg Fin.val hc)),
          swapFin_self_right,
          swapFin_of_ne (fun hc => hca (congrArg Fin.val hc))
            (fun hc => hab (congrArg Fin.val hc)),
          swapFin_self_left]
      · rw [swapFin_of_ne h1 h2, swapFin_of_ne h1 h3, swapFin_of_ne h3 h2,
          swapFin_of_ne h1 h3]

/-- 冒泡引理：相距 `d + 1` 的两槽对换使 `(p,q)` 楔积展开函数反号
（对距离 `d` 归纳）。 -/
lemma wedgeAnyFun_swap_flip_aux {p q : ℕ} {x : X}
    (ω : TangentFiber R X x [⋀^Fin p]→ₗ[R] R)
    (η : TangentFiber R X x [⋀^Fin q]→ₗ[R] R) :
    ∀ (d : ℕ) (a b : Fin (p + q)) (u : Fin (p + q) → TangentFiber R X x),
      (b : ℕ) = (a : ℕ) + d + 1 →
      wedgeAnyFun ω η (fun t => u ((FinPerm.swapPerm a b).toFun t))
        = -wedgeAnyFun ω η u := by
  intro d
  induction d with
  | zero =>
      intro a b u hb
      exact wedgeAnyFun_swap_adj ω η a b (by omega) u
  | succ d ih =>
      intro a b u hb
      have hb2 : (b : ℕ) = (a : ℕ) + d + 2 := hb
      obtain ⟨c, hcval⟩ : ∃ c : Fin (p + q), (c : ℕ) = (a : ℕ) + 1 :=
        ⟨⟨_, by have := b.isLt; omega⟩, rfl⟩
      have hac : (a : ℕ) + 1 = (c : ℕ) := hcval.symm
      have hlt : (c : ℕ) < (b : ℕ) := by omega
      have hid : (fun t => u ((FinPerm.swapPerm a b).toFun t))
          = (fun t => (fun t' => u ((FinPerm.swapPerm a c).toFun
              ((FinPerm.swapPerm c b).toFun t')))
            ((FinPerm.swapPerm a c).toFun t)) := by
        funext t
        rw [FinPerm.toFun_swapPerm, FinPerm.toFun_swapPerm, FinPerm.toFun_swapPerm,
          swapFin_triple hac hlt]
        simp only [Function.comp_apply]
      rw [hid, wedgeAnyFun_swap_adj ω η a c hac
        (fun t' => u ((FinPerm.swapPerm a c).toFun ((FinPerm.swapPerm c b).toFun t'))),
        ih c b (fun t' => u ((FinPerm.swapPerm a c).toFun t')) (by omega),
        neg_neg, wedgeAnyFun_swap_adj ω η a c hac u]

/-- **任意对换反号**：交换任意两个输入槽位使 `(p,q)` 楔积展开函数反号。 -/
lemma wedgeAnyFun_swap_ne {p q : ℕ} {x : X}
    (ω : TangentFiber R X x [⋀^Fin p]→ₗ[R] R)
    (η : TangentFiber R X x [⋀^Fin q]→ₗ[R] R)
    {a b : Fin (p + q)} (hne : a ≠ b)
    (v : Fin (p + q) → TangentFiber R X x) :
    wedgeAnyFun ω η (fun t => v ((FinPerm.swapPerm a b).toFun t))
      = -wedgeAnyFun ω η v := by
  have habn : (a : ℕ) ≠ (b : ℕ) := fun hc => hne (Fin.ext hc)
  by_cases hlt : (a : ℕ) < (b : ℕ)
  · exact wedgeAnyFun_swap_flip_aux ω η (b - a - 1) a b v (by omega)
  · have h1 := wedgeAnyFun_swap_flip_aux ω η (a - b - 1) b a v (by omega)
    rw [show (fun t => v ((FinPerm.swapPerm a b).toFun t))
        = (fun t => v ((FinPerm.swapPerm b a).toFun t)) from by
        funext t
        rw [FinPerm.toFun_swapPerm, FinPerm.toFun_swapPerm, FinPerm.swapFin_comm]]
    rw [h1]

/-- **等值消零**：两个输入槽位相等的向量在 `(p,q)` 楔积展开函数下为零
（需 2 可逆，此假设将随打包以 `Invertible`-式参数进入 `AlternatingMap`）。

证明：等值向量经对换不变（`habs`），故 `S = -S`（任意对换反号），
`2` 可逆消去即得。 -/
lemma wedgeAnyFun_eq_zero_of_eq {p q : ℕ} {x : X}
    (ω : TangentFiber R X x [⋀^Fin p]→ₗ[R] R)
    (η : TangentFiber R X x [⋀^Fin q]→ₗ[R] R)
    (h2 : ∃ y : R, y * 2 = 1)
    {a b : Fin (p + q)} (hne : a ≠ b)
    (v : Fin (p + q) → TangentFiber R X x) (h : v a = v b) :
    wedgeAnyFun ω η v = 0 := by
  have habs : (fun t => v ((FinPerm.swapPerm a b).toFun t)) = v := by
    funext t
    by_cases h1 : t = a
    · rw [h1, FinPerm.toFun_swapPerm, swapFin_self_left, h]
    · by_cases h2c : t = b
      · rw [h2c, FinPerm.toFun_swapPerm, swapFin_self_right, h]
      · rw [FinPerm.toFun_swapPerm, swapFin_of_ne h1 h2c]
  obtain ⟨y, hy2⟩ := h2
  have hneg : wedgeAnyFun ω η v = -wedgeAnyFun ω η v := by
    calc wedgeAnyFun ω η v
        = wedgeAnyFun ω η (fun t => v ((FinPerm.swapPerm a b).toFun t)) := by rw [habs]
      _ = -wedgeAnyFun ω η v := wedgeAnyFun_swap_ne ω η hne v
  have hsum : wedgeAnyFun ω η v + wedgeAnyFun ω η v = 0 := by
    nth_rewrite 1 [hneg]
    rw [neg_add_cancel]
  have h4 : (1 : R) * wedgeAnyFun ω η v = 0 := by
    rw [← hy2, mul_assoc, two_mul, hsum, mul_zero]
  exact Eq.trans (one_mul _).symm h4

end WedgeAlternating

/-! ### `(p,q)` 楔积的打包（AlternatingMap）

槽位 update 引理的关键：更新槽 `i` 在置换 `π` 下的预像（`FinPerm.preimage`，
构造性、无选择公理）以 `↑(preimage π i) < p` 与否决定落入 ω 块或 η 块
（两块像集不交且覆盖全 `Fin (p+q)`），块向量经
`update_comp_of_preimage` / `update_comp_of_not_mem` 分解后由 ω/η 的
槽线性（Mathlib `MultilinearMap.map_update_add/smul`，无选择）承担。 -/

section WedgeAnyPack

variable {R : Type u} [CommRing R] {X : Type u} [Microlinear R X]

/-- 置换作用的构造性原像：对 `cons σ i`，`i` 的原像是 `0`，其余 `t` 的
原像是 `σ` 对 `unshift i t` 的原像的后继。 -/
def FinPerm.preimage : {n : ℕ} → FinPerm n → Fin n → Fin n
  | 0, .nil, j => j
  | n + 1, .cons σ i, t =>
      if h : t = i then 0 else (preimage σ (FinPerm.unshift i t h)).succ

lemma FinPerm.preimage_apply : ∀ {n : ℕ} (π : FinPerm n) (i : Fin n),
    π.toFun (preimage π i) = i := by
  intro n
  induction n with
  | zero =>
      intro π i
      cases π with
      | nil => exact FinPerm.toFun_nil i
  | succ n ih =>
      intro π i
      cases π with
      | cons σ j =>
          show (FinPerm.cons σ j).toFun
            (if h : i = j then 0
              else (preimage σ (FinPerm.unshift j i h)).succ) = i
          by_cases h : i = j
          · rw [dif_pos h, FinPerm.toFun_cons_zero]
            exact h.symm
          · rw [dif_neg h, FinPerm.toFun_cons_succ,
              ih σ (FinPerm.unshift j i h), FinPerm.insertAt_unshift]

/-- 复合向量的槽更新分解（预像在块内）：更新经单射 `f` 的预像 `m`
恰好落入块向量 `v ∘ f` 的第 `m` 槽。 -/
lemma update_comp_of_preimage {n p : ℕ} {T : Type u} (f : Fin p → Fin n)
    (hinj : Function.Injective f) (v : Fin n → T) (i : Fin n) (m : Fin p)
    (hm : f m = i) (x : T) :
    (fun k => Function.update v i x (f k)) = Function.update (fun k => v (f k)) m x := by
  funext k
  by_cases hk : k = m
  · rw [hk, hm, Function.update_self, Function.update_self]
  · rw [Function.update_of_ne (fun hc => hk (hinj (hc.trans hm.symm))),
      Function.update_of_ne hk]

/-- 复合向量的槽更新分解（预像不在块内）：块向量不变。 -/
lemma update_comp_of_not_mem {n p : ℕ} {T : Type u} (f : Fin p → Fin n)
    (v : Fin n → T) (i : Fin n) (hni : ∀ k, f k ≠ i) (x : T) :
    (fun k => Function.update v i x (f k)) = fun k => v (f k) := by
  funext k
  rw [Function.update_of_ne (hni k)]

/-- `(p,q)` 楔积对第 `i` 槽的加法。预像落在 ω 块（`↑(preimage π i) < p`）时
η 块不受影响，反之亦然；两块像集不交且覆盖保证恰居其一。 -/
lemma wedgeAnyFun_update_add {p q : ℕ} {x : X} [DecidableEq (Fin (p + q))]
    (ω : TangentFiber R X x [⋀^Fin p]→ₗ[R] R)
    (η : TangentFiber R X x [⋀^Fin q]→ₗ[R] R)
    (v : Fin (p + q) → TangentFiber R X x) (i : Fin (p + q))
    (x₁ x₂ : TangentFiber R X x) :
    wedgeAnyFun ω η (Function.update v i (x₁ + x₂))
      = wedgeAnyFun ω η (Function.update v i x₁)
        + wedgeAnyFun ω η (Function.update v i x₂) := by
  unfold wedgeAnyFun
  rw [← FinPerm.permSum_add]
  refine permSum_congr (fun π => ?_)
  have hpre := FinPerm.preimage_apply π i
  by_cases hwp : (FinPerm.preimage π i : ℕ) < p
  · -- 预像在 ω 块：η 块不受影响
    have hmEq : (Fin.castAdd q (Fin.mk ((FinPerm.preimage π i : ℕ)) hwp : Fin p))
        = FinPerm.preimage π i := Fin.ext (by simp only [Fin.val_castAdd])
    have hmi : π.toFun (Fin.castAdd q (Fin.mk ((FinPerm.preimage π i : ℕ)) hwp : Fin p))
        = i := by rw [hmEq]; exact hpre
    have hηne : ∀ k : Fin q, π.toFun (Fin.natAdd p k) ≠ i := by
      intro k hc
      have h1 : Fin.natAdd p k = FinPerm.preimage π i :=
        π.toFun_injective (hc.trans hpre.symm)
      have hv : p + (k : ℕ) = (FinPerm.preimage π i : ℕ) := by
        simpa only [Fin.val_natAdd] using congrArg Fin.val h1
      have hkp := k.isLt
      omega
    have hωdec : ∀ x : TangentFiber R X x,
        (fun k => Function.update v i x (π.toFun (Fin.castAdd q k)))
          = Function.update (fun k => v (π.toFun (Fin.castAdd q k)))
            (Fin.mk ((FinPerm.preimage π i : ℕ)) hwp) x := by
      intro x
      funext k
      by_cases hk : k = Fin.mk ((FinPerm.preimage π i : ℕ)) hwp
      · rw [hk, hmEq, hpre, Function.update_self, Function.update_self]
      · have hne : π.toFun (Fin.castAdd q k) ≠ i := by
          intro hc
          have h1 : Fin.castAdd q k = FinPerm.preimage π i :=
            π.toFun_injective (hc.trans hpre.symm)
          have hv : (k : ℕ) = (FinPerm.preimage π i : ℕ) := by
            simpa only [Fin.val_castAdd] using congrArg Fin.val h1
          have hkv : (k : ℕ) ≠ (Fin.mk ((FinPerm.preimage π i : ℕ)) hwp : ℕ) :=
            fun hc2 => hk (Fin.ext hc2)
          have hmv : ((Fin.mk ((FinPerm.preimage π i : ℕ)) hwp : Fin p) : ℕ)
              = (FinPerm.preimage π i : ℕ) := rfl
          omega
        rw [Function.update_of_ne hne, Function.update_of_ne hk]
    have hηdec : ∀ x : TangentFiber R X x,
        (fun k => Function.update v i x (π.toFun (Fin.natAdd p k)))
          = fun k => v (π.toFun (Fin.natAdd p k)) := by
      intro x
      funext k
      rw [Function.update_of_ne (hηne k)]
    rw [hωdec (x₁ + x₂), hηdec (x₁ + x₂), hωdec x₁, hηdec x₁, hωdec x₂, hηdec x₂,
      ω.map_update_add]
    ring
  · -- 预像在 η 块：ω 块不受影响
    have hmq : (FinPerm.preimage π i : ℕ) - p < q := by
      have h1 := (FinPerm.preimage π i).isLt
      omega
    have hm'Eq : (Fin.natAdd p (Fin.mk ((FinPerm.preimage π i : ℕ) - p) hmq : Fin q))
        = FinPerm.preimage π i := Fin.ext (by simp only [Fin.val_natAdd]; omega)
    have hmi' : π.toFun (Fin.natAdd p (Fin.mk ((FinPerm.preimage π i : ℕ) - p) hmq : Fin q))
        = i := by rw [hm'Eq]; exact hpre
    have hωne : ∀ k : Fin p, π.toFun (Fin.castAdd q k) ≠ i := by
      intro k hc
      have h1 : Fin.castAdd q k = FinPerm.preimage π i :=
        π.toFun_injective (hc.trans hpre.symm)
      have hv : (k : ℕ) = (FinPerm.preimage π i : ℕ) := by
        simpa only [Fin.val_castAdd] using congrArg Fin.val h1
      have hkp := k.isLt
      omega
    have hωdec : ∀ x : TangentFiber R X x,
        (fun k => Function.update v i x (π.toFun (Fin.castAdd q k)))
          = fun k => v (π.toFun (Fin.castAdd q k)) := by
      intro x
      funext k
      rw [Function.update_of_ne (hωne k)]
    have hηdec : ∀ x : TangentFiber R X x,
        (fun k => Function.update v i x (π.toFun (Fin.natAdd p k)))
          = Function.update (fun k => v (π.toFun (Fin.natAdd p k)))
            (Fin.mk ((FinPerm.preimage π i : ℕ) - p) hmq) x := by
      intro x
      funext k
      by_cases hk : k = Fin.mk ((FinPerm.preimage π i : ℕ) - p) hmq
      · rw [hk, hm'Eq, hpre, Function.update_self, Function.update_self]
      · have hne : π.toFun (Fin.natAdd p k) ≠ i := by
          intro hc
          have h1 : Fin.natAdd p k = FinPerm.preimage π i :=
            π.toFun_injective (hc.trans hpre.symm)
          have hv : p + (k : ℕ) = (FinPerm.preimage π i : ℕ) := by
            simpa only [Fin.val_natAdd] using congrArg Fin.val h1
          have hkv : (k : ℕ) ≠ (Fin.mk ((FinPerm.preimage π i : ℕ) - p) hmq : ℕ) :=
            fun hc2 => hk (Fin.ext hc2)
          have hmv : ((Fin.mk ((FinPerm.preimage π i : ℕ) - p) hmq : Fin q) : ℕ)
              = (FinPerm.preimage π i : ℕ) - p := rfl
          omega
        rw [Function.update_of_ne hne, Function.update_of_ne hk]
    rw [hωdec (x₁ + x₂), hηdec (x₁ + x₂), hωdec x₁, hηdec x₁, hωdec x₂, hηdec x₂,
      η.map_update_add]
    ring

/-- `(p,q)` 楔积对第 `i` 槽的数乘。 -/
lemma wedgeAnyFun_update_smul {p q : ℕ} {x : X} [DecidableEq (Fin (p + q))]
    (ω : TangentFiber R X x [⋀^Fin p]→ₗ[R] R)
    (η : TangentFiber R X x [⋀^Fin q]→ₗ[R] R)
    (v : Fin (p + q) → TangentFiber R X x) (i : Fin (p + q))
    (c : R) (x₁ : TangentFiber R X x) :
    wedgeAnyFun ω η (Function.update v i (c • x₁))
      = c • wedgeAnyFun ω η (Function.update v i x₁) := by
  unfold wedgeAnyFun
  simp only [smul_eq_mul]
  rw [← permSum_mul_left]
  refine permSum_congr (fun π => ?_)
  have hpre := FinPerm.preimage_apply π i
  by_cases hwp : (FinPerm.preimage π i : ℕ) < p
  · have hmEq : (Fin.castAdd q (Fin.mk ((FinPerm.preimage π i : ℕ)) hwp : Fin p))
        = FinPerm.preimage π i := Fin.ext (by simp only [Fin.val_castAdd])
    have hmi : π.toFun (Fin.castAdd q (Fin.mk ((FinPerm.preimage π i : ℕ)) hwp : Fin p))
        = i := by rw [hmEq]; exact hpre
    have hηne : ∀ k : Fin q, π.toFun (Fin.natAdd p k) ≠ i := by
      intro k hc
      have h1 : Fin.natAdd p k = FinPerm.preimage π i :=
        π.toFun_injective (hc.trans hpre.symm)
      have hv : p + (k : ℕ) = (FinPerm.preimage π i : ℕ) := by
        simpa only [Fin.val_natAdd] using congrArg Fin.val h1
      have hkp := k.isLt
      omega
    have hωdec : ∀ x : TangentFiber R X x,
        (fun k => Function.update v i x (π.toFun (Fin.castAdd q k)))
          = Function.update (fun k => v (π.toFun (Fin.castAdd q k)))
            (Fin.mk ((FinPerm.preimage π i : ℕ)) hwp) x := by
      intro x
      funext k
      by_cases hk : k = Fin.mk ((FinPerm.preimage π i : ℕ)) hwp
      · rw [hk, hmEq, hpre, Function.update_self, Function.update_self]
      · have hne : π.toFun (Fin.castAdd q k) ≠ i := by
          intro hc
          have h1 : Fin.castAdd q k = FinPerm.preimage π i :=
            π.toFun_injective (hc.trans hpre.symm)
          have hv : (k : ℕ) = (FinPerm.preimage π i : ℕ) := by
            simpa only [Fin.val_castAdd] using congrArg Fin.val h1
          have hkv : (k : ℕ) ≠ (Fin.mk ((FinPerm.preimage π i : ℕ)) hwp : ℕ) :=
            fun hc2 => hk (Fin.ext hc2)
          have hmv : ((Fin.mk ((FinPerm.preimage π i : ℕ)) hwp : Fin p) : ℕ)
              = (FinPerm.preimage π i : ℕ) := rfl
          omega
        rw [Function.update_of_ne hne, Function.update_of_ne hk]
    have hηdec : ∀ x : TangentFiber R X x,
        (fun k => Function.update v i x (π.toFun (Fin.natAdd p k)))
          = fun k => v (π.toFun (Fin.natAdd p k)) := by
      intro x
      funext k
      rw [Function.update_of_ne (hηne k)]
    rw [hωdec (c • x₁), hηdec (c • x₁), hωdec x₁, hηdec x₁, ω.map_update_smul]
    simp only [smul_eq_mul]
    ring
  · have hmq : (FinPerm.preimage π i : ℕ) - p < q := by
      have h1 := (FinPerm.preimage π i).isLt
      omega
    have hm'Eq : (Fin.natAdd p (Fin.mk ((FinPerm.preimage π i : ℕ) - p) hmq : Fin q))
        = FinPerm.preimage π i := Fin.ext (by simp only [Fin.val_natAdd]; omega)
    have hmi' : π.toFun (Fin.natAdd p (Fin.mk ((FinPerm.preimage π i : ℕ) - p) hmq : Fin q))
        = i := by rw [hm'Eq]; exact hpre
    have hωne : ∀ k : Fin p, π.toFun (Fin.castAdd q k) ≠ i := by
      intro k hc
      have h1 : Fin.castAdd q k = FinPerm.preimage π i :=
        π.toFun_injective (hc.trans hpre.symm)
      have hv : (k : ℕ) = (FinPerm.preimage π i : ℕ) := by
        simpa only [Fin.val_castAdd] using congrArg Fin.val h1
      have hkp := k.isLt
      omega
    have hωdec : ∀ x : TangentFiber R X x,
        (fun k => Function.update v i x (π.toFun (Fin.castAdd q k)))
          = fun k => v (π.toFun (Fin.castAdd q k)) := by
      intro x
      funext k
      rw [Function.update_of_ne (hωne k)]
    have hηdec : ∀ x : TangentFiber R X x,
        (fun k => Function.update v i x (π.toFun (Fin.natAdd p k)))
          = Function.update (fun k => v (π.toFun (Fin.natAdd p k)))
            (Fin.mk ((FinPerm.preimage π i : ℕ) - p) hmq) x := by
      intro x
      funext k
      by_cases hk : k = Fin.mk ((FinPerm.preimage π i : ℕ) - p) hmq
      · rw [hk, hm'Eq, hpre, Function.update_self, Function.update_self]
      · have hne : π.toFun (Fin.natAdd p k) ≠ i := by
          intro hc
          have h1 : Fin.natAdd p k = FinPerm.preimage π i :=
            π.toFun_injective (hc.trans hpre.symm)
          have hv : p + (k : ℕ) = (FinPerm.preimage π i : ℕ) := by
            simpa only [Fin.val_natAdd] using congrArg Fin.val h1
          have hkv : (k : ℕ) ≠ (Fin.mk ((FinPerm.preimage π i : ℕ) - p) hmq : ℕ) :=
            fun hc2 => hk (Fin.ext hc2)
          have hmv : ((Fin.mk ((FinPerm.preimage π i : ℕ) - p) hmq : Fin q) : ℕ)
              = (FinPerm.preimage π i : ℕ) - p := rfl
          omega
        rw [Function.update_of_ne hne, Function.update_of_ne hk]
    rw [hωdec (c • x₁), hηdec (c • x₁), hωdec x₁, hηdec x₁, η.map_update_smul]
    simp only [smul_eq_mul]
    ring

/-- **一般 `(p,q)` 楔积**：`wedgeAnyFun` 的纤维层 `AlternatingMap` 打包。
交错性（等值槽消零）需 2 可逆，以参数 `h2 : ∃ y : R, y * 2 = 1` 进入。 -/
def wedgeAny {p q : ℕ} (h2 : ∃ y : R, y * 2 = 1)
    (ω : FiberwiseDifferentialForm R X p)
    (η : FiberwiseDifferentialForm R X q) :
    FiberwiseDifferentialForm R X (p + q) := by
  intro x
  exact
    { toMultilinearMap :=
        { toFun := wedgeAnyFun (ω x) (η x)
          map_update_add' := by
            intro _ v i x₁ x₂
            exact wedgeAnyFun_update_add (ω x) (η x) v i x₁ x₂
          map_update_smul' := by
            intro _ v i c x₁
            exact wedgeAnyFun_update_smul (ω x) (η x) v i c x₁ }
      map_eq_zero_of_eq' := by
        intro v i j h hij
        exact wedgeAnyFun_eq_zero_of_eq (ω x) (η x) h2 hij v h }

@[simp]
lemma wedgeAny_apply {p q : ℕ} (h2 : ∃ y : R, y * 2 = 1)
    (ω : FiberwiseDifferentialForm R X p) (η : FiberwiseDifferentialForm R X q)
    (x : X) (v : Fin (p + q) → TangentFiber R X x) :
    wedgeAny h2 ω η x v = wedgeAnyFun (ω x) (η x) v := rfl

/-- 楔积对第一因子的加法。 -/
lemma wedgeAny_add_left {p q : ℕ} (h2 : ∃ y : R, y * 2 = 1)
    (ω₁ ω₂ : FiberwiseDifferentialForm R X p)
    (η : FiberwiseDifferentialForm R X q) :
    wedgeAny h2 (ω₁ + ω₂) η = wedgeAny h2 ω₁ η + wedgeAny h2 ω₂ η := by
  funext x
  apply AlternatingMap.ext
  intro v
  show wedgeAnyFun ((ω₁ + ω₂) x) (η x) v
    = wedgeAnyFun (ω₁ x) (η x) v + wedgeAnyFun (ω₂ x) (η x) v
  rw [Pi.add_apply, wedgeAnyFun_add_left]

/-- 楔积对第二因子的加法。 -/
lemma wedgeAny_add_right {p q : ℕ} (h2 : ∃ y : R, y * 2 = 1)
    (ω : FiberwiseDifferentialForm R X p)
    (η₁ η₂ : FiberwiseDifferentialForm R X q) :
    wedgeAny h2 ω (η₁ + η₂) = wedgeAny h2 ω η₁ + wedgeAny h2 ω η₂ := by
  funext x
  apply AlternatingMap.ext
  intro v
  show wedgeAnyFun (ω x) ((η₁ + η₂) x) v
    = wedgeAnyFun (ω x) (η₁ x) v + wedgeAnyFun (ω x) (η₂ x) v
  rw [Pi.add_apply, wedgeAnyFun_add_right]

/-- 楔积对第一因子的数乘。 -/
lemma wedgeAny_smul_left {p q : ℕ} (h2 : ∃ y : R, y * 2 = 1)
    (c : R) (ω : FiberwiseDifferentialForm R X p)
    (η : FiberwiseDifferentialForm R X q) :
    wedgeAny h2 (c • ω) η = c • wedgeAny h2 ω η := by
  funext x
  apply AlternatingMap.ext
  intro v
  show wedgeAnyFun ((c • ω) x) (η x) v = c • wedgeAnyFun (ω x) (η x) v
  rw [Pi.smul_apply, wedgeAnyFun_smul_left]

/-- 楔积对第二因子的数乘。 -/
lemma wedgeAny_smul_right {p q : ℕ} (h2 : ∃ y : R, y * 2 = 1)
    (ω : FiberwiseDifferentialForm R X p) (c : R)
    (η : FiberwiseDifferentialForm R X q) :
    wedgeAny h2 ω (c • η) = c • wedgeAny h2 ω η := by
  funext x
  apply AlternatingMap.ext
  intro v
  show wedgeAnyFun (ω x) ((c • η) x) v = c • wedgeAnyFun (ω x) (η x) v
  rw [Pi.smul_apply, wedgeAnyFun_smul_right]

end WedgeAnyPack

/-! ### 分次交换律的符号机器

块交换 `bsFunV n q p`（前 `q` 槽与后 `p` 槽互换）的限定乘性
`sign (encode (bsFunV ∘ π.toFun)) = (-1)^(q*p) · sign π` 经三件套：
任意对换的 FLIP（共轭分解，对距离归纳）、循环移位 `cycFun` 的相邻链
（`n-1` 次 FLIP）、以及块交换递推
`bsFunV n (q+1) p = cycFun n ∘ bsFunV n q (p+1)`（对 `2q+p` 强归纳，
指数差 `2q` 为偶）。全部无选择公理。 -/

section GradComm

variable {R : Type u} [CommRing R]

/-- 共轭分解的置换形式：`(x y) = (x z) ∘ ((z y) ∘ (x z))`（`z = x+1 < y`），
toFun 级恒等式即 `swapFin_triple`。 -/
lemma swapPerm_triple {n : ℕ} {x y : Fin n} {z : Fin n}
    (hxz : (x : ℕ) + 1 = (z : ℕ)) (hlt : (z : ℕ) < (y : ℕ)) :
    FinPerm.swapPerm x y
      = FinPerm.compose (FinPerm.swapPerm x z)
          (FinPerm.compose (FinPerm.swapPerm z y) (FinPerm.swapPerm x z)) := by
      apply FinPerm.ext_toFun _ _
      rw [FinPerm.toFun_compose, FinPerm.toFun_compose]
      simp only [FinPerm.toFun_swapPerm]
      exact swapFin_triple hxz hlt

/-- **任意对换的 FLIP**：左复合任意对换（不要求相邻）使 sign 反号。
对距离 `d := y - x - 1` 归纳；递推用 `swapPerm_triple` 剥一层 +
归纳假设 + 相邻 FLIP。 -/
lemma sign_compose_swapPerm : ∀ (d : ℕ) {n : ℕ} (x y : Fin n),
    (y : ℕ) = (x : ℕ) + d + 1 → ∀ (π : FinPerm n),
    FinPerm.sign R (FinPerm.compose (FinPerm.swapPerm x y) π) = -FinPerm.sign R π := by
  intro d
  induction d with
  | zero =>
      intro n x y h π
      have hxy : (x : ℕ) + 1 = (y : ℕ) := by omega
      exact sign_compose_swapPerm_adj π x y hxy
  | succ d ih =>
      intro n x y h π
      have hy := y.isLt
      obtain ⟨z, hzv⟩ : ∃ z : Fin n, (z : ℕ) = (x : ℕ) + 1 :=
        ⟨⟨_, by omega⟩, rfl⟩
      have hxz : (x : ℕ) + 1 = (z : ℕ) := hzv.symm
      have hlt : (z : ℕ) < (y : ℕ) := by omega
      have hzy : (y : ℕ) = (z : ℕ) + d + 1 := by omega
      rw [swapPerm_triple hxz hlt, FinPerm.compose_assoc,
        sign_compose_swapPerm_adj _ _ _ hxz, FinPerm.compose_assoc,
        ih z y hzy, sign_compose_swapPerm_adj _ _ _ hxz]
      ring

/-- **任意对换的符号为 `-1`**（FLIP 与恒等置换复合）。 -/
lemma sign_swapPerm : ∀ (d : ℕ) {n : ℕ} (x y : Fin n),
    (y : ℕ) = (x : ℕ) + d + 1 → FinPerm.sign R (FinPerm.swapPerm x y) = -1 := by
  intro d
  induction d with
  | zero =>
      intro n x y h
      have hxy : (x : ℕ) + 1 = (y : ℕ) := by omega
      exact sign_swapPerm_adj hxy
  | succ d ih =>
      intro n x y h
      have hy := y.isLt
      obtain ⟨z, hzv⟩ : ∃ z : Fin n, (z : ℕ) = (x : ℕ) + 1 :=
        ⟨⟨_, by omega⟩, rfl⟩
      have hxz : (x : ℕ) + 1 = (z : ℕ) := hzv.symm
      have hlt : (z : ℕ) < (y : ℕ) := by omega
      have hzy : (y : ℕ) = (z : ℕ) + d + 1 := by omega
      rw [swapPerm_triple hxz hlt, sign_compose_swapPerm_adj _ _ _ hxz,
        sign_compose_swapPerm d z y hzy, sign_swapPerm_adj hxz]
      ring

end GradComm

/-! ### 循环左移与块交换（E3 续）

`cycLfun s p`：区间 `[s, s+p]` 的循环左移（`s ↦ s+p`，其余 `-1`）；
`bsFunV n q p`：`(p,q)`-shuffle（前 `q` 槽右移 `p`、后 `p` 槽左移 `q`）。
关键恒等式（均点态表验证）：
`cycLfun s (p+1) = swapFin⟨s+p⟩⟨s+p+1⟩ ∘ cycLfun s p` 与
`bsFunV n (q+1) p = bsFunV n q p ∘ cycLfun q p`，
由此 (P') `sign (encode (bsFunV ∘ π.toFun)) = (-1)^{q*p} sign π` 对 q 归纳。 -/


section CycleShift

/-- 区间 `[s, s+p]` 的循环左移：`s ↦ s+p`，`s < t ≤ s+p ↦ t-1`，其余不动。
守卫 `hsp : s + p < n` 保证右端落点合法。 -/
def cycLfun {n : ℕ} (s p : ℕ) (hsp : s + p < n) : Fin n → Fin n :=
  fun t =>
    dite ((t : ℕ) = s)
      (fun _hEq => (Fin.mk (s + p) hsp : Fin n))
      (fun _hne =>
        dite (s < (t : ℕ) ∧ (t : ℕ) ≤ s + p)
          (fun _hMid => (Fin.mk ((t : ℕ) - 1) (by have ht := t.isLt; omega) : Fin n))
          (fun _hOut => t))

/-- 循环左移在左端点的值：`↑t = s ↦ s+p`。 -/
lemma cycLfun_left {n : ℕ} {s p : ℕ} (hsp : s + p < n) {t : Fin n}
    (hEq : (t : ℕ) = s) :
    cycLfun s p hsp t = (Fin.mk (s + p) hsp : Fin n) := by
  unfold cycLfun
  rw [dif_pos hEq]

/-- 循环左移在中段的值：`s < t ≤ s+p ↦ t-1`。 -/
lemma cycLfun_mid {n : ℕ} {s p : ℕ} (hsp : s + p < n) {t : Fin n}
    (h1 : s < (t : ℕ)) (h2 : (t : ℕ) ≤ s + p) :
    cycLfun s p hsp t
      = (Fin.mk ((t : ℕ) - 1) (by have ht := t.isLt; omega) : Fin n) := by
  unfold cycLfun
  rw [dif_neg (by omega), dif_pos ⟨h1, h2⟩]

/-- 循环左移在区间外的值：不动。 -/
lemma cycLfun_out {n : ℕ} {s p : ℕ} (hsp : s + p < n) {t : Fin n}
    (hne : (t : ℕ) ≠ s) (hno : ¬(s < (t : ℕ) ∧ (t : ℕ) ≤ s + p)) :
    cycLfun s p hsp t = t := by
  unfold cycLfun
  rw [dif_neg hne, dif_neg hno]


/-- **循环左移的递推**：`cycLfun s (p+1)` = 右端对换复合 `cycLfun s p`。
五情形点态验证（`t = s` 直达右端、`t = s+p+1` 对换回落、`s < t ≤ s+p` 中段
`-1` 不变、其余区间外不动）。 -/
lemma cycLfun_succ {n : ℕ} {s p : ℕ} (hsp : s + (p + 1) < n) :
    cycLfun s (p + 1) hsp
      = (swapFin (Fin.mk (s + p) (by omega : (s + p : ℕ) < n))
          (Fin.mk (s + p + 1) hsp)) ∘
        (cycLfun s p (by omega : (s + p : ℕ) < n)) := by
  have hsp2 : (s + p : ℕ) < n := by omega
  funext t
  by_cases h1 : (t : ℕ) = s
  · -- t = s：subst 后两侧 dite 都走左端分支
    have hEq : t = (Fin.mk s (show (s : ℕ) < n from Nat.lt_of_le_of_lt (Nat.le_add_right s (p + 1)) hsp) : Fin n) := Fin.ext h1
    subst hEq
    show cycLfun s (p + 1) hsp (Fin.mk s (show (s : ℕ) < n from Nat.lt_of_le_of_lt (Nat.le_add_right s (p + 1)) hsp))
      = swapFin (Fin.mk (s + p) hsp2) (Fin.mk (s + p + 1) hsp)
        (cycLfun s p hsp2 (Fin.mk s (show (s : ℕ) < n from Nat.lt_of_le_of_lt (Nat.le_add_right s (p + 1)) hsp)))
    unfold cycLfun
    rw [dif_pos rfl, dif_pos rfl, swapFin_self_left]
    exact Fin.ext (by simp only [Fin.val_mk]; omega)
  · by_cases h2 : (t : ℕ) = s + (p + 1)
    · have hEq : t = (Fin.mk (s + p + 1) hsp : Fin n) := Fin.ext h2
      subst hEq
      have hM1 : s < ((Fin.mk (s + p + 1) hsp : Fin n) : ℕ) := show s < s + p + 1 by omega
      have hM2 : ((Fin.mk (s + p + 1) hsp : Fin n) : ℕ) ≤ s + p + 1 := show s + p + 1 ≤ s + p + 1 by omega
      have hO1 : ((Fin.mk (s + p + 1) hsp : Fin n) : ℕ) ≠ s := show s + p + 1 ≠ s by omega
      have hO2 : ¬(s < ((Fin.mk (s + p + 1) hsp : Fin n) : ℕ) ∧
          ((Fin.mk (s + p + 1) hsp : Fin n) : ℕ) ≤ s + p) :=
        show ¬(s < s + p + 1 ∧ s + p + 1 ≤ s + p) by omega
      show cycLfun s (p + 1) hsp (Fin.mk (s + p + 1) hsp)
        = swapFin (Fin.mk (s + p) hsp2) (Fin.mk (s + p + 1) hsp)
          (cycLfun s p hsp2 (Fin.mk (s + p + 1) hsp))
      rw [cycLfun_mid hsp hM1 hM2, cycLfun_out hsp2 hO1 hO2, swapFin_self_right]
      exact Fin.ext (by simp only [Fin.val_mk]; omega)
    · by_cases h3 : (t : ℕ) ≤ s + p
      · by_cases h4 : (t : ℕ) < s
        · -- t < s：两侧区间外
          have hO3 : (t : ℕ) ≠ s := fun hc => by rw [hc] at h4; omega
          have hO4 : ¬(s < (t : ℕ) ∧ (t : ℕ) ≤ s + (p + 1)) := fun hcon => by omega
          have hO5 : ¬(s < (t : ℕ) ∧ (t : ℕ) ≤ s + p) := fun hcon => by omega
          have hneA : t ≠ (Fin.mk (s + p) hsp2 : Fin n) := fun hc => by
            rw [hc, Fin.val_mk] at h4
            omega
          have hneB : t ≠ (Fin.mk (s + p + 1) hsp : Fin n) := fun hc => by
            rw [hc, Fin.val_mk] at h4
            omega
          show cycLfun s (p + 1) hsp t
            = swapFin (Fin.mk (s + p) hsp2) (Fin.mk (s + p + 1) hsp)
              (cycLfun s p hsp2 t)
          rw [cycLfun_out hsp hO3 hO4, cycLfun_out hsp2 hO3 hO5, swapFin_of_ne hneA hneB]
        · -- s < t ≤ s+p：两侧同为中段 `-1`
          have ht1 : s < (t : ℕ) := by omega
          have hUp1 : (t : ℕ) ≤ s + p + 1 := by omega
          have hneL : (Fin.mk ((t : ℕ) - 1) (by have ht := t.isLt; omega) : Fin n)
              ≠ (Fin.mk (s + p) hsp2 : Fin n) := by
            intro hc
            have hv : ((Fin.mk ((t : ℕ) - 1) (by have ht := t.isLt; omega) : Fin n) : ℕ)
                = ((Fin.mk (s + p) hsp2 : Fin n) : ℕ) := congrArg Fin.val hc
            have hv1 : ((Fin.mk ((t : ℕ) - 1) (by have ht := t.isLt; omega) : Fin n) : ℕ)
                = (t : ℕ) - 1 := rfl
            have hv2 : ((Fin.mk (s + p) hsp2 : Fin n) : ℕ) = s + p := rfl
            omega
          have hneR : (Fin.mk ((t : ℕ) - 1) (by have ht := t.isLt; omega) : Fin n)
              ≠ (Fin.mk (s + p + 1) hsp : Fin n) := by
            intro hc
            have hv : ((Fin.mk ((t : ℕ) - 1) (by have ht := t.isLt; omega) : Fin n) : ℕ)
                = ((Fin.mk (s + p + 1) hsp : Fin n) : ℕ) := congrArg Fin.val hc
            have hv1 : ((Fin.mk ((t : ℕ) - 1) (by have ht := t.isLt; omega) : Fin n) : ℕ)
                = (t : ℕ) - 1 := rfl
            have hv2 : ((Fin.mk (s + p + 1) hsp : Fin n) : ℕ) = s + p + 1 := rfl
            omega
          show cycLfun s (p + 1) hsp t
            = swapFin (Fin.mk (s + p) hsp2) (Fin.mk (s + p + 1) hsp)
              (cycLfun s p hsp2 t)
          rw [cycLfun_mid hsp ht1 hUp1, cycLfun_mid hsp2 ht1 h3, swapFin_of_ne hneL hneR]
      · -- t > s+p：两侧区间外
        have hO3 : (t : ℕ) ≠ s :=
          fun hc => h3 (Nat.le_trans (le_of_eq hc) (Nat.le_add_right s p))
        have hge : (s + p + 1 : ℕ) ≤ (t : ℕ) := Nat.succ_le_of_lt (Nat.lt_of_not_ge h3)
        have hO4 : ¬(s < (t : ℕ) ∧ (t : ℕ) ≤ s + (p + 1)) := fun hcon => by
          have hEq : (t : ℕ) = s + p + 1 := by omega
          exact h2 hEq
        have hO5 : ¬(s < (t : ℕ) ∧ (t : ℕ) ≤ s + p) := fun hcon => h3 hcon.2
        have hneA : t ≠ (Fin.mk (s + p) hsp2 : Fin n) := fun hc =>
          h3 (by rw [hc, Fin.val_mk])
        have hneB : t ≠ (Fin.mk (s + p + 1) hsp : Fin n) := fun hc =>
          h2 (by rw [hc]; simp only [Fin.val_mk]; omega)
        show cycLfun s (p + 1) hsp t
          = swapFin (Fin.mk (s + p) hsp2) (Fin.mk (s + p + 1) hsp)
            (cycLfun s p hsp2 t)
        rw [cycLfun_out hsp hO3 hO4, cycLfun_out hsp2 hO3 hO5, swapFin_of_ne hneA hneB]

end CycleShift

section BlockSwap

/-- `(p,q)`-shuffle 的位置函数：前 `q` 槽右移 `p`（`t ↦ t+p`）、
中段 `q ≤ t < q+p` 左移 `q`（`t ↦ t-q`）、其余不动。
守卫 `hsp : q + p ≤ n` 保证落点合法；`q = p` 时为对合，
一般与 `bsFunV p q` 互逆。 -/
def bsFunV {n : ℕ} (q p : ℕ) (hsp : q + p ≤ n) : Fin n → Fin n :=
  fun t =>
    dite ((t : ℕ) < q)
      (fun _hlt => (Fin.mk ((t : ℕ) + p) (by have ht := t.isLt; have h := hsp; omega) : Fin n))
      (fun _hge =>
        dite ((t : ℕ) < q + p)
          (fun _hlt2 => (Fin.mk ((t : ℕ) - q) (by have ht := t.isLt; have h := hsp; omega) : Fin n))
          (fun _hge2 => t))

/-- shuffle 在前段的值：`t < q ↦ t+p`。 -/
lemma bsFunV_front {n q p : ℕ} (hsp : q + p ≤ n) {t : Fin n} (hlt : (t : ℕ) < q) :
    bsFunV q p hsp t
      = (Fin.mk ((t : ℕ) + p) (by have ht := t.isLt; have h := hsp; omega) : Fin n) := by
  unfold bsFunV
  rw [dif_pos hlt]

/-- shuffle 在中段的值：`q ≤ t < q+p ↦ t-q`。 -/
lemma bsFunV_back {n q p : ℕ} (hsp : q + p ≤ n) {t : Fin n}
    (h1 : q ≤ (t : ℕ)) (h2 : (t : ℕ) < q + p) :
    bsFunV q p hsp t
      = (Fin.mk ((t : ℕ) - q) (by have ht := t.isLt; have h := hsp; omega) : Fin n) := by
  unfold bsFunV
  rw [dif_neg (by omega), dif_pos (by omega)]

/-- shuffle 在尾部区间的值：不动。 -/
lemma bsFunV_out {n q p : ℕ} (hsp : q + p ≤ n) {t : Fin n} (hge : q + p ≤ (t : ℕ)) :
    bsFunV q p hsp t = t := by
  unfold bsFunV
  rw [dif_neg (by omega), dif_neg (by omega)]

/-- **shuffle 与反参数 shuffle 互逆**：`bsFunV p q ∘ bsFunV q p = id`
（三分支点态表；由 `Function.LeftInverse.injective` 得单射性）。 -/
lemma bsFunV_comp_id {n q p : ℕ} (hsp : q + p ≤ n) :
    (fun t => bsFunV p q (show p + q ≤ n from by omega)
        (bsFunV q p hsp t)) = id := by
  funext t
  by_cases h1 : (t : ℕ) < q
  · have hv : bsFunV q p hsp t
        = (Fin.mk ((t : ℕ) + p) (by have ht := t.isLt; have h := hsp; omega) : Fin n) :=
      bsFunV_front hsp h1
    have h2 : ((Fin.mk ((t : ℕ) + p) (by have ht := t.isLt; have h := hsp; omega) : Fin n) : ℕ)
        ≥ p := by simp only [Fin.val_mk]; omega
    have h3 : ((Fin.mk ((t : ℕ) + p) (by have ht := t.isLt; have h := hsp; omega) : Fin n) : ℕ)
        < p + q := by simp only [Fin.val_mk]; omega
    rw [hv, bsFunV_back (show p + q ≤ n from by omega) h2 h3]
    simp only [Fin.val_mk]
    congr 1
    omega
  · by_cases h2 : (t : ℕ) < q + p
    · have hv : bsFunV q p hsp t
          = (Fin.mk ((t : ℕ) - q) (by have ht := t.isLt; have h := hsp; omega) : Fin n) :=
        bsFunV_back hsp (by omega) h2
      have h3 : ((Fin.mk ((t : ℕ) - q) (by have ht := t.isLt; have h := hsp; omega) : Fin n) : ℕ)
          < p := by simp only [Fin.val_mk]; omega
      rw [hv, bsFunV_front (show p + q ≤ n from by omega) h3]
      simp only [Fin.val_mk]
      congr 1
      omega
    · have hv : bsFunV q p hsp t = t := bsFunV_out hsp (by omega)
      rw [hv, bsFunV_out (show p + q ≤ n from by omega) (by omega)]
      rfl

/-- shuffle 单射（经逆复合）。 -/
lemma bsFunV_injective {n q p : ℕ} (hsp : q + p ≤ n) :
    Function.Injective (bsFunV q p hsp) :=
  Function.LeftInverse.injective
    (fun t => by
      have h := bsFunV_comp_id (show q + p ≤ n from hsp)
      exact congrFun h t)

end BlockSwap

end SDG.DifferentialForms
