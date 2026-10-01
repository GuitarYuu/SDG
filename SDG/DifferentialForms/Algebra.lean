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
def swapFinAdj {n : ℕ} (j : Fin (n + 1)) (a : Fin (n + 2)) : Fin (n + 2) :=
  if (a : ℕ) = (j : ℕ) then ⟨(j : ℕ) + 1, Nat.succ_lt_succ j.isLt⟩
  else if (a : ℕ) = (j : ℕ) + 1 then ⟨(j : ℕ), Nat.lt_succ_of_lt j.isLt⟩
  else a

lemma swapFinAdj_eq {n : ℕ} {j : Fin (n + 1)} {a : Fin (n + 2)} (h : (a : ℕ) = (j : ℕ)) :
    swapFinAdj j a = ⟨(j : ℕ) + 1, Nat.succ_lt_succ j.isLt⟩ := if_pos h

lemma swapFinAdj_eq_one {n : ℕ} {j : Fin (n + 1)} {a : Fin (n + 2)}
    (h : (a : ℕ) = (j : ℕ) + 1) :
    swapFinAdj j a = ⟨(j : ℕ), Nat.lt_succ_of_lt j.isLt⟩ := by
  rw [swapFinAdj, if_neg (show (a : ℕ) ≠ (j : ℕ) by omega), if_pos h]

lemma swapFinAdj_of_ne {n : ℕ} {j : Fin (n + 1)} {a : Fin (n + 2)}
    (h₁ : (a : ℕ) ≠ (j : ℕ)) (h₂ : (a : ℕ) ≠ (j : ℕ) + 1) :
    swapFinAdj j a = a := by
  rw [swapFinAdj, if_neg h₁, if_neg h₂]

lemma swapFinAdj_of_lt {n : ℕ} {j : Fin (n + 1)} {a : Fin (n + 2)}
    (h : (a : ℕ) < (j : ℕ)) : swapFinAdj j a = a :=
  swapFinAdj_of_ne (by omega) (by omega)

lemma swapFinAdj_of_gt {n : ℕ} {j : Fin (n + 1)} {a : Fin (n + 2)}
    (h : (a : ℕ) > (j : ℕ) + 1) : swapFinAdj j a = a :=
  swapFinAdj_of_ne (by omega) (by omega)

lemma swapFinAdj_val {n : ℕ} (j : Fin (n + 1)) (a : Fin (n + 2)) :
    ((swapFinAdj j a : Fin (n + 2)) : ℕ) =
      if (a : ℕ) = (j : ℕ) then (j : ℕ) + 1
      else if (a : ℕ) = (j : ℕ) + 1 then (j : ℕ) else (a : ℕ) := by
  by_cases h₁ : (a : ℕ) = (j : ℕ)
  · rw [swapFinAdj_eq h₁, if_pos h₁]
  · by_cases h₂ : (a : ℕ) = (j : ℕ) + 1
    · rw [swapFinAdj_eq_one h₂, if_neg h₁, if_pos h₂]
    · rw [swapFinAdj_of_ne h₁ h₂, if_neg h₁, if_neg h₂]

lemma swapFinAdj_self {n : ℕ} (j : Fin (n + 1)) (a : Fin (n + 2)) :
    swapFinAdj j (swapFinAdj j a) = a := by
  apply Fin.ext
  by_cases h₁ : (a : ℕ) = (j : ℕ)
  · have hval : ((swapFinAdj j a : Fin (n + 2)) : ℕ) = (j : ℕ) + 1 := by
      rw [swapFinAdj_val, if_pos h₁]
    rw [swapFinAdj_val, hval, if_neg (by omega), if_pos rfl]
    omega
  · by_cases h₂ : (a : ℕ) = (j : ℕ) + 1
    · have hval : ((swapFinAdj j a : Fin (n + 2)) : ℕ) = (j : ℕ) := by
        rw [swapFinAdj_val, if_neg h₁, if_pos h₂]
      rw [swapFinAdj_val, hval, if_pos (by omega)]
      omega
    · have hval : ((swapFinAdj j a : Fin (n + 2)) : ℕ) = (a : ℕ) := by
        rw [swapFinAdj_val, if_neg h₁, if_neg h₂]
      rw [swapFinAdj_val, hval, if_neg (by omega), if_neg (by omega)]

/-- 相邻对换与后继交换：在 `Fin (n+3)` 中对换位置 `j+1, j+2`，等价于先在
`Fin (n+2)` 中对换 `j, j+1` 再整体后移一格。 -/
lemma swapFinAdj_succ {n : ℕ} (j : Fin (n + 1)) (i : Fin (n + 2)) :
    swapFinAdj (j.succ) (i.succ) = (swapFinAdj j i).succ := by
  apply Fin.ext
  have hjv : ((j.succ : Fin (n + 2)) : ℕ) = (j : ℕ) + 1 := rfl
  have hiv : ((i.succ : Fin (n + 3)) : ℕ) = (i : ℕ) + 1 := rfl
  have hs : (((swapFinAdj j i).succ : Fin (n + 3)) : ℕ)
      = ((swapFinAdj j i : Fin (n + 2)) : ℕ) + 1 := rfl
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
lemma finSum_swapFinAdj : ∀ (n : ℕ) (f : Fin (n + 2) → R) (j : Fin (n + 1)),
    finSum R (n + 2) f = finSum R (n + 2) (fun a ↦ f (swapFinAdj j a))
  | 0, f, j => by
      have hj : j = (0 : Fin 1) := Fin.ext (by have := j.isLt; omega)
      subst hj
      exact finSum_swapFinAdj_zero f
  | n + 1, f, j => by
      by_cases h0 : (j : ℕ) = 0
      · have hfun : swapFinAdj j = swapFinAdj (0 : Fin (n + 2)) := by
          funext a
          apply Fin.ext
          rw [swapFinAdj_val, swapFinAdj_val]
          have hv0 : ((0 : Fin (n + 2)) : ℕ) = 0 := rfl
          rw [hv0, h0]
        rw [hfun]
        exact finSum_swapFinAdj_zero f
      · obtain ⟨j', rfl⟩ : ∃ k : Fin (n + 1), j = k.succ :=
            ⟨⟨(j : ℕ) - 1, by have := j.isLt; omega⟩, by
              apply Fin.ext
              simp only [Fin.val_succ]
              omega⟩
        rw [finSum_succ (R := R) (n := n + 2) (f := f),
            finSum_succ (R := R) (n := n + 2)
              (f := fun a : Fin (n + 3) ↦ f (swapFinAdj j'.succ a))]
        have hhead : swapFinAdj j'.succ (0 : Fin (n + 3)) = (0 : Fin (n + 3)) :=
          swapFinAdj_of_ne (by simp only [Fin.val_zero, Fin.val_succ]; omega)
            (by simp only [Fin.val_zero, Fin.val_succ]; omega)
        rw [hhead]
        rw [show (fun i : Fin (n + 2) ↦ f (swapFinAdj j'.succ i.succ)) =
            (fun i : Fin (n + 2) ↦ f ((swapFinAdj j' i).succ)) from by
          funext i
          exact congrArg f (swapFinAdj_succ j' i)]
        rw [finSum_swapFinAdj n (fun i : Fin (n + 2) ↦ f i.succ) j']

end SwapFinAdj

/-! ### `1 ∧ n` 楔积的原始函数公式 -/

section WedgeOneAny

variable {R : Type u} [CommRing R] {X : Type u} [Microlinear R X]

/-- `1 ∧ n` 楔积的原始函数。

Kock I.14 (14.7) 公式：
`(ω ∧ η)(v₀,…,vₙ) = Σᵢ₌₀ⁿ (-1)ⁱ · ω(vᵢ) · η(v₀,…,v̂ᵢ,…,vₙ)`

其中 `v̂ᵢ` 表示用 `Fin.removeNth` 删除第 `i` 个分量。
此函数尚未打包为 `AlternatingMap`（交错性证明需要 η 的置换变号理论，
留作后续工作）；但公式本身已完整定义且无选择公理。 -/
def wedgeOneAnyFun {n : ℕ} {x : X}
    (ω : TangentFiber R X x [⋀^Fin 1]→ₗ[R] R)
    (η : TangentFiber R X x [⋀^Fin n]→ₗ[R] R)
    (v : Fin (n + 1) → TangentFiber R X x) : R :=
  finSum R (n + 1) (fun i : Fin (n + 1) ↦
    (-1 : R) ^ (i : ℕ) * FiberwiseDifferentialForm.oneArg ω (v i) * η (i.removeNth v))

lemma wedgeOneAnyFun_eq {n : ℕ} {x : X}
    (ω : TangentFiber R X x [⋀^Fin 1]→ₗ[R] R)
    (η : TangentFiber R X x [⋀^Fin n]→ₗ[R] R)
    (v : Fin (n + 1) → TangentFiber R X x) :
    wedgeOneAnyFun ω η v =
      finSum R (n + 1) (fun i : Fin (n + 1) ↦
        (-1 : R) ^ (i : ℕ) * FiberwiseDifferentialForm.oneArg ω (v i) * η (i.removeNth v)) := rfl

end WedgeOneAny

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

end SDG.DifferentialForms