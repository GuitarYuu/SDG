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

end FiberwiseDifferentialForm

end SDG.DifferentialForms
