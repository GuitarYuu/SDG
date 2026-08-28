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

end FinPerm

end SDG.DifferentialForms
