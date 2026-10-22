import SDG.DifferentialForms.Algebra

/-!
# (R)：permSum 的右复合重排（分次交换律组装的缺失件）

目标：`permSum R (fun π => f (compose π σ)) = permSum R f`（σ 固定）。

路线（对 σ 用相邻对换分解）：
1. `encode_tailFun`：头部 `j`、尾部 `FinPerm.insertAt j ∘ h` 形状函数的编码
   = `cons (encode h) j`（cons-factoring）；
2. 清洁情形 `a ≥ 1` 的相邻对换：`(cons ρ j) ∘ swapPerm a b = cons (compose ρ s') j`
   （头部不动，尾部对换降一层）；
3. 清洁重排：对 n 归纳，`a ≥ 1` 时经 FinPerm.permSum_succ + 2 + IH（s' 在 n 层）；
4. 硬情形 `s01`（另行）：double coarea + `permSum_reindex_encode`
   （X = encode (Θ ∘ ρ'.toFun) 恰为左复合形状）。
-/

namespace SDG.DifferentialForms

section PermSumRightReindex

/-- 非 `0` 的 `Fin (n+1)` 元素是某个 `u.succ`。 -/
lemma fin_succ_of_ne_zero {n : ℕ} {t : Fin (n + 1)} (ht : ¬(t = 0)) :
    ∃ u : Fin n, u.succ = t :=
  ⟨Fin.mk ((t : ℕ) - 1) (by
      have h5 := t.isLt
      have h6 : (t : ℕ) ≠ 0 := fun hc => ht (Fin.ext hc)
      omega),
    Fin.ext (by
      have h5 := t.isLt
      have h6 : (t : ℕ) ≠ 0 := fun hc => ht (Fin.ext hc)
      show ((t : ℕ) - 1 + 1 : ℕ) = (t : ℕ)
      omega)⟩

/-- 尾部形状函数：`t = 0 ↦ j`，`t = u.succ ↦ insertAt j (h u)`。 -/
def tailFun {n : ℕ} (j : Fin (n + 1)) (h : Fin n → Fin n) : Fin (n + 1) → Fin (n + 1) :=
  fun t => dite (t = 0) (fun _ => j)
    (fun ht => FinPerm.insertAt j (h (Fin.mk ((t : ℕ) - 1) (by
      have ht2 := t.isLt; have h3 := ht; omega))))

lemma tailFun_zero {n : ℕ} (j : Fin (n + 1)) (h : Fin n → Fin n) :
    tailFun j h 0 = j := by
  unfold tailFun
  exact dif_pos rfl

lemma tailFun_succ {n : ℕ} (j : Fin (n + 1)) (h : Fin n → Fin n) (u : Fin n) :
    tailFun j h u.succ = FinPerm.insertAt j (h u) := by
  unfold tailFun
  rw [dif_neg (Fin.succ_ne_zero u)]
  exact congrArg (FinPerm.insertAt j) (congrArg h (Fin.ext (by
    simp only [Fin.val_succ]; omega)))

/-- `tailFun` 单射（`h` 单射时）：三分支点态。 -/
lemma tailFun_injective {n : ℕ} (j : Fin (n + 1)) (h : Fin n → Fin n)
    (hh : Function.Injective h) : Function.Injective (tailFun j h) := by
  intro t₁ t₂ hEq
  by_cases h1 : t₁ = 0
  · subst h1
    by_cases h2 : t₂ = 0
    · exact h2.symm
    · obtain ⟨u, hu⟩ := fin_succ_of_ne_zero h2
      rw [tailFun_zero, ← hu, tailFun_succ] at hEq
      exact absurd hEq.symm (FinPerm.insertAt_ne j (h u))
  · by_cases h2 : t₂ = 0
    · subst h2
      obtain ⟨u, hu⟩ := fin_succ_of_ne_zero h1
      rw [tailFun_zero, ← hu, tailFun_succ] at hEq
      exact absurd hEq (FinPerm.insertAt_ne j (h u))
    · obtain ⟨u, hu⟩ := fin_succ_of_ne_zero h1
      obtain ⟨v, hv⟩ := fin_succ_of_ne_zero h2
      rw [← hu, ← hv, tailFun_succ, tailFun_succ] at hEq
      have hcore : u = v := hh (FinPerm.insertAt_injective j hEq)
      rw [hcore] at hu
      exact hu.symm.trans hv

/-- **cons-factoring**：`tailFun j h` 的编码 = `cons (encode h) j`。 -/
lemma encode_tailFun {n : ℕ} (j : Fin (n + 1)) (h : Fin n → Fin n)
    (hh : Function.Injective h) :
    FinPerm.encode (tailFun j h) (tailFun_injective j h hh)
      = FinPerm.cons (FinPerm.encode h hh) j := by
  apply FinPerm.ext_toFun _ _
  have hEnc := FinPerm.toFun_encode (tailFun j h) (tailFun_injective j h hh)
  have hTail := FinPerm.toFun_encode h hh
  funext t
  cases t using Fin.cases with
  | zero => simp only [hEnc, tailFun_zero, FinPerm.toFun_cons_zero]
  | succ u => simp only [hEnc, tailFun_succ, FinPerm.toFun_cons_succ, hTail]

/-- **清洁右复合分解**：头部不动的相邻对换与 cons 置换的复合
= cons 保尾部对换降一层。 -/
lemma cons_compose_swapPerm_succ {n : ℕ} (ρ : FinPerm n) (j : Fin (n + 1))
    (m0 m1 : Fin n) (hm : (m0 : ℕ) + 1 = (m1 : ℕ)) :
    FinPerm.compose (FinPerm.cons ρ j)
        (FinPerm.swapPerm m0.succ m1.succ)
      = FinPerm.cons (FinPerm.compose ρ (FinPerm.swapPerm m0 m1)) j := by
  apply FinPerm.ext_toFun _ _
  rw [FinPerm.toFun_compose, FinPerm.toFun_swapPerm]
  funext t
  cases t using Fin.cases with
  | zero =>
      have hL : (FinPerm.cons ρ j).toFun (swapFin m0.succ m1.succ (0 : Fin (n + 1)))
          = j := by
        unfold swapFin
        rw [if_neg (fun hc => Fin.succ_ne_zero m0 (hc.symm)),
          if_neg (fun hc => Fin.succ_ne_zero m1 (hc.symm)),
          FinPerm.toFun_cons_zero]
      rw [hL, FinPerm.toFun_cons_zero]
  | succ u =>
      show (FinPerm.cons ρ j).toFun (swapFin m0.succ m1.succ u.succ)
        = (FinPerm.cons (FinPerm.compose ρ (FinPerm.swapPerm m0 m1)) j).toFun u.succ
      by_cases hua : u = m0
      · rw [hua]
        have hL : (FinPerm.cons ρ j).toFun (swapFin m0.succ m1.succ m0.succ)
            = FinPerm.insertAt j (ρ.toFun m1) := by
          unfold swapFin
          rw [if_pos rfl, FinPerm.toFun_cons_succ]
        have hR : (FinPerm.cons (FinPerm.compose ρ (FinPerm.swapPerm m0 m1)) j).toFun m0.succ
            = FinPerm.insertAt j (ρ.toFun m1) := by
          rw [FinPerm.toFun_cons_succ, FinPerm.toFun_compose, FinPerm.toFun_swapPerm]
          show FinPerm.insertAt j (ρ.toFun (swapFin m0 m1 m0))
            = FinPerm.insertAt j (ρ.toFun m1)
          unfold swapFin
          rw [if_pos rfl]
        rw [hL, hR]
      · by_cases hub : u = m1
        · rw [hub]
          have hL : (FinPerm.cons ρ j).toFun (swapFin m0.succ m1.succ m1.succ)
              = FinPerm.insertAt j (ρ.toFun m0) := by
            unfold swapFin
            rw [if_neg (show ¬((m1.succ : Fin (n + 1)) = m0.succ) from by
                intro hc
                have hv := congrArg Fin.val hc
                simp only [Fin.val_succ] at hv
                have h9 := m0.isLt
                omega),
              if_pos rfl, FinPerm.toFun_cons_succ]
          have hR : (FinPerm.cons (FinPerm.compose ρ (FinPerm.swapPerm m0 m1)) j).toFun
                m1.succ
              = FinPerm.insertAt j (ρ.toFun m0) := by
            rw [FinPerm.toFun_cons_succ, FinPerm.toFun_compose, FinPerm.toFun_swapPerm]
            show FinPerm.insertAt j (ρ.toFun (swapFin m0 m1 m1))
              = FinPerm.insertAt j (ρ.toFun m0)
            unfold swapFin
            rw [if_neg (show ¬((m1 : Fin n) = m0) from by
                intro hc
                have hv := congrArg Fin.val hc
                have h9 := m0.isLt
                omega),
              if_pos rfl]
          rw [hL, hR]
        · have hL : (FinPerm.cons ρ j).toFun (swapFin m0.succ m1.succ u.succ)
              = FinPerm.insertAt j (ρ.toFun u) := by
            unfold swapFin
            rw [if_neg (show ¬((u.succ : Fin (n + 1)) = m0.succ) from by
                intro hc
                have hv := congrArg Fin.val hc
                simp only [Fin.val_succ] at hv
                exact hua (Fin.ext (by omega))),
              if_neg (show ¬((u.succ : Fin (n + 1)) = m1.succ) from by
                intro hc
                have hv := congrArg Fin.val hc
                simp only [Fin.val_succ] at hv
                exact hub (Fin.ext (by omega))),
              FinPerm.toFun_cons_succ]
          have hR : (FinPerm.cons (FinPerm.compose ρ (FinPerm.swapPerm m0 m1)) j).toFun
                u.succ
              = FinPerm.insertAt j (ρ.toFun u) := by
            rw [FinPerm.toFun_cons_succ, FinPerm.toFun_compose, FinPerm.toFun_swapPerm]
            show FinPerm.insertAt j (ρ.toFun (swapFin m0 m1 u))
              = FinPerm.insertAt j (ρ.toFun u)
            unfold swapFin
            rw [if_neg (show ¬((u : Fin n) = m0) from hua),
              if_neg (show ¬((u : Fin n) = m1) from hub)]
          rw [hL, hR]

/-- **清洁重排步**：`a ≥ 1` 相邻对换的右复合 permSum 重排
（归纳步：cons 分解 + 尾部对换降层 + IH）。 -/
lemma permSum_compose_swap_succ_step {n : ℕ} (R : Type u) [CommRing R]
    (f : FinPerm (n + 2) → R) (m0 m1 : Fin (n + 1)) (hm : (m0 : ℕ) + 1 = (m1 : ℕ))
    (IH : ∀ (j : Fin (n + 2)) (a b : Fin (n + 1)), (a : ℕ) + 1 = (b : ℕ) →
      FinPerm.permSum R (fun ρ : FinPerm (n + 1) =>
          f (FinPerm.cons (FinPerm.compose ρ (FinPerm.swapPerm a b)) j))
        = FinPerm.permSum R (fun ρ : FinPerm (n + 1) => f (FinPerm.cons ρ j))) :
    FinPerm.permSum R (fun π : FinPerm (n + 2) =>
        f (FinPerm.compose π (FinPerm.swapPerm m0.succ m1.succ)))
      = FinPerm.permSum R f := by
  rw [FinPerm.permSum_succ R (n + 1) (fun π => f (FinPerm.compose π
      (FinPerm.swapPerm m0.succ m1.succ))),
    FinPerm.permSum_succ R (n + 1) f]
  refine finSum_congr R (fun j => ?_)
  rw [permSum_congr (fun ρ => congrArg f (cons_compose_swapPerm_succ ρ j m0 m1 hm)),
    IH j m0 m1 hm]

/-- 字面量 `1` 即 `0` 的后继（`if_pos rfl` 的桥）。 -/
lemma fin_one_eq_succ_zero {n : ℕ} :
    (1 : Fin (n + 2)) = Fin.succ (0 : Fin (n + 1)) := rfl

/-- **P1 双重插入换序**：先在 `k` 后在 `j` 插入 = 先在 `X₀` 后在 `m` 插入
（`m = insertAt j k`，`X₀ = unshift m j`）。 -/
lemma insertAt_insertAt_comm {n : ℕ} (j : Fin (n + 2)) (k : Fin (n + 1)) (x : Fin n) :
    FinPerm.insertAt j (FinPerm.insertAt k x)
      = FinPerm.insertAt (FinPerm.insertAt j k)
          (FinPerm.insertAt
            (FinPerm.unshift (FinPerm.insertAt j k) j
              (fun hc => FinPerm.insertAt_ne j k (hc.symm))) x) := by
  have hj := j.isLt
  have hk := k.isLt
  have hx := x.isLt
  apply Fin.ext
  simp only [FinPerm.insertAt_val,
    unshift_val_eq (FinPerm.insertAt j k) j
      (fun hc => FinPerm.insertAt_ne j k (hc.symm))]
  split_ifs <;> omega

/-- **s01 点态分解（硬情形核心）**：双层 cons 置换与 `s01` 的右复合
= 双层 cons 保 `ρ'` 换头（`(P1)` + `insertAt_unshift`）。 -/
lemma consCons_compose_swap01 {n : ℕ} (ρ' : FinPerm n) (k : Fin (n + 1))
    (j : Fin (n + 2)) :
    FinPerm.compose (FinPerm.cons (FinPerm.cons ρ' k) j)
        (FinPerm.swapPerm (0 : Fin (n + 2)) (1 : Fin (n + 2)))
      = FinPerm.cons (FinPerm.cons ρ'
          (FinPerm.unshift (FinPerm.insertAt j k) j
            (fun hc => FinPerm.insertAt_ne j k (hc.symm))))
          (FinPerm.insertAt j k) := by
  apply FinPerm.ext_toFun _ _
  rw [FinPerm.toFun_compose, FinPerm.toFun_swapPerm]
  funext t
  cases t using Fin.cases with
  | zero =>
      have hsw : swapFin (0 : Fin (n + 2)) (1 : Fin (n + 2)) (0 : Fin (n + 2))
          = Fin.succ (0 : Fin (n + 1)) := by
        unfold swapFin
        rw [fin_one_eq_succ_zero, if_pos rfl]
      rw [hsw, FinPerm.toFun_cons_succ, FinPerm.toFun_cons_zero,
        FinPerm.toFun_cons_zero]
  | succ u =>
      by_cases hu : u = 0
      · rw [hu]
        have hsw : swapFin (0 : Fin (n + 2)) (1 : Fin (n + 2))
            ((0 : Fin (n + 1)).succ) = (0 : Fin (n + 2)) := by
          unfold swapFin
          rw [if_neg (Fin.succ_ne_zero (0 : Fin (n + 1))),
            if_pos (by rw [fin_one_eq_succ_zero])]
        rw [hsw, FinPerm.toFun_cons_zero, FinPerm.toFun_cons_succ,
          FinPerm.toFun_cons_zero, FinPerm.insertAt_unshift]
      · obtain ⟨v, hv⟩ := fin_succ_of_ne_zero hu
        have hsw : swapFin (0 : Fin (n + 2)) (1 : Fin (n + 2)) u.succ = u.succ := by
          unfold swapFin
          rw [if_neg (Fin.succ_ne_zero u),
            if_neg (show ¬(u.succ = (1 : Fin (n + 2))) from by
              intro hc
              rw [fin_one_eq_succ_zero] at hc
              have hv2 := congrArg Fin.val hc
              simp only [Fin.val_succ] at hv2
              have h9 := u.isLt
              omega)]
        rw [hsw, FinPerm.toFun_cons_succ, ← hv, FinPerm.toFun_cons_succ,
          FinPerm.toFun_cons_succ, FinPerm.toFun_cons_succ]
        exact insertAt_insertAt_comm j k (ρ'.toFun v)

/-- **SLICE-A**：上三角指示子区域的坐标化重排（`a = k.succ`，`j = c`）。 -/
lemma finSum_slice_A {n : ℕ} (R : Type u) [AddCommMonoid R]
    (T : Fin (n + 1) → Fin (n + 2) → R) :
    finSum R (n + 2) (fun a => finSum R (n + 1) (fun c =>
        if (c : ℕ) < (a : ℕ) then T c a else 0))
      = finSum R (n + 1) (fun j => finSum R (n + 1) (fun k =>
        if (j : ℕ) ≤ (k : ℕ) then T j (Fin.succ k) else 0)) := by
  rw [finSum_succ R (n + 1) (fun a => finSum R (n + 1) (fun c =>
      if (c : ℕ) < (a : ℕ) then T c a else 0))]
  rw [Fin.val_zero]
  rw [finSum_eq_zero R (fun c => if_neg (Nat.not_lt_zero (c : ℕ)))]
  rw [zero_add]
  rw [finSum_sum_comm R (n + 1) (n + 1) (fun k => fun c =>
      if (c : ℕ) < ((Fin.succ k : Fin (n + 2)) : ℕ) then T c (Fin.succ k) else 0)]
  refine finSum_congr R (fun j => finSum_congr R (fun k => ?_))
  by_cases h : (j : ℕ) ≤ (k : ℕ)
  · rw [if_pos h, if_pos (show ((j : ℕ) < ((Fin.succ k : Fin (n + 2)) : ℕ)) from by
      simp only [Fin.val_succ]; omega)]
  · rw [if_neg h, if_neg (show ¬(((j : ℕ) < ((Fin.succ k : Fin (n + 2)) : ℕ))) from by
      simp only [Fin.val_succ]; omega)]

/-- **SLICE-B**：下三角含对角指示子区域的坐标化重排（`a = castSucc k`）。 -/
lemma finSum_slice_B {n : ℕ} (R : Type u) [AddCommMonoid R]
    (T : Fin (n + 1) → Fin (n + 2) → R) :
    finSum R (n + 2) (fun a => finSum R (n + 1) (fun c =>
        if (a : ℕ) ≤ (c : ℕ) then T c a else 0))
      = finSum R (n + 1) (fun c => finSum R (n + 1) (fun k =>
        if (k : ℕ) ≤ (c : ℕ) then T c (Fin.castSucc k) else 0)) := by
  rw [finSum_last R (n + 1) (fun a => finSum R (n + 1) (fun c =>
      if (a : ℕ) ≤ (c : ℕ) then T c a else 0))]
  have hlast : (finSum R (n + 1) (fun c =>
      if ((((Fin.last (n + 1) : Fin (n + 2))) : ℕ)) ≤ ((c : Fin (n + 1)) : ℕ)
        then T c (Fin.last (n + 1)) else 0) : R) = 0 := by
    rw [finSum_eq_zero R (fun c => if_neg (by
      have h1 := c.isLt
      simp only [Fin.val_last] at *
      omega))]
  rw [hlast, add_zero]
  rw [finSum_sum_comm R (n + 1) (n + 1) (fun k => fun c =>
      if ((((Fin.castSucc k : Fin (n + 2)) : ℕ)) ≤ ((c : Fin (n + 1)) : ℕ))
        then T c (Fin.castSucc k) else 0)]
  refine finSum_congr R (fun c => finSum_congr R (fun k => ?_))
  by_cases h : (k : ℕ) ≤ (c : ℕ)
  · rw [if_pos h, if_pos (show ((((Fin.castSucc k : Fin (n + 2)) : ℕ))
        ≤ ((c : Fin (n + 1)) : ℕ)) from by
      simp only [Fin.val_castSucc]; omega)]
  · rw [if_neg h, if_neg (show ¬((((Fin.castSucc k : Fin (n + 2)) : ℕ))
        ≤ ((c : Fin (n + 1)) : ℕ)) from by
      simp only [Fin.val_castSucc]; omega)]

/-- s01 求和项（组装用缩写）。 -/
def s01Term {n : ℕ} (R : Type u) [CommRing R] (f : FinPerm (n + 2) → R)
    (j : Fin (n + 2)) (k : Fin (n + 1)) : R :=
  FinPerm.permSum R (fun ρ' : FinPerm n =>
    f (FinPerm.cons (FinPerm.cons ρ'
        (FinPerm.unshift (FinPerm.insertAt j k) j
          (fun hc => FinPerm.insertAt_ne j k (hc.symm))))
      (FinPerm.insertAt j k)))

/-- A 桥：`c ≤ k` 时（`j = castSucc c`）`(m, X₀) = (k.succ, c)`。 -/
lemma s01Term_cast {n : ℕ} (R : Type u) [CommRing R] (f : FinPerm (n + 2) → R)
    (c k : Fin (n + 1)) (h : (c : ℕ) ≤ (k : ℕ)) :
    s01Term R f (Fin.castSucc c) k
      = FinPerm.permSum R (fun d : FinPerm n =>
          f (FinPerm.cons (FinPerm.cons d c) (Fin.succ k))) := by
  have hm : FinPerm.insertAt (Fin.castSucc c) k = Fin.succ k := by
    apply Fin.ext
    rw [FinPerm.insertAt_val, Fin.val_castSucc, Fin.val_succ,
      if_neg (show ¬((k : ℕ) < (c : ℕ)) from by omega)]
  have hx : FinPerm.unshift (FinPerm.insertAt (Fin.castSucc c) k) (Fin.castSucc c)
        (fun hc => FinPerm.insertAt_ne (Fin.castSucc c) k (hc.symm)) = c := by
    apply Fin.ext
    rw [unshift_val_eq _ _ (fun hc => FinPerm.insertAt_ne (Fin.castSucc c) k (hc.symm)),
      FinPerm.insertAt_val, Fin.val_castSucc]
    split_ifs <;> omega
  show FinPerm.permSum R (fun ρ' : FinPerm n =>
      f (FinPerm.cons (FinPerm.cons ρ'
          (FinPerm.unshift (FinPerm.insertAt (Fin.castSucc c) k) (Fin.castSucc c)
            (fun hc => FinPerm.insertAt_ne (Fin.castSucc c) k (hc.symm))))
        (FinPerm.insertAt (Fin.castSucc c) k)))
    = FinPerm.permSum R (fun d : FinPerm n =>
        f (FinPerm.cons (FinPerm.cons d c) (Fin.succ k)))
  rw [hx, hm]

/-- B 桥：`k ≤ c` 时（`j = succ c`）`(m, X₀) = (castSucc k, c)`。 -/
lemma s01Term_succL {n : ℕ} (R : Type u) [CommRing R] (f : FinPerm (n + 2) → R)
    (c k : Fin (n + 1)) (h : (k : ℕ) ≤ (c : ℕ)) :
    s01Term R f (Fin.succ c) k
      = FinPerm.permSum R (fun d : FinPerm n =>
          f (FinPerm.cons (FinPerm.cons d c) (Fin.castSucc k))) := by
  have hm : FinPerm.insertAt (Fin.succ c) k = Fin.castSucc k := by
    apply Fin.ext
    rw [FinPerm.insertAt_val, Fin.val_succ, Fin.val_castSucc, if_pos (by omega)]
  have hx : FinPerm.unshift (FinPerm.insertAt (Fin.succ c) k) (Fin.succ c)
        (fun hc => FinPerm.insertAt_ne (Fin.succ c) k (hc.symm)) = c := by
    apply Fin.ext
    rw [unshift_val_eq _ _ (fun hc => FinPerm.insertAt_ne (Fin.succ c) k (hc.symm)),
      FinPerm.insertAt_val, Fin.val_succ]
    split_ifs <;> omega
  show FinPerm.permSum R (fun ρ' : FinPerm n =>
      f (FinPerm.cons (FinPerm.cons ρ'
          (FinPerm.unshift (FinPerm.insertAt (Fin.succ c) k) (Fin.succ c)
            (fun hc => FinPerm.insertAt_ne (Fin.succ c) k (hc.symm))))
        (FinPerm.insertAt (Fin.succ c) k)))
    = FinPerm.permSum R (fun d : FinPerm n =>
        f (FinPerm.cons (FinPerm.cons d c) (Fin.castSucc k)))
  rw [hx, hm]

/-- A 逐点桥（两侧具体，供 finSum_congr 使用）。 -/
lemma s01Term_slice_pointwise_A {n : ℕ} (R : Type u) [CommRing R]
    (f : FinPerm (n + 2) → R) (c k : Fin (n + 1)) :
    (if ((Fin.castSucc c : Fin (n + 2)) : ℕ) ≤ (k : ℕ) then
          s01Term R f (Fin.castSucc c) k else 0)
      = (if (c : ℕ) ≤ (k : ℕ) then FinPerm.permSum R (fun d : FinPerm n =>
            f (FinPerm.cons (FinPerm.cons d c) (Fin.succ k))) else 0) := by
  by_cases h : (c : ℕ) ≤ (k : ℕ)
  · rw [if_pos (show ((Fin.castSucc c : Fin (n + 2)) : ℕ) ≤ (k : ℕ) from by
        simp only [Fin.val_castSucc]; omega), if_pos h, s01Term_cast R f c k h]
  · rw [if_neg (show ¬(((Fin.castSucc c : Fin (n + 2)) : ℕ) ≤ (k : ℕ)) from by
        simp only [Fin.val_castSucc]; omega), if_neg h]

/-- B 逐点桥（两侧具体，供 finSum_congr 使用）。 -/
lemma s01Term_slice_pointwise_B {n : ℕ} (R : Type u) [CommRing R]
    (f : FinPerm (n + 2) → R) (c k : Fin (n + 1)) :
    (if (k : ℕ) < ((Fin.succ c : Fin (n + 2)) : ℕ) then
          s01Term R f (Fin.succ c) k else 0)
      = (if (k : ℕ) ≤ (c : ℕ) then FinPerm.permSum R (fun d : FinPerm n =>
            f (FinPerm.cons (FinPerm.cons d c) (Fin.castSucc k))) else 0) := by
  by_cases h : (k : ℕ) ≤ (c : ℕ)
  · rw [if_pos (show (k : ℕ) < (Fin.succ c : Fin (n + 2)) from by
        simp only [Fin.val_succ]; omega), if_pos h, s01Term_succL R f c k h]
  · rw [if_neg (show ¬((k : ℕ) < (Fin.succ c : Fin (n + 2))) from by
        simp only [Fin.val_succ]; omega), if_neg h]

/-- **s01 硬情形重排主引理**：与 `s01` 的右复合不改变 permSum。 -/
lemma permSum_compose_swap01 {n : ℕ} (R : Type u) [CommRing R]
    (f : FinPerm (n + 2) → R) :
    FinPerm.permSum R (fun π : FinPerm (n + 2) =>
        f (FinPerm.compose π (FinPerm.swapPerm (0 : Fin (n + 2)) (1 : Fin (n + 2)))))
      = FinPerm.permSum R f := by
  -- 目标侧：双 succ + 指示子拆分 + SLICE
  have hsuccT : ∀ a : Fin (n + 2),
      FinPerm.permSum R (fun b : FinPerm (n + 1) => f (FinPerm.cons b a))
        = finSum R (n + 1) (fun c => FinPerm.permSum R (fun d : FinPerm n =>
            f (FinPerm.cons (FinPerm.cons d c) a))) :=
    fun a => FinPerm.permSum_succ R n (fun b : FinPerm (n + 1) => f (FinPerm.cons b a))
  have hsplT : ∀ (a : Fin (n + 2)) (c : Fin (n + 1)),
      FinPerm.permSum R (fun d : FinPerm n => f (FinPerm.cons (FinPerm.cons d c) a))
        = (if (c : ℕ) < (a : ℕ) then
              FinPerm.permSum R (fun d : FinPerm n =>
                f (FinPerm.cons (FinPerm.cons d c) a)) else 0)
          + (if (a : ℕ) ≤ (c : ℕ) then
              FinPerm.permSum R (fun d : FinPerm n =>
                f (FinPerm.cons (FinPerm.cons d c) a)) else 0) := by
    intro a c
    by_cases h : (c : ℕ) < (a : ℕ)
    · rw [if_pos h, if_neg (by omega), add_zero]
    · rw [if_neg h]
      by_cases h2 : (a : ℕ) ≤ (c : ℕ)
      · rw [if_pos h2, zero_add]
      · exact absurd (show (c : ℕ) < (a : ℕ) from by omega) h
  rw [FinPerm.permSum_succ R (n + 1) f, finSum_congr R hsuccT,
    finSum_congr R (fun a => finSum_congr R (hsplT a))]
  simp only [finSum_add]
  rw [finSum_slice_A R (fun c a => FinPerm.permSum R (fun d : FinPerm n =>
      f (FinPerm.cons (FinPerm.cons d c) a))),
    finSum_slice_B R (fun c a => FinPerm.permSum R (fun d : FinPerm n =>
      f (FinPerm.cons (FinPerm.cons d c) a)))]
  -- LHS 侧：双 succ + consCons 分解 + s01Term 折叠
  have hsuccL : ∀ j : Fin (n + 2),
      FinPerm.permSum R (fun ρ : FinPerm (n + 1) =>
          f (FinPerm.compose (FinPerm.cons ρ j)
              (FinPerm.swapPerm (0 : Fin (n + 2)) (1 : Fin (n + 2)))))
        = finSum R (n + 1) (fun k => FinPerm.permSum R (fun ρ' : FinPerm n =>
            f (FinPerm.compose (FinPerm.cons (FinPerm.cons ρ' k) j)
                (FinPerm.swapPerm (0 : Fin (n + 2)) (1 : Fin (n + 2)))))) :=
    fun j => FinPerm.permSum_succ R n (fun ρ : FinPerm (n + 1) =>
      f (FinPerm.compose (FinPerm.cons ρ j)
          (FinPerm.swapPerm (0 : Fin (n + 2)) (1 : Fin (n + 2)))))
  rw [FinPerm.permSum_succ R (n + 1) (fun π => f (FinPerm.compose π
      (FinPerm.swapPerm (0 : Fin (n + 2)) (1 : Fin (n + 2))))),
    finSum_congr R hsuccL,
    finSum_congr R (fun j => finSum_congr R (fun k => permSum_congr
      (fun ρ' => congrArg f (consCons_compose_swap01 ρ' k j)))),
    finSum_congr R (fun j => show finSum R (n + 1) (fun k =>
        FinPerm.permSum R (fun ρ' : FinPerm n =>
          f (FinPerm.cons (FinPerm.cons ρ'
              (FinPerm.unshift (FinPerm.insertAt j k) j
                (fun hc => FinPerm.insertAt_ne j k (hc.symm))))
            (FinPerm.insertAt j k))))
      = finSum R (n + 1) (fun k => s01Term R f j k) from rfl)]
  -- LHS 指示子拆分
  have hsplL : ∀ (j : Fin (n + 2)) (k : Fin (n + 1)),
      s01Term R f j k
        = (if (j : ℕ) ≤ (k : ℕ) then s01Term R f j k else 0)
          + (if (k : ℕ) < (j : ℕ) then s01Term R f j k else 0) := by
    intro j k
    by_cases h : (j : ℕ) ≤ (k : ℕ)
    · rw [if_pos h, if_neg (by omega), add_zero]
    · rw [if_neg h, if_pos (by omega), zero_add]
  rw [finSum_congr R (fun j => finSum_congr R (hsplL j))]
  simp only [finSum_add]
  -- A 半边：last-剥皮（last ≤ k 恒假）
  rw [finSum_last R (n + 1) (fun j => finSum R (n + 1) (fun k =>
      if (j : ℕ) ≤ (k : ℕ) then s01Term R f j k else 0))]
  rw [finSum_eq_zero R (fun k => if_neg (show ¬(((Fin.last (n + 1) : Fin (n + 2)) : ℕ)
      ≤ (k : ℕ)) from by
    have h1 := k.isLt
    simp only [Fin.val_last]
    omega)), add_zero]
  -- B 半边：succ-剥皮（k < 0 恒假）
  rw [finSum_succ R (n + 1) (fun j => finSum R (n + 1) (fun k =>
      if (k : ℕ) < (j : ℕ) then s01Term R f j k else 0))]
  rw [Fin.val_zero,
    finSum_eq_zero R (fun k => if_neg (Nat.not_lt_zero (k : ℕ))), zero_add]
  -- A/B 桥
  rw [finSum_congr R (fun c => finSum_congr R (fun k =>
      s01Term_slice_pointwise_A R f c k)),
    finSum_congr R (fun c => finSum_congr R (fun k =>
      s01Term_slice_pointwise_B R f c k))]

/-- FinPerm 复合的结合律。 -/
lemma compose_assoc {n : ℕ} (π₁ π₂ π₃ : FinPerm n) :
    FinPerm.compose π₁ (FinPerm.compose π₂ π₃)
      = FinPerm.compose (FinPerm.compose π₁ π₂) π₃ := by
  apply FinPerm.ext_toFun _ _
  rw [FinPerm.toFun_compose, FinPerm.toFun_compose, FinPerm.toFun_compose,
    FinPerm.toFun_compose]

/-- succ-mk 还原：非零的 `x` 是 `x-1` 的后继。 -/
lemma fin_succ_mk_eq {n : ℕ} {x : Fin (n + 2)} (hx : (x : ℕ) ≥ 1) :
    Fin.succ (Fin.mk ((x : ℕ) - 1) (by have h1 := x.isLt; omega)) = x := by
  apply Fin.ext
  show ((Fin.succ (Fin.mk ((x : ℕ) - 1) (by have h1 := x.isLt; omega)) :
      Fin (n + 1 + 1)) : ℕ) = (x : ℕ)
  simp only [Fin.val_succ, Fin.val_mk]
  have h1 := x.isLt
  omega

/-- 任意相邻对换的右复合重排（对 N 归纳，层级 N+2）：与任意相邻对换的
右复合不改变 permSum。 -/
lemma permSum_compose_swapPerm (R : Type u) [CommRing R] :
    ∀ (N : ℕ) (f : FinPerm (N + 2) → R) (a b : Fin (N + 2)), (a : ℕ) + 1 = (b : ℕ) →
      FinPerm.permSum R (fun π : FinPerm (N + 2) =>
          f (FinPerm.compose π (FinPerm.swapPerm a b)))
        = FinPerm.permSum R f := by
  intro N
  induction N with
  | zero =>
      intro f a b h
      have ha : a = (0 : Fin 2) := Fin.ext (by
        show (a : ℕ) = 0
        have h1 := a.isLt
        have h2 := b.isLt
        omega)
      have hb : b = (1 : Fin 2) := Fin.ext (by
        show (b : ℕ) = 1
        have h1 := a.isLt
        have h2 := b.isLt
        omega)
      rw [ha, hb]
      exact permSum_compose_swap01 R f
  | succ N ih =>
      intro f a b h
      by_cases ha : (a : ℕ) = 0
      · -- s01 情形（层级 (N+1)+2，泛 n 版直接用）
        have h0 : a = (0 : Fin (N + 3)) := Fin.ext ha
        have hb : b = (1 : Fin (N + 3)) := Fin.ext (by
          have h1 := b.isLt
          have hv0 : ((0 : Fin (N + 3)) : ℕ) = 0 := rfl
          rw [h0] at h
          rw [hv0] at h
          show (b : ℕ) = 1
          omega)
        rw [h0, hb]
        exact permSum_compose_swap01 R f
      · -- 清洁情形：obtain 型构造（避免 have-fvar 不透明）
        have hbv : (b : ℕ) = (a : ℕ) + 1 := by omega
        obtain ⟨m0, ha0⟩ : ∃ m0 : Fin (N + 1 + 1), Fin.succ m0 = a :=
          ⟨Fin.mk ((a : ℕ) - 1) (by have h1 := a.isLt; have h3 := b.isLt; have h4 := hbv; omega),
            fin_succ_mk_eq (by have h1 := a.isLt; have h3 := b.isLt; have h4 := hbv; omega)⟩
        have hv : (m0 : ℕ) + 1 = (a : ℕ) := by
          have hv2 := congrArg Fin.val ha0
          simp only [Fin.val_succ] at hv2
          exact hv2
        obtain ⟨m1, hm1⟩ : ∃ m1 : Fin (N + 1 + 1), (m0 : ℕ) + 1 = (m1 : ℕ) :=
          ⟨Fin.mk ((m0 : ℕ) + 1) (by
              have h1 := b.isLt
              have h2 := hbv
              omega),
            by simp only [Fin.val_mk]⟩
        have hb0 : Fin.succ m1 = b := by
          apply Fin.ext
          show ((Fin.succ m1 : Fin (N + 1 + 2)) : ℕ) = (b : ℕ)
          have h1 := b.isLt
          have hmk : (m1 : ℕ) = (m0 : ℕ) + 1 := hm1.symm
          simp only [Fin.val_succ]
          omega
        rw [← ha0, ← hb0]
        refine permSum_compose_swap_succ_step R f m0 m1 hm1 ?_
        intro j a' b' h'
        exact ih (fun ρ : FinPerm (N + 1 + 1) => f (FinPerm.cons ρ j)) a' b' h'

/-- 单步右复合换序：先过相邻对换再复合 σ = 先复合 σ 再过相邻对换。 -/
lemma permSum_compose_swap_step {n : ℕ} (R : Type u) [CommRing R]
    (Φ : FinPerm (n + 2) → R) (σ : FinPerm (n + 2)) (a b : Fin (n + 2))
    (h : (a : ℕ) + 1 = (b : ℕ)) :
    FinPerm.permSum R (fun π => Φ (FinPerm.compose π
        (FinPerm.compose (FinPerm.swapPerm a b) σ)))
      = FinPerm.permSum R (fun π => Φ (FinPerm.compose π σ)) := by
  have hpoint : ∀ π : FinPerm (n + 2),
      Φ (FinPerm.compose π (FinPerm.compose (FinPerm.swapPerm a b) σ))
        = Φ (FinPerm.compose (FinPerm.compose π (FinPerm.swapPerm a b)) σ) := by
    intro π
    rw [compose_assoc]
  rw [permSum_congr hpoint]
  exact permSum_compose_swapPerm (R := R) (N := n)
    (fun τ => Φ (FinPerm.compose τ σ)) a b h

/-- encode 复合引理：编码级复合 = FinPerm 复合。 -/
lemma encode_compose_encode {n : ℕ} (g : Fin n → Fin n) (hg : Function.Injective g)
    (h : Fin n → Fin n) (hh : Function.Injective h) :
    FinPerm.compose (FinPerm.encode g hg) (FinPerm.encode h hh)
      = FinPerm.encode (g ∘ h) (hg.comp hh) := by
  apply FinPerm.ext_toFun _ _
  rw [FinPerm.toFun_compose, FinPerm.toFun_encode, FinPerm.toFun_encode,
    FinPerm.toFun_encode]
  rfl

/-- 循环左移的 FinPerm 编码。 -/
def cycLperm {n : ℕ} (s p : ℕ) (hsp : s + p < n) : FinPerm n :=
  FinPerm.encode (cycLfun s p hsp) (cycLfun_injective p s hsp)

/-- cycLperm 的相邻对换分解（succ 步：swap 在最外层）。 -/
lemma cycLperm_succ {n : ℕ} (s p : ℕ) (hsp : s + (p + 1) < n) :
    cycLperm s (p + 1) hsp
      = FinPerm.compose
          (FinPerm.swapPerm (Fin.mk (s + p) (by omega : (s + p : ℕ) < n))
            (Fin.mk (s + p + 1) hsp))
          (cycLperm s p (by omega : (s + p : ℕ) < n)) := by
  apply FinPerm.ext_toFun _ _
  show (FinPerm.encode (cycLfun s (p + 1) hsp)
      (cycLfun_injective (p + 1) s hsp)).toFun
    = (FinPerm.compose
        (FinPerm.encode (swapFin (Fin.mk (s + p) (by omega : (s + p : ℕ) < n))
          (Fin.mk (s + p + 1) hsp))
          (swapFin_injective (Fin.mk (s + p) (by omega : (s + p : ℕ) < n))
            (Fin.mk (s + p + 1) hsp)))
        (FinPerm.encode (cycLfun s p (by omega : (s + p : ℕ) < n))
          (cycLfun_injective p s (by omega : (s + p : ℕ) < n)))).toFun
  rw [FinPerm.toFun_encode, FinPerm.toFun_compose, FinPerm.toFun_encode,
    FinPerm.toFun_encode, cycLfun_succ hsp]
  rfl

/-- 块交换的 FinPerm 编码。 -/
def bsPerm {n : ℕ} (q p : ℕ) (hsp : q + p ≤ n) : FinPerm n :=
  FinPerm.encode (bsFunV q p hsp) (bsFunV_injective hsp)

/-- bsPerm 的递推（succ 步）。 -/
lemma bsPerm_succ {n : ℕ} (q p : ℕ) (hsp : (q + 1) + p ≤ n) :
    bsPerm (q + 1) p hsp
      = FinPerm.compose (bsPerm q p (show q + p ≤ n from by omega))
          (cycLperm q p (show q + p < n from by omega)) := by
  apply FinPerm.ext_toFun _ _
  show (FinPerm.encode (bsFunV (q + 1) p hsp) (bsFunV_injective hsp)).toFun
    = (FinPerm.compose
        (FinPerm.encode (bsFunV q p (show q + p ≤ n from by omega))
          (bsFunV_injective (show q + p ≤ n from by omega)))
        (FinPerm.encode (cycLfun q p (show q + p < n from by omega))
          (cycLfun_injective p q (show q + p < n from by omega)))).toFun
  rw [FinPerm.toFun_encode, FinPerm.toFun_compose, FinPerm.toFun_encode,
    FinPerm.toFun_encode, bsFunV_succ_left hsp]
  rfl

/-- bsPerm 在 q = 0 时是恒等。 -/
lemma bsPerm_zero {n : ℕ} (p : ℕ) (hsp : (0 : ℕ) + p ≤ n) :
    bsPerm 0 p hsp = FinPerm.identity := by
  show FinPerm.encode (bsFunV 0 p hsp) (bsFunV_injective hsp) = FinPerm.identity
  apply FinPerm.ext_toFun _ _
  rw [FinPerm.toFun_encode, FinPerm.toFun_identity]
  funext k
  have hid : bsFunV 0 p hsp = id := by
    funext t
    by_cases h1 : (t : ℕ) < p
    · have hv : bsFunV 0 p hsp t
          = (Fin.mk ((t : ℕ) - 0) (by have ht := t.isLt; omega) : Fin n) :=
        bsFunV_back hsp (by omega) (by omega)
      rw [hv]
      simp only [Fin.val_mk, Nat.sub_zero]
      exact Fin.ext (by simp only [Fin.val_mk, id_eq])
    · exact bsFunV_out hsp (by omega)
  rw [hid, id_eq]

/-- cycLperm 外层链剥除（含尾接 τ）：r 归纳 + swap_step 逐层剥相邻对换。 -/
lemma permSum_compose_cycL_outer_gen {n : ℕ} (R : Type u) [CommRing R] :
    ∀ (r : ℕ) (s : ℕ) (hsp : s + r < n + 2), ∀ (τ : FinPerm (n + 2))
      (G : FinPerm (n + 2) → R),
      FinPerm.permSum R (fun π => G (FinPerm.compose π
          (FinPerm.compose (cycLperm s r hsp) τ)))
        = FinPerm.permSum R (fun π => G (FinPerm.compose π τ)) := by
  set_option maxHeartbeats 2000000 in
  intro r
  induction r with
  | zero =>
      intro s hsp τ G
      have hid : cycLperm s 0 hsp = FinPerm.identity := by
        unfold cycLperm
        apply FinPerm.ext_toFun _ _
        rw [FinPerm.toFun_encode, FinPerm.toFun_identity]
        funext k
        show cycLfun s 0 hsp k = id k
        by_cases h1 : (k : ℕ) = s
        · rw [cycLfun_left hsp h1]
          exact Fin.ext (by
            simp only [Fin.val_mk, Nat.add_zero]
            exact h1.symm)
        · rw [cycLfun_out hsp h1 (by have h3 := k.isLt; omega)]
          rfl
      rw [hid, FinPerm.compose_identity_left]
  | succ r ih =>
      intro s hsp τ G
      have hsp2 : s + r < n + 2 := by omega
      have hpoint1 : ∀ π : FinPerm (n + 2),
          G (FinPerm.compose π (FinPerm.compose (cycLperm s (r + 1) hsp) τ))
            = G (FinPerm.compose π (FinPerm.compose
                (FinPerm.compose (FinPerm.swapPerm (Fin.mk (s + r) (by omega : (s + r : ℕ) < n + 2))
                  (Fin.mk (s + r + 1) hsp)) (cycLperm s r hsp2)) τ)) := by
        intro π
        rw [cycLperm_succ s r hsp]
      have hpoint2 : ∀ π : FinPerm (n + 2),
          G (FinPerm.compose π (FinPerm.compose
              (FinPerm.compose (FinPerm.swapPerm (Fin.mk (s + r) (by omega : (s + r : ℕ) < n + 2))
                (Fin.mk (s + r + 1) hsp)) (cycLperm s r hsp2)) τ))
            = G (FinPerm.compose π (FinPerm.compose (FinPerm.swapPerm
                (Fin.mk (s + r) (by omega : (s + r : ℕ) < n + 2))
                (Fin.mk (s + r + 1) hsp)) (FinPerm.compose (cycLperm s r hsp2) τ))) := by
        intro π
        rw [← compose_assoc (FinPerm.swapPerm (Fin.mk (s + r) (by omega : (s + r : ℕ) < n + 2))
          (Fin.mk (s + r + 1) hsp)) (cycLperm s r hsp2)]
      rw [permSum_congr hpoint1]
      rw [permSum_congr hpoint2]
      rw [permSum_compose_swap_step R G
        (FinPerm.compose (cycLperm s r hsp2) τ)
        (Fin.mk (s + r) (by omega : (s + r : ℕ) < n + 2))
        (Fin.mk (s + r + 1) hsp)
        (by simp only [Fin.val_mk, Fin.val_succ])]
      exact ih s hsp2 τ G

set_option maxHeartbeats 8000000 in
/-- **(R) 块交换链引理（尾巴泛化）**：前缀 bsPerm 可逐层剥除——
IH 平移 G（G' := fun ρ => G (ρ ∘ cycLperm)）+ cycL_outer_gen 剥内层 cycL 链。 -/
lemma permSum_compose_bsPerm_gen {n : ℕ} (R : Type u) [CommRing R] :
    ∀ (k : ℕ) (p : ℕ) (hsp : k + p ≤ n + 2), ∀ (tail : FinPerm (n + 2))
      (G : FinPerm (n + 2) → R),
      FinPerm.permSum R (fun π => G (FinPerm.compose π
          (FinPerm.compose (bsPerm k p hsp) tail)))
        = FinPerm.permSum R (fun π => G (FinPerm.compose π tail)) := by
  intro k
  induction k with
  | zero =>
      intro p hsp tail G
      rw [bsPerm_zero p hsp, FinPerm.compose_identity_left]
  | succ k ih =>
      intro p hsp tail G
      have hle : k + p ≤ n + 2 := by omega
      have hlt : k + p < n + 2 := by omega
      have hp1 : ∀ π : FinPerm (n + 2),
          G (FinPerm.compose π (FinPerm.compose (bsPerm (k + 1) p hsp) tail))
            = G (FinPerm.compose (FinPerm.compose π (bsPerm (k + 1) p hsp)) tail) := by
        intro π
        rw [compose_assoc]
      have hp2 : ∀ π : FinPerm (n + 2),
          G (FinPerm.compose (FinPerm.compose π (bsPerm (k + 1) p hsp)) tail)
            = G (FinPerm.compose (FinPerm.compose π
                (FinPerm.compose (bsPerm k p hle) (cycLperm k p hlt))) tail) := by
        intro π
        rw [bsPerm_succ k p hsp]
      have hp3 : ∀ π : FinPerm (n + 2),
          G (FinPerm.compose (FinPerm.compose π
              (FinPerm.compose (bsPerm k p hle) (cycLperm k p hlt))) tail)
            = G (FinPerm.compose π (FinPerm.compose (bsPerm k p hle)
                (FinPerm.compose (cycLperm k p hlt) tail))) := by
        intro π
        rw [← compose_assoc π
          (FinPerm.compose (bsPerm k p hle) (cycLperm k p hlt)) tail,
          ← compose_assoc (bsPerm k p hle) (cycLperm k p hlt) tail]
      have hih := ih p hle (FinPerm.compose (cycLperm k p hlt) tail) G
      have hout := permSum_compose_cycL_outer_gen R p k hlt tail G
      rw [permSum_congr hp1]
      rw [permSum_congr hp2]
      rw [permSum_congr hp3]
      exact hih.trans hout

/-- **(R) 块交换主引理**：与块交换的右复合不改变 permSum。 -/
lemma permSum_compose_bsPerm {n : ℕ} (R : Type u) [CommRing R] :
    ∀ (k : ℕ) (p : ℕ) (hsp : k + p ≤ n + 2), ∀ (G : FinPerm (n + 2) → R),
      FinPerm.permSum R (fun π => G (FinPerm.compose π (bsPerm k p hsp)))
        = FinPerm.permSum R G := by
  intro k p hsp G
  have hgen := permSum_compose_bsPerm_gen (R := R) k p hsp FinPerm.identity G
  simp only [FinPerm.compose_identity_right] at hgen
  exact hgen

end PermSumRightReindex

end SDG.DifferentialForms
