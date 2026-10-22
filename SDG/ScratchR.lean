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

section CastBridge

variable {R : Type u} [CommRing R]

/-- FinPerm 的类型转换（encode 基，toFun 可直接计算）。 -/
def permCast {m n : ℕ} (h : m = n) (π : FinPerm m) : FinPerm n :=
  FinPerm.encode
    (fun k => Fin.cast h (π.toFun (Fin.cast (h.symm) k)))
    (Function.Injective.comp (Fin.cast_injective (h := h))
      (Function.Injective.comp π.toFun_injective
        (Fin.cast_injective (h := h.symm))))

lemma permCast_id {m : ℕ} (π : FinPerm m) : permCast rfl π = π := by
  apply FinPerm.ext_toFun _ _
  unfold permCast
  funext k
  rw [FinPerm.toFun_encode]
  rfl

/-- permSum 的类型桥：m = n 时两类求和一致。 -/
lemma permSum_typeCast {m n : ℕ} (h : m = n) (f : FinPerm n → R) :
    FinPerm.permSum R (fun π : FinPerm m => f (permCast h π))
      = FinPerm.permSum R f := by
  subst h
  rw [permSum_congr (fun π => congrArg f (permCast_id π))]

end CastBridge


section GradCommSlot

variable {R : Type u} [CommRing R]

/-- 槽位恒等式 A：块交换把 η-块第 j 槽送回原 η-位置（hT-cast 形）。 -/
lemma bsFunV_castAdd {q p : ℕ} (hT : p + q = q + p) (j : Fin q) :
    bsFunV q p (le_refl (q + p)) (Fin.castAdd p j)
      = Fin.cast hT (Fin.natAdd p j) := by
  apply Fin.ext
  have hj := j.isLt
  rw [bsFunV_front (le_refl (q + p)) (show ((Fin.castAdd p j : Fin (q + p)) : ℕ) < q from by
    simp only [Fin.val_castAdd]; omega), Fin.val_cast, Fin.val_mk, Fin.val_castAdd,
    Fin.val_natAdd, Nat.add_comm]

/-- 槽位恒等式 B：块交换把 ω-块第 i 槽送回原 ω-位置（hT-cast 形）。 -/
lemma bsFunV_natAdd {q p : ℕ} (hT : p + q = q + p) (i : Fin p) :
    bsFunV q p (le_refl (q + p)) (Fin.natAdd q i)
      = Fin.cast hT (Fin.castAdd q i) := by
  apply Fin.ext
  have hi := i.isLt
  rw [bsFunV_back (le_refl (q + p)) (show (q : ℕ) ≤ ((Fin.natAdd q i : Fin (q + p)) : ℕ) from by
    simp only [Fin.val_natAdd]; omega)
    (show ((Fin.natAdd q i : Fin (q + p)) : ℕ) < q + p from by
    simp only [Fin.val_natAdd]; omega), Fin.val_cast, Fin.val_mk, Fin.val_natAdd,
    Fin.val_castAdd, Nat.add_sub_cancel_left]

end GradCommSlot
end PermSumRightReindex

section GradComm

/-! ## 分次交换律组装（E3 收官）

目标：`wedgeAnyFun ω η v = (-1)^(p*q) • wedgeAnyFun η ω (v 经 ambient 转置)`。

架构（关键决策）：`wedgeAnyFun` 的 ambient 锁定字面 `p + q`，而 `(R)` 链
（`permSum_compose_bsPerm`）只在 `n + 2` 层级存在。ambient 的 cases 重写
（`p + q` 与 `N + 2` 互换）因 motive 类型不正确不可行（`v` 的类型依赖
`p + q`，wedgeAnyFun 应用对泛化 ambient 不合类型）。正解：**不做 ambient
重写**——主引理带显式运输等式 `hA : p + q = N + 2`、`hE : q + p = N + 2`，
两侧经 `permSum_typeCast` + `sign_permCast` + cast 消去搬到 `FinPerm (N + 2)`
求和世界（`wedgeAnyFun_permSum_cast`），在 N+2 世界内完成 `(R)` 归位 +
槽位恒等式 + `sign_mul`/`bsPerm_sign` 收符号。最终定理按 `2 ≤ p + q`
分派：主分支 `obtain N` 直接调用；`p + q ≤ 1` 三个具体退化引理。 -/

variable {R : Type u} [CommRing R] {X : Type u} [Microlinear R X]

/-- cast 复合消去：`cast h.symm ∘ cast h = id`（点态，val 层平凡）。 -/
lemma finCast_cancel {a b : ℕ} (h : a = b) (s : Fin a) :
    Fin.cast h.symm (Fin.cast h s) = s := by
  apply Fin.ext
  rw [Fin.val_cast, Fin.val_cast]

/-- sign 的 ambient-cast 不变性：subst 后 `permCast rfl π = π`。 -/
lemma sign_permCast {m n : ℕ} (h : m = n) (π : FinPerm m) :
    FinPerm.sign R (permCast h π) = FinPerm.sign R π := by
  subst h
  rw [permCast_id]

/-- **块交换的符号**：`sign (bsPerm q p hsp) = (-1)^(q*p)`。
由 (P') 于恒等置换处取：encode ∘ id 桥回 bsPerm。 -/
lemma bsPerm_sign {n q p : ℕ} (hsp : q + p ≤ n) :
    FinPerm.sign R (bsPerm q p hsp) = (-1 : R)^(q * p) := by
  have h1 := sign_encode_bsFunV (R := R) q p hsp FinPerm.identity (bsFunV_injective hsp)
  have hE : FinPerm.encode (bsFunV q p hsp ∘ FinPerm.identity.toFun)
      (Function.Injective.comp (bsFunV_injective hsp) FinPerm.identity.toFun_injective)
      = bsPerm q p hsp := by
    apply FinPerm.ext_toFun _ _
    unfold bsPerm
    rw [FinPerm.toFun_encode, FinPerm.toFun_encode]
    funext k
    rw [FinPerm.toFun_identity]
    rfl
  rw [hE] at h1
  rw [h1, FinPerm.sign_identity R, mul_one]

/-- N+2 世界的槽位恒等式 A：块交换把 η-块第 j 槽送回原 η-位置
（双 cast 形：入口沿 hE 运输、出口沿 hA 运输）。 -/
lemma bsFunV_cast_hE {q p N : ℕ} (hE : q + p = N + 2) (hA : p + q = N + 2) (j : Fin q) :
    bsFunV q p (show q + p ≤ N + 2 from by omega)
        (Fin.cast hE (Fin.castAdd p j))
      = Fin.cast hA (Fin.natAdd p j) := by
  apply Fin.ext
  have hj := j.isLt
  have hval : ((Fin.cast hE (Fin.castAdd p j) : Fin (N + 2)) : ℕ) < q := by
    rw [Fin.val_cast, Fin.val_castAdd]
    omega
  rw [bsFunV_front _ hval, Fin.val_mk, Fin.val_cast, Fin.val_castAdd,
    Fin.val_cast, Fin.val_natAdd]
  omega

/-- N+2 世界的槽位恒等式 B：块交换把 ω-块第 i 槽送回原 ω-位置。 -/
lemma bsFunV_natAdd_hE {q p N : ℕ} (hE : q + p = N + 2) (hA : p + q = N + 2) (i : Fin p) :
    bsFunV q p (show q + p ≤ N + 2 from by omega)
        (Fin.cast hE (Fin.natAdd q i))
      = Fin.cast hA (Fin.castAdd q i) := by
  apply Fin.ext
  have hi := i.isLt
  have hval1 : (q : ℕ) ≤ ((Fin.cast hE (Fin.natAdd q i) : Fin (N + 2)) : ℕ) := by
    rw [Fin.val_cast, Fin.val_natAdd]
    omega
  have hval2 : ((Fin.cast hE (Fin.natAdd q i) : Fin (N + 2)) : ℕ) < q + p := by
    rw [Fin.val_cast, Fin.val_natAdd]
    omega
  rw [bsFunV_back _ hval1 hval2, Fin.val_mk, Fin.val_cast, Fin.val_natAdd,
    Fin.val_cast, Fin.val_castAdd]
  omega

set_option maxHeartbeats 2000000 in
/-- **ambient 运输引理**：把 `wedgeAnyFun` 的 permSum 表达式搬到任意
ambient `m`（`h : p + q = m`），槽位经 `Fin.cast h` 运输。
`permSum_typeCast` + `sign_permCast` + cast 消去的三合一桥，
是 N+2 世界主引理两侧的统一入口。 -/
lemma wedgeAnyFun_permSum_cast {p q m : ℕ} (h : p + q = m) {x : X}
    (ω : TangentFiber R X x [⋀^Fin p]→ₗ[R] R)
    (η : TangentFiber R X x [⋀^Fin q]→ₗ[R] R)
    (w : Fin m → TangentFiber R X x) :
    wedgeAnyFun ω η (fun t : Fin (p + q) => w (Fin.cast h t))
      = FinPerm.permSum R (fun π : FinPerm m => FinPerm.sign R π *
          (ω (fun i : Fin p => w (π.toFun (Fin.cast h (Fin.castAdd q i)))) *
          η (fun j : Fin q => w (π.toFun (Fin.cast h (Fin.natAdd p j)))))) := by
  unfold wedgeAnyFun
  rw [← permSum_typeCast h (fun π : FinPerm m => FinPerm.sign R π *
      (ω (fun i : Fin p => w (π.toFun (Fin.cast h (Fin.castAdd q i)))) *
      η (fun j : Fin q => w (π.toFun (Fin.cast h (Fin.natAdd p j))))))]
  have hpoint : ∀ τ : FinPerm (p + q),
      FinPerm.sign R τ *
        (ω (fun i : Fin p => w (Fin.cast h (τ.toFun (Fin.castAdd q i)))) *
        η (fun j : Fin q => w (Fin.cast h (τ.toFun (Fin.natAdd p j)))))
      = FinPerm.sign R (permCast h τ) *
        (ω (fun i : Fin p =>
            w ((permCast h τ).toFun (Fin.cast h (Fin.castAdd q i)))) *
        η (fun j : Fin q =>
            w ((permCast h τ).toFun (Fin.cast h (Fin.natAdd p j))))) := by
    intro τ
    rw [sign_permCast]
    have hslotA : (fun i : Fin p =>
            w ((permCast h τ).toFun (Fin.cast h (Fin.castAdd q i))))
        = (fun i : Fin p => w (Fin.cast h (τ.toFun (Fin.castAdd q i)))) := by
      funext i
      unfold permCast
      rw [FinPerm.toFun_encode, finCast_cancel]
    have hslotB : (fun j : Fin q =>
            w ((permCast h τ).toFun (Fin.cast h (Fin.natAdd p j))))
        = (fun j : Fin q => w (Fin.cast h (τ.toFun (Fin.natAdd p j)))) := by
      funext j
      unfold permCast
      rw [FinPerm.toFun_encode, finCast_cancel]
    rw [hslotA, hslotB]
  rw [permSum_congr hpoint]

set_option maxHeartbeats 4000000 in
/-- **N+2 桥世界主引理**：显式运输等式下分次交换律成立。
两侧经 `wedgeAnyFun_permSum_cast` 搬到 `FinPerm (N + 2)` 求和；
`(R)` `permSum_compose_bsPerm` 归位后点态收符号
（sign_mul + bsPerm_sign + 槽位恒等式 + mul 交换）。 -/
lemma wedgeAnyFun_grad_comm_at {p q N : ℕ} (hA : p + q = N + 2) (hE : q + p = N + 2)
    {x : X} (ω : TangentFiber R X x [⋀^Fin p]→ₗ[R] R)
    (η : TangentFiber R X x [⋀^Fin q]→ₗ[R] R)
    (v : Fin (p + q) → TangentFiber R X x) :
    wedgeAnyFun ω η v
      = (-1 : R)^(p * q) • wedgeAnyFun η ω
          (fun t : Fin (q + p) => v (Fin.cast (Nat.add_comm q p) t)) := by
  obtain ⟨w, hwdef⟩ : ∃ w : Fin (N + 2) → TangentFiber R X x,
      ∀ t, w t = v (Fin.cast hA.symm t) :=
    ⟨fun t => v (Fin.cast hA.symm t), fun t => rfl⟩
  have hpow1 : (-1 : R)^(p * q) * (-1 : R)^(p * q) = 1 := by
    rw [← mul_pow (a := (-1 : R)) (b := (-1 : R)) (n := p * q),
      show ((-1 : R) * (-1 : R)) = 1 from by ring, one_pow]
  have hLv : (fun t : Fin (p + q) => w (Fin.cast hA t)) = v := by
    funext t
    rw [hwdef (Fin.cast hA t)]
    exact congrArg v (finCast_cancel hA t)
  have hRv : (fun t : Fin (q + p) => v (Fin.cast (Nat.add_comm q p) t))
      = (fun t : Fin (q + p) => w (Fin.cast hE t)) := by
    funext t
    rw [hwdef (Fin.cast hE t)]
    exact congrArg v (Fin.ext (by simp only [Fin.val_cast]))
  rw [hRv, ← hLv, wedgeAnyFun_permSum_cast hA ω η w,
    wedgeAnyFun_permSum_cast hE η ω w, smul_eq_mul]
  have hsp'' : q + p ≤ N + 2 := by omega
  -- (R) 归位：Σ Gq = Σ Gq(π ∘ bs)
  rw [← permSum_compose_bsPerm R q p hsp'' (fun π : FinPerm (N + 2) =>
    FinPerm.sign R π *
      (η (fun j : Fin q => w (π.toFun (Fin.cast hE (Fin.castAdd p j)))) *
      ω (fun i : Fin p => w (π.toFun (Fin.cast hE (Fin.natAdd q i))))))]
  -- 点态核心
  have hpoint : ∀ π : FinPerm (N + 2),
      FinPerm.sign R (FinPerm.compose π (bsPerm q p hsp'')) *
        (η (fun j : Fin q => w ((FinPerm.compose π (bsPerm q p hsp'')).toFun
            (Fin.cast hE (Fin.castAdd p j)))) *
        ω (fun i : Fin p => w ((FinPerm.compose π (bsPerm q p hsp'')).toFun
            (Fin.cast hE (Fin.natAdd q i)))))
      = (-1 : R)^(p * q) * (FinPerm.sign R π *
        (ω (fun i : Fin p => w (π.toFun (Fin.cast hA (Fin.castAdd q i)))) *
        η (fun j : Fin q => w (π.toFun (Fin.cast hA (Fin.natAdd p j)))))) := by
    intro π
    have hslotπ1 : ∀ j : Fin q, w ((FinPerm.compose π (bsPerm q p hsp'')).toFun
        (Fin.cast hE (Fin.castAdd p j)))
        = w (π.toFun (Fin.cast hA (Fin.natAdd p j))) := by
      intro j
      unfold bsPerm
      rw [FinPerm.toFun_compose, FinPerm.toFun_encode]
      simp only []
      rw [bsFunV_cast_hE hE hA]
    have hslotπ2 : ∀ i : Fin p, w ((FinPerm.compose π (bsPerm q p hsp'')).toFun
        (Fin.cast hE (Fin.natAdd q i)))
        = w (π.toFun (Fin.cast hA (Fin.castAdd q i))) := by
      intro i
      unfold bsPerm
      rw [FinPerm.toFun_compose, FinPerm.toFun_encode]
      simp only []
      rw [bsFunV_natAdd_hE hE hA]
    rw [sign_mul (N + 2) R, bsPerm_sign]
    simp only [hslotπ1, hslotπ2]
    rw [Nat.mul_comm q p]
    ring
  rw [permSum_congr hpoint, permSum_mul_left, ← mul_assoc, hpow1, one_mul]

/-- 退化 (0,0)：双平凡因子（Fin 0 槽函数两两相等）。 -/
lemma wedgeAnyFun_grad_comm_zero_zero {x : X}
    (ω : TangentFiber R X x [⋀^Fin 0]→ₗ[R] R)
    (η : TangentFiber R X x [⋀^Fin 0]→ₗ[R] R)
    (v : Fin (0 + 0) → TangentFiber R X x) :
    wedgeAnyFun ω η v
      = (-1 : R)^(0 * 0) • wedgeAnyFun η ω
          (fun t : Fin (0 + 0) => v (Fin.cast (Nat.add_comm 0 0) t)) := by
  unfold wedgeAnyFun
  rw [zero_mul, pow_zero, one_smul]
  have hpt : ∀ π : FinPerm (0 + 0),
      FinPerm.sign R π *
        (ω (fun i : Fin 0 => v (π.toFun (Fin.castAdd 0 i))) *
        η (fun j : Fin 0 => v (π.toFun (Fin.natAdd 0 j))))
      = FinPerm.sign R π *
        (η (fun j : Fin 0 =>
            v (Fin.cast (Nat.add_comm 0 0) (π.toFun (Fin.castAdd 0 j)))) *
        ω (fun i : Fin 0 =>
            v (Fin.cast (Nat.add_comm 0 0) (π.toFun (Fin.natAdd 0 i))))) := by
    intro π
    have hEq0 : ∀ f : Fin 0 → TangentFiber R X x, f = fun t => t.elim0 :=
      fun f => funext (fun t => t.elim0)
    have hωL : ω (fun i : Fin 0 => v (π.toFun (Fin.castAdd 0 i)))
        = ω (fun t => t.elim0) := congrArg ω (hEq0 _)
    have hηL : η (fun j : Fin 0 => v (π.toFun (Fin.natAdd 0 j)))
        = η (fun t => t.elim0) := congrArg η (hEq0 _)
    have hηR : η (fun j : Fin 0 =>
          v (Fin.cast (Nat.add_comm 0 0) (π.toFun (Fin.castAdd 0 j))))
        = η (fun t => t.elim0) := congrArg η (hEq0 _)
    have hωR : ω (fun i : Fin 0 =>
          v (Fin.cast (Nat.add_comm 0 0) (π.toFun (Fin.natAdd 0 i))))
        = ω (fun t => t.elim0) := congrArg ω (hEq0 _)
    rw [hωL, hηL, hηR, hωR]
    ring
  rw [permSum_congr hpt]

/-- 退化 (0,1)：ω 因子平凡，η 槽经 natAdd 0 / castAdd 0 值等值。 -/
lemma wedgeAnyFun_grad_comm_zero_one {x : X}
    (ω : TangentFiber R X x [⋀^Fin 0]→ₗ[R] R)
    (η : TangentFiber R X x [⋀^Fin 1]→ₗ[R] R)
    (v : Fin (0 + 1) → TangentFiber R X x) :
    wedgeAnyFun ω η v
      = (-1 : R)^(0 * 1) • wedgeAnyFun η ω
          (fun t : Fin (1 + 0) => v (Fin.cast (Nat.add_comm 1 0) t)) := by
  unfold wedgeAnyFun
  rw [zero_mul, pow_zero, one_smul]
  have hpt : ∀ π : FinPerm (0 + 1),
      FinPerm.sign R π *
        (ω (fun i : Fin 0 => v (π.toFun (Fin.castAdd 1 i))) *
        η (fun j : Fin 1 => v (π.toFun (Fin.natAdd 0 j))))
      = FinPerm.sign R π *
        (η (fun j : Fin 1 =>
            v (Fin.cast (Nat.add_comm 1 0) (π.toFun (Fin.castAdd 0 j)))) *
        ω (fun i : Fin 0 =>
            v (Fin.cast (Nat.add_comm 1 0) (π.toFun (Fin.natAdd 1 i))))) := by
    intro π
    have hEq0 : ∀ f : Fin 0 → TangentFiber R X x, f = fun t => t.elim0 :=
      fun f => funext (fun t => t.elim0)
    have hωL : ω (fun i : Fin 0 => v (π.toFun (Fin.castAdd 1 i)))
        = ω (fun t => t.elim0) := congrArg ω (hEq0 _)
    have hωR : ω (fun i : Fin 0 =>
          v (Fin.cast (Nat.add_comm 1 0) (π.toFun (Fin.natAdd 1 i))))
        = ω (fun t => t.elim0) := congrArg ω (hEq0 _)
    have hlam : (fun j : Fin 1 => v (π.toFun (Fin.natAdd 0 j)))
        = (fun j : Fin 1 =>
            v (Fin.cast (Nat.add_comm 1 0) (π.toFun (Fin.castAdd 0 j)))) := by
      funext j
      have hFin : (Fin.natAdd 0 j : Fin (0 + 1))
          = Fin.cast (Nat.add_comm 1 0) (Fin.castAdd 0 j) := by
        apply Fin.ext
        rw [Fin.val_natAdd, Fin.val_cast, Fin.val_castAdd]
        omega
      rw [hFin]
      rfl
    rw [hωL, hωR, congrArg η hlam]
    ring
  rw [permSum_congr hpt]

/-- 退化 (1,0)：η 因子平凡，ω 槽经 castAdd 0 / natAdd 0 值等值。 -/
lemma wedgeAnyFun_grad_comm_one_zero {x : X}
    (ω : TangentFiber R X x [⋀^Fin 1]→ₗ[R] R)
    (η : TangentFiber R X x [⋀^Fin 0]→ₗ[R] R)
    (v : Fin (1 + 0) → TangentFiber R X x) :
    wedgeAnyFun ω η v
      = (-1 : R)^(1 * 0) • wedgeAnyFun η ω
          (fun t : Fin (0 + 1) => v (Fin.cast (Nat.add_comm 0 1) t)) := by
  unfold wedgeAnyFun
  rw [one_mul, pow_zero, one_smul]
  have hpt : ∀ π : FinPerm (1 + 0),
      FinPerm.sign R π *
        (ω (fun i : Fin 1 => v (π.toFun (Fin.castAdd 0 i))) *
        η (fun j : Fin 0 => v (π.toFun (Fin.natAdd 1 j))))
      = FinPerm.sign R π *
        (η (fun j : Fin 0 =>
            v (Fin.cast (Nat.add_comm 0 1) (π.toFun (Fin.castAdd 1 j)))) *
        ω (fun i : Fin 1 =>
            v (Fin.cast (Nat.add_comm 0 1) (π.toFun (Fin.natAdd 0 i))))) := by
    intro π
    have hEq0 : ∀ f : Fin 0 → TangentFiber R X x, f = fun t => t.elim0 :=
      fun f => funext (fun t => t.elim0)
    have hηL : η (fun j : Fin 0 => v (π.toFun (Fin.natAdd 1 j)))
        = η (fun t => t.elim0) := congrArg η (hEq0 _)
    have hηR : η (fun j : Fin 0 =>
          v (Fin.cast (Nat.add_comm 0 1) (π.toFun (Fin.castAdd 1 j))))
        = η (fun t => t.elim0) := congrArg η (hEq0 _)
    have hlam : (fun i : Fin 1 => v (π.toFun (Fin.castAdd 0 i)))
        = (fun i : Fin 1 =>
            v (Fin.cast (Nat.add_comm 0 1) (π.toFun (Fin.natAdd 0 i)))) := by
      funext i
      have hFin : (Fin.castAdd 0 i : Fin (1 + 0))
          = Fin.cast (Nat.add_comm 0 1) (Fin.natAdd 0 i) := by
        apply Fin.ext
        rw [Fin.val_castAdd, Fin.val_cast, Fin.val_natAdd]
        omega
      rw [hFin]
      rfl
    rw [hηL, hηR, congrArg ω hlam]
    ring
  rw [permSum_congr hpt]

set_option maxHeartbeats 4000000 in
/-- **分次交换律（点态，E3 主定理）**：`ω∧η = (-1)^{p·q} · η∧ω`
（ambient 经 `Fin.cast (Nat.add_comm q p)` 转置）。
主分支：`obtain N : p + q = N + 2` + N+2 桥主引理；
`p + q ≤ 1` 时三个具体退化引理。 -/
lemma wedgeAnyFun_grad_comm {p q : ℕ} {x : X}
    (ω : TangentFiber R X x [⋀^Fin p]→ₗ[R] R)
    (η : TangentFiber R X x [⋀^Fin q]→ₗ[R] R)
    (v : Fin (p + q) → TangentFiber R X x) :
    wedgeAnyFun ω η v
      = (-1 : R)^(p * q) • wedgeAnyFun η ω
          (fun t : Fin (q + p) => v (Fin.cast (Nat.add_comm q p) t)) := by
  sorry

#print axioms wedgeAnyFun_permSum_cast
#print axioms sign_permCast
#print axioms bsPerm_sign
#print axioms wedgeAnyFun_grad_comm_at
#print axioms wedgeAnyFun_grad_comm_zero_zero
#print axioms wedgeAnyFun_grad_comm_zero_one
#print axioms wedgeAnyFun_grad_comm_one_zero
#print axioms Nat.lt_or_ge
#print axioms Nat.eq_zero_or_pos

theorem probeMain (p q : ℕ) (h2 : 2 ≤ p + q) : ∃ N : ℕ, p + q = N + 2 ∧ q + p = N + 2 := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, p + q = N + 2 := ⟨p + q - 2, by omega⟩
  exact ⟨N, hN, by omega⟩

theorem probeGlue (p q : ℕ) : True := by
  rcases Nat.lt_or_ge (p + q) 2 with h1 | h2
  · rcases Nat.eq_zero_or_pos p with hp0 | hp1
    · subst hp0
      rcases Nat.eq_zero_or_pos q with hq0 | hq1
      · subst hq0
        trivial
      · have hq1' : q = 1 := by omega
        subst hq1'
        trivial
    · rcases Nat.eq_zero_or_pos q with hq0 | hq1
      · have hp1' : p = 1 := by omega
        subst hp1'
        subst hq0
        trivial
      · omega
  · trivial

#print axioms probeMain
#print axioms probeGlue

theorem probeSig {p q : ℕ} {x : X}
    (ω : TangentFiber R X x [⋀^Fin p]→ₗ[R] R)
    (η : TangentFiber R X x [⋀^Fin q]→ₗ[R] R)
    (v : Fin (p + q) → TangentFiber R X x) :
    wedgeAnyFun ω η v
      = (-1 : R)^(p * q) • wedgeAnyFun η ω
          (fun t : Fin (q + p) => v (Fin.cast (Nat.add_comm q p) t)) := sorry

theorem probeGlue4 {p q : ℕ} (h2 : 2 ≤ p + q) : ∃ N : ℕ, p + q = N + 2 := by
  obtain ⟨N, hN⟩ : ∃ N, p + q = N + 2 := ⟨p + q - 2, by omega⟩
  exact ⟨N, hN⟩

#print axioms probeSig

theorem probeGlue5 {p q : ℕ} {x : X}
    (ω : TangentFiber R X x [⋀^Fin p]→ₗ[R] R)
    (η : TangentFiber R X x [⋀^Fin q]→ₗ[R] R)
    (v : Fin (p + q) → TangentFiber R X x) : True := by
  rcases Nat.lt_or_ge (p + q) 2 with h1 | h2
  · rcases Nat.eq_zero_or_pos p with hp0 | hp1
    · subst hp0
      rcases Nat.eq_zero_or_pos q with hq0 | hq1
      · subst hq0
        trivial
      · have hq1' : q = 1 := by omega
        subst hq1'
        trivial
    · rcases Nat.eq_zero_or_pos q with hq0 | hq1
      · have hp1' : p = 1 := by omega
        subst hp1'
        subst hq0
        trivial
      · omega
  · trivial
#print axioms probeGlue4
#print axioms probeGlue5
#print axioms probeGlue6

theorem probeGlue6 {p q : ℕ} {x : X}
    (ω : TangentFiber R X x [⋀^Fin p]→ₗ[R] R)
    (η : TangentFiber R X x [⋀^Fin q]→ₗ[R] R)
    (v : Fin (p + q) → TangentFiber R X x)
    (h1 : p + q < 2) (hp1 : 1 ≤ p) (hq1 : 0 < q) :
    wedgeAnyFun ω η v
      = (-1 : R)^(p * q) • wedgeAnyFun η ω
          (fun t : Fin (q + p) => v (Fin.cast (Nat.add_comm q p) t)) := by
  omega
#print axioms wedgeAnyFun_grad_comm

end GradComm

end SDG.DifferentialForms
