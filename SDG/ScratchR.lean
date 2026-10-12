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

end PermSumRightReindex

end SDG.DifferentialForms
