import SDG.DifferentialForms.Algebra

namespace SDG.DifferentialForms

variable {R : Type u} [CommRing R]

section GradComm

/-- **块交换递推 (S)**：`bsFunV (q+1) p = bsFunV q p ∘ cycLfun q p`
（前 q+1 段与后 p 段互换 = 先做 [q, q+p] 左移循环，再交换前 q 与后 p）。
六情形点态验证。 -/
lemma bsFunV_succ_left {n q p : ℕ} (hsp : q + 1 + p ≤ n) :
    bsFunV (q+1) p hsp
      = (bsFunV q p (show q + p ≤ n from by omega)) ∘
        (cycLfun q p (show q + p < n from by omega)) := by
  funext t
  have ht := t.isLt
  have hsp' : (q + p : ℕ) ≤ n := by omega
  have hltC : (q + p : ℕ) < n := by omega
  show bsFunV (q+1) p hsp t = (bsFunV q p hsp' ∘ cycLfun q p hltC) t
  by_cases h1 : (t : ℕ) < q
  · -- t < q：cycL 不动，两侧 bs 前段 ↦ t+p
    have hb2 : (t : ℕ) < n := by omega
    have hb3 : (t : ℕ) + p < n := by omega
    have hlt1 : (t : ℕ) < q + 1 := by omega
    have hv1 : bsFunV (q+1) p hsp t
        = (Fin.mk ((t : ℕ) + p) (by exact hb3) : Fin n) :=
      bsFunV_front hsp hlt1
    have hv2 : cycLfun q p hltC t = t :=
      cycLfun_out hltC (by omega) (by omega)
    have hv3 : bsFunV q p hsp' t
        = (Fin.mk ((t : ℕ) + p) (by exact hb3) : Fin n) :=
      bsFunV_front hsp' h1
    simp only [Function.comp_apply, hv1, hv2, hv3]
  · by_cases h2 : (t : ℕ) = q
    · -- t = q：cycL 左端 ↦ q+p，bs(q,p) 尾部不动；bs(q+1,p) 前端 ↦ q+p
      have hb4 : (q : ℕ) < n := by omega
      have hb5 : (q + p : ℕ) < n := by omega
      have hv1 : bsFunV (q+1) p hsp (Fin.mk q (by exact hb4) : Fin n)
          = (Fin.mk (q + p) (by exact hb5) : Fin n) :=
        bsFunV_front hsp (Nat.lt_succ_self q)
      have hv2 : cycLfun q p hltC (Fin.mk q (by exact hb4) : Fin n)
          = (Fin.mk (q + p) (by exact hb5) : Fin n) :=
        cycLfun_left hltC (by simp only [Fin.val_mk])
      have hv3 : bsFunV q p hsp' (Fin.mk (q + p) (by exact hb5) : Fin n)
          = (Fin.mk (q + p) (by exact hb5) : Fin n) :=
        bsFunV_out hsp' (le_refl _)
      simp only [Function.comp_apply, hv1, hv2, hv3, show t = (Fin.mk q (by exact hb4) : Fin n) from Fin.ext h2]
    · by_cases h3 : (t : ℕ) < q + 1 + p
      · -- q < t < q+1+p：cycL 中段 ↦ t-1，bs(q,p) 中段 ↦ t-1-q；bs(q+1,p) 中段 ↦ t-(q+1)
        have hb7 : (t : ℕ) - 1 < n := by omega
        have hb8 : (t : ℕ) - (q+1) < n := by omega
        have hb9 : (t : ℕ) - 1 - q < n := by omega
        have hgt : (q : ℕ) < (t : ℕ) := by omega
        have hge1 : (q + 1 : ℕ) ≤ (t : ℕ) := by omega
        have hge2 : (q : ℕ) ≤ (t : ℕ) - 1 := by omega
        have hlt2 : ((t : ℕ) - 1 : ℕ) < q + p := by omega
        have hv1 : bsFunV (q+1) p hsp t
            = (Fin.mk ((t : ℕ) - (q+1)) (by exact hb8) : Fin n) :=
          bsFunV_back hsp hge1 (by omega)
        have hv2 : cycLfun q p hltC t
            = (Fin.mk ((t : ℕ) - 1) (by exact hb7) : Fin n) :=
          cycLfun_mid hltC hgt (by omega)
        have hv3 : bsFunV q p hsp' (Fin.mk ((t : ℕ) - 1) (by exact hb7) : Fin n)
            = (Fin.mk ((t : ℕ) - 1 - q) (by exact hb9) : Fin n) :=
          bsFunV_back hsp' hge2 hlt2
        simp only [Function.comp_apply, hv1, hv2, hv3]
        exact Fin.ext (by simp only [Fin.val_mk]; omega)
      · -- t ≥ q+1+p：全尾部不动
        have hge0 : (q + p : ℕ) ≤ (t : ℕ) := by omega
        have hge1 : (q + 1 + p : ℕ) ≤ (t : ℕ) := by omega
        have hne2 : (t : ℕ) ≠ q := by omega
        have hv1 : bsFunV (q+1) p hsp t = t :=
          bsFunV_out hsp hge1
        have hv2 : cycLfun q p hltC t = t :=
          cycLfun_out hltC hne2 (by omega)
        have hv3 : bsFunV q p hsp' t = t :=
          bsFunV_out hsp' hge0
        simp only [Function.comp_apply, hv1, hv2, hv3]

end GradComm

end SDG.DifferentialForms
