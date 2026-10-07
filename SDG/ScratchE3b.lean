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

/-- **(P') 块交换的符号公式**：sign (encode (bsFunV q p 与 pi.toFun 的复合))
= (-1)^(q*p) * sign pi。对 q 归纳：(S) 递推的 encode 级复合 + IH +
循环移位符号引理；无需 sign 乘性——hStep 保持 encode 形式，
IH 直接应用于 sigma := encode (cycLfun 与 pi.toFun 的复合)。 -/
lemma sign_encode_bsFunV : forall (q : Nat) {n : Nat} (p : Nat) (hsp : q + p <= n)
    (pi : FinPerm n) (hinj : Function.Injective (bsFunV q p hsp)),
    FinPerm.sign R (FinPerm.encode (bsFunV q p hsp ∘ pi.toFun)
        (hinj.comp pi.toFun_injective))
      = (-1 : R)^(q * p) * FinPerm.sign R pi := by
  intro q
  induction q with
  | zero =>
      intro n p hsp pi hinj
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
      show FinPerm.sign R (FinPerm.encode (bsFunV 0 p hsp ∘ pi.toFun)
          (hinj.comp pi.toFun_injective)) = (-1 : R)^(0 * p) * FinPerm.sign R pi
      have hE : FinPerm.encode (bsFunV 0 p hsp ∘ pi.toFun)
          (hinj.comp pi.toFun_injective) = pi := by
        apply FinPerm.ext_toFun _ _
        rw [FinPerm.toFun_encode]
        funext k
        show bsFunV 0 p hsp (pi.toFun k) = pi.toFun k
        rw [hid, id_eq]
      rw [hE, zero_mul, pow_zero, one_mul]
  | succ q ih =>
      intro n p hsp pi hinj
      have hsp' : q + p <= n := by omega
      have hltC : (q + p : Nat) < n := by omega
      have hinjC : Function.Injective (cycLfun q p hltC) := cycLfun_injective p q hltC
      have hinj' : Function.Injective (bsFunV q p hsp') :=
        bsFunV_injective (show q + p <= n from by omega)
      have hX : Function.Injective (cycLfun q p hltC ∘ pi.toFun) :=
        hinjC.comp pi.toFun_injective
      have hrec := bsFunV_succ_left hsp
      show FinPerm.sign R (FinPerm.encode (bsFunV (q+1) p hsp ∘ pi.toFun)
          (hinj.comp pi.toFun_injective)) = (-1 : R)^((q+1) * p) * FinPerm.sign R pi
      have hStep : FinPerm.encode (bsFunV (q+1) p hsp ∘ pi.toFun)
          (hinj.comp pi.toFun_injective)
        = FinPerm.encode
            (bsFunV q p hsp' ∘
              (FinPerm.encode (cycLfun q p hltC ∘ pi.toFun) hX).toFun)
            (hinj'.comp
              (FinPerm.toFun_injective
                (FinPerm.encode (cycLfun q p hltC ∘ pi.toFun) hX))) := by
        apply FinPerm.ext_toFun _ _
        rw [FinPerm.toFun_encode, FinPerm.toFun_encode, FinPerm.toFun_encode]
        funext k
        exact congrFun hrec (pi.toFun k)
      rw [hStep]
      rw [ih p hsp' (FinPerm.encode (cycLfun q p hltC ∘ pi.toFun) hX) hinj']
      have hCyc : FinPerm.sign R (FinPerm.encode (cycLfun q p hltC ∘ pi.toFun)
          (hinjC.comp pi.toFun_injective)) = (-1 : R)^p * FinPerm.sign R pi :=
        sign_encode_cycLfun p q hltC pi hinjC
      have hrw : (q + 1) * p = q * p + p := Nat.succ_mul q p
      rw [hCyc]
      rw [hrw]
      rw [pow_add]
      ring

variable {X : Type u} [Microlinear R X]

/-- **槽块恒等式（grad comm 引擎）**：输入向量预复合块交换 `bsFunV p q`
（前 p 槽与后 q 槽互换）使 `(p,q)` 楔积展开函数乘 `(-1)^{p*q}`。

关键：(P') 以 `le_refl` 守卫直接应用于 `bsFunV p q : Fin (p+q) → Fin (p+q)`
（守卫 `p + q ≤ p + q` 成立——(P') 的 ≤ 守卫在边界无需缓冲维度），
点态恒等式两侧括号逐项相同，重排经 `permSum_reindex_compose`。 -/
lemma wedgeAnyFun_grad_comm_block {p q : ℕ} {x : X}
    (ω : TangentFiber R X x [⋀^Fin p]→ₗ[R] R)
    (η : TangentFiber R X x [⋀^Fin q]→ₗ[R] R)
    (v : Fin (p + q) → TangentFiber R X x) :
    wedgeAnyFun ω η (fun t => v (bsFunV p q (le_refl (p + q)) t))
      = (-1 : R)^(p * q) • wedgeAnyFun ω η v := by
  unfold wedgeAnyFun
  have hpow : (-1 : R)^(p * q) * (-1 : R)^(p * q) = 1 := by
    rw [← mul_pow (a := (-1 : R)) (b := (-1 : R)) (n := p * q),
      show ((-1 : R) * (-1 : R)) = 1 from by ring, one_pow]
  have hinjB : Function.Injective (bsFunV p q (le_refl (p + q))) :=
    bsFunV_injective (le_refl (p + q))
  have hpoint : ∀ π : FinPerm (p + q),
      FinPerm.sign R π * (ω (fun i : Fin p =>
          v (bsFunV p q (le_refl (p + q)) (π.toFun (Fin.castAdd q i)))) *
        η (fun j : Fin q =>
          v (bsFunV p q (le_refl (p + q)) (π.toFun (Fin.natAdd p j)))))
    = (-1 : R)^(p * q) * (FinPerm.sign R (FinPerm.compose
          (FinPerm.encode (bsFunV p q (le_refl (p + q))) hinjB) π) *
        (ω (fun i : Fin p => v ((FinPerm.compose
            (FinPerm.encode (bsFunV p q (le_refl (p + q))) hinjB) π).toFun
              (Fin.castAdd q i))) *
        η (fun j : Fin q => v ((FinPerm.compose
            (FinPerm.encode (bsFunV p q (le_refl (p + q))) hinjB) π).toFun
              (Fin.natAdd p j))))) := by
    intro π
    have hsig' : FinPerm.sign R π
        = (-1 : R)^(p * q) * FinPerm.sign R (FinPerm.encode
            (bsFunV p q (le_refl (p + q)) ∘ π.toFun)
            (hinjB.comp π.toFun_injective)) := by
      have h1 := sign_encode_bsFunV (R := R) p q (le_refl (p + q)) π hinjB
      rw [h1, ← mul_assoc, hpow, one_mul]
    rw [hsig', encode_comp_toFun (bsFunV p q (le_refl (p + q))) hinjB π,
      FinPerm.toFun_compose, FinPerm.toFun_encode]
    simp only [Function.comp_apply]
    ring
  rw [permSum_congr hpoint, permSum_mul_left,
    permSum_reindex_compose (p + q) (FinPerm.encode (bsFunV p q (le_refl (p + q))) hinjB)
      (fun τ' : FinPerm (p + q) => FinPerm.sign R τ' *
        (ω (fun i : Fin p => v (τ'.toFun (Fin.castAdd q i))) *
        η (fun j : Fin q => v (τ'.toFun (Fin.natAdd p j))))),
    smul_eq_mul]

end GradComm

end SDG.DifferentialForms
