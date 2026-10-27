import SDG.DifferentialForms.Algebra

/-!
# 分次 Leibniz：∂(c₁ ∪ c₂) = (∂c₁) ∪ c₂ + (-1)^p · c₁ ∪ (∂c₂)

F 线在 cochain 世界的最后一件（Algebra.lean 的 deferred 项）。
上积为 Alexander-Whitney 型：`(c₁ ∪ c₂)(σ) = c₁(σ₀..σ_p) · c₂(σ_p..σ_{p+q})`。

证明策略（RESUME 第三十七接力点）：
1. cupLeft/cupRight 与 coFace 的复合分解引理（j ≤ p / j ≥ p+1 两段）；
2. LHS 双指标拆分（finSum_split_at × 2 拆出 i = p 与 i = p+1）；
3. 前后缀重排后与 RHS 两项的展开配对；中间项相消。
-/

namespace SDG.DifferentialForms

section CupLeibniz

variable {R : Type u} [CommRing R] {X : Type}

/-- cupLeft 的 succ 位移：第 `j` 面与 cupLeft 复合在前段 = castSucc-型后继。 -/
lemma coFace_cupLeft_le {p q : ℕ} (σ : Fin (p + q + 2) → X) (j : Fin (p + 1))
    (hj : (j : ℕ) ≤ (p : ℕ)) :
    coFace (fun k : Fin (p + 1) => σ (cupLeft p q k)) j
      = fun k : Fin (p + 1) =>
          σ ((Fin.cast (by omega : (p + q + 1) = (p + 1) + (q + 1))
              (Fin.castSucc (Fin.cast (by omega) j.succAbove k)))) := by
  funext k
  show σ (cupLeft p q (j.succAbove k))
    = σ ((Fin.cast (by omega : (p + q + 1) = (p + 1) + (q + 1))
        (Fin.castSucc (Fin.cast (by omega) j.succAbove k))))
  have h1 := j.isLt
  have h2 := k.isLt
  simp only [cupLeft, Fin.val_cast, Fin.val_castAdd, Fin.val_castSucc,
    Fin.succAbove_val_succ (Fin.cast (by omega) j) (Fin.cast (by omega) k)]
  unfold Fin.succAbove
  split <;> simp only [Fin.val_mk] <;> omega

end CupLeibniz

end SDG.DifferentialForms
