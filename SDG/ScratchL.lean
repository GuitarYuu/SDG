import SDG.DifferentialForms.Algebra

/-!
# 分次 Leibniz：∂(c₁ ∪ c₂) = (∂c₁) ∪ c₂ + (-1)^p · c₁ ∪ (∂c₂)

F 线在 cochain 世界的最后一件（Algebra.lean 的 deferred 项）。
上积为 Alexander-Whitney 型：`(c₁ ∪ c₂)(σ) = c₁(σ₀..σ_p) · c₂(σ_p..σ_{p+q})`。

层级备忘：σ : Fin (p+q+2) → X（(p+q+1)-单形）；
cupLeft (p+1) q : Fin (p+2) → Fin (p+q+2)；cupRight p (q+1) : Fin (q+2) → Fin (p+q+2)。
-/

namespace SDG.DifferentialForms

section CupLeibniz

variable {R : Type u} [CommRing R] {X : Type}

/-- **L1**：`(σ ∘ cupLeft (p+1) q)` 的第 `j` 面（`j ≤ p`）
= `(coFace σ j)` 限制在 `cupLeft p q` 上（前段不受位移影响）。 -/
lemma coFace_cupLeft_front {p q : ℕ} (σ : Fin (p + q + 2) → X) (j : Fin (p + 2))
    (hj : (j : ℕ) ≤ (p : ℕ)) (k : Fin (p + 1)) :
    cupLeft (p + 1) q (j.succAbove k)
      = (Fin.castLE (by have h1 := j.isLt; omega) j).succAbove (cupLeft p q k) := by
  apply Fin.ext
  rw [succAbove_val]
  have h1 := j.isLt
  have h2 := k.isLt
  show ((Fin.succAbove j k : Fin (p + q + 2)) : ℕ)
    = ((Fin.succAbove (Fin.castLE (by have h1 := j.isLt; omega) j)
      (cupLeft p q k) : Fin (p + q + 2)) : ℕ)
  rw [succAbove_val]
  simp only [cupLeft, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd]
  split <;> omega

/-- **L3**：`(σ ∘ cupRight (p+1) q)`（常值侧）的第 `j` 面（`j ≤ p`）
= `(coFace σ j)` 限制在 `cupRight p q` 上（后段位移一位）。 -/
lemma coFace_cupRight_front {p q : ℕ} (σ : Fin (p + q + 2) → X) (j : Fin (p + 2))
    (hj : (j : ℕ) ≤ (p : ℕ)) (k : Fin (q + 1)) :
    cupRight (p + 1) q k
      = (Fin.castLE (by have h1 := j.isLt; omega) j).succAbove (cupRight p q k) := by
  apply Fin.ext
  rw [succAbove_val]
  have h1 := j.isLt
  have h2 := k.isLt
  show ((Fin.succAbove j k : Fin (p + q + 2)) : ℕ)
    = ((Fin.succAbove (Fin.castLE (by have h1 := j.isLt; omega) j)
      (cupRight p q k) : Fin (p + q + 2)) : ℕ)
  rw [succAbove_val]
  simp only [cupRight, Fin.val_cast, Fin.val_natAdd]
  omega

/-- **L5**：`(σ ∘ cupLeft p (q+1))` 与 cupLeft p q：`j ≥ p+1` 时前段不变。 -/
lemma coFace_cupLeft_back {p q : ℕ} (σ : Fin (p + q + 2) → X) (j : Fin (p + q + 2))
    (hj : (p : ℕ) < (j : ℕ)) (k : Fin (p + 1)) :
    cupLeft p (q + 1) k = (Fin.castLE (by omega) j).succAbove (cupLeft p q k) := by
  apply Fin.ext
  rw [succAbove_val]
  have h1 := j.isLt
  have h2 := k.isLt
  show ((Fin.succAbove j k : Fin (p + q + 2)) : ℕ)
    = ((Fin.succAbove (Fin.castLE (by omega) j)
      (cupLeft p q k) : Fin (p + q + 2)) : ℕ)
  rw [succAbove_val]
  simp only [cupLeft, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd]
  omega

/-- **L4**：`(σ ∘ cupRight p (q+1))` 的第 `j` 面（`j ≥ 1`）
= `(coFace σ (p+j))` 限制在 `cupRight p q` 上。 -/
lemma coFace_cupRight_back {p q : ℕ} (σ : Fin (p + q + 2) → X) (j : Fin (q + 2))
    (hj : (1 : ℕ) ≤ (j : ℕ)) (k : Fin (q + 1)) :
    cupRight p (q + 1) (j.succAbove k)
      = (Fin.natAdd p (Fin.castSucc j)).succAbove (cupRight p q k) := by
  apply Fin.ext
  rw [succAbove_val]
  have h1 := j.isLt
  have h2 := k.isLt
  show ((Fin.succAbove j k : Fin (p + q + 2)) : ℕ)
    = ((Fin.succAbove (Fin.natAdd p (Fin.castSucc j)) (cupRight p q k) :
      Fin (p + q + 2)) : ℕ)
  rw [succAbove_val]
  simp only [cupRight, Fin.val_cast, Fin.val_natAdd, Fin.val_castSucc]
  split <;> omega

/-- **L2a**：共享顶点对（∂c₁ 末项的 c₁-因子）：
`(coFace σ (p+q+1-位)) ∘ cupLeft p q = σ ∘ cupLeft p (q+1)`。 -/
lemma coFace_cupLeft_last {p q : ℕ} (σ : Fin (p + q + 2) → X) (k : Fin (p + 1)) :
    (coFace σ (Fin.natAdd p (Fin.last (q + 1)))) (cupLeft p q k)
      = σ (cupLeft p (q + 1) k) := by
  have h1 := k.isLt
  show σ ((Fin.natAdd p (Fin.last (q + 1)) : Fin (p + q + 2)).succAbove (cupLeft p q k))
    = σ (cupLeft p (q + 1) k)
  rw [succAbove_val]
  simp only [cupLeft, cupRight, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd,
    Fin.val_last]
  omega

/-- **L2b**：共享顶点对（∂c₂ 首项的 c₂-因子）：
`(coFace σ p) ∘ cupRight p q = (σ ∘ cupRight p (q+1))` 的第 `0` 面。 -/
lemma coFace_cupRight_zero {p q : ℕ} (σ : Fin (p + q + 2) → X) (k : Fin (q + 1)) :
    (coFace σ (Fin.castLE (by omega : p ≤ p + 1) (0 : Fin (p + 1)))) (cupRight p q k)
      = σ ((σ ∘ cupRight p (q + 1)) (0.succAbove k)) := by
  show σ ((Fin.castLE (by omega : p ≤ p + 1) (0 : Fin (p + 1))).succAbove (cupRight p q k))
    = σ ((0 : Fin (q + 2)).succAbove (cupRight p (q + 1) k))
  rw [succAbove_val]
  simp only [cupRight, Fin.val_cast, Fin.val_natAdd, Fin.val_zero, Fin.val_succ]
  split <;> omega

end CupLeibniz

end SDG.DifferentialForms
