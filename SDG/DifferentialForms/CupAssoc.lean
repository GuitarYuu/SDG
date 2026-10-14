import SDG.DifferentialForms.Algebra

/-!
# SDG.DifferentialForms.CupAssoc

上积的结合律：`(c₁ ⌣ c₂) ⌣ c₃ = c₁ ⌣ (c₂ ⌣ c₃)`。

Alexander–Whitney 对角的三角一致性使结合律**严格成立**（无需链同伦）：
两侧都是同一个三因子读值乘积

`c₁(σ|[v₀..v_p]) · c₂(σ|[v_p..v_{p+q}]) · c₃(σ|[v_{p+q}..v_{p+q+r}])`，

仅参数化路径不同——三条值恒等式（全部归结为 `cupLeft`/`cupRight` 的
顶点值引理与度数 cast 的值恒等）：

* `cupLeft (p+q) r ∘ cupLeft p q` 与 `cast ∘ cupLeft p (q+r)` 同值（读 `v_k`）；
* `cupLeft (p+q) r ∘ cupRight p q` 与 `cast ∘ cupRight p (q+r) ∘ cupLeft q r`
  同值（读 `v_{p+k}`）；
* `cupRight (p+q) r` 与 `cast ∘ cupRight p (q+r) ∘ cupRight q r` 同值
  （读 `v_{p+q+k}`，此处需 Nat 加法结合 `omega`）。
-/

namespace SDG.DifferentialForms

variable {R : Type u} [CommRing R] {X : Type u}

/-- 度数 cast 的值恒等（消 cast 用）。 -/
lemma cast_val_eq {m n : ℕ} (h : m = n) (k : Fin m) :
    ((Fin.cast h k : Fin n) : ℕ) = (k : ℕ) := Fin.val_cast h k

/-- `cupLeft p q k` 的顶点值 = `k`。 -/
lemma cupLeft_val (p q : ℕ) (k : Fin (p + 1)) :
    ((cupLeft p q k : Fin (p + q + 1)) : ℕ) = (k : ℕ) := by
  simp [cupLeft]

/-- `cupRight p q k` 的顶点值 = `p + k`。 -/
lemma cupRight_val (p q : ℕ) (k : Fin (q + 1)) :
    ((cupRight p q k : Fin (p + q + 1)) : ℕ) = p + (k : ℕ) := by
  simp [cupRight]

/-- 上链的度数重标记（`h : m = n`；顶点经 `Fin.cast` 值恒等复合）。 -/
def cochainCast {m n : ℕ} (h : m = n) (c : Cochain R X m) : Cochain R X n :=
  fun σ => c (fun k => σ (Fin.cast (show m + 1 = n + 1 from by rw [h]) k))

@[simp]
theorem cochainCast_apply {m n : ℕ} (h : m = n) (c : Cochain R X m)
    (σ : SimplexPts X n) :
    cochainCast h c σ
      = c (fun k => σ (Fin.cast (show m + 1 = n + 1 from by rw [h]) k)) := rfl

/-- **上积结合律（点态版）**：在 `(p+q)+r` 次单纯形 `σ` 上，两侧都是
`c₁(σ|[0..p]) · c₂(σ|[p..p+q]) · c₃(σ|[p+q..])`。右_simplex_ 经度数
cast 重标记（值恒等）。 -/
theorem cupProduct_assoc_apply {p q r : ℕ} (c₁ : Cochain R X p) (c₂ : Cochain R X q)
    (c₃ : Cochain R X r) (σ : SimplexPts X ((p + q) + r)) :
    cupProduct (cupProduct c₁ c₂) c₃ σ
      = cupProduct c₁ (cupProduct c₂ c₃)
          (fun k : Fin (p + (q + r) + 1) => σ (Fin.cast (by omega) k)) := by
  rw [cupProduct_apply, cupProduct_apply, cupProduct_apply, cupProduct_apply]
  have h1 : (fun k : Fin (p + 1) => σ (cupLeft (p + q) r (cupLeft p q k)))
      = (fun k : Fin (p + 1) =>
          σ (Fin.cast (by omega) (cupLeft p (q + r) k))) := by
    funext k
    exact congrArg σ (Fin.ext (by simp only [cast_val_eq, cupLeft_val]))
  have h2 : (fun k : Fin (q + 1) => σ (cupLeft (p + q) r (cupRight p q k)))
      = (fun k : Fin (q + 1) =>
          σ (Fin.cast (by omega)
            (cupRight p (q + r) (cupLeft q r k)))) := by
    funext k
    exact congrArg σ (Fin.ext (by simp only [cast_val_eq, cupLeft_val, cupRight_val]))
  have h3 : (fun k : Fin (r + 1) => σ (cupRight (p + q) r k))
      = (fun k : Fin (r + 1) =>
          σ (Fin.cast (by omega)
            (cupRight p (q + r) (cupRight q r k)))) := by
    funext k
    exact congrArg σ (Fin.ext (by
      simp only [cast_val_eq, cupRight_val]; omega))
  rw [h1, h2, h3, mul_assoc]

/-- **上积结合律**：度数句法 `(p+q)+r` 与 `p+(q+r)` 经 `cochainCast`
桥接（值恒等）。 -/
theorem cupProduct_assoc {p q r : ℕ} (c₁ : Cochain R X p) (c₂ : Cochain R X q)
    (c₃ : Cochain R X r) :
    cupProduct (cupProduct c₁ c₂) c₃
      = cochainCast (by omega) (cupProduct c₁ (cupProduct c₂ c₃)) := by
  ext σ
  exact cupProduct_assoc_apply c₁ c₂ c₃ σ

#print axioms SDG.DifferentialForms.cupProduct_assoc_apply
#print axioms SDG.DifferentialForms.cupProduct_assoc

end SDG.DifferentialForms
