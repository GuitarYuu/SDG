import SDG.NoChoice
import SDG.Infinitesimal
import SDG.Derivative
import SDG.Rational

/-!
# SDG.Taylor

$D_k$ 上的 Kock-Lawvere 公理（Axiom 1'）与 Taylor 公式。

主要内容：
* 多项式求值 `polyEval`（$a \mapsto \sum_i a_i t^i$，用无选择公理的 `finSum`）；
* **$D_k$ 上的 Kock-Lawvere 公理** `IsKockLawvereDkAt`（每个 $f : D_k \to R$
  唯一地是次数 $\le k$ 的多项式）与类 `IsKockLawvereDk`（Axiom 1'：对一切 $k$ 成立）；
* **Taylor 公式**：在 $R$ 是 $\mathbb{Q}$-代数（`[Algebra SDG.Rational.Q R]`，
  基环为无选择公理构造的 `SDG.Rational.Q`）的假设下，
  $$f(x+d) = \sum_{i=0}^{k} \frac{f^{(i)}(x)}{i!}\, d^i \qquad (d \in D_k).$$
-/

/-! ## $D_k$ 上的 Kock-Lawvere 公理（Axiom 1'）

一维高阶无穷小量 $D_k = \{ x \mid x^{k+1} = 0 \}$（Kock 记号，见 `SDG.Infinitesimal`）
上的 Kock-Lawvere 公理断言：每个函数 $f : D_k \to R$ 唯一地是次数 $\le k$ 的多项式
$$f(d) = a_0 + a_1 d + \cdots + a_k d^k \qquad (\forall d \in D_k).$$
这是 Kock 的 **Axiom 1'**（Kock SDG 2006，Axiom 1 的 $D_k$ 版本）；$k = 1$ 时
$D_1 = D$ 且多项式为一次（仿射）函数，正是 `IsKockLawvere_one`（KL for $D$）。

求和用无选择公理的 `finSum`（Mathlib 的 `Finset.sum` 经 `Finset.univ` 依赖选择公理，
见 `SDG.FinSumProd`）。
-/

/-- 多项式求值：$\mathrm{polyEval}\ a\ t = \sum_{i=0}^{n-1} a_i t^i$
（求和用无选择公理的 `finSum`）。 -/
def polyEval (R) [CommRing R] {n : ℕ} (a : Fin n → R) (t : R) : R :=
  finSum R n (fun i : Fin n ↦ a i * t ^ i.1)

/-- **$D_k$ 上的 Kock-Lawvere 公理（第 $k$ 个）**：每个函数 $f : D_k \to R$
唯一地是次数 $\le k$ 的多项式 $d \mapsto \sum_{i=0}^{k} a_i d^i$（$a : \mathrm{Fin}\ (k+1) \to R$）。

这是 Kock 的 Axiom 1'；$k = 1$ 时即 KL for $D$（`IsKockLawvere_one`）。
「存在且唯一」用 `ExistsUnique'` 编码（携带数据的子类型）。 -/
def IsKockLawvereDkAt (R : Type u) [CommRing R] (k : ℕ) : Type u :=
  ∀ f : Dk R k → R,
    ExistsUnique' fun (a : Fin (k+1) → R) ↦
      ∀ d : Dk R k, f d = polyEval R a (d : R)

/-- **Axiom 1'**：对一切 $k \in \mathbb{N}$，每个 $f : D_k \to R$ 唯一地是次数 $\le k$
的多项式。因为 $k = 1$ 情形正是 `IsKockLawvere_one`（KL for $D$），
由 `instIsKockLawvereOne` 证明 `IsKockLawvereDk` 蕴含 `IsKockLawvere_one`。 -/
class IsKockLawvereDk (R : Type u) extends CommRing R where
  isKockLawvereDk : ∀ {k : ℕ}, IsKockLawvereDkAt R k

/-! ## 一阶特例：Axiom 1' 蕴含 KL for $D$

$k = 1$ 时 $D_1 = D$（`D R := Dk R 1`），次数 $\le 1$ 的多项式 $a_0 + a_1 d$
即仿射函数。故 `IsKockLawvereDk`（Axiom 1'）蕴含 `IsKockLawvere_one`（KL for $D$）。
下面先给多项式求值的两个基本引理，再证明该蕴含。 -/

/-- 多项式在 $0$ 处的取值就是常数项：$\mathrm{polyEval}\ a\ 0 = a_0$。 -/
lemma polyEval_zero {R} [CommRing R] {n : ℕ} (a : Fin (n+1) → R) :
    polyEval R a (0 : R) = a 0 := by
  unfold polyEval
  rw [finSum_succ]
  have hrest : finSum R n (fun i : Fin n ↦ a i.succ * (0 : R) ^ (i.succ).1) = 0 := by
    apply finSum_eq_zero
    intro i
    have hv : (i.succ).1 = i.1 + 1 := rfl
    rw [hv]
    have hp : (0 : R) ^ (i.1 + 1) = 0 := zero_pow (n := i.1 + 1) (Nat.succ_ne_zero i.1)
    rw [hp]
    simp
  rw [hrest]
  simp [pow_zero]

/-- 二次多项式求值：$\mathrm{polyEval}\ a\ t = a_0 + a_1 t$（$a : \mathrm{Fin}\ 2 \to R$）。 -/
lemma polyEval_two {R} [CommRing R] (a : Fin 2 → R) (t : R) :
    polyEval R a t = a 0 + a 1 * t := by
  unfold polyEval
  rw [finSum_succ]
  rw [finSum_succ]
  rw [finSum_zero]
  have hsucc : (0 : Fin 1).succ = (1 : Fin 2) := by
    ext
    rfl
  rw [hsucc]
  simp [pow_zero, pow_one]

/-- Axiom 1'（`IsKockLawvereDk`）蕴含 KL for $D$（`IsKockLawvere_one`）：
$k = 1$ 情形 $D_1 = D$，次数 $\le 1$ 的多项式即仿射函数 $d \mapsto a_0 + a_1 d$，
其线性部分 $a_1$ 正是 KL 公理要求的导数 $b$（常数项 $a_0 = f(0)$）。 -/
instance instIsKockLawvereOne {R : Type u} [IsKockLawvereDk R] : IsKockLawvere_one R where
  isKockLawvere_one := by
    intro f
    let h := (IsKockLawvereDk.isKockLawvereDk (k := 1)) f
    refine ⟨h.1 1, ?_, ?_⟩
    · intro d
      have hspec := h.2.1 d
      rw [hspec, polyEval_two]
      have h0spec : f (0 : D R) = h.1 0 := by
        have hraw := h.2.1 (0 : D R)
        change f (0 : D R) = polyEval R h.1 (0 : R) at hraw
        rw [polyEval_zero] at hraw
        exact hraw
      rw [h0spec]
    · intro b hb
      let b' : Fin 2 → R := fun i ↦ if i = 0 then f (0 : D R) else b
      have hb1 : b' 1 = b := by simp [b']
      have hb' : ∀ d : Dk R 1, f d = polyEval R b' (d : R) := by
        intro d
        rw [polyEval_two]
        have hb0 : b' 0 = f (0 : D R) := by simp [b']
        rw [hb0, hb1]
        exact hb d
      have huniq : b' = h.1 := h.2.2 b' hb'
      have hb1' : b' 1 = h.1 1 := congrArg (fun x : Fin 2 → R ↦ x 1) huniq
      rw [hb1] at hb1'
      exact hb1'

/-! ## Q-代数结构（Taylor 公式的除法前提）

Taylor 公式中的系数 $\frac{1}{i!}$ 需要 $R$ 是 $\mathbb{Q}$-代数，即存在
`Algebra SDG.Rational.Q R` 结构：无选择公理构造的有理数环
`SDG.Rational.Q`（见 `SDG.Rational`）通过 `algebraMap` 映入 $R$。
$\frac{1}{n!}$ 即 $\mathbb{Q}$ 中的逆元（`instInvertiblePNat` 给出正整数可逆）
经 `algebraMap` 映入 $R$，记为 `invFactorial R n`。 -/

/-! ## 多项式的形式导数

多项式 $p(t) = \sum_{i=0}^{m+1} c_i t^i$ 的形式导数 $\sum_{j=0}^{m} (j+1)c_{j+1} t^j$
（重新索引为 $\mathrm{Fin}(m+1)$ 求和）。 -/

/-- 多项式 $c$ 的形式导数在 $t$ 处的值：$\sum_{j=0}^{m} (j+1) c_{j+1} t^j$。 -/
def derivEval {R} [CommRing R] {m : ℕ} (c : Fin (m+2) → R) (t : R) : R :=
  finSum R (m+1) (fun j : Fin (m+1) ↦ (j.1 + 1 : R) * c j.succ * t ^ j.1)

/-- 形式导数的另一种求和形式（保留 $i = 0$ 项，其系数为零）与标准形式一致：
$\sum_{i=0}^{m+1} i\, c_i t^{i-1} = \sum_{j=0}^{m} (j+1) c_{j+1} t^j$。 -/
lemma derivEval_eq {R} [CommRing R] {m : ℕ} (c : Fin (m+2) → R) (t : R) :
    finSum R (m + 2) (fun i : Fin (m + 2) ↦ (i.1 : R) * c i * t ^ (i.1 - 1)) = derivEval c t := by
  unfold derivEval
  rw [finSum_succ]
  have h0 : (0 : Fin (m+2)).1 * c 0 * t ^ ((0 : Fin (m+2)).1 - 1) = 0 := by
    simp only [Fin.val_zero, Nat.cast_zero, Nat.zero_sub, pow_zero, zero_mul]
  rw [h0, zero_add]
  apply congrArg (fun φ : Fin (m+1) → R ↦ finSum R (m+1) φ)
  funext i
  simp only [Fin.val_succ, Nat.cast_add, Nat.add_sub_cancel, Nat.cast_one]

/-- 多项式在 $d + e$（$e \in D$）处取值按 $e$ 线性展开：
$\mathrm{polyEval}\ c\ (d+e) = \mathrm{polyEval}\ c\ d + (\mathrm{derivEval}\ c\ d)\, e$。 -/
lemma polyEval_add {R} [CommRing R] {m : ℕ} (c : Fin (m+2) → R) (d : R) (e : D R) :
    polyEval R c (d + (e : R)) = polyEval R c d + derivEval c d * (e : R) := by
  unfold polyEval
  calc
    finSum R (m+2) (fun i : Fin (m+2) ↦ c i * (d + (e : R)) ^ i.1)
        = finSum R (m+2) (fun i : Fin (m+2) ↦ c i * (d ^ i.1 + (i.1 : R) * d ^ (i.1 - 1) * (e : R))) := by
            apply congrArg (fun φ : Fin (m+2) → R ↦ finSum R (m+2) φ)
            funext i
            rw [pow_add_sq_zero d e i.1]
    _ = finSum R (m+2) (fun i : Fin (m+2) ↦ c i * d ^ i.1 + (i.1 : R) * c i * d ^ (i.1 - 1) * (e : R)) := by
            apply congrArg (fun φ : Fin (m+2) → R ↦ finSum R (m+2) φ)
            funext i
            ring
    _ = finSum R (m+2) (fun i : Fin (m+2) ↦ c i * d ^ i.1) +
        finSum R (m+2) (fun i : Fin (m+2) ↦ (i.1 : R) * c i * d ^ (i.1 - 1) * (e : R)) := by
            rw [finSum_add R (m+2)]
    _ = finSum R (m+2) (fun i : Fin (m+2) ↦ c i * d ^ i.1) +
        finSum R (m+2) (fun i : Fin (m+2) ↦ (i.1 : R) * c i * d ^ (i.1 - 1)) * (e : R) := by
            rw [finSum_mul_right R (m+2)]
    _ = polyEval R c d + derivEval c d * (e : R) := by
            rw [derivEval_eq]
            rfl

/-! ## KL-$D_k$ 系数提取

给定 Axiom 1'（`IsKockLawvereDk`），每个 $f(x + \cdot) : D_k \to R$ 有唯一的多项式
展开，其系数记为 $\mathrm{kockCoeffs}\ f\ x$。 -/

/-- $f(x + \cdot)$ 在 $D_k$ 上的 KL 多项式展开的系数（由 Axiom 1' 唯一决定）。 -/
def kockCoeffs {R : Type u} [IsKockLawvereDk R] {k : ℕ}
    (f : R → R) (x : R) : Fin (k+1) → R :=
  ((IsKockLawvereDk.isKockLawvereDk (k := k)) (fun d : Dk R k ↦ f (x + (d : R)))).1

/-- 系数展开的正确性：$f(x + d) = \sum_i (\mathrm{kockCoeffs}\ f\ x)_i d^i$。 -/
lemma kockCoeffs_spec {R : Type u} [IsKockLawvereDk R] {k : ℕ}
    (f : R → R) (x : R) (d : Dk R k) :
    f (x + (d : R)) = polyEval R (kockCoeffs (k := k) f x) (d : R) := by
  change f (x + (d : R)) = polyEval R
    ((IsKockLawvereDk.isKockLawvereDk (k := k) (fun d : Dk R k ↦ f (x + (d : R)))).1) (d : R)
  exact (IsKockLawvereDk.isKockLawvereDk (k := k) (fun d : Dk R k ↦ f (x + (d : R)))).2.1 d

/-- 系数展开的唯一性：任何满足同一多项式等式的系数组等于 KL 系数。 -/
lemma kockCoeffs_unique {R : Type u} [IsKockLawvereDk R] {k : ℕ}
    (f : R → R) (x : R) {a : Fin (k+1) → R}
    (ha : ∀ d : Dk R k, f (x + (d : R)) = polyEval R a (d : R)) :
    a = kockCoeffs (k := k) f x := by
  change a = (IsKockLawvereDk.isKockLawvereDk (k := k) (fun d : Dk R k ↦ f (x + (d : R)))).1
  exact (IsKockLawvereDk.isKockLawvereDk (k := k) (fun d : Dk R k ↦ f (x + (d : R)))).2.2 a ha

/-! ## 导数展开引理

**关键引理**（Taylor 归纳的基石）：若 $g(x + \cdot)$ 在 $D_{m+1}$ 上展开为
$g(x+d) = \sum_{i=0}^{m+1} c_i d^i$，则 $g'(x + \cdot)$ 在 $D_m$ 上展开为
$g'(x+d) = \sum_{j=0}^{m} (j+1) c_{j+1} d^j$。

**证明**：固定 $d \in D_m$。对 $e \in D$，$d + e \in D_{m+1}$，故
$g(x+d+e) = \sum_i c_i (d+e)^i = \sum_i c_i d^i + e \sum_i i c_i d^{i-1}$
（用 `pow_add_sq_zero`）；另一方面由导数的刻画
$g(x+d+e) = g(x+d) + g'(x+d)e$。两式相减得对一切 $e \in D$ 有
$(g'(x+d) - \sum_i i c_i d^{i-1}) e = 0$，由微商消去律（`smul_cancel_d`）得结论。 -/
theorem sderiv_expansion {R} [IsKockLawvere_one R] {m : ℕ}
    (g : R → R) (x : R) (c : Fin (m+2) → R)
    (hc : ∀ d : Dk R (m+1), g (x + (d : R)) = polyEval R c (d : R)) :
    ∀ d' : Dk R m, sderiv g (x + (d' : R)) = derivEval c (d' : R) := by
  intro d'
  apply sub_eq_zero.mp
  apply smul_cancel_d
  intro e
  have h1 := sderiv_spec g (x + (d' : R)) e
  have hEq1 : sderiv g (x + (d' : R)) * (e : R) =
      g ((x + (d' : R)) + (e : R)) - g (x + (d' : R)) := by
    have h1' : g ((x + (d' : R)) + (e : R)) - g (x + (d' : R)) =
        sderiv g (x + (d' : R)) * (e : R) := by
      rw [h1]
      ring
    exact h1'.symm
  have hc1 := hc (Dk.add R d' e)
  have hp := polyEval_add (m := m) c (d' : R) e
  have hc0 := hc (Dk.inclusion R d')
  have hEq2 : derivEval c (d' : R) * (e : R) =
      g ((x + (d' : R)) + (e : R)) - g (x + (d' : R)) := by
    calc
      derivEval c (d' : R) * (e : R)
          = polyEval R c ((d' : R) + (e : R)) - polyEval R c (d' : R) := by
              rw [hp]
              ring
      _ = g (x + ((d' : R) + (e : R))) - g (x + (d' : R)) := by
              have hc1' : g (x + ((d' : R) + (e : R))) = polyEval R c ((d' : R) + (e : R)) := by
                change g (x + (((Dk.add R d' e : Dk R (m+1)) : R))) = polyEval R c (((Dk.add R d' e : Dk R (m+1)) : R))
                exact hc1
              have hc0' : g (x + (d' : R)) = polyEval R c (d' : R) := by
                change g (x + (((Dk.inclusion R d' : Dk R (m+1)) : R))) = polyEval R c (((Dk.inclusion R d' : Dk R (m+1)) : R))
                exact hc0
              rw [← hc1', ← hc0']
      _ = g ((x + (d' : R)) + (e : R)) - g (x + (d' : R)) := by
              rw [← add_assoc]
  calc
    (sderiv g (x + (d' : R)) - derivEval c (d' : R)) * (e : R)
        = sderiv g (x + (d' : R)) * (e : R) - derivEval c (d' : R) * (e : R) := by ring
    _ = (g ((x + (d' : R)) + (e : R)) - g (x + (d' : R))) - derivEval c (d' : R) * (e : R) := by rw [hEq1]
    _ = (g ((x + (d' : R)) + (e : R)) - g (x + (d' : R))) -
        (g ((x + (d' : R)) + (e : R)) - g (x + (d' : R))) := by rw [hEq2]
    _ = 0 := by ring

/-! ## Taylor 公式

**定理（Taylor 公式）**：在 Axiom 1'（`IsKockLawvereDk`）下，对 $d \in D_k$，
$$f(x+d) = \sum_{i=0}^{k} \frac{f^{(i)}(x)}{i!}\, d^i .$$

先证明无除法的系数版本 `taylor_coeff`：$i! \cdot a_i = f^{(i)}(x)$（$a$ 为 $f(x+\cdot)$
的 KL 系数），对 $k$ 归纳：$a_0 = f(x)$；对 $i = j+1$，由「导数展开引理」$f'$ 在
$D_k$ 上的系数是 $(j+1)a_{j+1}$，配合归纳假设得 $j!\,(j+1)a_{j+1} = f^{(j+1)}(x)$，
即 $(j+1)!\,a_{j+1} = f^{(j+1)}(x)$。最后在 $R$ 是 $\mathbb{Q}$-代数时除以 $i!$ 得
Taylor 公式。 -/

/-- $\mathrm{Fin}(n+1)$ 的穷举：元素要么是 $0$，要么是某 $j : \mathrm{Fin}\ n$ 的后继 $j.\mathrm{succ}$。 -/
lemma fin_eq_zero_or_succ {n : ℕ} (i : Fin (n+1)) : i = 0 ∨ ∃ j : Fin n, i = j.succ := by
  by_cases hi : i = 0
  · exact Or.inl hi
  · right
    have hi1 : i.1 ≠ 0 := by
      intro h
      apply hi
      ext
      exact h
    let j : Fin n := ⟨i.1 - 1, by omega⟩
    refine ⟨j, ?_⟩
    apply Fin.ext
    have hpred : (i.1 - 1) + 1 = i.1 := by omega
    simp [j, hpred]

/-- **Taylor 系数（无除法的系数版本）**：设 $a = \mathrm{kockCoeffs}\ f\ x$（$f(x+\cdot)$
在 $D_k$ 上的 KL 系数），则对每个 $i$，
$$i! \cdot a_i = f^{(i)}(x).$$
由 Axiom 1' 与「导数展开引理」对 $k$ 归纳证明，不需除法。 -/
theorem taylor_coeff {R : Type u} [IsKockLawvereDk R] :
    ∀ (k : ℕ) (f : R → R) (x : R), ∀ i : Fin (k+1),
      (Nat.factorial i.1 : R) * kockCoeffs f x i = sderiv^[i.1] f x := by
  intro k
  induction k with
  | zero =>
      intro f x i
      rcases fin_eq_zero_or_succ i with hi | ⟨j, hj⟩
      · have hzero_i : kockCoeffs f x i = f x := by
          have hspec := kockCoeffs_spec f x (0 : Dk R 0)
          rw [hi]
          simpa [polyEval_zero] using hspec.symm
        rw [hi] at hzero_i
        rw [hi]
        simp [hzero_i]
      · exact False.elim (Nat.not_lt_zero j.1 j.2)
  | succ k ih =>
      intro f x i
      rcases fin_eq_zero_or_succ i with hi | ⟨j, hj⟩
      · have hzero_i : kockCoeffs f x i = f x := by
          have hspec := kockCoeffs_spec f x (0 : Dk R (k + 1))
          rw [hi]
          simpa [polyEval_zero] using hspec.symm
        rw [hi] at hzero_i
        rw [hi]
        simp [hzero_i]
      · subst i
        have hderex := sderiv_expansion (m := k) (g := f) (x := x)
            (c := kockCoeffs f x) (kockCoeffs_spec f x)
        have hb : ∀ d' : Dk R k,
            sderiv f (x + (d' : R)) =
              polyEval R (fun j : Fin (k+1) ↦ (j.1 + 1 : R) * (kockCoeffs f x) j.succ) (d' : R) := by
          intro d'
          simpa [derivEval, polyEval] using hderex d'
        have hb' : (fun j : Fin (k+1) ↦ (j.1 + 1 : R) * (kockCoeffs f x) j.succ) =
            kockCoeffs (sderiv f) x := by
          exact kockCoeffs_unique (sderiv f) x hb
        have hj' := ih (sderiv f) x j
        have hk : (Nat.factorial j.1 : R) * ((j.1 + 1 : R) * (kockCoeffs f x) j.succ) =
            sderiv^[j.1] (sderiv f) x := by
          rw [← congrFun hb' j] at hj'
          exact hj'
        calc
          (Nat.factorial (j.succ).1 : R) * (kockCoeffs f x) j.succ
              = (Nat.factorial (j.1 + 1) : R) * (kockCoeffs f x) j.succ := by
                  have hv : (j.succ).1 = j.1 + 1 := rfl
                  rw [hv]
          _ = (Nat.factorial j.1 : R) * ((j.1 + 1 : R) * (kockCoeffs f x) j.succ) := by
                  rw [Nat.factorial_succ]
                  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
                  ring
          _ = sderiv^[j.1 + 1] f x := by
                  simp [hk]
          _ = sderiv^[(j.succ).1] f x := by
                  have hv : (j.succ).1 = j.1 + 1 := rfl
                  rw [hv]

/-- $\mathbb{Q}$ 中正整数 $n$ 的逆元 $\frac{1}{n}$（`instInvertiblePNat` 给出）。 -/
def invNatQ (n : ℕ) (hn : n ≠ 0) : SDG.Rational.Q :=
  (SDG.Rational.instInvertiblePNat ⟨n, by omega⟩).invOf

/-- 阶乘的逆元 $\frac{1}{n!}$ 在 $R$ 中：$\mathbb{Q}$ 中的 $1/n!$ 经 `algebraMap`
映入 $R$（$R$ 是 $\mathbb{Q}$-代数，`[Algebra SDG.Rational.Q R]`）。 -/
def invFactorial (R : Type u) [CommRing R] [Algebra SDG.Rational.Q R]
    (n : ℕ) : R :=
  algebraMap SDG.Rational.Q R (invNatQ (Nat.factorial n) (Nat.factorial_ne_zero n))

/-- $\frac{1}{n!} \cdot n! = 1$（`algebraMap` 是环同态，且 $\mathbb{Q}$ 中 $n!$ 可逆）。 -/
lemma invFactorial_mul (R : Type u) [CommRing R] [Algebra SDG.Rational.Q R] (n : ℕ) :
    invFactorial R n * (Nat.factorial n : R) = 1 := by
  unfold invFactorial invNatQ
  rw [← map_natCast (algebraMap SDG.Rational.Q R : SDG.Rational.Q →+* R) (Nat.factorial n)]
  rw [← map_mul (algebraMap SDG.Rational.Q R)]
  have hh : (SDG.Rational.instInvertiblePNat (⟨Nat.factorial n, Nat.factorial_pos n⟩ : ℕ+)).invOf *
      (Nat.factorial n : SDG.Rational.Q) = 1 :=
    (SDG.Rational.instInvertiblePNat (⟨Nat.factorial n, Nat.factorial_pos n⟩ : ℕ+)).invOf_mul_self
  rw [hh]
  exact map_one (algebraMap SDG.Rational.Q R : SDG.Rational.Q →+* R)

/-- **Taylor 公式**：在 Axiom 1'（`IsKockLawvereDk`）且 $R$ 是 $\mathbb{Q}$-代数
（`[Algebra SDG.Rational.Q R]`）的假设下，对 $d \in D_k$：
$$f(x+d) = \sum_{i=0}^{k} \frac{f^{(i)}(x)}{i!}\, d^i .$$
由 `taylor_coeff`（$i!\,a_i = f^{(i)}(x)$）两边乘 $\frac{1}{i!}$ 得到。 -/
theorem taylor_formula {R : Type u} [IsKockLawvereDk R] [Algebra SDG.Rational.Q R]
    (f : R → R) (x : R) {k : ℕ} (d : Dk R k) :
    f (x + (d : R)) =
      polyEval R (fun i : Fin (k+1) ↦ invFactorial R i.1 * sderiv^[i.1] f x) (d : R) := by
  have hspec := kockCoeffs_spec f x d
  have hk : kockCoeffs f x = fun i : Fin (k+1) ↦ invFactorial R i.1 * sderiv^[i.1] f x := by
    funext i
    have hc := taylor_coeff k f x i
    calc
      kockCoeffs f x i
          = (invFactorial R i.1 * (Nat.factorial i.1 : R)) * kockCoeffs f x i := by
              rw [invFactorial_mul, one_mul]
      _ = invFactorial R i.1 * ((Nat.factorial i.1 : R) * kockCoeffs f x i) := by rw [← mul_assoc]
      _ = invFactorial R i.1 * sderiv^[i.1] f x := by rw [hc]
  rw [hk] at hspec
  exact hspec
