import SDG.NoChoice
import SDG.Infinitesimal
import SDG.Taylor

/-!
# SDG.KockLawvereDkn

$D_k(n)$ 上的 Kock-Lawvere 公理（Kock 的 Axiom 1'' 的 $k$ 阶版本）。

一维情形 $D_k$（Axiom 1'）见 `SDG.Taylor`（`IsKockLawvereDk`）。这里处理
$n$ 维高阶无穷小邻域 $D_k(n) = \{ x \in R^n \mid \text{任意 } k+1 \text{ 个分量的
乘积为零} \}$ 上的 KL 公理：

> 每个函数 $f : D_k(n) \to R$ 唯一地是总次数 $\le k$ 的多项式
> $$f(x_1,\dots,x_n) = \sum_{|\alpha| \le k} a_\alpha\, x_1^{\alpha_1}\cdots x_n^{\alpha_n}
> \qquad (\forall x \in D_k(n)).$$

$k = 1$ 时 $D_1(n) = D(n)$ 且多项式是仿射的（$a + \sum_i b_i x_i$），正是
Axiom 1''（「KL for all $D(n)$」，见 `IsKockLawvereDknAt` 的 $k=1$ 情形）；
$n = 1$ 时回到一维情形 $D_k$（`IsKockLawvereDkAt`）。

主要内容：
* **多元多项式的系数** `PolyCoeff R k n`：总次数 $\le k$ 的 $n$ 元多项式的系数类型，
  定义为**归纳类型**（$R$ 是参数、$k,n$ 是指标）。用「首变量 $x_0$ 的次数 $j$」
  递归分解（$x_0^j$ 的系数是 $n-1$ 个变量的总次数 $\le k-j$ 的多项式的系数），
  从而与「总次数 $\le k$ 的单项式」一一对应，并且**无需选择公理**（只用归纳类型
  与无选择的 `finSum`，不依赖 `Fintype`——本仓库的 `Fintype` 依赖
  `Classical.choice`，见 `SDG.FinSumProd`）；
* **求值** `polyEvalDkn R k n a x`：系数 $a$ 在点 $x : R^n$ 处的多项式值；
* **KL 公理** `IsKockLawvereDknAt R k n`（第 $(k,n)$ 个）：每个 $f : D_k(n) \to R$
  唯一地由某个总次数 $\le k$ 的多项式给出，与类 `IsKockLawvereDkn`
  （Axiom 1'' 的 $k$ 阶版本：对一切 $k,n$ 成立）；
* **一维特例**：`IsKockLawvereDknAt R k 1` 与 `IsKockLawvereDkAt R k` 互相蕴含
  （$D_k(1) \cong D_k$，系数类型 `PolyCoeff R k 1$ 与 $\mathrm{Fin}\ (k+1) \to R$
  等价 `polyCoeffOneEquiv`）。

**关于选择公理**：全部声明无选择公理（`finSum` 求和，见 `SDG.FinSumProd`），
通过本仓库的无选择公理 linter。
-/

/-! ## 多元多项式的系数（总次数 $\le k$）与求值

$n$ 元、总次数 $\le k$ 的多项式的系数集合定义为**归纳类型**（参数 $R$，指标
$k, n$）：$n = 0$ 时只有常数项（构造子 `const`）；$n + 1$ 时把首变量 $x_0$ 的
次数 $j \in \{0,\dots,k\}$ 分解出来，$x_0^j$ 的系数是剩下 $n$ 个变量的总次数
$\le k - j$ 的多项式的系数（构造子 `cons`）。这与「总次数 $\le k$ 的单项式」的
集合一一对应（$\sum_{j=0}^k \#\{\alpha : |\alpha| \le k-j\}$）。
-/

/-- 总次数 $\le k$ 的 $n$ 元多项式的系数类型（归纳类型）：$R$ 是参数、$k, n$ 是指标。
$\mathrm{PolyCoeff}\ R\ k\ 0$ 的构造子是 `const`（$r : R$ 即常数项）；
$\mathrm{PolyCoeff}\ R\ k\ (n+1)$ 的构造子是 `cons`，参数为
$(j : \mathrm{Fin}\ (k+1)) \to \mathrm{PolyCoeff}\ R\ (k - j)\ n$（$j$ 是首变量
$x_0$ 的次数）。与「总次数 $\le k$ 的单项式 $x^\alpha$（$|\alpha| \le k$）」
一一对应；只依赖归纳类型与 `finSum`，**无需选择公理**（不依赖 `Fintype`）。 -/
inductive PolyCoeff (R : Type u) : ℕ → ℕ → Type u where
  | const : {k : ℕ} → R → PolyCoeff R k 0
  | cons : {k : ℕ} → {n : ℕ} → ((j : Fin (k + 1)) → PolyCoeff R (k - (j : ℕ)) n) → PolyCoeff R k (n + 1)

/-- 多项式求值：$\mathrm{polyEvalDkn}\ R\ k\ n\ a\ x$ 是系数 $a$ 在点
$x : R^n$ 处的值。递归地：$n = 0$ 时即常数（`const`）；$n + 1$ 时把首变量 $x_0$
的次数 $j$ 分离
$$\sum_{j=0}^{k} (\text{系数 } a_j \text{ 在剩余坐标上的值}) \cdot x_0^j .$$
求和用无选择公理的 `finSum`（见 `SDG.FinSumProd`）。 -/
def polyEvalDkn (R : Type u) [CommRing R] (k : ℕ) :
    (n : ℕ) → PolyCoeff R k n → (Fin n → R) → R
  | 0, PolyCoeff.const r, _x => r
  | n + 1, PolyCoeff.cons a, x =>
      finSum R (k + 1) (fun j : Fin (k + 1) ↦
        polyEvalDkn R (k - (j : ℕ)) n (a j) (fun i : Fin n ↦ x i.succ) * x 0 ^ (j : ℕ))

/-- 零元情况：$n = 0$ 时系数是 `PolyCoeff.const r`，求值即 $r$。 -/
lemma polyEvalDkn_zero (R : Type u) [CommRing R] (k : ℕ) (r : R) (x : Fin 0 → R) :
    polyEvalDkn R k 0 (PolyCoeff.const r : PolyCoeff R k 0) x = r := by
  rfl

/-- 一元情形：`polyEvalDkn R k 1 a x = \sum_{j=0}^k a_j x_0^j$，与一维多项式求值
`polyEval`（`SDG.Taylor`）一致。 -/
lemma polyEvalDkn_one (R : Type u) [CommRing R] (k : ℕ)
    (a : (j : Fin (k+1)) → R) (x : Fin 1 → R) :
    polyEvalDkn R k 1 (PolyCoeff.cons (fun j : Fin (k+1) ↦ PolyCoeff.const (a j)) : PolyCoeff R k 1) x =
      finSum R (k + 1) (fun j : Fin (k + 1) ↦ a j * x 0 ^ (j : ℕ)) := by
  simp [polyEvalDkn]

/-! ## 一元系数类型：$\mathrm{PolyCoeff}\ R\ k\ 1 \cong \mathrm{Fin}\ (k+1) \to R$

归纳类型下 `PolyCoeff R k 1` 的元素都是 `cons f$`（$f : (j : \mathrm{Fin}\ (k+1)) \to
\mathrm{PolyCoeff}\ R\ (k-j)\ 0$），而每个 $\mathrm{PolyCoeff}\ R\ \cdot\ 0$ 的元素
都是 `const r`。故一元系数类型与 $\mathrm{Fin}\ (k+1) \to R$ 等价
（`polyCoeffOneEquiv`），求值与 `polyEval` 一致（`polyEvalDkn_eq_polyEval`）。
-/

/-- 一元系数取分量：$\mathrm{polyCoeffOneToFun}\ R\ k\ (\mathrm{cons}\ f)\ j$
是 $f\ j = \mathrm{const}\ r$ 中的 $r$。 -/
def polyCoeffOneToFun (R : Type u) [CommRing R] (k : ℕ) : PolyCoeff R k 1 → (Fin (k+1) → R)
  | PolyCoeff.cons f => fun j ↦ match f j with | PolyCoeff.const r => r

/-- 由分量函数构造一元系数：$\mathrm{polyCoeffOneInvFun}\ R\ k\ b =
\mathrm{cons}\ (j \mapsto \mathrm{const}\ (b\ j))$。 -/
def polyCoeffOneInvFun (R : Type u) [CommRing R] (k : ℕ) : (Fin (k+1) → R) → PolyCoeff R k 1 :=
  fun b ↦ PolyCoeff.cons (fun j ↦ PolyCoeff.const (b j))

/-- 一元系数类型与 $\mathrm{Fin}\ (k+1) \to R$ 的等价（`toFun` = `polyCoeffOneToFun`，
`invFun` = `polyCoeffOneInvFun`）。 -/
def polyCoeffOneEquiv (R : Type u) [CommRing R] (k : ℕ) : PolyCoeff R k 1 ≃ (Fin (k+1) → R) where
  toFun := polyCoeffOneToFun R k
  invFun := polyCoeffOneInvFun R k
  left_inv := by
    intro a
    cases a with
    | cons f =>
        apply congrArg PolyCoeff.cons
        funext j
        have hred : polyCoeffOneToFun R k (PolyCoeff.cons f) j =
            match f j with | PolyCoeff.const r => r := by
          rfl
        rw [hred]
        cases f j with
        | const r => rfl
  right_inv := by
    intro b
    rfl

/-- 一元求值的一致：`polyEvalDkn R k 1 a x = polyEval R (polyCoeffOneToFun R k a) (x 0)`。 -/
lemma polyEvalDkn_eq_polyEval (R : Type u) [CommRing R] (k : ℕ)
    (a : PolyCoeff R k 1) (x : Fin 1 → R) :
    polyEvalDkn R k 1 a x = polyEval R (polyCoeffOneToFun R k a) (x 0) := by
  cases a with
  | cons f =>
      calc
        polyEvalDkn R k 1 (PolyCoeff.cons f) x
            = finSum R (k + 1) (fun j : Fin (k + 1) ↦
                polyEvalDkn R (k - (j : ℕ)) 0 (f j) (fun i : Fin 0 ↦ x i.succ) * x 0 ^ (j : ℕ)) := by
              rfl
        _ = finSum R (k + 1) (fun j : Fin (k + 1) ↦
                (match f j with | PolyCoeff.const r => r) * x 0 ^ (j : ℕ)) := by
              apply congrArg (fun φ : Fin (k + 1) → R ↦ finSum R (k + 1) φ)
              funext j
              have h : polyEvalDkn R (k - (j : ℕ)) 0 (f j) (fun i : Fin 0 ↦ x i.succ) =
                  match f j with | PolyCoeff.const r => r := by
                cases f j with
                | const r => rfl
              rw [h]
        _ = polyEval R (polyCoeffOneToFun R k (PolyCoeff.cons f)) (x 0) := by
              rfl

/-- 一元求值的反向一致：`polyEvalDkn R k 1 (polyCoeffOneInvFun R k b) (x : Fin 1 → R) =
\mathrm{polyEval}\ R\ b\ (x_0)$。 -/
lemma polyEvalDkn_invFun (R : Type u) [CommRing R] (k : ℕ)
    (b : Fin (k+1) → R) (x : Fin 1 → R) :
    polyEvalDkn R k 1 (polyCoeffOneInvFun R k b) (x : Fin 1 → R) = polyEval R b (x 0) := by
  rw [polyEvalDkn_eq_polyEval]
  rfl

/-! ## 仿射系数（$k = 1$ 的多项式即仿射函数）

$k = 1$ 时 $D_1(n) = D(n)$（`Dn`），总次数 $\le 1$ 的多项式即仿射函数
$f(x) = c + \sum_i l_i x_i$。归纳类型的系数 `PolyCoeff R 1 n` 需提取「常数部分」
与「线性部分」才能回到仿射系数 $R \times (\mathrm{Fin}\ n \to R)$：
* `polyCoeff0eval`：零次多项式（$k = 0$）的常数值（`PolyCoeff R 0 n$ 是 $R$ 的包装）；
* `polyCoeff1const` / `polyCoeff1lin`：仿射系数（$k = 1$）的常数与线性部分；
* `polyEvalDkn_affine`：仿射形式 $\mathrm{polyEvalDkn}\ R\ 1\ n\ a\ x =
  \mathrm{polyCoeff1const}\ R\ n\ a + \sum_i \mathrm{polyCoeff1lin}\ R\ n\ a\ i \cdot x_i$；
* `polyEvalDkn_axis`：坐标轴上取值 $c + l_k d$。

这些结果把 `PolyCoeff R 1 n` 与仿射系数 $R \times (\mathrm{Fin}\ n \to R)$ 对齐，
是「`IsKockLawvereDkn` 蕴含 $R$ 微线性」（Prop I.6.4 的 $k$ 阶推广，见
`SDG.Microlinear`）中唯一性部分的基础。
-/

/-- 零次多项式（$k = 0$）的常数值：$\mathrm{PolyCoeff}\ R\ 0\ n$ 是 $R$ 的包装
（递归地把 `cons` 剥掉）。 -/
def polyCoeff0eval (R : Type u) [CommRing R] : (n : ℕ) → PolyCoeff R 0 n → R
  | 0, PolyCoeff.const r => r
  | n + 1, PolyCoeff.cons g => polyCoeff0eval R n (g 0)

/-- 仿射系数（$k = 1$）的常数部分。 -/
def polyCoeff1const (R : Type u) [CommRing R] : (n : ℕ) → PolyCoeff R 1 n → R
  | 0, PolyCoeff.const r => r
  | n + 1, PolyCoeff.cons f => polyCoeff1const R n (f 0)

/-- 仿射系数（$k = 1$）的线性部分：`polyCoeff1lin R n a i` 是 $x_i$ 的系数。
用 `Fin.cases` 定义（$0$ 处取 `f 1` 的常数值、$k.\mathrm{succ}$ 处递归），保证在
$0$ 与 $k.\mathrm{succ}$ 上**定义性**约简。 -/
def polyCoeff1lin (R : Type u) [CommRing R] : (n : ℕ) → PolyCoeff R 1 n → (Fin n → R)
  | 0, _ => fun _i : Fin 0 ↦ 0
  | n + 1, PolyCoeff.cons f => fun i : Fin (n + 1) ↦
      Fin.cases (polyCoeff0eval R n (f 1)) (fun k : Fin n ↦ polyCoeff1lin R n (f 0) k) i

/-- `polyCoeff1lin` 在指标 $0$ 处的取值（`Fin.cases` 定义性约简）。 -/
lemma polyCoeff1lin_zero (R : Type u) [CommRing R] (n : ℕ)
    (f : (j : Fin 2) → PolyCoeff R (1 - (j : ℕ)) n) :
    polyCoeff1lin R (n+1) (PolyCoeff.cons f) 0 = polyCoeff0eval R n (f 1) := by
  rfl

/-- `polyCoeff1lin` 在后继指标 $k.\mathrm{succ}$ 处的取值（`Fin.cases` 定义性约简）。 -/
lemma polyCoeff1lin_succ (R : Type u) [CommRing R] (n : ℕ)
    (f : (j : Fin 2) → PolyCoeff R (1 - (j : ℕ)) n) (k : Fin n) :
    polyCoeff1lin R (n+1) (PolyCoeff.cons f) k.succ = polyCoeff1lin R n (f 0) k := by
  rfl

/-- $\mathrm{finSum}\ R\ 2\ f = f_0 + f_1$（两项和，`finSum_succ` 两次的便捷形式）。 -/
lemma finSum_two (R : Type u) [AddCommMonoid R] (f : Fin 2 → R) :
    finSum R 2 f = f 0 + f 1 := by
  rw [finSum_succ R 1, finSum_succ R 0, finSum_zero]
  have h : (0 : Fin 1).succ = (1 : Fin 2) := by ext; rfl
  rw [h, add_zero]

/-- 零次多项式求值即常数值：
$\mathrm{polyEvalDkn}\ R\ 0\ n\ a\ x = \mathrm{polyCoeff0eval}\ R\ n\ a$。 -/
lemma polyEvalDkn_zero_degree (R : Type u) [CommRing R] (n : ℕ) (a : PolyCoeff R 0 n) (x : Fin n → R) :
    polyEvalDkn R 0 n a x = polyCoeff0eval R n a := by
  induction n with
  | zero =>
      cases a with
      | const r => rfl
  | succ n ih =>
      cases a with
      | cons g =>
          rw [polyEvalDkn]
          change finSum R 1 (fun j : Fin 1 ↦
              polyEvalDkn R (0 - (j : ℕ)) n (g j) (fun i : Fin n ↦ x i.succ) * x 0 ^ (j : ℕ)) =
            polyCoeff0eval R n (g 0)
          rw [finSum_succ R 0, finSum_zero]
          simp only [Fin.val_zero, pow_zero, mul_one, add_zero, Nat.sub_zero]
          rw [ih (g 0) (fun i : Fin n ↦ x i.succ)]

/-- 仿射多项式在零点取值即常数部分：
$\mathrm{polyEvalDkn}\ R\ 1\ n\ a\ 0 = \mathrm{polyCoeff1const}\ R\ n\ a$。 -/
lemma polyEvalDkn_zero_const (R : Type u) [CommRing R] (n : ℕ) (a : PolyCoeff R 1 n) :
    polyEvalDkn R 1 n a (0 : Fin n → R) = polyCoeff1const R n a := by
  induction n with
  | zero =>
      cases a with
      | const r => rfl
  | succ n ih =>
      cases a with
      | cons f =>
          rw [polyEvalDkn]
          change finSum R 2 (fun j : Fin 2 ↦
              polyEvalDkn R (1 - (j : ℕ)) n (f j) (fun i : Fin n ↦ (0 : Fin (n+1) → R) i.succ) * (0 : R) ^ (j : ℕ)) =
            polyCoeff1const R n (f 0)
          rw [finSum_two R (fun j : Fin 2 ↦
              polyEvalDkn R (1 - (j : ℕ)) n (f j) (fun i : Fin n ↦ (0 : Fin (n+1) → R) i.succ) * (0 : R) ^ (j : ℕ))]
          simp only [Fin.val_zero, Fin.val_one, Nat.sub_zero, pow_zero, pow_one, mul_one, mul_zero, add_zero]
          change polyEvalDkn R 1 n (f 0) (0 : Fin n → R) = polyCoeff1const R n (f 0)
          rw [ih (f 0)]

/-- **仿射形式**：$\mathrm{polyEvalDkn}\ R\ 1\ n\ a\ x =
\mathrm{polyCoeff1const}\ R\ n\ a + \sum_i \mathrm{polyCoeff1lin}\ R\ n\ a\ i \cdot x_i$
（总次数 $\le 1$ 的多项式即仿射函数；对 $n$ 归纳）。 -/
lemma polyEvalDkn_affine (R : Type u) [CommRing R] (n : ℕ) (a : PolyCoeff R 1 n) (x : Fin n → R) :
    polyEvalDkn R 1 n a x =
      polyCoeff1const R n a + finSum R n (fun i : Fin n ↦ polyCoeff1lin R n a i * x i) := by
  induction n with
  | zero =>
      cases a with
      | const r =>
          simp [polyEvalDkn, polyCoeff1const, polyCoeff1lin]
  | succ n ih =>
      cases a with
      | cons f =>
          have hL : polyEvalDkn R 1 (n + 1) (PolyCoeff.cons f) x =
              (polyCoeff1const R n (f 0) + finSum R n (fun i : Fin n ↦ polyCoeff1lin R n (f 0) i * x i.succ))
                + polyCoeff0eval R n (f 1) * x 0 := by
            rw [polyEvalDkn]
            change finSum R 2 (fun j : Fin 2 ↦
                polyEvalDkn R (1 - (j : ℕ)) n (f j) (fun i : Fin n ↦ x i.succ) * x 0 ^ (j : ℕ)) =
              (polyCoeff1const R n (f 0) + finSum R n (fun i : Fin n ↦ polyCoeff1lin R n (f 0) i * x i.succ))
                + polyCoeff0eval R n (f 1) * x 0
            rw [finSum_two R (fun j : Fin 2 ↦
                polyEvalDkn R (1 - (j : ℕ)) n (f j) (fun i : Fin n ↦ x i.succ) * x 0 ^ (j : ℕ))]
            simp only [Fin.val_zero, Fin.val_one, Nat.sub_zero, pow_zero, pow_one, mul_one]
            rw [ih (f 0) (fun i : Fin n ↦ x i.succ)]
            rw [polyEvalDkn_zero_degree R n (f 1)]
          have hR : polyCoeff1const R (n + 1) (PolyCoeff.cons f)
              + finSum R (n + 1) (fun i : Fin (n+1) ↦ polyCoeff1lin R (n+1) (PolyCoeff.cons f) i * x i) =
              polyCoeff1const R n (f 0)
                + (polyCoeff0eval R n (f 1) * x 0 + finSum R n (fun i : Fin n ↦ polyCoeff1lin R n (f 0) i * x i.succ)) := by
            change polyCoeff1const R n (f 0)
              + finSum R (n + 1) (fun i : Fin (n+1) ↦ polyCoeff1lin R (n+1) (PolyCoeff.cons f) i * x i) =
              polyCoeff1const R n (f 0)
                + (polyCoeff0eval R n (f 1) * x 0 + finSum R n (fun i : Fin n ↦ polyCoeff1lin R n (f 0) i * x i.succ))
            rw [finSum_succ R n]
            simp [polyCoeff1lin_zero, polyCoeff1lin_succ]
          rw [hL, hR]
          abel

/-- 坐标轴上的取值：$\mathrm{polyEvalDkn}\ R\ 1\ n\ a\ (e_k(d)) =
\mathrm{polyCoeff1const}\ R\ n\ a + \mathrm{polyCoeff1lin}\ R\ n\ a\ k \cdot d$
（由 `polyEvalDkn_affine` 与 `finSum_eq_single` 把和塌缩为单项）。 -/
lemma polyEvalDkn_axis (R : Type u) [CommRing R] (n : ℕ) (a : PolyCoeff R 1 n) (k : Fin n) (d : D R) :
    polyEvalDkn R 1 n a (Dn.embed R k d : Fin n → R) =
      polyCoeff1const R n a + polyCoeff1lin R n a k * (d : R) := by
  rw [polyEvalDkn_affine R n a (Dn.embed R k d : Fin n → R)]
  have hsum : finSum R n (fun i : Fin n ↦ polyCoeff1lin R n a i * (Dn.embed R k d).1 i) =
      polyCoeff1lin R n a k * (d : R) := by
    have hterm : ∀ i : Fin n, polyCoeff1lin R n a i * (Dn.embed R k d).1 i =
        if i = k then polyCoeff1lin R n a k * (d : R) else 0 := by
      intro i
      by_cases hik : i = k
      · subst i
        simp [Dn.embed, Function.update]
      · simp [Dn.embed, Function.update, hik]
    calc
      finSum R n (fun i ↦ polyCoeff1lin R n a i * (Dn.embed R k d).1 i)
          = finSum R n (fun i ↦ if i = k then polyCoeff1lin R n a k * (d : R) else 0) := by
            exact congrArg (fun φ : Fin n → R ↦ finSum R n φ) (funext hterm)
      _ = polyCoeff1lin R n a k * (d : R) := finSum_eq_single R k (polyCoeff1lin R n a k * (d : R))
  rw [hsum]

/-! ## $D_k(n)$ 上的 Kock-Lawvere 公理（Axiom 1'' 的 $k$ 阶版本）

高阶无穷小邻域 $D_k(n)$（`SDG.Infinitesimal`）上的 KL 公理断言：每个
$f : D_k(n) \to R$ 唯一地是总次数 $\le k$ 的多项式。这是 Kock 的 Axiom 1''
（KL for all $D(n)$）的 $k$ 阶推广：$k = 1$ 时 $D_1(n) = D(n)$ 且多项式为仿射
（$a + \sum_i b_i x_i$），即 Axiom 1''；$n = 1$ 时 $D_k(1) \cong D_k$ 且多项式
是一元的（次数 $\le k$），即 Axiom 1'（`IsKockLawvereDkAt`）。
「存在且唯一」用 `ExistsUnique'` 编码（携带数据的子类型，见
`SDG.Infinitesimal`）。 -/

/-- **$D_k(n)$ 上的 Kock-Lawvere 公理（第 $(k,n)$ 个）**：每个函数
$f : D_k(n) \to R$ 唯一地是总次数 $\le k$ 的多项式
$$f(x) = \sum_{|\alpha| \le k} a_\alpha x^\alpha \qquad (\forall x \in D_k(n)),$$
即存在唯一的总次数 $\le k$ 的系数 $a : \mathrm{PolyCoeff}\ R\ k\ n$ 使上式成立。
这是 Kock 的 Axiom 1'' 的 $k$ 阶版本；$k = 1$ 时即「KL for all $D(n)$」
（仿射情形），$n = 1$ 时回到一维 `IsKockLawvereDkAt`（Axiom 1'）。 -/
def IsKockLawvereDknAt (R : Type u) [CommRing R] (k n : ℕ) : Type u :=
  ∀ f : Dkn R k n → R,
    ExistsUnique' fun (a : PolyCoeff R k n) ↦
      ∀ x : Dkn R k n, f x = polyEvalDkn R k n a (x : Fin n → R)

/-- **Axiom 1'' 的 $k$ 阶版本**：对一切 $k, n \in \mathbb{N}$，每个
$f : D_k(n) \to R$ 唯一地是总次数 $\le k$ 的多项式。由于 $n = 1$ 情形正是
`IsKockLawvereDkAt`（Axiom 1'，见 `SDG.Taylor`），由此类可推出
`IsKockLawvereDk`；$k = 1$、$n$ 任意时是 Axiom 1''（「KL for all $D(n)$」）。 -/
class IsKockLawvereDkn (R : Type u) extends CommRing R where
  isKockLawvereDkn : ∀ {k n : ℕ}, IsKockLawvereDknAt R k n

/-! ## 一维特例：$D_k(1)$ 上的 KL 公理即 $D_k$ 上的 KL 公理（Axiom 1'）

$n = 1$ 时 $D_k(1) \cong D_k$（`Dk_equiv_Dkn1`，见 `SDG.Infinitesimal`），
且系数类型 `PolyCoeff R k 1$ 与 $\mathrm{Fin}\ (k+1) \to R$ 等价
（`polyCoeffOneEquiv`）。故 `IsKockLawvereDknAt R k 1$（$D_k(1)$ 上唯一的总次数
$\le k$ 多项式）与 `IsKockLawvereDkAt R k$（Axiom 1'，$D_k$ 上唯一的次数 $\le k$
一元多项式）等价。证明经 `Dk_equiv_Dkn1` 在 $D_k$ 与 $D_k(1)$ 之间传递函数，
一元求值用 `polyEvalDkn_eq_polyEval`/`polyEvalDkn_invFun` 与 `polyEval`
（`SDG.Taylor`）对齐。 -/

/-- $D_k(1)$ 上的 KL 公理蕴含 $D_k$ 上的 KL 公理（Axiom 1'）：
`IsKockLawvereDknAt R k 1 → IsKockLawvereDkAt R k`。

**注意**：`IsKockLawvereDknAt`/`IsKockLawvereDkAt` 是携带数据的类型（`ExistsUnique'`
子类型）而非命题，故用 `def` 而非 `theorem`。 -/
def kL_DkAt_of_kL_DknAt (R : Type u) [CommRing R] (k : ℕ)
    (h : IsKockLawvereDknAt R k 1) : IsKockLawvereDkAt R k := by
  intro f
  let f' : Dkn R k 1 → R := fun x ↦ f ((Dk_equiv_Dkn1 R k).symm x)
  let ha := h f'
  refine ⟨polyCoeffOneToFun R k ha.1, ?_, ?_⟩
  · intro d
    have hsymm : (Dk_equiv_Dkn1 R k).symm ((Dk_equiv_Dkn1 R k) d) = d :=
      (Dk_equiv_Dkn1 R k).symm_apply_apply d
    have hx0 : (((Dk_equiv_Dkn1 R k) d : Dkn R k 1) : Fin 1 → R) 0 = (d : R) := by
      rfl
    calc
      f d = f' ((Dk_equiv_Dkn1 R k) d) := by
        dsimp [f']
        rw [hsymm]
      _ = polyEvalDkn R k 1 ha.1 (((Dk_equiv_Dkn1 R k) d : Dkn R k 1) : Fin 1 → R) :=
        ha.2.1 ((Dk_equiv_Dkn1 R k) d)
      _ = polyEval R (polyCoeffOneToFun R k ha.1) (d : R) := by
        rw [polyEvalDkn_eq_polyEval]
        rw [hx0]
  · intro b hb
    have hb' : ∀ x : Dkn R k 1,
        f' x = polyEvalDkn R k 1 (polyCoeffOneInvFun R k b) (x : Fin 1 → R) := by
      intro x
      have hsymm : (Dk_equiv_Dkn1 R k) ((Dk_equiv_Dkn1 R k).symm x) = x :=
        (Dk_equiv_Dkn1 R k).apply_symm_apply x
      have hx0 : (((Dk_equiv_Dkn1 R k).symm x : Dk R k) : R) = (x : Fin 1 → R) 0 := by
        rfl
      calc
        f' x = f ((Dk_equiv_Dkn1 R k).symm x) := rfl
        _ = polyEval R b (((Dk_equiv_Dkn1 R k).symm x : Dk R k) : R) := hb _
        _ = polyEval R b ((x : Fin 1 → R) 0) := by rw [hx0]
        _ = polyEvalDkn R k 1 (polyCoeffOneInvFun R k b) (x : Fin 1 → R) := by
          rw [polyEvalDkn_invFun]
    have huniq := ha.2.2 (polyCoeffOneInvFun R k b) hb'
    have hri : polyCoeffOneToFun R k (polyCoeffOneInvFun R k b) = b :=
      (polyCoeffOneEquiv R k).right_inv b
    have hconvert := congrArg (polyCoeffOneToFun R k) huniq
    rwa [hri] at hconvert

/-- $D_k$ 上的 KL 公理（Axiom 1'）蕴含 $D_k(1)$ 上的 KL 公理：
`IsKockLawvereDkAt R k → IsKockLawvereDknAt R k 1`。

**注意**：`IsKockLawvereDknAt`/`IsKockLawvereDkAt` 是携带数据的类型而非命题，
故用 `def` 而非 `theorem`。 -/
def kL_DknAt_of_kL_DkAt (R : Type u) [CommRing R] (k : ℕ)
    (h : IsKockLawvereDkAt R k) : IsKockLawvereDknAt R k 1 := by
  intro f
  let f' : Dk R k → R := fun d ↦ f ((Dk_equiv_Dkn1 R k) d)
  let ha := h f'
  refine ⟨polyCoeffOneInvFun R k ha.1, ?_, ?_⟩
  · intro x
    have hsymm : (Dk_equiv_Dkn1 R k) ((Dk_equiv_Dkn1 R k).symm x) = x :=
      (Dk_equiv_Dkn1 R k).apply_symm_apply x
    have hx0 : (((Dk_equiv_Dkn1 R k).symm x : Dk R k) : R) = (x : Fin 1 → R) 0 := by
      rfl
    calc
      f x = f' ((Dk_equiv_Dkn1 R k).symm x) := by
        dsimp [f']
        rw [hsymm]
      _ = polyEval R ha.1 (((Dk_equiv_Dkn1 R k).symm x : Dk R k) : R) := ha.2.1 _
      _ = polyEval R ha.1 ((x : Fin 1 → R) 0) := by rw [hx0]
      _ = polyEvalDkn R k 1 (polyCoeffOneInvFun R k ha.1) (x : Fin 1 → R) := by
        rw [polyEvalDkn_invFun]
  · intro b hb
    have hb' : ∀ d : Dk R k, f' d = polyEval R (polyCoeffOneToFun R k b) (d : R) := by
      intro d
      have hsymm : (Dk_equiv_Dkn1 R k).symm ((Dk_equiv_Dkn1 R k) d) = d :=
        (Dk_equiv_Dkn1 R k).symm_apply_apply d
      have hx0 : (((Dk_equiv_Dkn1 R k) d : Dkn R k 1) : Fin 1 → R) 0 = (d : R) := by
        rfl
      calc
        f' d = f ((Dk_equiv_Dkn1 R k) d) := rfl
        _ = polyEvalDkn R k 1 b (((Dk_equiv_Dkn1 R k) d : Dkn R k 1) : Fin 1 → R) := hb _
        _ = polyEval R (polyCoeffOneToFun R k b) ((((Dk_equiv_Dkn1 R k) d : Dkn R k 1) : Fin 1 → R) 0) := by
          rw [polyEvalDkn_eq_polyEval]
        _ = polyEval R (polyCoeffOneToFun R k b) (d : R) := by rw [hx0]
    have huniq := ha.2.2 (polyCoeffOneToFun R k b) hb'
    have hli : polyCoeffOneInvFun R k (polyCoeffOneToFun R k b) = b :=
      (polyCoeffOneEquiv R k).left_inv b
    have hconvert := congrArg (polyCoeffOneInvFun R k) huniq
    rwa [hli] at hconvert

/-- $D_k(1)$ 与 $D_k$ 上的 KL 公理互相蕴含（$n = 1$ 特例）：
`IsKockLawvereDknAt R k 1 → IsKockLawvereDkAt R k` 与
`IsKockLawvereDkAt R k → IsKockLawvereDknAt R k 1` 两个方向都存在
（`kL_DkAt_of_kL_DknAt` / `kL_DknAt_of_kL_DkAt`）。 -/
def kL_DknAt_iff_kL_DkAt (R : Type u) [CommRing R] (k : ℕ) :
    (IsKockLawvereDknAt R k 1 → IsKockLawvereDkAt R k) ×
    (IsKockLawvereDkAt R k → IsKockLawvereDknAt R k 1) :=
  ⟨kL_DkAt_of_kL_DknAt R k, kL_DknAt_of_kL_DkAt R k⟩

/-- Axiom 1'' 的 $k$ 阶版本（`IsKockLawvereDkn`）蕴含 Axiom 1'（`IsKockLawvereDk`）：
`IsKockLawvereDkn` 的 $n = 1$ 情形正是 `IsKockLawvereDkAt`，故
`IsKockLawvereDkn R` 自动给出 `IsKockLawvereDk R`。 -/
instance instIsKockLawvereDk_of_IsKockLawvereDkn (R : Type u) [IsKockLawvereDkn R] :
    IsKockLawvereDk R where
  isKockLawvereDk := by
    intro k
    exact kL_DkAt_of_kL_DknAt R k (IsKockLawvereDkn.isKockLawvereDkn (k := k) (n := 1))
