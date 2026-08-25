import SDG.NoChoice
import SDG.Infinitesimal

/-!
# SDG.Derivative

Kock-Lawvere 公理、合成导数与偏导数。

主要内容：
* Kock-Lawvere 公理 `IsKockLawvere_one` 及其等价形式 $D \to R \cong R \times R$；
* 合成导数 `sderiv` 及其基本性质、微商消去律；
* $n$ 元偏导数 `spartial`、梯度 `sgradient`、混合偏导数 `spartial2` 与 Schwarz 交换律。
-/

/-! ## Kock-Lawvere 公理 -/

/-- **Kock-Lawvere 公理**（单个无穷小情形）：
每个函数 $f : D \to R$ 在 $D$ 上都是「仿射」的，即存在唯一的 $b$ 使得
$$f(d) = f(0) + b \cdot d \quad (\forall d \in D).$$
这里的 $b$ 就是 $f$ 在 $0$ 处的导数。 -/
class IsKockLawvere_one R extends CommRing R where
  isKockLawvere_one (f : D R → R) : ExistsUnique' fun b ↦ ∀ d, f d = f 0 + b * d


/-- Kock-Lawvere 公理的等价表述：$D$ 上的函数由 $f(0)$ 和导数 $b$ 唯一决定，
即 $\mathrm{Hom}(D, R) \cong R \times R$。 -/
def DRtoREquivRR {R} [IsKockLawvere_one R] : (D R → R) ≃ R × R where
  toFun f := ⟨f 0, (IsKockLawvere_one.isKockLawvere_one f).1⟩
  invFun x d := x.1 + x.2 * d
  left_inv := by
    intro f
    ext d
    simpa using ((IsKockLawvere_one.isKockLawvere_one f).2.1 d).symm
  right_inv := by
    intro x
    ext
    · simp
    · symm
      apply (IsKockLawvere_one.isKockLawvere_one (fun d ↦ x.1 + x.2 * d.1)).2.2 x.2
      intro d
      simp


/-! ## 导数 (Synthetic Derivative)

在综合微分几何中，导数由 Kock-Lawvere 公理直接定义：
对 $f : R \to R$ 和 $x : R$，$f$ 在 $x$ 处的导数 $f'(x)$ 是
使得对所有无穷小量 $d \in D$ 都有 $f(x+d) = f(x) + f'(x)\,d$ 成立的唯一元素。 -/

/-- 合成导数：$f'(x)$。 -/
def sderiv {R} [IsKockLawvere_one R] (f : R → R) (x : R) : R :=
  (IsKockLawvere_one.isKockLawvere_one fun d : D R ↦ f (x + (d : R))).1


/-- 导数的基本刻画：$f(x+d) = f(x) + f'(x)\, d$ 对所有 $d \in D$ 成立。 -/
theorem sderiv_spec {R} [IsKockLawvere_one R] (f : R → R) (x : R) (d : D R) :
    f (x + d) = f x + sderiv f x * d := by
  simpa [sderiv] using (IsKockLawvere_one.isKockLawvere_one fun d ↦ f (x + d)).2.1 d


/-- 常函数的导数为零。 -/
theorem sderiv_const {R} [IsKockLawvere_one R] (c x : R) :
    sderiv (fun _ ↦ c) x = 0 := by
  symm
  exact (IsKockLawvere_one.isKockLawvere_one fun _ : D R ↦ c).2.2 0 (by intro d; simp)


/-- 恒等函数的导数为 $1$。 -/
theorem sderiv_id {R} [IsKockLawvere_one R] (x : R) :
    sderiv (fun x : R ↦ x) x = 1 := by
  symm
  exact (IsKockLawvere_one.isKockLawvere_one fun d ↦ x + (d : R)).2.2 1
    (by intro d; simp)


/-- 二次函数 $x \mapsto x^2$ 的导数为 $2x$。 -/
theorem sderiv_pow_two {R} [IsKockLawvere_one R] (x : R) :
    sderiv (fun x ↦ x * x) x = 2 * x := by
  symm
  exact (IsKockLawvere_one.isKockLawvere_one
    fun d ↦ (x + (d : R)) * (x + (d : R))).2.2 (2 * x) (by
      intro d
      have hd : d * (d : R) = 0 := by
        exact D.mul_eq_zero R d
      simp
      ring_nf
      simpa [pow_two] using hd)


/-! ## 微商消去与辅助引理

SDG 中的关键技巧是「微商消去」：如果一个量乘以任意无穷小都为零，
则该量本身为零。这是由 Kock-Lawvere 公理的唯一性直接推出的。 -/

/-- **微商消去律**：若 $a \cdot d = 0$ 对所有无穷小量 $d \in D$ 成立，则 $a = 0$。 -/
theorem smul_cancel_d {R} [IsKockLawvere_one R] {a : R} :
    (∀ d : D R, a * (d : R) = 0) → a = 0 := by
  intro h
  let P := fun d : D R ↦ a * (d : R)
  have hb : (IsKockLawvere_one.isKockLawvere_one P).1 = a := by
    symm
    exact (IsKockLawvere_one.isKockLawvere_one P).property.right a (by
      intro d
      simp [P])
  have h0 : (IsKockLawvere_one.isKockLawvere_one P).1 = 0 := by
    symm
    exact (IsKockLawvere_one.isKockLawvere_one P).property.right 0 (by
      intro d
      simpa [P] using h d)
  calc
    a = (IsKockLawvere_one.isKockLawvere_one P).1 := hb.symm
    _ = 0 := h0


/-- **双重微商消去**：若 $c \cdot d_1 d_2 = 0$ 对所有 $d_1, d_2 \in D$ 成立，则 $c = 0$。 -/
theorem two_smul_cancel_d {R} [IsKockLawvere_one R] {c : R} :
    (∀ d1 d2 : D R, c * ((d1 : R) * (d2 : R)) = 0) → c = 0 := by
  intro h
  apply smul_cancel_d
  intro d2
  apply smul_cancel_d
  intro d1
  calc
    c * (d2 : R) * (d1 : R) = c * ((d1 : R) * (d2 : R)) := by ring
    _ = 0 := h d1 d2


/-- **线性函数的导数**：$\frac{d}{dx}(a x + b) = a$。 -/
theorem sderiv_linear {R} [IsKockLawvere_one R] (a b x : R) :
    sderiv (fun t ↦ a * t + b) x = a := by
  symm
  exact (IsKockLawvere_one.isKockLawvere_one fun d : D R ↦ a * (x + (d : R)) + b).property.right a (by
    intro d
    rw [zero_coeD]
    ring)


/-! ## 幂函数的导数

幂函数 $x \mapsto x^n$ 的导数公式 $(x^n)' = n\,x^{n-1}$。二项式线性化
$(d+e)^n = d^n + n\,d^{n-1} e$（$e \in D$）是纯环论事实（`SDG.Infinitesimal`
的 `pow_add_sq_zero`）；`sderiv_pow` 将其表述为幂函数的导数，`pow_add_sderiv`
把 KL 导数展开写作 `sderiv` 形式。 -/

/-- 幂函数 $x \mapsto x^n$ 的导数：$(x^n)' = n\,x^{n-1}$
（$n = 0$ 时 $x^{n-1} = x^0 = 1$、系数 $0$，等式自然成立）。 -/
theorem sderiv_pow {R} [IsKockLawvere_one R] (x : R) (n : ℕ) :
    sderiv (fun x : R ↦ x ^ n) x = (n : R) * x ^ (n - 1) := by
  apply sub_eq_zero.mp
  apply smul_cancel_d
  intro e
  have hbin := pow_add_sq_zero x e n
  have hspec := sderiv_spec (fun x : R ↦ x ^ n) x e
  calc
    (sderiv (fun x : R ↦ x ^ n) x - (n : R) * x ^ (n - 1)) * (e : R)
        = sderiv (fun x : R ↦ x ^ n) x * (e : R) - (n : R) * x ^ (n - 1) * (e : R) := by ring
    _ = ((x + (e : R)) ^ n - x ^ n) - (n : R) * x ^ (n - 1) * (e : R) := by
            rw [hspec]
            ring
    _ = ((x ^ n + (n : R) * x ^ (n - 1) * (e : R)) - x ^ n) - (n : R) * x ^ (n - 1) * (e : R) := by rw [hbin]
    _ = 0 := by ring


/-! ## n元偏导数 (Partial Derivatives)

在多变量微分中，$n$ 元函数 $f : \mathbb{R}^n \to \mathbb{R}$（表示为 $f : \text{Fin } n \to R \to R$）
的偏导数通过固定其他变量，只沿着某一坐标方向取导数来定义。

对于 $f : \text{Fin } n \to R \to R$ 和点 $\mathbf{x} : \text{Fin } n \to R$，
$f$ 在 $\mathbf{x}$ 处关于第 $i$ 个变量的偏导数定义为：
$$\frac{\partial f}{\partial x_i}(\mathbf{x}) = \frac{d}{dt}\Big|_{t=0} f(\mathbf{x} \text{ with } x_i := x_i + t)$$

在 SDG 框架中，这直接通过 Kock-Lawvere 公理实现。
-/

/-- **n元偏导数**：函数 $f : \text{Fin } n \to R \to R$ 在点 $\mathbf{x}$ 处
关于第 $i$ 个变量的偏导数。

具体地，固定所有变量除了 $x_i$，然后对 $x_i$ 求导。 -/
def spartial {R} [IsKockLawvere_one R] {n : ℕ}
    (f : (Fin n → R) → R) (x : Fin n → R) (i : Fin n) : R :=
  sderiv (fun t : R ↦ f (Function.update x i t)) (x i)


/-- **n元偏导数的刻画**：$f$ 在 $\mathbf{x}$ 处关于 $x_i$ 的偏导数满足
$$f(\mathbf{x} + d \cdot \mathbf{e}_i) = f(\mathbf{x}) + \frac{\partial f}{\partial x_i}(\mathbf{x}) \cdot d$$
其中 $d \in D$，$\mathbf{e}_i$ 是第 $i$ 个标准基向量。 -/
theorem spartial_spec {R} [IsKockLawvere_one R] {n : ℕ}
    (f : (Fin n → R) → R) (x : Fin n → R) (i : Fin n) (d : D R) :
    f (Function.update x i (x i + d)) = f x + spartial f x i * d := by
  unfold spartial
  have h := sderiv_spec (fun t : R ↦ f (Function.update x i t)) (x i) d
  rw [h]
  have eq : Function.update x i (x i) = x := by
    ext j
    simp [Function.update]
    tauto
  rw [eq]


/-- 常函数的所有偏导数都为零。 -/
theorem spartial_const {R} [IsKockLawvere_one R] {n : ℕ}
    (c : R) (x : Fin n → R) (i : Fin n) :
    spartial (fun _ ↦ c) x i = 0 := by
  unfold spartial
  exact sderiv_const c (x i)


/-- 投影函数（提取第 $j$ 个坐标）的偏导数：
$$\frac{\partial x_j}{\partial x_i} = \begin{cases} 1 & \text{if } i = j \\ 0 & \text{otherwise} \end{cases}$$ -/
theorem spartial_proj {R} [IsKockLawvere_one R] {n : ℕ}
    (x : Fin n → R) (i j : Fin n) :
    spartial (fun v ↦ v j) x i = if i = j then 1 else 0 := by
  unfold spartial
  by_cases hij : i = j
  · simp [hij]
    exact sderiv_id (x j)
  · simp [hij]
    have eq_const : (fun t : R ↦ Function.update x i t j) = fun _ : R ↦ x j := by
      funext t
      simp [Function.update, Ne.symm hij]
    rw [eq_const]
    exact sderiv_const (x j) (x i)


/-- **梯度向量**（所有偏导数组成的向量）：
$$\nabla f(\mathbf{x}) = \left( \frac{\partial f}{\partial x_1}(\mathbf{x}), \ldots, \frac{\partial f}{\partial x_n}(\mathbf{x}) \right)$$ -/
def sgradient {R} [IsKockLawvere_one R] {n : ℕ}
    (f : (Fin n → R) → R) (x : Fin n → R) : Fin n → R :=
  fun i ↦ spartial f x i


/-- 梯度的刻画：梯度向量包含了 $f$ 在 $\mathbf{x}$ 处沿所有坐标方向的偏导数。 -/
theorem sgradient_spec {R} [IsKockLawvere_one R] {n : ℕ}
    (f : (Fin n → R) → R) (x : Fin n → R) (i : Fin n) :
    sgradient f x i = spartial f x i := rfl


/-- **更新交换律**：若 $i \neq j$，则两次不同的坐标更新可以交换：
$\mathbf{x}[i \mapsto v_i][j \mapsto v_j] = \mathbf{x}[j \mapsto v_j][i \mapsto v_i]$。 -/
lemma update_update_comm {R} {n : ℕ} (x : Fin n → R) (i j : Fin n) (hij : i ≠ j)
    (vi vj : R) :
    Function.update (Function.update x i vi) j vj = Function.update (Function.update x j vj) i vi := by
  funext k
  by_cases hik : k = i
  · subst k
    simp [Function.update, hij]
  · by_cases hjk : k = j
    · subst k
      simp [Function.update, Ne.symm hij]
    · simp [Function.update, hik, hjk]


/-! ## 混合偏导数 (Mixed Partial Derivatives) 及其交换律

在多变量微分中，混合偏导数（也称为高阶偏导数）是通过对不同变量依次求偏导来定义的。
关键的结果是**Schwarz定理**：在连续性条件下，混合偏导数与求导顺序无关。

在 SDG 框架中，这直接从 Kock-Lawvere 公理的二元版本跟随而出：
由于函数在两个无穷小量方向上必须是双线性的，所以自动满足交换律。
-/

/-- **混合偏导数**：函数 $f$ 在点 $\mathbf{x}$ 处先对 $x_i$ 后对 $x_j$ 的二阶偏导数。 -/
def spartial2 {R} [IsKockLawvere_one R] {n : ℕ}
    (f : (Fin n → R) → R) (x : Fin n → R) (i j : Fin n) : R :=
  spartial (fun y ↦ spartial f y i) x j


/-- **混合偏导数的刻画**（对称形式）：函数在两个方向上的二阶变化。

对于 $d_i, d_j \in D$ 且 $i \neq j$，有：
$$f(\mathbf{x} + d_i \mathbf{e}_i + d_j \mathbf{e}_j) = f(\mathbf{x}) + \frac{\partial f}{\partial x_i}(\mathbf{x}) d_i + \frac{\partial f}{\partial x_j}(\mathbf{x}) d_j + \frac{\partial^2 f}{\partial x_j \partial x_i}(\mathbf{x}) d_j d_i$$
这里二阶项的系数是 $\partial^2 f/\partial x_j \partial x_i$（先对 $x_i$ 再对 $x_j$ 求偏导）。 -/
theorem spartial2_spec_sym {R} [IsKockLawvere_one R] {n : ℕ}
    (f : (Fin n → R) → R) (x : Fin n → R) (i j : Fin n) (hij : i ≠ j)
    (di dj : D R) :
    f (Function.update (Function.update x i (x i + di)) j (x j + dj)) =
      f x + spartial f x i * di + spartial f x j * dj +
            spartial2 f x j i * (dj * di) := by
  -- 第一步：在更新后的点 x + di·e_i 处，沿 j 方向应用偏导数规范
  have hstep := spartial_spec f (Function.update x i (x i + di)) j dj
  have hxj : (Function.update x i (x i + di)) j = x j := by
    simp [Function.update, Ne.symm hij]
  have hstep' : f (Function.update (Function.update x i (x i + di)) j (x j + dj)) =
      f (Function.update x i (x i + di)) +
        spartial f (Function.update x i (x i + di)) j * dj := by
    simpa [hxj] using hstep
  rw [hstep']
  -- 第二步：展开 f(x + di·e_i)
  have h1 := spartial_spec f x i di
  rw [h1]
  -- 第三步：展开 spartial f (x + di·e_i) j，即 ∂_j f 沿 i 方向的增量
  have h2 := spartial_spec (fun y ↦ spartial f y j) x i di
  rw [h2]
  -- 第四步：spartial2 f x j i 正是 spartial (fun y ↦ spartial f y j) x i
  unfold spartial2
  -- 最后：纯代数化简
  ring


/-- **混合偏导数的交换律**：$\frac{\partial^2 f}{\partial x_i \partial x_j} = \frac{\partial^2 f}{\partial x_j \partial x_i}$

这是 Schwarz 定理在综合微分几何中的版本。由于函数在无穷小方向上必须是双线性的，
两个偏导数的顺序不会影响结果。

**证明思路**：用对称形式的泰勒展开（`spartial2_spec_sym`）分别计算
$f(\mathbf{x} + d_i \mathbf{e}_i + d_j \mathbf{e}_j)$，得到两个关于
$\partial^2 f/\partial x_j \partial x_i$ 和 $\partial^2 f/\partial x_i \partial x_j$
的表达式；两者左端相同，故系数相等（用双重微商消去）。 -/
theorem spartial2_comm {R} [IsKockLawvere_one R] {n : ℕ}
    (f : (Fin n → R) → R) (x : Fin n → R) (i j : Fin n) :
    spartial2 f x i j = spartial2 f x j i := by
  by_cases hij : i = j
  · subst j
    rfl
  · -- i ≠ j：用双重微商消去
    have hcancel : ∀ (di dj : D R),
        (spartial2 f x i j - spartial2 f x j i) * (di * dj) = 0 := by
      intro di dj
      -- 两种方向的对称泰勒展开
      have A := spartial2_spec_sym f x i j hij di dj
      have B := spartial2_spec_sym f x j i (Ne.symm hij) dj di
      -- 两个左端相同（更新可交换）
      have hcomm := update_update_comm x i j hij (x i + di) (x j + dj)
      -- 由 A、B 的左端相等推出二阶系数相等
      have hEq : spartial2 f x j i * (dj * di) = spartial2 f x i j * (di * dj) := by
        have hA : spartial2 f x j i * (dj * di) =
            f (Function.update (Function.update x i (x i + di)) j (x j + dj)) -
            (f x + spartial f x i * di + spartial f x j * dj) := by
          rw [A]
          ring
        have hB : spartial2 f x i j * (di * dj) =
            f (Function.update (Function.update x j (x j + dj)) i (x i + di)) -
            (f x + spartial f x j * dj + spartial f x i * di) := by
          rw [B]
          ring
        rw [hA, hB]
        rw [hcomm]
        ring
      -- 调整 dj*di 为 di*dj
      have hEq'' : spartial2 f x j i * (di * dj) = spartial2 f x i j * (di * dj) := by
        calc
          spartial2 f x j i * (di * dj) = spartial2 f x j i * (dj * di) := by ring
          _ = spartial2 f x i j * (di * dj) := hEq
      -- 化为 (a - b) * (di*dj) = 0
      calc
        (spartial2 f x i j - spartial2 f x j i) * (di * dj)
            = spartial2 f x i j * (di * dj) - spartial2 f x j i * (di * dj) := by ring
        _ = spartial2 f x i j * (di * dj) - spartial2 f x i j * (di * dj) := by rw [hEq'']
        _ = 0 := by ring
    have hsub : spartial2 f x i j - spartial2 f x j i = 0 := two_smul_cancel_d hcancel
    exact sub_eq_zero.mp hsub


/-- **混合偏导数的刻画**：函数在两个方向上的二阶变化。

对于 $d_i, d_j \in D$ 且 $i \neq j$，有：
$$f(\mathbf{x} + d_i \mathbf{e}_i + d_j \mathbf{e}_j) = f(\mathbf{x}) + \frac{\partial f}{\partial x_i}(\mathbf{x}) d_i + \frac{\partial f}{\partial x_j}(\mathbf{x}) d_j + \frac{\partial^2 f}{\partial x_i \partial x_j}(\mathbf{x}) d_i d_j$$

这是二变量泰勒展开的规范形式。由 `spartial2_spec_sym`（对称形式）结合
Schwarz 定理（`spartial2_comm`）直接得出。 -/
theorem spartial2_spec {R} [IsKockLawvere_one R] {n : ℕ}
    (f : (Fin n → R) → R) (x : Fin n → R) (i j : Fin n) (hij : i ≠ j)
    (di dj : D R) :
    f (Function.update (Function.update x i (x i + di)) j (x j + dj)) =
      f x + spartial f x i * di + spartial f x j * dj +
            spartial2 f x i j * (di * dj) := by
  -- 对称形式 + 交换律
  have hsym := spartial2_spec_sym f x i j hij di dj
  rw [spartial2_comm] at hsym
  rw [hsym]
  ring


/-- **二阶偏导数为零**（对常函数）：$\frac{\partial^2 c}{\partial x_i \partial x_j} = 0$ -/
theorem spartial2_const {R} [IsKockLawvere_one R] {n : ℕ}
    (c : R) (x : Fin n → R) (i j : Fin n) :
    spartial2 (fun _ ↦ c) x i j = 0 := by
  unfold spartial2
  simp [spartial_const]


/-! ## 混合偏导数的应用 -/

/-- **投影函数的二阶偏导数为零**：$\frac{\partial^2 x_k}{\partial x_i \partial x_j} = 0$ -/
theorem spartial2_proj {R} [IsKockLawvere_one R] {n : ℕ}
    (x : Fin n → R) (i j k : Fin n) :
    spartial2 (fun v ↦ v k) x i j = 0 := by
  unfold spartial2
  simp [spartial_proj]
  split_ifs <;> simp [spartial_const]
