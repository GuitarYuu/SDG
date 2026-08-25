import SDG.NoChoice
import SDG.Infinitesimal
import SDG.Microlinear
import SDG.Derivative

/-!
# SDG.WeilAlgebra

一般坐标 Weil 代数与一般 Kock-Lawvere 公理（Axiom 1W，Kock 的「the general Kock axiom」）。

在综合微分几何 (SDG) 中，Kock-Lawvere 公理的最一般形式（Kock SDG 2006 第 I.12 节、
nLab 的「Weil algebra」/「Kock-Lawvere axiom」词条）断言：

> 对每个内部 Weil 代数 $W$，典范求值变换
> $$W \longrightarrow R^{\operatorname{Spec} W}, \qquad w \longmapsto \bigl(\sigma \mapsto \sigma(w)\bigr)$$
> 是双射，即 $R^{\operatorname{Spec} W} \cong W$：谱上的函数恰好由 $W$ 的元素给出。

这里 $\operatorname{Spec} W$ 是 $W$ 的**谱**（点集）：全体 $R$-代数同态 $\sigma : W \to R$。
对由 $W = R[x_1,\dots,x_n]/I$ 给出的 Weil 代数，同态 $\sigma$ 由 $(\sigma(x_1),\dots,\sigma(x_n)) \in R^n$
决定且恰好满足 $I$ 的零点方程，故这正是 Kock 的无穷小邻域 $D_W \subseteq R^n$。

主要内容：
* **一般坐标 Weil 代数** `Weil mu = R \oplus (\mathrm{Fin}\ n \to R)`：元素 $(a, b)$，
  乘法由 $R$-双线性、对称、结合的 $\mu : (R^n) \times (R^n) \to R^n$ 给出：
  $$(a,b)(c,d) = (ac,\ a d + c b + \mu(b,d)),$$
  编码一般理想关系 $x_i x_j = \sum_k c_{ijk} x_k$。`WeilMul` 类（见 `Weil`）除
  双线性/对称/结合外还要求**线性部分（增广理想）幂零**（字段 `linNilpotent`，配合 `muProd`），
  这是内部 Weil 代数的定义性条件。交换环与 $R$-代数结构对**任意** `WeilMul` 的 `mu`
  构造（`Weil.instCommRing`、`Weil.instAlgebra`）；
* 当 $\mu = 0$ 时 `Weil R n 0` 正是 $D(n)$ 的 Weil 代数 $R[x_1,\dots,x_n]/(x_ix_j)$
  （`Weil.zeroWeilMul`，其线性部分幂零指数为 $2$）；
* **$W$ 到 $R$ 的 $R$-代数同态**：`Weil.constAlgHom`（常值投影 $w \mapsto w_{\rm const}$
  是 $R$-代数同态），其核正是线性部分 `Weil.linIdeal`（`Weil.constAlgHom_ker`）；
  生成元 `Weil.gen` 与坐标分解 `Weil.decomp`
  （$w = w_{\rm const}\cdot 1 + \sum_i (w_{\rm lin})_i\, x_i$）；
* **一般 KL 公理（Axiom 1W）**：`IsKockLawvereWeilAt R n mu` —— 谱上的每个函数
  $f : \operatorname{Spec} W \to R$ 唯一地由某个 $w \in W$ 的求值 $g \mapsto g\,w$ 给出
  （即典范求值变换是双射）；`IsKockLawvereWeil R` 是断言其对一切 $n$、`WeilMul` 的 $\mu$
  成立的类。

**关于选择公理**：本文件中所有有限和（坐标分解等）均使用无选择公理的 `finSum`
（见 `SDG.Infinitesimal`），全部声明都通过无选择公理 linter，
无需 `set_option linter.noAxiomOfChoice false`。
-/

/-! ## 一般坐标 Weil 代数 -/

/-- 线性部分 $\mathfrak{m} = (\mathrm{Fin}\ n \to R)$ 上 $k + 1$ 个元素的「迭代 $\mu$ 乘积」
（右嵌套）：$\mathrm{muProd}\ mu\ k\ (b_1,\dots,b_{k+1}) = \mu(b_1,\ \mu(b_2,\dots
\mu(b_k, b_{k+1})\dots))$。$k = 0$ 时即单元素 $b_1$。
用于表述「lin 理想幂零」：$\mathfrak{m}^{k+1} = 0$ 即任意 $k + 1$ 个线性部分的迭代乘积为零。
无选择公理（对 $k$ 的结构递归）。 -/
def muProd {R} [CommRing R] {n : ℕ}
    (mu : (Fin n → R) → (Fin n → R) → (Fin n → R)) :
    (k : ℕ) → (Fin (k + 1) → (Fin n → R)) → (Fin n → R)
  | 0, xs => xs 0
  | k + 1, xs => mu (xs 0) (muProd mu k (fun i ↦ xs i.succ))

/-- 一般 Weil 代数的乘法数据：线性部分 $\mathfrak{m} = (\mathrm{Fin}\ n \to R)$ 上的
$R$-双线性、对称、结合映射 $\mu : \mathfrak{m} \times \mathfrak{m} \to \mathfrak{m}$，
编码理想关系（如 $x_i x_j = \sum_k c_{ijk} x_k$）。乘法由
$$(a,b)(c,d) = (ac,\ a d + c b + \mu(b,d))$$
给出。当 $\mu = 0$ 时正是 $D(n)$ 的 Weil 代数 $R[x_1,\dots,x_n]/(x_ix_j)$。

**幂零性**：字段 `linNilpotent` 要求线性部分 $\mathfrak{m} = \{w \mid w_{\rm const} = 0\}$
（增广理想）是幂零的——存在 $k$ 使 $\mathfrak{m}^{k+1} = 0$，即任意 $k + 1$ 个线性部分的
`muProd` 乘积为零（这正是内部 Weil 代数的定义性条件）。 -/
class WeilMul {R} [CommRing R] {n : ℕ}
    (mu : (Fin n → R) → (Fin n → R) → (Fin n → R)) : Prop where
  map_add_left : ∀ a b c, mu (a + b) c = mu a c + mu b c
  map_smul_left : ∀ (r : R) a b, mu (r • a) b = r • mu a b
  map_add_right : ∀ a b c, mu a (b + c) = mu a b + mu a c
  map_smul_right : ∀ (r : R) a b, mu a (r • b) = r • mu a b
  symmetric : ∀ a b, mu a b = mu b a
  associative : ∀ a b c, mu (mu a b) c = mu a (mu b c)
  linNilpotent : ∃ k : ℕ, ∀ xs : Fin (k + 1) → (Fin n → R), muProd mu k xs = 0

/-- 一般坐标 Weil 代数：底层类型为 $R \times (\mathrm{Fin}\ n \to R)$（$R$-模 $R \oplus \mathfrak{m}$），
元素 $(a, b) = a + \sum_i b_i x_i$。乘法由 `mu` 决定：
$$(a,b)(c,d) = (ac,\ a d + c b + \mu(b,d)).$$
其谱 $\operatorname{Spec} W$（全体 $R$-代数同态 $W \to R$）正是 $D(n) \subseteq R^n$；
当 $\mu = 0$ 时它是 $D(n)$ 的 Weil 代数 $R[x_1,\dots,x_n]/(x_ix_j)$。 -/
structure Weil {R} [CommRing R] {n : ℕ}
    (mu : (Fin n → R) → (Fin n → R) → (Fin n → R)) [WeilMul mu] where
  const : R
  lin : Fin n → R

namespace Weil

variable {R} [CommRing R] {n : ℕ}
  {mu : (Fin n → R) → (Fin n → R) → (Fin n → R)} [wmu : WeilMul mu]

omit mu wmu in
/-- 零乘法 $\mu = 0$：`Weil R n 0` 正是 $D(n)$ 的 Weil 代数 $R[x_1,\dots,x_n]/(x_ix_j)$。
其线性部分（增广理想）幂零指数为 $2$（`linNilpotent` 取 $k = 1$：任意两个线性部分的
迭代乘积为零）。 -/
instance zeroWeilMul : WeilMul (0 : (Fin n → R) → (Fin n → R) → (Fin n → R)) where
  map_add_left := by intro a b c; funext i; simp
  map_smul_left := by intro r a b; funext i; simp
  map_add_right := by intro a b c; funext i; simp
  map_smul_right := by intro r a b; funext i; simp
  symmetric := by intro a b; funext i; simp
  associative := by intro a b c; funext i; simp
  linNilpotent := ⟨1, by
    intro xs
    rfl
  ⟩

/-- `Weil` 的外延性：两个元素相等当且仅当其常值部分与线性部分分别相等。 -/
@[ext]
theorem ext {x y : Weil mu} (h1 : x.const = y.const) (h2 : x.lin = y.lin) :
    x = y := by
  cases x with
  | mk c l =>
    cases y with
    | mk c' l' =>
      change c = c' at h1
      change l = l' at h2
      subst c'
      subst l'
      rfl

instance instZero : Zero (Weil mu) where
  zero := ⟨0, fun _ ↦ 0⟩

instance instAdd : Add (Weil mu) where
  add x y := ⟨x.const + y.const, fun i ↦ x.lin i + y.lin i⟩

instance instNeg : Neg (Weil mu) where
  neg x := ⟨-x.const, fun i ↦ -x.lin i⟩

instance instMul : Mul (Weil mu) where
  mul x y := ⟨x.const * y.const, fun i ↦ x.const * y.lin i + x.lin i * y.const +
    mu x.lin y.lin i⟩

instance instOne : One (Weil mu) where
  one := ⟨1, fun _ ↦ 0⟩

instance instSMul : SMul R (Weil mu) where
  smul r x := ⟨r * x.const, fun i ↦ r * x.lin i⟩

@[simp] lemma const_zero : (0 : Weil mu).const = 0 := rfl
@[simp] lemma lin_zero : (0 : Weil mu).lin = fun _ ↦ 0 := rfl
@[simp] lemma const_one : (1 : Weil mu).const = 1 := rfl
@[simp] lemma lin_one : (1 : Weil mu).lin = fun _ ↦ 0 := rfl
@[simp] lemma const_add (x y : Weil mu) : (x + y).const = x.const + y.const := rfl
@[simp] lemma lin_add (x y : Weil mu) : (x + y).lin = x.lin + y.lin := rfl
@[simp] lemma const_neg (x : Weil mu) : (-x).const = -x.const := rfl
@[simp] lemma lin_neg (x : Weil mu) : (-x).lin = -x.lin := rfl
@[simp] lemma const_mul (x y : Weil mu) : (x * y).const = x.const * y.const := rfl
@[simp] lemma lin_mul (x y : Weil mu) :
    (x * y).lin = fun i ↦ x.const * y.lin i + x.lin i * y.const + mu x.lin y.lin i := rfl

/-- 线性部分的乘法：$(xy).lin = a\,d + c\,b + \mu(b,d)$（向量形式）。 -/
lemma lin_mul' (x y : Weil mu) :
    (x * y).lin = x.const • y.lin + y.const • x.lin + mu x.lin y.lin := by
  funext i
  simp [lin_mul]
  ring

/-- 加法结合律。 -/
theorem add_assoc (a b c : Weil mu) : a + b + c = a + (b + c) := by
  apply ext
  · simp
    ring
  · funext i
    simp
    ring

/-- 零元是加法单位元（左）。 -/
theorem zero_add (a : Weil mu) : 0 + a = a := by
  apply ext
  · simp
  · funext i
    simp

/-- 零元是加法单位元（右）。 -/
theorem add_zero (a : Weil mu) : a + 0 = a := by
  apply ext
  · simp
  · funext i
    simp

/-- 加法交换律。 -/
theorem add_comm (a b : Weil mu) : a + b = b + a := by
  apply ext
  · simp
    ring
  · funext i
    simp
    ring

/-- 加法逆元：$-a + a = 0$。 -/
theorem neg_add_cancel (a : Weil mu) : -a + a = 0 := by
  apply ext
  · simp
  · funext i
    simp

/-- 乘法结合律（利用 $\mu$ 的双线性与结合性）。 -/
theorem mul_assoc (a b c : Weil mu) : a * b * c = a * (b * c) := by
  apply ext
  · simp; ring
  · -- .lin：用向量形式展开，再按 μ 双线性/结合化简
    simp only [lin_mul', const_mul]
    simp only [wmu.map_add_left, wmu.map_smul_left, wmu.map_add_right, wmu.map_smul_right,
      wmu.associative]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- 单位元是乘法单位元（左）。 -/
theorem one_mul (a : Weil mu) : 1 * a = a := by
  apply ext
  · simp
  · rw [lin_mul']
    rw [lin_one, const_one]
    have hsmul : a.const • (fun _ : Fin n ↦ 0) = 0 := by
      funext i
      simp
    have h0 : mu (fun _ : Fin n ↦ 0) a.lin = 0 := by
      have hs : (0 : R) • (fun _ : Fin n ↦ 0) = fun _ : Fin n ↦ 0 := by
        funext i
        simp
      rw [← hs, wmu.map_smul_left]
      simp
    rw [hsmul, h0]
    simp

/-- 单位元是乘法单位元（右）。 -/
theorem mul_one (a : Weil mu) : a * 1 = a := by
  apply ext
  · simp
  · rw [lin_mul']
    rw [lin_one, const_one]
    have hsmul : a.const • (fun _ : Fin n ↦ 0) = 0 := by
      funext i
      simp
    have h0 : mu a.lin (fun _ : Fin n ↦ 0) = 0 := by
      have hs : (0 : R) • (fun _ : Fin n ↦ 0) = fun _ : Fin n ↦ 0 := by
        funext i
        simp
      rw [← hs, wmu.map_smul_right]
      simp
    rw [hsmul, h0]
    simp

/-- 乘法交换律。 -/
theorem mul_comm (a b : Weil mu) : a * b = b * a := by
  apply ext
  · simp; ring
  · rw [lin_mul', lin_mul', wmu.symmetric]
    funext i
    simp [Pi.smul_apply, smul_eq_mul]
    ring

/-- 零乘任何元素为零（左）。 -/
theorem zero_mul (a : Weil mu) : 0 * a = 0 := by
  apply ext
  · simp
  · rw [lin_mul']
    rw [lin_zero, const_zero]
    have hsmul : a.const • (fun _ : Fin n ↦ 0) = 0 := by
      funext i
      simp
    have h0 : mu (fun _ : Fin n ↦ 0) a.lin = 0 := by
      have hs : (0 : R) • (fun _ : Fin n ↦ 0) = fun _ : Fin n ↦ 0 := by
        funext i
        simp
      rw [← hs, wmu.map_smul_left]
      simp
    rw [hsmul, h0]
    funext i
    simp

/-- 任何元素乘零为零（右）。 -/
theorem mul_zero (a : Weil mu) : a * 0 = 0 := by
  apply ext
  · simp
  · rw [lin_mul']
    rw [lin_zero, const_zero]
    have hsmul : a.const • (fun _ : Fin n ↦ 0) = 0 := by
      funext i
      simp
    have h0 : mu a.lin (fun _ : Fin n ↦ 0) = 0 := by
      have hs : (0 : R) • (fun _ : Fin n ↦ 0) = fun _ : Fin n ↦ 0 := by
        funext i
        simp
      rw [← hs, wmu.map_smul_right]
      simp
    rw [hsmul, h0]
    funext i
    simp

/-- 左分配律。 -/
theorem left_distrib (a b c : Weil mu) : a * (b + c) = a * b + a * c := by
  apply ext
  · simp; ring
  · simp [lin_add, const_add, wmu.map_add_right]
    funext i
    simp
    ring

/-- 右分配律。 -/
theorem right_distrib (a b c : Weil mu) : (a + b) * c = a * c + b * c := by
  apply ext
  · simp; ring
  · simp [lin_add, const_add, wmu.map_add_left]
    funext i
    simp
    ring

/-- `Weil mu` 的交换环结构（乘法由 $\mu$ 决定）。 -/
instance instCommRing : CommRing (Weil mu) where
  toAddMonoid := {
    add := (· + ·)
    zero := 0
    add_assoc := add_assoc
    zero_add := zero_add
    add_zero := add_zero
    nsmul := nsmulRec
  }
  add_comm := add_comm
  toMonoid := {
    mul := (· * ·)
    one := 1
    mul_assoc := mul_assoc
    one_mul := one_mul
    mul_one := mul_one
  }
  zero_mul := zero_mul
  mul_zero := mul_zero
  left_distrib := left_distrib
  right_distrib := right_distrib
  natCast := fun n ↦ ⟨(n : R), fun _ ↦ 0⟩
  natCast_zero := by
    apply ext
    · change ((0 : ℕ) : R) = 0
      simp
    · funext i
      rfl
  natCast_succ := by
    intro n
    apply ext
    · change ((n + 1 : ℕ) : R) = (n : R) + 1
      norm_num
    · funext i
      change 0 = 0 + 0
      simp
  toNeg := ⟨fun a ↦ -a⟩
  toSub := ⟨fun a b ↦ a + -b⟩
  toZSMul := ⟨zsmulRec⟩
  sub_eq_add_neg := by intro a b; rfl
  neg_add_cancel := neg_add_cancel
  intCast := fun z ↦ ⟨(z : R), fun _ ↦ 0⟩
  intCast_ofNat := by
    intro n
    apply ext
    · change ((n : ℤ) : R) = (n : R)
      simp
    · funext i
      change 0 = 0
      rfl
  intCast_negSucc := by
    intro n
    apply ext
    · change ((Int.negSucc n) : R) = -((n + 1 : ℕ) : R)
      simp
    · funext i
      change 0 = -0
      simp
  mul_comm := mul_comm

/-- `Weil mu` 作为 $R$-代数的结构：`algebraMap r = (r, 0)`，标量作用逐点。 -/
instance instAlgebra : Algebra R (Weil mu) where
  smul := (· • ·)
  algebraMap := {
    toFun := fun r ↦ ⟨r, fun _ ↦ 0⟩
    map_zero' := by apply ext <;> rfl
    map_one' := by apply ext <;> rfl
    map_add' := by
      intro a b
      apply ext
      · rfl
      · funext i
        change 0 = 0 + 0
        simp
    map_mul' := by
      intro a b
      apply ext
      · rfl
      · funext i
        change 0 = a * 0 + 0 * b + mu (fun _ : Fin n ↦ 0) (fun _ : Fin n ↦ 0) i
        have h0 : mu (fun _ : Fin n ↦ 0) (fun _ : Fin n ↦ 0) = 0 := by
          have hs : (0 : R) • (fun _ : Fin n ↦ 0) = fun _ : Fin n ↦ 0 := by
            funext i
            simp
          rw [← hs, wmu.map_smul_left]
          simp
        simp [h0]
  }
  commutes' := by
    intro r x
    apply ext
    · change r * x.const = x.const * r
      ring
    · funext i
      change r * x.lin i + 0 * x.const + mu (fun _ : Fin n ↦ 0) x.lin i =
          x.const * 0 + x.lin i * r + mu x.lin (fun _ : Fin n ↦ 0) i
      have h0l : mu (fun _ : Fin n ↦ 0) x.lin = 0 := by
        have hs : (0 : R) • (fun _ : Fin n ↦ 0) = fun _ : Fin n ↦ 0 := by
          funext i
          simp
        rw [← hs, wmu.map_smul_left]
        simp
      have h0r : mu x.lin (fun _ : Fin n ↦ 0) = 0 := by
        have hs : (0 : R) • (fun _ : Fin n ↦ 0) = fun _ : Fin n ↦ 0 := by
          funext i
          simp
        rw [← hs, wmu.map_smul_right]
        simp
      simp [h0l, h0r]
      ring
  smul_def' := by
    intro r x
    apply ext
    · change r * x.const = r * x.const
      rfl
    · funext i
      change r * x.lin i = r * x.lin i + 0 * x.const + mu (fun _ : Fin n ↦ 0) x.lin i
      have h0 : mu (fun _ : Fin n ↦ 0) x.lin = 0 := by
        have hs : (0 : R) • (fun _ : Fin n ↦ 0) = fun _ : Fin n ↦ 0 := by
          funext i
          simp
        rw [← hs, wmu.map_smul_left]
        simp
      simp [h0]

@[simp] lemma const_smul (r : R) (x : Weil mu) : (r • x).const = r * x.const := by
  rw [Algebra.smul_def]
  change r * x.const = r * x.const
  rfl

@[simp] lemma lin_smul (r : R) (x : Weil mu) : (r • x).lin = fun i ↦ r * x.lin i := by
  rw [Algebra.smul_def]
  funext i
  change r * x.lin i + 0 * x.const + mu (fun _ : Fin n ↦ 0) x.lin i = r * x.lin i
  have h0 : mu (fun _ : Fin n ↦ 0) x.lin = 0 := by
    have hs : (0 : R) • (fun _ : Fin n ↦ 0) = fun _ : Fin n ↦ 0 := by
      funext i
      simp
    rw [← hs, wmu.map_smul_left]
    simp
  simp [h0]

/-! ## Weil 代数到 $R$ 的 $R$-代数同态 -/

/-- 常值投影 $w \mapsto w_{\rm const}$ 是加群同态。 -/
def constHom : Weil mu →+ R where
  toFun := fun w ↦ w.const
  map_zero' := rfl
  map_add' := by intro a b; rfl

/-- **`Weil.const` 作为 $R$-代数同态**：常值投影 $w \mapsto w_{\rm const}$ 是
$R$-代数同态 $W \to R$（保 $1$、乘法、加法、$0$，且与标量作用交换）。 -/
def constAlgHom : Weil mu →ₐ[R] R where
  toFun := fun w ↦ w.const
  map_one' := by simp
  map_mul' := by intro a b; simp
  map_zero' := by simp
  map_add' := by intro a b; simp
  commutes' := by intro r; rfl

@[simp] lemma constAlgHom_apply (w : Weil mu) : constAlgHom w = w.const := rfl

/-- 线性部分（增广理想）：$\mathfrak{m} = \{w \mid w_{\rm const} = 0\}$，
即常值投影（`constAlgHom`）的核。 -/
def linIdeal : Ideal (Weil mu) where
  carrier := {w | w.const = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change a.const = 0 at ha
    change b.const = 0 at hb
    simp [ha, hb]
  smul_mem' := by
    intro c w hw
    change w.const = 0 at hw
    change (c * w).const = 0
    simp [hw]

@[simp] lemma mem_linIdeal (w : Weil mu) : w ∈ linIdeal ↔ w.const = 0 := by
  rfl

/-- **`constAlgHom` 的核就是线性部分**：
$\ker(w \mapsto w_{\rm const}) = \mathfrak{m} = \{w \mid w_{\rm const} = 0\}$。 -/
theorem constAlgHom_ker : RingHom.ker (constAlgHom.toRingHom : Weil mu →+* R) = linIdeal := by
  apply Ideal.ext
  intro w
  rw [mem_linIdeal]
  simp

/-- 线性投影 $w \mapsto w_{\rm lin}$ 是加群同态（到 $\mathrm{Fin}\ n \to R$）。 -/
def linHom : Weil mu →+ (Fin n → R) where
  toFun := fun w ↦ w.lin
  map_zero' := rfl
  map_add' := by intro a b; rfl

omit mu wmu in
/-- 第 $i$ 个生成元 $x_i = (0, e_i)$，其中 $e_i$ 是 $\mathrm{Fin}\ n$ 的单位向量
（$e_i(j) = 1$ 若 $j = i$，否则 $0$）。`mu` 显式传入以保证类型解析（`gen` 本身不依赖
`[WeilMul mu]`）。 -/
def gen (mu : (Fin n → R) → (Fin n → R) → (Fin n → R)) (i : Fin n) [WeilMul mu] : Weil mu :=
  ⟨0, fun j ↦ if j = i then (1 : R) else 0⟩

@[simp] lemma gen_const (i : Fin n) : (gen mu i).const = (0 : R) := rfl

@[simp] lemma gen_lin (i : Fin n) : (gen mu i).lin = fun j ↦ if j = i then (1 : R) else 0 := rfl

/-- $w$ 分解为常值部分与生成元的线性组合：
$w = w_{\rm const} \cdot 1 + \sum_i (w_{\rm lin})_i\, x_i$（求和用无选择公理的 `finSum`）。 -/
lemma decomp (w : Weil mu) :
    w = w.const • (1 : Weil mu) + finSum (Weil mu) n (fun i : Fin n ↦ w.lin i • gen mu i) := by
  apply ext
  · change w.const = (w.const • (1 : Weil mu)).const
      + constHom (finSum (Weil mu) n (fun i : Fin n ↦ w.lin i • gen mu i))
    have hmap : constHom (finSum (Weil mu) n (fun i ↦ w.lin i • gen mu i)) = finSum R n (fun i ↦ constHom (w.lin i • gen mu i)) := by
      exact map_finSum (Weil mu) R (constHom : Weil mu →+ R) n (fun i ↦ w.lin i • gen mu i)
    rw [hmap]
    change w.const = (w.const • (1 : Weil mu)).const + finSum R n (fun i : Fin n ↦ (w.lin i • gen mu i).const)
    simp [finSum_eq_zero]
  · funext j
    change w.lin j = (w.const • (1 : Weil mu)).lin j
        + (linHom : Weil mu →+ (Fin n → R)) (finSum (Weil mu) n (fun i : Fin n ↦ w.lin i • gen mu i)) j
    rw [map_finSum (Weil mu) (Fin n → R) (linHom : Weil mu →+ (Fin n → R)) n (fun i ↦ w.lin i • gen mu i)]
    rw [finSum_apply]
    change w.lin j = (w.const • (1 : Weil mu)).lin j + finSum R n (fun i : Fin n ↦ (w.lin i • gen mu i).lin j)
    have hsingle : finSum R n (fun i : Fin n ↦ (w.lin i • gen mu i).lin j) = w.lin j := by
      have hterm : ∀ i : Fin n, (w.lin i • gen mu i).lin j = (if i = j then w.lin j * 1 else 0) := by
        intro i
        rw [lin_smul]
        change w.lin i * (gen mu i).lin j = (if i = j then w.lin j * 1 else 0)
        have hg : (gen mu i).lin j = if j = i then (1 : R) else 0 := by
          rfl
        rw [hg]
        by_cases h : i = j
        · subst i
          simp
        · have hji : j ≠ i := fun hj => h hj.symm
          simp [h, hji]
      calc
        finSum R n (fun i ↦ (w.lin i • gen mu i).lin j)
            = finSum R n (fun i ↦ if i = j then w.lin j * 1 else 0) := by
              exact congrArg (fun φ : Fin n → R ↦ finSum R n φ) (funext hterm)
        _ = w.lin j * 1 := finSum_eq_single R j (w.lin j * 1)
        _ = w.lin j := by simp
    rw [hsingle]
    simp

end Weil

/-- **一般 KL 公理（Axiom 1W）在坐标 Weil 代数 `Weil mu` 上的实例**：谱上的每个函数
$f : \operatorname{Spec} W \to R$（即 $f : (W \to_R R) \to R$）唯一地是求值函数
$g \mapsto g\,w$（对某个唯一的 $w \in W$），即典范求值变换
$W \to R^{\operatorname{Spec} W}$ 是双射。 -/
def IsKockLawvereWeilAt {R} [CommRing R] {n : ℕ}
    (mu : (Fin n → R) → (Fin n → R) → (Fin n → R)) [WeilMul mu] :=
  (f : (Weil mu →ₐ[R] R) → R) → ExistsUnique' fun x ↦ f = fun g ↦ g x

/-- **一般 Kock-Lawvere 公理（Axiom 1W）**：对一切坐标 Weil 代数 `Weil mu`（任意 $n$、
任意 `WeilMul` 的 $\mu$）成立 `IsKockLawvereWeilAt`，即谱上的函数恰由 `Weil mu` 的元素给出。 -/
class IsKockLawvereWeil (R) extends CommRing R where
  isKockLawvereWeil n mu [WeilMul (R := R) (n := n) mu] : IsKockLawvereWeilAt mu
