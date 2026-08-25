import SDG.NoChoice
import SDG.FinSumProd
import Mathlib

/-!
# SDG.Infinitesimal

无穷小量 (infinitesimals)：综合微分几何 (SDG) 的基础对象。

与经典分析不同，SDG 不依赖极限：我们直接假定「无穷小量」存在，
并利用 Kock-Lawvere 公理将函数在无穷小量上的行为线性化，从而定义导数
（Kock-Lawvere 公理与导数见 `SDG.Derivative`）。

主要内容：
* 有理数代数 `NontrivialRatCommAlgebra R`（每个正整数可逆）；
* 无穷小量集合 $D = \{ x \mid x^2 = 0 \}$；
* $n$ 维无穷小邻域 $D(n)$ 与 $n$ 重积 $D^n$，以及包含关系 $D(n) \subseteq D^n$；
* 「存在且唯一」编码 `ExistsUnique'`（被 Kock-Lawvere 公理与微线性对象共用）。

无选择公理的 $\mathrm{Fin}\ n$ 求和与乘积工具（`finSum`/`finProd`，连同 `Fin`
索引辅助）已拆至 `SDG.FinSumProd`，本文件通过 import 再导出（re-export）。
-/

/-! ## 一维高阶无穷小量 $D_k$（$D = D_1$ 为其特例）

一维高阶无穷小量（Kock 记号，Axiom 1' 所用对象）：
$$D_k = D_k(1) = \{ x \mid x^{k+1} = 0 \}.$$
即「$k+1$ 个 $x$ 相乘为零」=$x^{k+1}=0$，与 $D_k(n)$（`Dkn`）取 $n = 1$ 时一致：
唯一坐标重复 $k+1$ 次。用幂运算直接编码。

一阶特例即无穷小量集合 $D = D_1 = \{ x \mid x^2 = 0 \}$（见 `D`）；
与 $D_k(n)$ 的对应（$D_k \cong D_k(1)$）见 `Dk_equiv_Dkn1`。
-/

/-- 一维高阶无穷小量 $D_k = \{ x \mid x^{k+1} = 0 \}$，由 $D_k(n)$ 取 $n = 1$ 得到：
「$k+1$ 个 $x$（唯一坐标）相乘为零」=$x^{k+1}=0$。作为 $R$ 在数乘下封闭的子集
（标量即乘法）。 -/
def Dk (R) [CommRing R] (k : ℕ) : SubMulAction R R where
  carrier := { x | x ^ (k + 1) = 0 }
  smul_mem' := by
    intro c x hx
    change (c * x) ^ (k + 1) = 0
    calc
      (c * x) ^ (k + 1) = c ^ (k + 1) * x ^ (k + 1) := by rw [mul_pow]
      _ = 0 := by rw [hx]; simp


/-- 零元属于 $D_k$：$0^{k+1} = 0$，故 $D_k$ 带有零元。 -/
instance instZeroDk R [CommRing R] (k : ℕ) : Zero (Dk R k) where
  zero := ⟨0, by
    exact zero_pow (n := k + 1) (Nat.succ_ne_zero k)
  ⟩


/-- $D_k$ 中的零元在 $R$ 中的像就是 $0$。 -/
@[simp]
theorem zero_coeDk {R} [CommRing R] {k : ℕ} :
    ((0 : Dk R k) : R) = 0 := rfl


/-- 无穷小量集合 $D = \{ x \mid x^2 = 0 \}$：**一维一阶无穷小量，即 $D_k$ 的 $k = 1$ 特例**。
$$D = D_1 = \{ x \mid x^2 = 0 \}.$$
在经典分析中 $D = \{ 0 \}$，但在 SDG 中我们假定其中还含有非零元素。 -/
abbrev D R [CommRing R] : SubMulAction R R := Dk R 1


/-- $D$ 元素的两两乘积为零：$d \cdot d = 0$（由 `D = D_1` 的成员证明经 `pow_two` 转换）。 -/
lemma D.mul_eq_zero (R) [CommRing R] (d : D R) : (d : R) * (d : R) = 0 := by
  have h : (d : R) ^ (1 + 1) = 0 := d.2
  change (d : R) ^ 2 = 0 at h
  rw [pow_two] at h
  exact h


/-- 由 $x \cdot x = 0$ 构造 $D$ 元素（`D = D_1` 的成员证明便捷形式）。 -/
@[reducible] def D.ofMul (R) [CommRing R] (x : R) (h : x * x = 0) : D R := ⟨x, by
  change x ^ 2 = 0
  rw [pow_two]
  exact h
⟩


/-- $D$ 中的零元在 $R$ 中的像就是 $0$。 -/
@[simp]
theorem zero_coeD {R} [CommRing R] :
    ((0 : D R) : R) = 0 := rfl


/-! ## $D_k$ 的包含与加法

$D_k$ 的两个基本结构事实（纯环论，不需 KL 公理）：$D_m \subseteq D_{m+1}$，
以及若 $d \in D_m$、$e \in D$（$e^2 = 0$）则 $d + e \in D_{m+1}$。这给出「沿
$e$ 方向扰动仍在 $D_{m+1}$ 内」的事实，配合 $D_{m+1}$ 上的多项式展开求导数
（后者见 `SDG.Derivative` 的 `sderiv_expansion`）。 -/

/-- 幂的二项式线性化（纯环论）：对 $e \in D$，$(d + e)^n = d^n + n\,d^{n-1} e$
（$n = 0$ 时 $d^{n-1} = d^0 = 1$、系数 $0$，等式自然成立）。
`SDG.Derivative` 的 `sderiv_pow` 将其表述为幂函数导数
$\mathrm{sderiv}\,(x \mapsto x^n)\, d = n\,d^{n-1}$。 -/
lemma pow_add_sq_zero {R} [CommRing R] (d : R) (e : D R) (n : ℕ) :
    (d + (e : R)) ^ n = d ^ n + (n : R) * d ^ (n - 1) * (e : R) := by
  induction n with
  | zero => simp
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        simp [pow_succ, ih, pow_zero]
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        have hsub : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hnpos
        have hd : d ^ (n - 1) * d = d ^ n := by
          rw [← pow_succ, hsub]
        rw [pow_succ, ih]
        ring_nf
        rw [show (e : R) ^ 2 = (e : R) * (e : R) by rw [pow_two]]
        rw [D.mul_eq_zero R e]
        rw [mul_zero]
        rw [add_zero]
        rw [show d * d ^ (n - 1) = d ^ (n - 1) * d by ring]
        rw [hd]
        rw [show 1 + n - 1 = n by omega]
        rw [show ((1 + n : ℕ) : R) = (n : R) + 1 by
          rw [Nat.cast_add, Nat.cast_one]
          ring]
        ring


/-- 包含 $D_m \hookrightarrow D_{m+1}$：$d^{m+1} = 0 \implies d^{m+2} = 0$。 -/
def Dk.inclusion (R) [CommRing R] {m : ℕ} (d : Dk R m) : Dk R (m+1) :=
  ⟨(d : R), by
    change (d : R) ^ ((m + 1) + 1) = 0
    rw [pow_succ, d.2]
    simp
  ⟩


/-- 若 $d \in D_m$、$e \in D$（$e^2 = 0$），则 $d + e \in D_{m+1}$。
（由二项式线性化：$(d+e)^{m+2} = d^{m+2} + (m+2)d^{m+1}e = 0$。） -/
def Dk.add (R) [CommRing R] {m : ℕ} (d : Dk R m) (e : D R) : Dk R (m+1) :=
  ⟨(d : R) + (e : R), by
    change ((d : R) + (e : R)) ^ ((m + 1) + 1) = 0
    rw [pow_add_sq_zero (d : R) e (m + 2)]
    have hd : (d : R) ^ (m + 1) = 0 := d.2
    have hd2 : (d : R) ^ (m + 2) = 0 := by
      change (d : R) ^ ((m + 1) + 1) = 0
      rw [pow_succ, hd]
      simp
    have hsub : (m + 2) - 1 = m + 1 := by omega
    rw [hd2, hsub, hd]
    simp
  ⟩


/-! ## 高阶无穷小邻域 $D_k(n)$（基础定义）

高阶无穷小邻域（Kock 记号）：$R^n$ 中所有「任意 $k+1$ 个分量（允许重复）的
乘积为零」的 $n$ 元组构成的集合
$$D_k(n) = \left\{ (x_1, \ldots, x_n) \in R^n \;\middle|\; x_{i_1} \cdots x_{i_{k+1}} = 0 \ (\forall\, i_1, \ldots, i_{k+1}) \right\}.$$

$k+1$ 重乘积用无选择公理的 `finProd` 编码。一维情形 $D_k(1) = \{ x \mid x^{k+1} = 0 \}$
是单变量高阶无穷小量（Kock 的 Axiom 1'）；$k$ 越大条件越弱，故 $D_k(n) \subseteq D_{k+1}(n)$。
`Dn`（即 $D(n)$）定义为 $k = 1$ 特例，`D` 与其一维情形同构（见后文）。
-/

/-- 高阶无穷小邻域 $D_k(n)$：任意 $k+1$ 个分量（允许重复）的乘积为零。
$$D_k(n) = \{ x : \text{Fin } n \to R \mid \forall \iota : \text{Fin } (k+1) \to \text{Fin } n,\ \prod_j x_{\iota_j} = 0 \}$$
作为 $\text{Fin } n \to R$ 在数乘下封闭的子集（标量逐点作用）。 -/
def Dkn (R) [CommRing R] (k n : ℕ) : SubMulAction R (Fin n → R) where
  carrier := { x | ∀ ι : Fin (k+1) → Fin n, finProd R (k+1) (fun j ↦ x (ι j)) = 0 }
  smul_mem' := by
    intro c x hx ι
    have h : finProd R (k+1) (fun j : Fin (k+1) ↦ x (ι j)) = 0 := hx ι
    change finProd R (k+1) (fun j : Fin (k+1) ↦ c * x (ι j)) = 0
    calc
      finProd R (k+1) (fun j : Fin (k+1) ↦ c * x (ι j))
          = finProd R (k+1) (fun _ : Fin (k+1) ↦ c) * finProd R (k+1) (fun j : Fin (k+1) ↦ x (ι j)) := by
              exact finProd_mul R (k+1) (fun _ : Fin (k+1) ↦ c) (fun j : Fin (k+1) ↦ x (ι j))
      _ = 0 := by
              rw [h]
              exact mul_zero _


/-- 零元属于 $D_k(n)$：全零元组的任意 $k+1$ 重乘积为零，故 $D_k(n)$ 带有零元。 -/
instance instZeroDkn R [CommRing R] (k n : ℕ) : Zero (Dkn R k n) where
  zero := ⟨fun _ : Fin n ↦ 0, by
    intro ι
    exact finProd_zero_succ R k
  ⟩


/-- $D_k(n)$ 中的零元在 $R^n$ 中的像就是零元组。 -/
@[simp]
theorem zero_coeDkn {R} [CommRing R] {k n : ℕ} :
    ((0 : Dkn R k n) : Fin n → R) = fun _ ↦ 0 := rfl


/-! ## n维无穷小邻域 $D(n)$

将一维无穷小量 $D$ 推广到 $n$ 维：$R^n$（表示为 $\text{Fin } n \to R$）中
所有「两两乘积为零」的 $n$ 元组构成的集合
$$D(n) = \left\{ (x_1, \ldots, x_n) \in R^n \;\middle|\; x_i x_j = 0 \ (\forall i, j) \right\}.$$

当 $i = j$ 时，条件退化为 $x_i^2 = 0$，即每个分量都在 $D$ 中，
因此 $D(n) \subseteq D^n = D \times \cdots \times D$。
-/

/-- $n$ 维无穷小邻域 $D(n)$：**高阶无穷小邻域 $D_k(n)$ 的一阶特例（$k = 1$）**。
$$D(n) = D_1(n) = \{ x : \text{Fin } n \to R \mid \forall \iota : \text{Fin } 2 \to \text{Fin } n,\ \prod_j x_{\iota_j} = 0 \}$$
即任意两个分量（允许重复）的乘积为零。作为 $\text{Fin } n \to R$ 在数乘下封闭的子集
（标量逐点作用）。成员证明的「两两乘积」便捷形式见 `Dn.mul_eq_zero`，反向构造见
`Dn.ofPairwise`。 -/
abbrev Dn (R) [CommRing R] (n : ℕ) : SubMulAction R (Fin n → R) := Dkn R 1 n


/-- 从两两乘积为零构造 $D(n)$ 元素（`Dn` 成员证明的便捷形式）。 -/
@[reducible] def Dn.ofPairwise (R) [CommRing R] {n : ℕ} (x : Fin n → R)
    (h : ∀ i j : Fin n, x i * x j = 0) : Dn R n :=
  ⟨x, by
    intro ι
    rw [finProd_two]
    exact h (ι 0) (ι 1)
  ⟩

/-- $D(n)$ 元素的两两乘积为零（`Dn` 成员证明的便捷形式）。 -/
lemma Dn.mul_eq_zero (R) [CommRing R] {n : ℕ} (u : Dn R n) (i j : Fin n) :
    u.1 i * u.1 j = 0 := by
  have h := u.2 (fun k : Fin 2 ↦ if k = 0 then i else j)
  rw [finProd_two] at h
  simpa using h


/-- $D(n)$ 中的零元在 $R^n$ 中的像就是零元组。 -/
@[simp]
theorem zero_coeDn {R} [CommRing R] {n : ℕ} :
    ((0 : Dn R n) : Fin n → R) = fun _ ↦ 0 := rfl


/-- 由 $D(2)$ 元素 $u$ 的第 0 个坐标给出的无穷小量 $u_0 \in D$。 -/
def Dn.comp0 (R) [CommRing R] (u : Dn R 2) : D R := D.ofMul R (u.1 0) (Dn.mul_eq_zero R u 0 0)

/-- 由 $D(2)$ 元素 $u$ 的第 1 个坐标给出的无穷小量 $u_1 \in D$。 -/
def Dn.comp1 (R) [CommRing R] (u : Dn R 2) : D R := D.ofMul R (u.1 1) (Dn.mul_eq_zero R u 1 1)

/-- 由 $D(2)$ 元素 $u$ 的两个坐标之和给出的无穷小量 $u_0 + u_1 \in D$
（因两两乘积为零，$u_0 + u_1$ 的平方为零）。 -/
def Dn.add01 (R) [CommRing R] (u : Dn R 2) : D R :=
  ⟨u.1 0 + u.1 1, by
    change (u.1 0 + u.1 1) ^ 2 = 0
    rw [pow_two]
    have h00 : u.1 0 * u.1 0 = 0 := Dn.mul_eq_zero R u 0 0
    have h01 : u.1 0 * u.1 1 = 0 := Dn.mul_eq_zero R u 0 1
    have h11 : u.1 1 * u.1 1 = 0 := Dn.mul_eq_zero R u 1 1
    calc
      (u.1 0 + u.1 1) * (u.1 0 + u.1 1)
          = u.1 0 * u.1 0 + 2 * (u.1 0 * u.1 1) + u.1 1 * u.1 1 := by ring
      _ = 0 := by simp [h00, h01, h11]
  ⟩


/-- 由 $d \in D$ 构造 $D(2)$ 元素 $(d, -d)$（两坐标乘积为零，因 $d^2 = 0$）。 -/
def Dn.mkDiagNeg (R) [CommRing R] (d : D R) : Dn R 2 :=
  Dn.ofPairwise R (fun i : Fin 2 ↦ if i = 0 then (d : R) else -(d : R)) (by
    intro i j
    by_cases hi : i = 0
    · by_cases hj : j = 0
      · -- d · d = 0
        simp [hi, hj]
        exact D.mul_eq_zero R d
      · -- d · (-d) = 0
        simp [hi, hj]
        ring_nf
        have h : (d : R) * (d : R) = 0 := D.mul_eq_zero R d
        rw [pow_two, h]
    · by_cases hj : j = 0
      · -- (-d) · d = 0
        simp [hi, hj]
        ring_nf
        have h : (d : R) * (d : R) = 0 := D.mul_eq_zero R d
        rw [pow_two, h]
      · -- (-d) · (-d) = 0
        simp [hi, hj]
        ring_nf
        have h : (d : R) * (d : R) = 0 := D.mul_eq_zero R d
        rw [pow_two, h]
  )

/-- $(d, -d)$ 的第 0 坐标是 $d$。 -/
@[simp]
lemma Dn.comp0_mkDiagNeg (R) [CommRing R] (d : D R) :
    Dn.comp0 R (Dn.mkDiagNeg R d) = d := by
  apply Subtype.ext
  dsimp [Dn.comp0, Dn.mkDiagNeg]

/-- $(d, -d)$ 的第 1 坐标是 $-d$。 -/
@[simp]
lemma Dn.comp1_mkDiagNeg (R) [CommRing R] (d : D R) :
    Dn.comp1 R (Dn.mkDiagNeg R d) = -d := by
  apply Subtype.ext
  dsimp [Dn.comp1, Dn.mkDiagNeg]

/-- $(d, -d)$ 的两坐标之和为 $0$。 -/
@[simp]
lemma Dn.add01_mkDiagNeg (R) [CommRing R] (d : D R) :
    Dn.add01 R (Dn.mkDiagNeg R d) = 0 := by
  apply Subtype.ext
  dsimp [Dn.add01, Dn.mkDiagNeg]
  simp


/-- 坐标嵌入 $e_i : D \to D(n)$：把无穷小量 $d$ 放在第 $i$ 个坐标，其余为 $0$。 -/
def Dn.embed (R) [CommRing R] {n : ℕ} (i : Fin n) (d : D R) : Dn R n :=
  Dn.ofPairwise R (Function.update (fun _ : Fin n ↦ (0 : R)) i (d : R)) (by
    intro a b
    by_cases ha : a = i
    · subst a
      by_cases hb : b = i
      · subst b
        simp [Function.update]
        exact D.mul_eq_zero R d
      · simp [Function.update, hb]
    · by_cases hb : b = i
      · subst b
        simp [Function.update, ha]
      · simp [Function.update, ha, hb]
  )

/-- 坐标嵌入在 $0$ 处给出 $D(n)$ 的零元：$e_i(0) = 0_{D(n)}$。 -/
@[simp]
lemma Dn.embed_zero (R) [CommRing R] {n : ℕ} (i : Fin n) :
    Dn.embed R i 0 = 0 := by
  apply Subtype.ext
  funext k
  -- 用 dsimp 只做定义展开，避免 simp 展开时简化证明部分（会引入选择公理）
  dsimp [Dn.embed]
  simp [Function.update]


/-- 切向量族在基点上的纤维积：
一族切向量 $(v_i)_{i : \text{Fin } n}$，满足所有 $v_i$ 在 $0$ 处取值相同（同一基点）。 -/
def TangentFiberProduct (R) [CommRing R] (X : Type*) (n : ℕ) :
    Set (Fin n → (D R → X)) :=
  { v | ∀ i j : Fin n, v i 0 = v j 0 }


/-- 典范映射 $\Phi_n : X^{D(n)} \to (X^D)^n$：把 $g$ 沿各坐标方向拉回。 -/
def Dn.restrict (R) [CommRing R] {X} {n : ℕ}
    (g : Dn R n → X) : Fin n → (D R → X) :=
  fun i d ↦ g (Dn.embed R i d)


/-- $\Phi_n$ 的值域限制到纤维积上：$X^{D(n)} \to X^D \times_X \cdots \times_X X^D$。 -/
def Dn.restrict' (R) [CommRing R] {X} {n : ℕ}
    (g : Dn R n → X) : TangentFiberProduct R X n :=
  ⟨Dn.restrict R g, by
    intro i j
    dsimp [Dn.restrict]
    rw [Dn.embed_zero, Dn.embed_zero]
  ⟩

/-- 第 0 坐标经坐标嵌入 $e_0$ 后为 $d$。 -/
@[simp]
lemma Dn.comp0_embed0 (R) [CommRing R] (d : D R) :
    Dn.comp0 R (Dn.embed R (0 : Fin 2) d) = d := by
  apply Subtype.ext
  dsimp [Dn.comp0, Dn.embed]
  simp [Function.update]

/-- 第 0 坐标经坐标嵌入 $e_1$ 后为 $0$。 -/
@[simp]
lemma Dn.comp0_embed1 (R) [CommRing R] (d : D R) :
    Dn.comp0 R (Dn.embed R (1 : Fin 2) d) = 0 := by
  apply Subtype.ext
  dsimp [Dn.comp0, Dn.embed]
  simp [Function.update]

/-- 第 1 坐标经坐标嵌入 $e_0$ 后为 $0$。 -/
@[simp]
lemma Dn.comp1_embed0 (R) [CommRing R] (d : D R) :
    Dn.comp1 R (Dn.embed R (0 : Fin 2) d) = 0 := by
  apply Subtype.ext
  dsimp [Dn.comp1, Dn.embed]
  simp [Function.update]

/-- 第 1 坐标经坐标嵌入 $e_1$ 后为 $d$。 -/
@[simp]
lemma Dn.comp1_embed1 (R) [CommRing R] (d : D R) :
    Dn.comp1 R (Dn.embed R (1 : Fin 2) d) = d := by
  apply Subtype.ext
  dsimp [Dn.comp1, Dn.embed]
  simp [Function.update]

/-- 坐标之和经坐标嵌入 $e_0$ 后为 $d$。 -/
@[simp]
lemma Dn.add01_embed0 (R) [CommRing R] (d : D R) :
    Dn.add01 R (Dn.embed R (0 : Fin 2) d) = d := by
  apply Subtype.ext
  dsimp [Dn.add01, Dn.embed]
  simp [Function.update]

/-- 坐标之和经坐标嵌入 $e_1$ 后为 $d$。 -/
@[simp]
lemma Dn.add01_embed1 (R) [CommRing R] (d : D R) :
    Dn.add01 R (Dn.embed R (1 : Fin 2) d) = d := by
  apply Subtype.ext
  dsimp [Dn.add01, Dn.embed]
  simp [Function.update]

/-- 对角映射 $\Delta : D \to D(2)$，$d \mapsto (d, d)$。 -/
def Dn.diag (R) [CommRing R] (d : D R) : Dn R 2 :=
  Dn.ofPairwise R (fun _ : Fin 2 ↦ (d : R)) (by
    intro i j
    exact D.mul_eq_zero R d
  )


/-- 交换 $D(2)$ 的两个坐标：$(x_1, x_2) \mapsto (x_2, x_1)$。 -/
def Dn.swap (R) [CommRing R] (x : Dn R 2) : Dn R 2 :=
  Dn.ofPairwise R (fun i ↦ x.1 (if i = 0 then (1 : Fin 2) else 0)) (by
    intro i j
    exact Dn.mul_eq_zero R x (if i = 0 then (1 : Fin 2) else 0) (if j = 0 then (1 : Fin 2) else 0)
  )


/-- 交换坐标后 $e_0$ 变成 $e_1$：$\mathrm{swap}(e_0(d)) = e_1(d)$。 -/
lemma Dn.swap_embed_0 (R) [CommRing R] (d : D R) :
    Dn.swap R (Dn.embed R 0 d) = Dn.embed R 1 d := by
  apply Subtype.ext
  funext i
  by_cases hi : i = 0
  · subst i
    simp [Dn.swap, Dn.embed, Function.update]
  · have hi1 : i = (1 : Fin 2) := fin_two_eq_one_of_ne_zero hi
    subst i
    simp [Dn.swap, Dn.embed, Function.update]


/-- 交换坐标后 $e_1$ 变成 $e_0$：$\mathrm{swap}(e_1(d)) = e_0(d)$。 -/
lemma Dn.swap_embed_1 (R) [CommRing R] (d : D R) :
    Dn.swap R (Dn.embed R 1 d) = Dn.embed R 0 d := by
  apply Subtype.ext
  funext i
  by_cases hi : i = 0
  · subst i
    simp [Dn.swap, Dn.embed, Function.update]
  · have hi1 : i = (1 : Fin 2) := fin_two_eq_one_of_ne_zero hi
    subst i
    simp [Dn.swap, Dn.embed, Function.update]


/-- 交换坐标后第 0 坐标变成原来的第 1 坐标。 -/
@[simp]
lemma Dn.comp0_swap (R) [CommRing R] (u : Dn R 2) :
    Dn.comp0 R (Dn.swap R u) = Dn.comp1 R u := by
  apply Subtype.ext
  simp [Dn.comp0, Dn.comp1, Dn.swap]

/-- 交换坐标后第 1 坐标变成原来的第 0 坐标。 -/
@[simp]
lemma Dn.comp1_swap (R) [CommRing R] (u : Dn R 2) :
    Dn.comp1 R (Dn.swap R u) = Dn.comp0 R u := by
  apply Subtype.ext
  simp [Dn.comp0, Dn.comp1, Dn.swap]

/-- 交换坐标不改变两坐标之和。 -/
@[simp]
lemma Dn.add01_swap (R) [CommRing R] (u : Dn R 2) :
    Dn.add01 R (Dn.swap R u) = Dn.add01 R u := by
  apply Subtype.ext
  simp [Dn.add01, Dn.swap]
  ring


/-- 缩放与坐标嵌入交换：$a \cdot e_i(d) = e_i(a \cdot d)$。 -/
lemma Dn.embed_smul (R) [CommRing R] {n : ℕ} (a : R) (i : Fin n) (d : D R) :
    a • Dn.embed R i d = Dn.embed R i (a • d) := by
  apply Subtype.ext
  funext k
  by_cases hk : k = i
  · subst k
    simp [Dn.embed, Function.update, smul_eq_mul]
  · simp [Dn.embed, Function.update, hk]


/-- 缩放与对角映射交换：$a \cdot \Delta(d) = \Delta(a \cdot d)$。 -/
lemma Dn.diag_smul (R) [CommRing R] (a : R) (d : D R) :
    a • Dn.diag R d = Dn.diag R (a • d) := by
  apply Subtype.ext
  funext k
  change a • (d : R) = a • (d : R)
  rfl


/-- 由 $D(2)$ 元素 $x$ 与系数 $a, b$ 的线性组合 $a x_0 + b x_1 \in D$。 -/
def Dn.linComb (R) [CommRing R] (a b : R) (x : Dn R 2) : D R :=
  ⟨a * x.1 0 + b * x.1 1, by
    change (a * x.1 0 + b * x.1 1) ^ 2 = 0
    rw [pow_two]
    have h00 : x.1 0 * x.1 0 = 0 := Dn.mul_eq_zero R x 0 0
    have h01 : x.1 0 * x.1 1 = 0 := Dn.mul_eq_zero R x 0 1
    have h11 : x.1 1 * x.1 1 = 0 := Dn.mul_eq_zero R x 1 1
    calc
      (a * x.1 0 + b * x.1 1) * (a * x.1 0 + b * x.1 1)
          = a * a * (x.1 0 * x.1 0) + 2 * (a * b * (x.1 0 * x.1 1)) + b * b * (x.1 1 * x.1 1) := by ring
      _ = 0 := by simp [h00, h01, h11]
  ⟩


/-- 线性组合在坐标嵌入 $e_0$ 处的值：$a e_0(t)_0 + b e_0(t)_1 = a t$。 -/
lemma Dn.linComb_embed_0 (R) [CommRing R] (a b : R) (t : D R) :
    Dn.linComb R a b (Dn.embed R 0 t) = a • t := by
  apply Subtype.ext
  simp [Dn.linComb, Dn.embed, Function.update, smul_eq_mul]


/-- 线性组合在坐标嵌入 $e_1$ 处的值：$a e_1(t)_0 + b e_1(t)_1 = b t$。 -/
lemma Dn.linComb_embed_1 (R) [CommRing R] (a b : R) (t : D R) :
    Dn.linComb R a b (Dn.embed R 1 t) = b • t := by
  apply Subtype.ext
  simp [Dn.linComb, Dn.embed, Function.update, smul_eq_mul]


/-- 线性组合在对角映射处的值：$a \Delta(d)_0 + b \Delta(d)_1 = (a+b) d$。 -/
lemma Dn.linComb_diag (R) [CommRing R] (a b : R) (d : D R) :
    Dn.linComb R a b (Dn.diag R d) = (a + b) • d := by
  apply Subtype.ext
  simp [Dn.linComb, Dn.diag, smul_eq_mul]
  ring


/-- 由两个同基点切向量构造 $D(2)$ 的纤维积元素 $(v_1, v_2)$。 -/
def mkFiberProduct2 (R) [CommRing R] {X : Type*}
    (v1 v2 : D R → X) (h : v1 0 = v2 0) : TangentFiberProduct R X 2 :=
  ⟨fun i ↦ if i = 0 then v1 else v2, by
    intro i j
    -- 用 by_cases（而非 fin_cases）以避免引入选择公理
    by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [hi, hj, h]
  ⟩


/-! ### $D(3)$ 基础设施（用于加法结合律） -/

/-- 把 $D(2)$ 嵌入 $D(3)$ 的前两个坐标：$(x_0, x_1) \mapsto (x_0, x_1, 0)$。 -/
def Dn.emb3_0 (R) [CommRing R] (x : Dn R 2) : Dn R 3 :=
  Dn.ofPairwise R (fun i : Fin 3 ↦ if i = 0 then x.1 (0 : Fin 2) else if i = 1 then x.1 (1 : Fin 2) else 0) (by
    intro i j
    by_cases hi0 : i = 0 <;> by_cases hi1 : i = 1 <;> by_cases hj0 : j = 0 <;> by_cases hj1 : j = 1
    <;> simp [hi0, hi1, hj0, hj1]
    <;> first | simp | exact Dn.mul_eq_zero R x 0 0 | exact Dn.mul_eq_zero R x 0 1 | exact Dn.mul_eq_zero R x 1 0 | exact Dn.mul_eq_zero R x 1 1
  )


/-- 把 $D(2)$ 嵌入 $D(3)$ 的后两个坐标：$(x_0, x_1) \mapsto (0, x_0, x_1)$。 -/
def Dn.emb3_2 (R) [CommRing R] (x : Dn R 2) : Dn R 3 :=
  Dn.ofPairwise R (fun i : Fin 3 ↦ if i = 0 then 0 else if i = 1 then x.1 (0 : Fin 2) else x.1 (1 : Fin 2)) (by
    intro i j
    by_cases hi0 : i = 0 <;> by_cases hi1 : i = 1 <;> by_cases hj0 : j = 0 <;> by_cases hj1 : j = 1
    <;> simp [hi0, hi1, hj0, hj1]
    <;> first | simp | exact Dn.mul_eq_zero R x 0 0 | exact Dn.mul_eq_zero R x 0 1 | exact Dn.mul_eq_zero R x 1 0 | exact Dn.mul_eq_zero R x 1 1
  )


/-- 三重对角：$d \mapsto (d, d, d)$。 -/
def Dn.diag3 (R) [CommRing R] (d : D R) : Dn R 3 :=
  Dn.ofPairwise R (fun i : Fin 3 ↦ d) (by
    intro i j
    exact D.mul_eq_zero R d
  )


/-- 「前两坐标相加并复制」：$(x_0, x_1, x_2) \mapsto (x_0 + x_1, x_0 + x_1, x_2)$。 -/
def Dn.squash01 (R) [CommRing R] (x : Dn R 3) : Dn R 3 :=
  Dn.ofPairwise R (fun i : Fin 3 ↦ if i = 0 then x.1 0 + x.1 1 else if i = 1 then x.1 0 + x.1 1 else x.1 2) (by
    intro i j
    by_cases hi0 : i = 0 <;> by_cases hi1 : i = 1 <;> by_cases hj0 : j = 0 <;> by_cases hj1 : j = 1
    <;> simp [hi0, hi1, hj0, hj1]
    <;> ring_nf
    <;> simp [pow_two, Dn.mul_eq_zero R x 0 0, Dn.mul_eq_zero R x 0 1, Dn.mul_eq_zero R x 0 2, Dn.mul_eq_zero R x 1 1, Dn.mul_eq_zero R x 1 2, Dn.mul_eq_zero R x 2 0, Dn.mul_eq_zero R x 2 1, Dn.mul_eq_zero R x 2 2]
  )


/-- 「后两坐标相加并复制」：$(x_0, x_1, x_2) \mapsto (x_0, x_1 + x_2, x_1 + x_2)$。 -/
def Dn.squash12 (R) [CommRing R] (x : Dn R 3) : Dn R 3 :=
  Dn.ofPairwise R (fun i : Fin 3 ↦ if i = 0 then x.1 0 else if i = 1 then x.1 1 + x.1 2 else x.1 1 + x.1 2) (by
    intro i j
    by_cases hi0 : i = 0 <;> by_cases hi1 : i = 1 <;> by_cases hj0 : j = 0 <;> by_cases hj1 : j = 1
    <;> simp [hi0, hi1, hj0, hj1]
    <;> ring_nf
    <;> simp [pow_two, Dn.mul_eq_zero R x 0 0, Dn.mul_eq_zero R x 0 1, Dn.mul_eq_zero R x 0 2, Dn.mul_eq_zero R x 1 0, Dn.mul_eq_zero R x 1 1, Dn.mul_eq_zero R x 1 2, Dn.mul_eq_zero R x 2 0, Dn.mul_eq_zero R x 2 2]
  )


/-- 前两坐标相加：$(x_0, x_1, x_2) \mapsto (x_0 + x_1, x_2) \in D(2)$。 -/
def Dn.alpha (R) [CommRing R] (x : Dn R 3) : Dn R 2 :=
  Dn.ofPairwise R (fun i : Fin 2 ↦ if i = 0 then x.1 0 + x.1 1 else x.1 2) (by
    intro i j
    by_cases hi : i = 0 <;> by_cases hj : j = 0
    <;> simp [hi, hj]
    <;> ring_nf
    <;> simp [pow_two, Dn.mul_eq_zero R x 0 0, Dn.mul_eq_zero R x 0 1, Dn.mul_eq_zero R x 0 2, Dn.mul_eq_zero R x 1 1, Dn.mul_eq_zero R x 1 2, Dn.mul_eq_zero R x 2 0, Dn.mul_eq_zero R x 2 1, Dn.mul_eq_zero R x 2 2]
  )


/-- 后两坐标相加：$(x_0, x_1, x_2) \mapsto (x_0, x_1 + x_2) \in D(2)$。 -/
def Dn.beta (R) [CommRing R] (x : Dn R 3) : Dn R 2 :=
  Dn.ofPairwise R (fun i : Fin 2 ↦ if i = 0 then x.1 0 else x.1 1 + x.1 2) (by
    intro i j
    by_cases hi : i = 0 <;> by_cases hj : j = 0
    <;> simp [hi, hj]
    <;> ring_nf
    <;> simp [pow_two, Dn.mul_eq_zero R x 0 0, Dn.mul_eq_zero R x 0 1, Dn.mul_eq_zero R x 0 2, Dn.mul_eq_zero R x 1 0, Dn.mul_eq_zero R x 1 1, Dn.mul_eq_zero R x 1 2, Dn.mul_eq_zero R x 2 0, Dn.mul_eq_zero R x 2 2]
  )


/-- 三个切向量 $(v_1, v_2, v_3)$ 的纤维积数据（基点相同）。 -/
def mkFiberProduct3 (R) [CommRing R] {X : Type*}
    (v1 v2 v3 : D R → X) (h12 : v1 0 = v2 0) (h23 : v2 0 = v3 0) :
    TangentFiberProduct R X 3 :=
  ⟨fun i ↦ if i = 0 then v1 else if i = 1 then v2 else v3, by
    intro i j
    by_cases hi0 : i = 0 <;> by_cases hi1 : i = 1 <;> by_cases hj0 : j = 0 <;> by_cases hj1 : j = 1
    <;> simp [hi0, hi1, hj0, hj1, h12, h23]
  ⟩


/-- 点 $(d, 0, d) \in D(3)$。 -/
def Dn.mk02 (R) [CommRing R] (d : D R) : Dn R 3 :=
  Dn.ofPairwise R (fun i : Fin 3 ↦ if i = 0 then d else if i = 1 then 0 else d) (by
    intro i j
    by_cases hi0 : i = 0 <;> by_cases hi1 : i = 1 <;> by_cases hj0 : j = 0 <;> by_cases hj1 : j = 1
    <;> simp [hi0, hi1, hj0, hj1]
    <;> first | simp | exact D.mul_eq_zero R d
  )


/-- $D(2)$ 第 0 坐标嵌入经 $\\mathrm{emb3}_0$ 后成为 $D(3)$ 第 0 坐标嵌入。 -/
@[simp]
lemma Dn.emb3_0_embed0 (R) [CommRing R] (e : D R) :
    Dn.emb3_0 R (Dn.embed R (0 : Fin 2) e) = Dn.embed R (0 : Fin 3) e := by
  apply Subtype.ext
  funext k
  by_cases hk0 : k = 0 <;> by_cases hk1 : k = 1
  <;> simp [Dn.emb3_0, Dn.embed, Function.update, hk0, hk1]


/-- $D(2)$ 第 1 坐标嵌入经 $\\mathrm{emb3}_0$ 后成为 $D(3)$ 第 1 坐标嵌入。 -/
@[simp]
lemma Dn.emb3_0_embed1 (R) [CommRing R] (e : D R) :
    Dn.emb3_0 R (Dn.embed R (1 : Fin 2) e) = Dn.embed R (1 : Fin 3) e := by
  apply Subtype.ext
  funext k
  by_cases hk0 : k = 0 <;> by_cases hk1 : k = 1
  <;> simp [Dn.emb3_0, Dn.embed, Function.update, hk0, hk1]


/-- $D(2)$ 第 0 坐标嵌入经 $\\mathrm{emb3}_2$ 后成为 $D(3)$ 第 1 坐标嵌入。 -/
@[simp]
lemma Dn.emb3_2_embed0 (R) [CommRing R] (e : D R) :
    Dn.emb3_2 R (Dn.embed R (0 : Fin 2) e) = Dn.embed R (1 : Fin 3) e := by
  apply Subtype.ext
  funext k
  by_cases hk0 : k = 0 <;> by_cases hk1 : k = 1
  <;> simp [Dn.emb3_2, Dn.embed, Function.update, hk0, hk1]


/-- $D(2)$ 第 1 坐标嵌入经 $\\mathrm{emb3}_2$ 后成为 $D(3)$ 第 2 坐标嵌入。 -/
@[simp]
lemma Dn.emb3_2_embed1 (R) [CommRing R] (e : D R) :
    Dn.emb3_2 R (Dn.embed R (1 : Fin 2) e) = Dn.embed R (2 : Fin 3) e := by
  apply Subtype.ext
  funext k
  by_cases hk0 : k = 0
  · subst k
    simp [Dn.emb3_2, Dn.embed, Function.update]
  · by_cases hk1 : k = 1
    · subst k
      simp [Dn.emb3_2, Dn.embed, Function.update]
    · have hk2 : k = (2 : Fin 3) := fin_three_eq_two_of_ne_zero_ne_one hk0 hk1
      subst k
      simp [Dn.emb3_2, Dn.embed, Function.update]


/-- $\\mathrm{squash01}$ 沿方向 0 作用为 $(t,t,0)$。 -/
@[simp]
lemma Dn.squash01_embed0 (R) [CommRing R] (e : D R) :
    Dn.squash01 R (Dn.embed R (0 : Fin 3) e) = Dn.emb3_0 R (Dn.diag R e) := by
  apply Subtype.ext
  funext k
  by_cases hk0 : k = 0 <;> by_cases hk1 : k = 1
  <;> simp [Dn.squash01, Dn.emb3_0, Dn.diag, Dn.embed, Function.update, hk0, hk1]


/-- $\\mathrm{squash01}$ 沿方向 1 作用为 $(t,t,0)$。 -/
@[simp]
lemma Dn.squash01_embed1 (R) [CommRing R] (e : D R) :
    Dn.squash01 R (Dn.embed R (1 : Fin 3) e) = Dn.emb3_0 R (Dn.diag R e) := by
  apply Subtype.ext
  funext k
  by_cases hk0 : k = 0 <;> by_cases hk1 : k = 1
  <;> simp [Dn.squash01, Dn.emb3_0, Dn.diag, Dn.embed, Function.update, hk0, hk1]


/-- $\\mathrm{squash01}$ 沿方向 2 作用不变。 -/
@[simp]
lemma Dn.squash01_embed2 (R) [CommRing R] (e : D R) :
    Dn.squash01 R (Dn.embed R (2 : Fin 3) e) = Dn.embed R (2 : Fin 3) e := by
  apply Subtype.ext
  funext k
  by_cases hk0 : k = 0
  · subst k
    simp [Dn.squash01, Dn.embed, Function.update]
  · by_cases hk1 : k = 1
    · subst k
      simp [Dn.squash01, Dn.embed, Function.update]
    · have hk2 : k = (2 : Fin 3) := fin_three_eq_two_of_ne_zero_ne_one hk0 hk1
      subst k
      simp [Dn.squash01, Dn.embed, Function.update]


/-- $\\mathrm{squash12}$ 沿方向 0 作用不变。 -/
@[simp]
lemma Dn.squash12_embed0 (R) [CommRing R] (e : D R) :
    Dn.squash12 R (Dn.embed R (0 : Fin 3) e) = Dn.embed R (0 : Fin 3) e := by
  apply Subtype.ext
  funext k
  by_cases hk0 : k = 0 <;> by_cases hk1 : k = 1
  <;> simp [Dn.squash12, Dn.embed, Function.update, hk0, hk1]


/-- $\\mathrm{squash12}$ 沿方向 1 作用为 $(0,t,t)$。 -/
@[simp]
lemma Dn.squash12_embed1 (R) [CommRing R] (e : D R) :
    Dn.squash12 R (Dn.embed R (1 : Fin 3) e) = Dn.emb3_2 R (Dn.diag R e) := by
  apply Subtype.ext
  funext k
  by_cases hk0 : k = 0 <;> by_cases hk1 : k = 1
  <;> simp [Dn.squash12, Dn.emb3_2, Dn.diag, Dn.embed, Function.update, hk0, hk1]


/-- $\\mathrm{squash12}$ 沿方向 2 作用为 $(0,t,t)$。 -/
@[simp]
lemma Dn.squash12_embed2 (R) [CommRing R] (e : D R) :
    Dn.squash12 R (Dn.embed R (2 : Fin 3) e) = Dn.emb3_2 R (Dn.diag R e) := by
  apply Subtype.ext
  funext k
  by_cases hk0 : k = 0 <;> by_cases hk1 : k = 1
  <;> simp [Dn.squash12, Dn.emb3_2, Dn.diag, Dn.embed, Function.update, hk0, hk1]


/-- $\\mathrm{alpha}$ 沿方向 0 作用为第 0 坐标嵌入。 -/
@[simp]
lemma Dn.alpha_embed0 (R) [CommRing R] (e : D R) :
    Dn.alpha R (Dn.embed R (0 : Fin 3) e) = Dn.embed R (0 : Fin 2) e := by
  apply Subtype.ext
  funext k
  by_cases hk : k = 0
  <;> simp [Dn.alpha, Dn.embed, Function.update, hk]


/-- $\\mathrm{alpha}$ 沿方向 1 作用为第 0 坐标嵌入。 -/
@[simp]
lemma Dn.alpha_embed1 (R) [CommRing R] (e : D R) :
    Dn.alpha R (Dn.embed R (1 : Fin 3) e) = Dn.embed R (0 : Fin 2) e := by
  apply Subtype.ext
  funext k
  by_cases hk : k = 0
  <;> simp [Dn.alpha, Dn.embed, Function.update, hk]


/-- $\\mathrm{alpha}$ 沿方向 2 作用为第 1 坐标嵌入。 -/
@[simp]
lemma Dn.alpha_embed2 (R) [CommRing R] (e : D R) :
    Dn.alpha R (Dn.embed R (2 : Fin 3) e) = Dn.embed R (1 : Fin 2) e := by
  apply Subtype.ext
  funext k
  by_cases hk : k = 0
  · subst k
    simp [Dn.alpha, Dn.embed, Function.update]
  · have hk1 : k = (1 : Fin 2) := fin_two_eq_one_of_ne_zero hk
    subst k
    simp [Dn.alpha, Dn.embed, Function.update]


/-- $\\mathrm{beta}$ 沿方向 0 作用为第 0 坐标嵌入。 -/
@[simp]
lemma Dn.beta_embed0 (R) [CommRing R] (e : D R) :
    Dn.beta R (Dn.embed R (0 : Fin 3) e) = Dn.embed R (0 : Fin 2) e := by
  apply Subtype.ext
  funext k
  by_cases hk : k = 0
  <;> simp [Dn.beta, Dn.embed, Function.update, hk]


/-- $\\mathrm{beta}$ 沿方向 1 作用为第 1 坐标嵌入。 -/
@[simp]
lemma Dn.beta_embed1 (R) [CommRing R] (e : D R) :
    Dn.beta R (Dn.embed R (1 : Fin 3) e) = Dn.embed R (1 : Fin 2) e := by
  apply Subtype.ext
  funext k
  by_cases hk : k = 0
  · subst k
    simp [Dn.beta, Dn.embed, Function.update]
  · have hk1 : k = (1 : Fin 2) := fin_two_eq_one_of_ne_zero hk
    subst k
    simp [Dn.beta, Dn.embed, Function.update]


/-- $\\mathrm{beta}$ 沿方向 2 作用为第 1 坐标嵌入。 -/
@[simp]
lemma Dn.beta_embed2 (R) [CommRing R] (e : D R) :
    Dn.beta R (Dn.embed R (2 : Fin 3) e) = Dn.embed R (1 : Fin 2) e := by
  apply Subtype.ext
  funext k
  by_cases hk : k = 0
  · subst k
    simp [Dn.beta, Dn.embed, Function.update]
  · have hk1 : k = (1 : Fin 2) := fin_two_eq_one_of_ne_zero hk
    subst k
    simp [Dn.beta, Dn.embed, Function.update]


/-- $\\mathrm{squash01}(d, 0, d) = (d, d, d)$。 -/
lemma Dn.squash01_mk02 (R) [CommRing R] (d : D R) :
    Dn.squash01 R (Dn.mk02 R d) = Dn.diag3 R d := by
  apply Subtype.ext
  funext k
  by_cases hk0 : k = 0 <;> by_cases hk1 : k = 1
  <;> simp [Dn.squash01, Dn.mk02, Dn.diag3, hk0, hk1]


/-- $\\mathrm{squash12}(d, 0, d) = (d, d, d)$。 -/
lemma Dn.squash12_mk02 (R) [CommRing R] (d : D R) :
    Dn.squash12 R (Dn.mk02 R d) = Dn.diag3 R d := by
  apply Subtype.ext
  funext k
  by_cases hk0 : k = 0 <;> by_cases hk1 : k = 1
  <;> simp [Dn.squash12, Dn.mk02, Dn.diag3, hk0, hk1]


/-- $\\mathrm{alpha}(d, 0, d) = (d, d) = \\Delta(d)$。 -/
lemma Dn.alpha_mk02 (R) [CommRing R] (d : D R) :
    Dn.alpha R (Dn.mk02 R d) = Dn.diag R d := by
  apply Subtype.ext
  funext k
  by_cases hk : k = 0
  <;> simp [Dn.alpha, Dn.mk02, Dn.diag, hk]


/-- $\\mathrm{beta}(d, 0, d) = (d, d) = \\Delta(d)$。 -/
lemma Dn.beta_mk02 (R) [CommRing R] (d : D R) :
    Dn.beta R (Dn.mk02 R d) = Dn.diag R d := by
  apply Subtype.ext
  funext k
  by_cases hk : k = 0
  <;> simp [Dn.beta, Dn.mk02, Dn.diag, hk]

/-- $n$ 个 $D$ 的笛卡尔积 $D^n = D \times \cdots \times D$：每个分量都属于 $D$，
即每个分量平方为零。
$$D^n = \{ x : \text{Fin } n \to R \mid \forall i,\ (x_i)^2 = 0 \}$$
作为 $\text{Fin } n \to R$ 在数乘下封闭的子集（标量逐点作用）。 -/
def Dpow (R) [CommRing R] (n : ℕ) : SubMulAction R (Fin n → R) where
  carrier := { x | ∀ i : Fin n, x i * x i = 0 }
  smul_mem' := by
    intro c x hx i
    have h : x i * x i = 0 := hx i
    change (c * x i) * (c * x i) = 0
    calc
      (c * x i) * (c * x i) = c * (c * (x i * x i)) := by ring
      _ = 0 := by simp [h]


/-- 零元属于 $D^n$：全零元组的每个分量平方为零，故 $D^n$ 带有零元。 -/
instance instZeroDpow R [CommRing R] (n : ℕ) : Zero (Dpow R n) where
  zero := ⟨fun _ : Fin n ↦ 0, by
    intro i
    simp
  ⟩


/-- $D^n$ 中的零元在 $R^n$ 中的像就是零元组。 -/
@[simp]
theorem zero_coeDpow {R} [CommRing R] {n : ℕ} :
    ((0 : Dpow R n) : Fin n → R) = fun _ ↦ 0 := rfl


/-- $D(n) \subseteq D^n$：两两乘积为零蕴含每个分量平方为零。

**证明**：设 $x \in D(n)$。对任意 $i$，在 $x \in D(n)$ 的条件中取 $i = j$，
即得 $x_i \cdot x_i = 0$，这正是 $x_i \in D$ 的定义。

这里用 carrier 上的集合包含表示子对象的包含（`SubMulAction` 本身没有 `⊆` 实例）。 -/
theorem Dn_subset_Dpow {R} [CommRing R] (n : ℕ) :
    (Dn R n : Set _) ⊆ (Dpow R n : Set (Fin n → R)) := by
  intro x hx i
  exact Dn.mul_eq_zero R ⟨x, hx⟩ i i


/-! ### $D_k(n)$ 与 $D$、$D(n)$ 的联系

`Dn`（即 $D(n)$）定义为 $D_k(n)$ 的 $k = 1$ 特例（定义性相等，见前）；这里记录
一阶、一维情形的对应关系。基础定义见前文「高阶无穷小邻域 $D_k(n)$（基础定义）」。
-/

/-- 一阶情形回到 $D(n)$：$D_1(n) = D(n)$（定义性相等，因 `Dn` 定义为 `Dkn R 1 n`）。 -/
theorem Dkn_one (R) [CommRing R] (n : ℕ) : Dkn R 1 n = Dn R n := by
  rfl


/-- 一维情形：$D_k \cong D_k(1)$（由 $D_k(n)$ 取 $n = 1$ 给出，即「利用 $D_k(n)$ 定义 $D_k$」的对应证明）。 -/
def Dk_equiv_Dkn1 (R) [CommRing R] (k : ℕ) : Dk R k ≃ Dkn R k 1 where
  toFun := fun x ↦ ⟨fun _ : Fin 1 ↦ (x : R), by
    intro ι
    change finProd R (k+1) (fun _ : Fin (k+1) ↦ (x : R)) = 0
    rw [finProd_const]
    exact x.2
  ⟩
  invFun := fun u ↦ ⟨u.1 0, by
    change (u.1 0) ^ (k + 1) = 0
    rw [← finProd_const R k (u.1 0)]
    exact u.2 (fun _ : Fin (k+1) ↦ (0 : Fin 1))
  ⟩
  left_inv := by
    intro x
    rfl
  right_inv := by
    intro u
    apply Subtype.ext
    funext i
    have hi : i = (0 : Fin 1) := by
      ext
      omega
    subst i
    rfl


/-- 一维一阶情形：$D = D_1 \cong D_1(1)$（`Dk_equiv_Dkn1` 的 $k = 1$ 特例）。 -/
def D_equiv_Dkn11 (R) [CommRing R] : D R ≃ Dkn R 1 1 := Dk_equiv_Dkn1 R 1


/-! ## 「存在且唯一」的编码 -/

/-- 「存在且唯一」的编码：元素 $x$ 连同「$p(x)$ 成立」以及
「任何满足 $p$ 的 $y$ 都等于 $x$」这两条证明。
此编码同时被 Kock-Lawvere 公理与微线性对象使用。 -/
abbrev ExistsUnique' (p : α → Prop) := { x // p x ∧ ∀ y, p y → y = x }
