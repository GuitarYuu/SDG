import SDG.NoChoice
import Mathlib

/-!
# SDG.FinSumProd

无选择公理的 $\mathrm{Fin}\ n$ 求和与乘积工具（被整个项目复用）。

Mathlib 的 `Finset.sum` / `Finset.prod` 在 $\mathrm{Fin}\ n$ 上（经
`Finset.univ` / `Fin.fintype`）依赖 `Classical.choice`；本模块改用
`List.ofFn` + `List.sum` / `List.prod`（纯递归）提供等价的求和 `finSum` 与
乘积 `finProd`，**全程无选择公理**。

主要内容：
* `Fin` 小维度索引辅助（`Fin 2`、`Fin 3` 上的穷举引理）；
* 求和 `finSum` 及其基本性质（`finSum_zero`、`finSum_succ`、`finSum_add`、
  `finSum_eq_single`、`map_finSum`、`finSum_apply` 等）；
* 乘积 `finProd` 及其基本性质（`finProd_one`、`finProd_succ`、`finProd_mul`、
  `finProd_eq_single`、`map_finProd`、`finProd_apply` 等）。

本模块被 `SDG.Infinitesimal` 等模块引用并再导出；可用 `#assert_no_choice`
复核所列声明均不依赖选择公理。
-/

/-! ## Fin 索引辅助 -/

/-- 在 `Fin 2` 中，不等于 0 的元素必为 1。 -/
lemma fin_two_eq_one_of_ne_zero {i : Fin 2} (h : i ≠ 0) : i = 1 := by
  ext
  have hi0 : i.1 ≠ 0 := by
    intro hz
    apply h
    ext
    exact hz
  omega

/-- 在 `Fin 3` 中，不等于 0 且不等于 1 的元素必为 2。 -/
lemma fin_three_eq_two_of_ne_zero_ne_one {i : Fin 3} (h0 : i ≠ 0) (h1 : i ≠ 1) : i = 2 := by
  ext
  have hz0 : i.1 ≠ 0 := by intro hz; apply h0; ext; exact hz
  have hz1 : i.1 ≠ 1 := by intro hz; apply h1; ext; exact hz
  omega

/-! ### 无选择公理的 `Fin n` 求和 -/

/-- 不依赖选择公理的 `Fin n` 求和：把 `f` 的取值展成列表后累加。

Mathlib 的 `Finset.sum` 在 $\mathrm{Fin}\ n$ 上（经 `Finset.univ`/`Fin.fintype`）
依赖 `Classical.choice`；而 `finSum` 经 `List.ofFn` + `List.sum`（纯递归）构造，
**全程无选择公理**（本模块 linter 已自动通过，可用 `#assert_no_choice` 复核）。
凡只需「对 $\mathrm{Fin}\ n$ 求和」之处都可用它替换 `∑ i : Fin n, f i` 以保持无选择公理；
它与标准求和一致（`finSum_eq_sum`）。 -/
def finSum (R : Type u) [AddCommMonoid R] (n : ℕ) (f : Fin n → R) : R :=
  (List.ofFn f).sum

/-- 空求和：$\mathrm{finSum}\ 0\ f = 0$。 -/
@[simp] lemma finSum_zero (R : Type u) [AddCommMonoid R] (f : Fin 0 → R) :
    finSum R 0 f = 0 := by
  rfl

/-- 递推（分离首元素 $f_0$）：
$\mathrm{finSum}\ (n+1)\ f = f_0 + \mathrm{finSum}\ n\ (i \mapsto f_{i+1})$。 -/
lemma finSum_succ (R : Type u) [AddCommMonoid R] (n : ℕ) (f : Fin (n+1) → R) :
    finSum R (n+1) f = f 0 + finSum R n (fun i : Fin n ↦ f i.succ) := by
  dsimp [finSum]
  rw [List.ofFn_succ, List.sum_cons]

/-- 各项为零则和为零。 -/
lemma finSum_eq_zero (R : Type u) [AddCommMonoid R] {n : ℕ} {f : Fin n → R}
    (h : ∀ i, f i = 0) : finSum R n f = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [finSum_succ]
      rw [h 0, ih (fun i ↦ h i.succ)]
      simp

/-- 和关于逐点加法可分配（加法保形）。 -/
lemma finSum_add (R : Type u) [AddCommMonoid R] (n : ℕ) (f g : Fin n → R) :
    finSum R n (fun i ↦ f i + g i) = finSum R n f + finSum R n g := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [finSum_succ, finSum_succ, finSum_succ]
      rw [ih]
      abel

/-- 和关于数乘（左乘）可提出。 -/
lemma finSum_mul_left (R : Type u) [Semiring R] (n : ℕ) (a : R) (f : Fin n → R) :
    finSum R n (fun i ↦ a * f i) = a * finSum R n f := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [finSum_succ, finSum_succ]
      rw [ih]
      rw [mul_add]

/-- 和关于数乘（右乘）可提出。 -/
lemma finSum_mul_right (R : Type u) [Semiring R] (n : ℕ) (f : Fin n → R) (a : R) :
    finSum R n (fun i ↦ f i * a) = finSum R n f * a := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [finSum_succ, finSum_succ]
      rw [ih]
      rw [add_mul]

/-- 单点求和：只有第 $k$ 项非零（为 $a$），其余为零。 -/
lemma finSum_eq_single (R : Type u) [AddCommMonoid R] {n : ℕ} (k : Fin n) (a : R) :
    finSum R n (fun i : Fin n ↦ if i = k then a else 0) = a := by
  revert a
  induction n with
  | zero =>
      exact Fin.elim0 k
  | succ n ih =>
      intro a
      by_cases hk0 : k = 0
      · subst k
        rw [finSum_succ]
        have hz : ∀ i : Fin n, (if i.succ = 0 then a else 0) = 0 := by
          intro i
          have h : i.succ ≠ 0 := Fin.succ_ne_zero i
          simp [h]
        rw [finSum_eq_zero R hz]
        simp
      · -- k ≠ 0，取 j : Fin n 使 k = j.succ
        have hkpos : 0 < k.1 := by
          have hz : k.1 ≠ 0 := by
            intro h
            apply hk0
            ext
            exact h
          omega
        let j : Fin n := ⟨k.1 - 1, by
          have hklt : k.1 < n + 1 := k.2
          omega⟩
        have hks : k = j.succ := by
          ext
          dsimp [j, Fin.succ]
          omega
        rw [hks]
        rw [finSum_succ]
        have h0 : (if 0 = j.succ then a else 0) = 0 := by
          have h : 0 ≠ j.succ := fun h' => Fin.succ_ne_zero j h'.symm
          simp [h]
        rw [h0]
        have hij : ∀ i : Fin n, (if i.succ = j.succ then a else 0) = (if i = j then a else 0) := by
          intro i
          by_cases h : i = j
          · simp [h]
          · have h' : i.succ ≠ j.succ := by
              intro hs
              apply h
              exact Fin.succ_inj.mp hs
            simp [h, h']
        rw [show finSum R n (fun i : Fin n ↦ if i.succ = j.succ then a else 0) =
            finSum R n (fun i : Fin n ↦ if i = j then a else 0) by
          exact congrArg (fun φ : Fin n → R ↦ finSum R n φ) (funext hij)]
        simpa using ih j a

/-- 加法同态穿过求和：$g\,(\mathrm{finSum}\ f) = \mathrm{finSum}\ (g \circ f)$。 -/
lemma map_finSum (A B : Type u) [AddCommMonoid A] [AddCommMonoid B]
    (g : A →+ B) (n : ℕ) (f : Fin n → A) :
    g (finSum A n f) = finSum B n (fun i ↦ g (f i)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [finSum_succ, finSum_succ]
      rw [map_add, ih]

/-- 函数之和在点 $j$ 处的值等于逐点求和：
$(\mathrm{finSum}\ h)\, j = \mathrm{finSum}\ (i \mapsto h\,i\,j)$。 -/
lemma finSum_apply (R : Type u) [AddCommMonoid R] (n : ℕ) {m : ℕ}
    (h : Fin n → Fin m → R) (j : Fin m) :
    (finSum (Fin m → R) n h) j = finSum R n (fun i ↦ h i j) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [finSum_succ, finSum_succ]
      rw [Pi.add_apply, ih]


/-! ### 无选择公理的 `Fin n` 乘积 -/

/-- 不依赖选择公理的 `Fin n` 乘积：把 `f` 的取值展成列表后累乘。

Mathlib 的 `Finset.prod` 在 $\mathrm{Fin}\ n$ 上（经 `Finset.univ`/`Fin.fintype`）
依赖 `Classical.choice`；而 `finProd` 经 `List.ofFn` + `List.prod`（纯递归）构造，
**全程无选择公理**（本模块 linter 已自动通过，可用 `#assert_no_choice` 复核）。
凡只需「对 $\mathrm{Fin}\ n$ 求积」之处都可用它替换 `∏ i : Fin n, f i` 以保持无选择公理。 -/
def finProd (R : Type u) [CommMonoid R] (n : ℕ) (f : Fin n → R) : R :=
  (List.ofFn f).prod

/-- 空乘积：$\mathrm{finProd}\ 0\ f = 1$。 -/
@[simp] lemma finProd_one (R : Type u) [CommMonoid R] (f : Fin 0 → R) :
    finProd R 0 f = 1 := by
  rfl

/-- 递推（分离首元素 $f_0$）：
$\mathrm{finProd}\ (n+1)\ f = f_0 \cdot \mathrm{finProd}\ n\ (i \mapsto f_{i+1})$。 -/
lemma finProd_succ (R : Type u) [CommMonoid R] (n : ℕ) (f : Fin (n+1) → R) :
    finProd R (n+1) f = f 0 * finProd R n (fun i : Fin n ↦ f i.succ) := by
  dsimp [finProd]
  rw [List.ofFn_succ, List.prod_cons]

/-- 各项为一则乘积为一。 -/
lemma finProd_eq_one (R : Type u) [CommMonoid R] {n : ℕ} {f : Fin n → R}
    (h : ∀ i, f i = 1) : finProd R n f = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [finProd_succ]
      rw [h 0, ih (fun i ↦ h i.succ)]
      simp

/-- 乘积关于逐点乘法可分配（乘性保形）。 -/
lemma finProd_mul (R : Type u) [CommMonoid R] (n : ℕ) (f g : Fin n → R) :
    finProd R n (fun i ↦ f i * g i) = finProd R n f * finProd R n g := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [finProd_succ, finProd_succ, finProd_succ]
      rw [ih]
      ac_rfl

/-- 单点乘积：只有第 $k$ 项非一（为 $a$），其余为一。 -/
lemma finProd_eq_single (R : Type u) [CommMonoid R] {n : ℕ} (k : Fin n) (a : R) :
    finProd R n (fun i : Fin n ↦ if i = k then a else 1) = a := by
  revert a
  induction n with
  | zero =>
      exact Fin.elim0 k
  | succ n ih =>
      intro a
      by_cases hk0 : k = 0
      · subst k
        rw [finProd_succ]
        have hz : ∀ i : Fin n, (if i.succ = 0 then a else 1) = 1 := by
          intro i
          have h : i.succ ≠ 0 := Fin.succ_ne_zero i
          simp [h]
        rw [finProd_eq_one R hz]
        simp
      · -- k ≠ 0，取 j : Fin n 使 k = j.succ
        have hkpos : 0 < k.1 := by
          have hz : k.1 ≠ 0 := by
            intro h
            apply hk0
            ext
            exact h
          omega
        let j : Fin n := ⟨k.1 - 1, by
          have hklt : k.1 < n + 1 := k.2
          omega⟩
        have hks : k = j.succ := by
          ext
          dsimp [j, Fin.succ]
          omega
        rw [hks]
        rw [finProd_succ]
        have h0 : (if 0 = j.succ then a else 1) = 1 := by
          have h : 0 ≠ j.succ := fun h' => Fin.succ_ne_zero j h'.symm
          simp [h]
        rw [h0]
        have hij : ∀ i : Fin n, (if i.succ = j.succ then a else 1) = (if i = j then a else 1) := by
          intro i
          by_cases h : i = j
          · simp [h]
          · have h' : i.succ ≠ j.succ := by
              intro hs
              apply h
              exact Fin.succ_inj.mp hs
            simp [h, h']
        rw [show finProd R n (fun i : Fin n ↦ if i.succ = j.succ then a else 1) =
            finProd R n (fun i : Fin n ↦ if i = j then a else 1) by
          exact congrArg (fun φ : Fin n → R ↦ finProd R n φ) (funext hij)]
        simpa using ih j a

/-- 乘法同态穿过乘积：$g\,(\mathrm{finProd}\ f) = \mathrm{finProd}\ (g \circ f)$。 -/
lemma map_finProd (A B : Type u) [CommMonoid A] [CommMonoid B]
    (g : A →* B) (n : ℕ) (f : Fin n → A) :
    g (finProd A n f) = finProd B n (fun i ↦ g (f i)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [finProd_succ, finProd_succ]
      rw [map_mul, ih]

/-- 函数之积在点 $j$ 处的值等于逐点乘积：
$(\mathrm{finProd}\ h)\, j = \mathrm{finProd}\ (i \mapsto h\,i\,j)$。 -/
lemma finProd_apply (R : Type u) [CommMonoid R] (n : ℕ) {m : ℕ}
    (h : Fin n → Fin m → R) (j : Fin m) :
    (finProd (Fin m → R) n h) j = finProd R n (fun i ↦ h i j) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [finProd_succ, finProd_succ]
      rw [Pi.mul_apply, ih]

/-- 常值乘积等于幂：$\mathrm{finProd}\ (k+1)\ (\lambda \_,\ x) = x^{k+1}$。 -/
lemma finProd_const (R : Type u) [CommMonoid R] (k : ℕ) (x : R) :
    finProd R (k+1) (fun _ : Fin (k+1) ↦ x) = x ^ (k+1) := by
  induction k with
  | zero =>
      rw [finProd_succ, finProd_one]
      change x * (1 : R) = x ^ 1
      rw [pow_one, mul_one]
  | succ k ih =>
      change finProd R (k + 1 + 1) (fun _ : Fin (k + 1 + 1) ↦ x) = x ^ (k + 1 + 1)
      rw [finProd_succ]
      change x * finProd R (k + 1) (fun _ : Fin (k + 1) ↦ x) = x ^ (k + 1 + 1)
      rw [ih]
      rw [pow_succ x (k + 1)]
      rw [mul_comm]

/-- 二元乘积：$\mathrm{finProd}\ 2\ f = f_0 \cdot f_1$。 -/
lemma finProd_two (R : Type u) [CommMonoid R] (f : Fin 2 → R) :
    finProd R 2 f = f 0 * f 1 := by
  rw [finProd_succ, finProd_succ, finProd_one]
  simp

/-- 常值零的乘积为零：$k+1$ 个零相乘为 $0$（空积为 $1$，故仅对非空指标成立）。 -/
lemma finProd_zero_succ (R : Type u) [CommMonoidWithZero R] (k : ℕ) :
    finProd R (k+1) (fun _ : Fin (k+1) ↦ (0 : R)) = 0 := by
  induction k with
  | zero =>
      rw [finProd_succ, finProd_one]
      change (0 : R) * (1 : R) = 0
      exact zero_mul (1 : R)
  | succ k ih =>
      rw [finProd_succ]
      change (0 : R) * finProd R (k+1) (fun i : Fin (k+1) ↦ (0 : R)) = 0
      rw [ih]
      exact zero_mul (0 : R)
