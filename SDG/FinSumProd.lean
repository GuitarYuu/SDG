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

/-- `finSum` 在任意位置拆出单项。 -/
lemma finSum_split_at (R : Type u) [AddCommMonoid R] {n : ℕ} (f : Fin n → R) (i : Fin n) :
    finSum R n f = f i + finSum R n (Function.update f i 0) := by
  induction n with
  | zero => exact absurd i.isLt (by simp)
  | succ m ih =>
      by_cases hi : i = 0
      · subst hi
        rw [finSum_succ]
        congr 1
        rw [finSum_succ]
        simp
      · have hin : (i : ℕ) ≠ 0 := fun hh => hi (Fin.ext hh)
        obtain ⟨i', rfl⟩ : ∃ k : Fin m, i = k.succ :=
            ⟨⟨(i : ℕ) - 1, by have h1 := i.isLt; omega⟩,
              Fin.ext (by show (i : ℕ) = (i : ℕ) - 1 + 1; have h1 := i.isLt; omega)⟩
        rw [finSum_succ, finSum_succ]
        have h0 : (Function.update f (i'.succ) 0) (0 : Fin (m + 1)) = f 0 := by
          rw [Function.update_of_ne (Fin.succ_ne_zero i').symm]
        rw [h0]
        have htail : ∀ a : Fin m, Function.update f (i'.succ) 0 a.succ
            = Function.update (fun a : Fin m ↦ f a.succ) i' 0 a := by
          intro a
          simp only [Function.update_apply]
          by_cases hk : a = i'
          · subst hk; simp
          · rw [if_neg (fun hh => hk (Fin.succ_injective m hh)), if_neg hk]
        rw [ih (fun a : Fin m ↦ f a.succ) i']
        simp only [htail]
        abel

/-- 和的负号可以逐项提出。 -/
lemma finSum_neg (R : Type u) [AddCommGroup R] {n : ℕ} (f : Fin n → R) :
    finSum R n (fun i ↦ -f i) = -finSum R n f := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [finSum_succ, finSum_succ, ih]
      abel

/-- 逐项相等则和相等。 -/
lemma finSum_congr (R : Type u) [AddCommMonoid R] {n : ℕ} {f g : Fin n → R}
    (h : ∀ i, f i = g i) : finSum R n f = finSum R n g := by
  induction n with
  | zero => rfl
  | succ m ih =>
      rw [finSum_succ, finSum_succ]
      rw [h (0 : Fin (m + 1)), ih (fun i ↦ h i.succ)]

/-! ### 区间拆分与三角求和（∂² = 0 的组合基础设施） -/

/-- 求和的指标集平移（subst 基础，无动机问题）。 -/
lemma finSum_index_congr (R : Type u) [AddCommMonoid R] {m n : ℕ} (he : m = n)
    (f : Fin m → R) :
    finSum R m f = finSum R n (fun i => f (Fin.cast he.symm i)) := by
  subst he
  rfl

/-- 区间拆分：`Fin (d+k)` 上的求和按位置 `k` 拆成前 `k` 项与后 `d` 项。 -/
lemma finSum_front (R : Type u) [AddCommMonoid R] : ∀ (k d : ℕ) (h : Fin (d + k) → R),
    finSum R (d + k) h
      = finSum R k (fun i => h ⟨(i : ℕ), by have := i.isLt; omega⟩)
        + finSum R d (fun i => h ⟨k + (i : ℕ), by have := i.isLt; omega⟩) := by
  intro k
  induction k with
  | zero =>
      intro d h
      show finSum R d h = finSum R 0 (fun i => h ⟨(i : ℕ), by have := i.isLt; omega⟩)
        + finSum R d (fun i => h ⟨(0 : ℕ) + (i : ℕ), by have := i.isLt; omega⟩)
      rw [finSum_zero, zero_add]
      refine finSum_congr R (f := h)
        (g := fun i => h ⟨(0 : ℕ) + (i : ℕ), by have := i.isLt; omega⟩)
        (fun i => congrArg h (Fin.ext (by show (i : ℕ) = (0 : ℕ) + (i : ℕ); omega)))
  | succ k ih =>
      intro d h
      show finSum R (d + k + 1) h = finSum R (k + 1) (fun i => h ⟨(i : ℕ), by have := i.isLt; omega⟩)
        + finSum R d (fun i => h ⟨k + 1 + (i : ℕ), by have := i.isLt; omega⟩)
      rw [finSum_succ (R := R) (n := d + k) (f := h)]
      rw [ih d (fun i => h i.succ)]
      rw [finSum_succ (R := R) (n := k) (f := fun i => h ⟨(i : ℕ), by have := i.isLt; omega⟩)]
      have e0 : (h (0 : Fin (d + k + 1)) : R) = h ⟨(0 : ℕ), by omega⟩ := rfl
      rw [e0, add_assoc]
      congr 1
      · congr 1
        · exact finSum_congr R (fun i => congrArg h (Fin.ext (by
            have := i.isLt
            simp only [Fin.val_succ, Fin.val_mk]
            omega)))

/-- 下三角嵌入：带指标条件的项求和恰为前 `k` 项和。 -/
lemma finSum_tri_lower (R : Type u) [AddCommMonoid R] {m k : ℕ} (hkm : k ≤ m)
    (g : Fin m → R) :
    finSum R m (fun p => if (p : ℕ) < k then g ⟨(p : ℕ), by have := p.isLt; omega⟩ else 0)
      = finSum R k (fun p => g ⟨(p : ℕ), by have := p.isLt; have := hkm; omega⟩) := by
    obtain ⟨d, rfl⟩ : ∃ d, m = d + k := ⟨m - k, by omega⟩
    rw [finSum_front R k d (fun p => if (p : ℕ) < k then g ⟨(p : ℕ), by have := p.isLt; omega⟩ else 0)]
    simp only [Fin.val_mk]
    rw [finSum_congr R (fun i => if_pos (by have := i.isLt; omega))]
    rw [finSum_eq_zero R (fun i => if_neg (by have := i.isLt; omega))]
    abel

/-- 上三角提取：`Fin (d + (k+1))` 上按 `k < i` 截取的项和恰为位移和。 -/
lemma finSum_tri_upper (R : Type u) [AddCommMonoid R] {k d : ℕ}
    (h : Fin (d + (k + 1)) → R) :
    finSum R (d + (k + 1)) (fun i => if k < (i : ℕ) then h i else 0)
      = finSum R d (fun s => h ⟨k + 1 + (s : ℕ), by have := s.isLt; omega⟩) := by
    rw [finSum_front R (k + 1) d (fun i => if k < (i : ℕ) then h i else 0)]
    simp only [Fin.val_mk]
    rw [finSum_eq_zero R (fun i => if_neg (by have := i.isLt; omega)), zero_add]
    rw [finSum_congr R (fun s => if_pos (by have := s.isLt; omega))]

/-- 二重求和换序。 -/
lemma finSum_sum_comm (R : Type u) [AddCommMonoid R] : ∀ (m n : ℕ) (f : Fin m → Fin n → R),
    finSum R m (fun i => finSum R n (f i))
      = finSum R n (fun j => finSum R m (fun i => f i j)) := by
  intro m
  induction m with
  | zero =>
      intro n f
      rw [finSum_zero, finSum_eq_zero R (fun j => finSum_zero R (fun i => f i j))]
  | succ m ih =>
      intro n f
      rw [finSum_succ, ih n (fun i => f i.succ), ← finSum_add]
      rw [finSum_congr R (fun j => finSum_succ R m (fun i => f i j))]

/-- 末项提取：`Fin (m+1)` 上的和 = 前 `m` 项（经 `castSucc`）+ 末项。 -/
lemma finSum_last (R : Type u) [AddCommMonoid R] : ∀ (m : ℕ) (h : Fin (m + 1) → R),
    finSum R (m + 1) h = finSum R m (fun i => h i.castSucc) + h (Fin.last m) := by
  intro m
  induction m with
  | zero =>
      intro h
      show h (0 : Fin 1) + finSum R 0 (fun i : Fin 0 => h i.succ)
        = finSum R 0 (fun i : Fin 0 => h i.castSucc) + h (Fin.last 0)
      rw [finSum_zero, finSum_zero]
      show h (0 : Fin 1) + 0 = 0 + h (0 : Fin 1)
      rw [add_zero, zero_add]
  | succ m ih =>
      intro h
      rw [finSum_succ (R := R) (n := m + 1) (f := h)]
      rw [ih (fun i : Fin (m + 1) => h i.succ)]
      rw [finSum_succ (R := R) (n := m) (f := fun i : Fin (m + 1) => h i.castSucc)]
      rw [finSum_congr R (f := fun i : Fin m => h (Fin.castSucc i).succ)
        (g := fun i : Fin m => h (Fin.castSucc i.succ)) (fun i => rfl)]
      rw [add_assoc (a := h (Fin.castSucc (0 : Fin (m + 1))))
        (b := finSum R m (fun i : Fin m => h (Fin.castSucc i.succ)))
        (c := h (Fin.last (m + 1)))]
      congr 1
      all_goals rfl

/-- **矩形和 = 三角和**（一般 n 的 ∂² = 0 的组合核心）：

`(W+1) × W` 矩形上的双和，等于按下三角 `(i, j)`, `j < i ≤ W` 逐点配对
`t i j + t j (i-1)` 的和。对任意全函数 `t : ℕ → ℕ → R` 成立：矩形 =
下三角 ∪ 闭上三角，上三角经 `(a, b) ↦ (b+1, a)` 转置后与下三角同形。 -/
lemma finSum_rect_eq_tri (R : Type u) [AddCommMonoid R] : ∀ (W : ℕ) (t : ℕ → ℕ → R),
    finSum R (W + 1) (fun i : Fin (W + 1) => finSum R W (fun j : Fin W => t (i : ℕ) (j : ℕ)))
      = finSum R (W + 1) (fun i : Fin (W + 1) => finSum R ((i : ℕ)) (fun j : Fin ((i : ℕ)) =>
          t (i : ℕ) (j : ℕ) + t (j : ℕ) ((i : ℕ) - 1))) := by
  intro W
  induction W with
  | zero =>
      intro t
      rw [finSum_succ (R := R) (n := 0)
        (f := fun i : Fin 1 => finSum R 0 (fun j : Fin 0 => t (i : ℕ) (j : ℕ)))]
      rw [finSum_succ (R := R) (n := 0) (f := fun i : Fin 1 => finSum R ((i : ℕ))
        (fun j : Fin ((i : ℕ)) => t (i : ℕ) (j : ℕ) + t (j : ℕ) ((i : ℕ) - 1)))]
      have h0 : (((0 : Fin 1) : Fin 1) : ℕ) = 0 := rfl
      rw [h0]
      simp only [finSum_zero]
  | succ W ih =>
      intro t
      -- 左侧：拆末行，再把每行的内和拆出末列
      rw [finSum_last (R := R) (m := W + 1)
        (h := fun i : Fin (W + 2) => finSum R (W + 1) (fun j : Fin (W + 1) => t (i : ℕ) (j : ℕ)))]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [finSum_congr R (f := fun i : Fin (W + 1) => finSum R (W + 1) (fun j : Fin (W + 1) => t (i : ℕ) (j : ℕ)))
        (g := fun i : Fin (W + 1) => finSum R W (fun j : Fin W => t (i : ℕ) (j : ℕ)) + t (i : ℕ) W)
        (fun i => by
          rw [finSum_last (R := R) (m := W) (h := fun j : Fin (W + 1) => t (i : ℕ) (j : ℕ))]
          simp only [Fin.val_castSucc, Fin.val_last])]
      rw [finSum_add (R := R) (n := W + 1)
        (f := fun i : Fin (W + 1) => finSum R W (fun j : Fin W => t (i : ℕ) (j : ℕ)))
        (g := fun i : Fin (W + 1) => t (i : ℕ) W)]
      -- 右侧：拆末行，末行两项和拆开
      rw [finSum_last (R := R) (m := W + 1)
        (h := fun i : Fin (W + 2) => finSum R ((i : ℕ)) (fun j : Fin ((i : ℕ)) =>
          t (i : ℕ) (j : ℕ) + t (j : ℕ) ((i : ℕ) - 1)))]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [show ((W : ℕ) + 1) - 1 = W from by omega]
      rw [finSum_add (R := R) (n := W + 1)
        (f := fun j : Fin (W + 1) => t (W + 1) (j : ℕ))
        (g := fun j : Fin (W + 1) => t (j : ℕ) W)]
      rw [ih t]
      abel

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
