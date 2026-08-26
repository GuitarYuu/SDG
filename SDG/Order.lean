import SDG.NoChoice
import SDG.Infinitesimal

/-!
# SDG.Order

序结构（非严格序 `≤`，预序）。

在综合微分几何中，光滑直线 $R$ 上的序结构以**非严格序** `≤` 为主，且是一个
**预序**（`Preorder`：自反、传递，但**不必反对称**）。$R$ 是带预序的有序交换环
（加法单调、非负元素相乘非负、$0 \le 1$），并满足 SDG 特有的**无穷小量公理**：

$$d \in D_k \quad\Longrightarrow\quad 0 \le d \ \land\ d \le 0 ,$$

即每个无穷小量都被 $0$ 从两侧夹住。由于序是**预序而非偏序**（没有反对称律
`le_antisymm`），$0 \le d \le 0$ 并不强迫 $d = 0$，这与 $D_k$ 含非零元相容。
同时它推出「无穷小量不严格为正、不严格为负」：$\neg(0 < d)$ 且 $\neg(d < 0)$。
严格 `<` 只是 `Preorder` 按 $a < b :\equiv a \le b \land \neg(b \le a)$ 派生的
记号，不作为公理基础。
-/

namespace SDG.Order

/-! ## 序公理 -/

/-- **SDG 序公理**：$R$ 是带**预序**（非严格序 `≤`，不必反对称）的有序交换环，
并且每个无穷小量都被 $0$ 夹住：$d \in D_k \implies 0 \le d \land d \le 0$。

序与环相容的公理：
* `add_le_add_left`：加法单调（左平移保序）：$a \le b \implies a + c \le b + c$；
* `mul_nonneg`：非负元素之积非负：$0 \le a \land 0 \le b \implies 0 \le a \cdot b$；
* `zero_le_one`：$0 \le 1$；
* `infinitesimal_le`：$d \in D_k \implies 0 \le d \land d \le 0$（无穷小量公理）。

「非严格序」：`≤` 是主关系（来自 `Preorder`），`<` 只是派生记号，不作为公理
基础。 -/
class IsSDGOrder (R : Type u) extends CommRing R, Preorder R where
  add_le_add_left : ∀ {a b : R}, a ≤ b → ∀ c : R, a + c ≤ b + c
  mul_nonneg : ∀ {a b : R}, 0 ≤ a → 0 ≤ b → 0 ≤ a * b
  zero_le_one : (0 : R) ≤ 1
  infinitesimal_le : ∀ (k : ℕ), ∀ d : Dk R k, 0 ≤ (d : R) ∧ (d : R) ≤ 0

/-! ## 序的基本性质 -/

/-- 加法单调（右平移）：$a \le b \implies c + a \le c + b$。 -/
theorem add_le_add_right {R} [IsSDGOrder R] {a b : R} (h : a ≤ b) (c : R) :
    c + a ≤ c + b := by
  rw [add_comm c a, add_comm c b]
  exact IsSDGOrder.add_le_add_left h c

/-- 非负元素之和非负：$0 \le a \land 0 \le b \implies 0 \le a + b$。 -/
theorem add_nonneg {R} [IsSDGOrder R] {a b : R} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ a + b := by
  calc
    0 ≤ b := hb
    _ ≤ a + b := by
      have h1 := IsSDGOrder.add_le_add_left ha b
      simpa using h1

/-- 非负数的平方非负：$0 \le a \implies 0 \le a^2$。 -/
theorem sq_nonneg {R} [IsSDGOrder R] {a : R} (ha : 0 ≤ a) :
    0 ≤ a ^ 2 := by
  rw [pow_two]
  exact IsSDGOrder.mul_nonneg ha ha

/-- $0 \le 1$（序公理，`IsSDGOrder.zero_le_one` 的便捷别名）。 -/
theorem zero_le_one {R} [IsSDGOrder R] : (0 : R) ≤ 1 := IsSDGOrder.zero_le_one

/-! ## 无穷小量公理的推论 -/

/-- 无穷小量被 $0$ 夹住（$D = D_1$ 情形）：
$d \in D \implies 0 \le d \land d \le 0$。 -/
theorem inf_le {R} [IsSDGOrder R] (d : D R) :
    0 ≤ (d : R) ∧ (d : R) ≤ 0 :=
  IsSDGOrder.infinitesimal_le 1 d

/-- 无穷小量非负：$d \in D \implies 0 \le d$。 -/
theorem inf_nonneg {R} [IsSDGOrder R] (d : D R) :
    0 ≤ (d : R) := (inf_le d).1

/-- 无穷小量非正：$d \in D \implies d \le 0$。 -/
theorem inf_nonpos {R} [IsSDGOrder R] (d : D R) :
    (d : R) ≤ 0 := (inf_le d).2

/-- 无穷小量不严格为正：$d \in D \implies \neg(0 < d)$。
由 `infinitesimal_le`（$d \le 0$）与 `Preorder` 的 `lt_iff_le_not_ge` 推出。 -/
theorem no_strict_pos_infinitesimal {R} [IsSDGOrder R] (d : D R) :
    ¬ (0 : R) < (d : R) := by
  intro h
  exact (lt_iff_le_not_ge.mp h).2 (inf_le d).2

/-- 无穷小量不严格为负：$d \in D \implies \neg(d < 0)$。
由 `infinitesimal_le`（$0 \le d$）与 `Preorder` 的 `lt_iff_le_not_ge` 推出。 -/
theorem no_strict_neg_infinitesimal {R} [IsSDGOrder R] (d : D R) :
    ¬ (d : R) < (0 : R) := by
  intro h
  exact (lt_iff_le_not_ge.mp h).2 (inf_le d).1

/-! ## 单位区间 $I = [0,1]$ -/

/-- 单位区间 $I = [0,1] = \{ x : R \mid 0 \le x \land x \le 1 \}$（序结构由非严格
序 `≤` 定义）。 -/
abbrev UnitInterval (R : Type u) [IsSDGOrder R] : Set R :=
  Set.Icc 0 1

namespace UnitInterval

/-- 区间零点 $0 \in I$（$0 \le 0$ 且 $0 \le 1$）。 -/
instance instZero (R : Type u) [IsSDGOrder R] : Zero (UnitInterval R) where
  zero := ⟨0, by exact ⟨le_rfl, IsSDGOrder.zero_le_one⟩⟩

/-- 区间零点的像为零：$((0 : I) : R) = 0$。 -/
@[simp]
theorem zero_coeUnitInterval {R : Type u} [IsSDGOrder R] :
    ((0 : UnitInterval R) : R) = 0 := rfl

/-- 区间单位元 $1 \in I$（$0 \le 1$ 且 $1 \le 1$）。 -/
instance instOne (R : Type u) [IsSDGOrder R] : One (UnitInterval R) where
  one := ⟨1, by exact ⟨IsSDGOrder.zero_le_one, le_rfl⟩⟩

/-- 区间单位元的像为一：$((1 : I) : R) = 1$。 -/
@[simp]
theorem one_coeUnitInterval {R : Type u} [IsSDGOrder R] :
    ((1 : UnitInterval R) : R) = 1 := rfl

/-- 区间点在无穷小方向扰动后仍在区间内：$x \in I,\ d \in D \implies x + d \in I$。
由无穷小量被 $0$ 夹住（$0 \le d \le 0$）与序的单调性推出。这是区间上导数
`SDG.Integration.sderiv_I` 良定的关键。 -/
def add_d (R : Type u) [IsSDGOrder R] (x : UnitInterval R) (d : D R) : UnitInterval R :=
  ⟨(x : R) + (d : R), by
    constructor
    · exact add_nonneg x.2.1 (inf_nonneg d)
    · calc
        (x : R) + (d : R) ≤ (x : R) + 0 := add_le_add_right (inf_nonpos d) (x : R)
        _ = (x : R) := by simp
        _ ≤ 1 := x.2.2
  ⟩

end UnitInterval

end SDG.Order
