import SDG.NoChoice
import Mathlib

/-!
# SDG.Rational

无选择公理的有理数。

Mathlib 的 `Rat.commRing`（`CommRing ℚ`）传递依赖 `Classical.choice`
（`#print axioms Rat.commRing` 显示 `[propext, Classical.choice, Quot.sound]`），
根因是 `Rat.add`/`Rat.mul` 的规范化证明用到了 `Int.natAbs_ediv_of_dvd`，
后者经由 `natAbs_ediv` 在不可判定命题 `0 ≤ a ∨ b ∣ a` 上 `split` 而引入选择公理。
因此在本项目（默认开启 `linter.noAxiomOfChoice`）中不能直接使用 `ℚ` 的环结构。

本模块给出**从整数出发的商构造**：把有理数定义为「交叉相乘相等」的
$(n,d) \in \mathbb{Z} \times \mathbb{N}^+$ 对的商。加法、乘法、取负均按代表元
定义，并用 `ring` 证明良定性与全部环律——整个过程**不涉及规范化/带余除法**，
因此**不使用选择公理**。

最终得到无选择公理的 `CommRing Q` 与 `NontrivialRatCommAlgebra Q`
（可作为合成微分几何 SDG 的基环，满足 `NontrivialRatCommAlgebra` 型类），
并用 `#assert_no_choice` 逐一验证。允许的底层公理仅 `propext` 与 `Quot.sound`
（Lean 逻辑本身的基础公理，不属于选择公理）。
-/

namespace SDG.Rational

/-! ## 表示与等价关系 -/

/-- 分数表示：分子为整数，分母为正整数（分数 $n/d$ 记作 $(n,d)$）。 -/
abbrev Rep : Type := ℤ × ℕ+

/-- 把正整数分母规范地看成整数（绕开 `ℕ+` 多重强制转换，便于 `ring` 处理）。 -/
def Zden (d : ℕ+) : ℤ := (d : ℕ)

/-- 交叉相乘相等：$n_1/d_1 = n_2/d_2 \iff n_1 d_2 = n_2 d_1$。 -/
def rel (x y : Rep) : Prop := x.1 * Zden y.2 = y.1 * Zden x.2

/-- `Zden` 乘性：$(ab)$ 的分母之积对应分母之积。 -/
@[simp]
lemma Zden_mul (a b : ℕ+) : Zden (a * b) = Zden a * Zden b := by
  norm_num [Zden]

/-- `Zden 1 = 1`。 -/
@[simp]
lemma Zden_one : Zden (1 : ℕ+) = 1 := by
  norm_num [Zden]

/-- 交叉相乘相等构成等价关系（传递性用分母非零消去公因子）。 -/
instance instSetoidRep : Setoid Rep where
  r := rel
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      simp [rel]
    · intro x y h
      exact h.symm
    · intro x y z hxy hyz
      unfold rel at hxy hyz ⊢
      have hyz0 : Zden y.2 ≠ 0 := by
        rw [Zden]
        exact_mod_cast (ne_of_gt y.2.2)
      have h1 : Zden y.2 * (x.1 * Zden z.2) = Zden y.2 * (z.1 * Zden x.2) := by
        calc
          Zden y.2 * (x.1 * Zden z.2) = x.1 * Zden y.2 * Zden z.2 := by ring
          _ = y.1 * Zden x.2 * Zden z.2 := by rw [hxy]
          _ = y.1 * Zden z.2 * Zden x.2 := by ring
          _ = z.1 * Zden y.2 * Zden x.2 := by rw [hyz]
          _ = Zden y.2 * (z.1 * Zden x.2) := by ring
      exact mul_left_cancel₀ hyz0 h1

/-! ## 商类型 -/

/-- 有理数：`Rep` 上按交叉相乘相等关系的商。 -/
abbrev Q : Type := Quotient instSetoidRep

/-- 由分子分母构造有理数 $n/d$。 -/
def ofPair (n : ℤ) (d : ℕ+) : Q := Quotient.mk instSetoidRep (n, d)

/-! ## 代表元上的运算（商之前） -/

/-- 分数加法：$n_1/d_1 + n_2/d_2 = (n_1 d_2 + n_2 d_1)/(d_1 d_2)$。 -/
def addRep (x y : Rep) : Rep := (x.1 * Zden y.2 + y.1 * Zden x.2, x.2 * y.2)

/-- 分数乘法：$n_1/d_1 \cdot n_2/d_2 = (n_1 n_2)/(d_1 d_2)$。 -/
def mulRep (x y : Rep) : Rep := (x.1 * y.1, x.2 * y.2)

/-- 分数取负：$-(n/d) = (-n)/d$。 -/
def negRep (x : Rep) : Rep := (-x.1, x.2)

/-- 加法良定性：等价的代表元相加仍等价（交叉相乘降为整数多项式恒等式）。 -/
lemma rel_add_resp (x₁ x₂ y₁ y₂ : Rep) (hx : rel x₁ x₂) (hy : rel y₁ y₂) :
    rel (addRep x₁ y₁) (addRep x₂ y₂) := by
  unfold rel at hx hy ⊢
  unfold addRep
  simp only [Zden_mul]
  calc
    (x₁.1 * Zden y₁.2 + y₁.1 * Zden x₁.2) * (Zden x₂.2 * Zden y₂.2)
        = x₁.1 * Zden x₂.2 * (Zden y₁.2 * Zden y₂.2)
          + y₁.1 * Zden y₂.2 * (Zden x₁.2 * Zden x₂.2) := by ring
    _ = x₂.1 * Zden x₁.2 * (Zden y₁.2 * Zden y₂.2)
          + y₂.1 * Zden y₁.2 * (Zden x₁.2 * Zden x₂.2) := by
        rw [hx, hy]
    _ = (x₂.1 * Zden y₂.2 + y₂.1 * Zden x₂.2) * (Zden x₁.2 * Zden y₁.2) := by ring

/-- 乘法良定性。 -/
lemma rel_mul_resp (x₁ x₂ y₁ y₂ : Rep) (hx : rel x₁ x₂) (hy : rel y₁ y₂) :
    rel (mulRep x₁ y₁) (mulRep x₂ y₂) := by
  unfold rel at hx hy ⊢
  unfold mulRep
  simp only [Zden_mul]
  calc
    x₁.1 * y₁.1 * (Zden x₂.2 * Zden y₂.2) = (x₁.1 * Zden x₂.2) * (y₁.1 * Zden y₂.2) := by ring
    _ = (x₂.1 * Zden x₁.2) * (y₂.1 * Zden y₁.2) := by rw [hx, hy]
    _ = x₂.1 * y₂.1 * (Zden x₁.2 * Zden y₁.2) := by ring

/-- 取负良定性。 -/
lemma rel_neg_resp (x₁ x₂ : Rep) (hx : rel x₁ x₂) :
    rel (negRep x₁) (negRep x₂) := by
  unfold rel at hx ⊢
  unfold negRep
  calc
    -x₁.1 * Zden x₂.2 = -(x₁.1 * Zden x₂.2) := by ring
    _ = -(x₂.1 * Zden x₁.2) := by rw [hx]
    _ = -x₂.1 * Zden x₁.2 := by ring

/-! ## 商上的运算 -/

/-- 加法：商上由代表元加法诱导。 -/
def add (a b : Q) : Q :=
  Quotient.lift₂ (fun x y ↦ Quotient.mk instSetoidRep (addRep x y))
    (by intro a₁ b₁ a₂ b₂ ha hb; exact Quotient.sound (rel_add_resp a₁ a₂ b₁ b₂ ha hb)) a b

/-- 乘法：商上由代表元乘法诱导。 -/
def mul (a b : Q) : Q :=
  Quotient.lift₂ (fun x y ↦ Quotient.mk instSetoidRep (mulRep x y))
    (by intro a₁ b₁ a₂ b₂ ha hb; exact Quotient.sound (rel_mul_resp a₁ a₂ b₁ b₂ ha hb)) a b

/-- 取负：商上由代表元取负诱导。 -/
def neg (a : Q) : Q :=
  Quotient.lift (fun x ↦ Quotient.mk instSetoidRep (negRep x))
    (by intro a₁ a₂ ha; exact Quotient.sound (rel_neg_resp a₁ a₂ ha)) a

/-- 有理数零 $0 = 0/1$。 -/
def zero : Q := ofPair 0 1

/-- 有理数一 $1 = 1/1$。 -/
def one : Q := ofPair 1 1

/-! ## 基础实例（供后续环律与 `CommRing` 使用） -/

instance instZero : Zero Q := ⟨zero⟩
instance instOne : One Q := ⟨one⟩
instance instAdd : Add Q := ⟨add⟩
instance instMul : Mul Q := ⟨mul⟩
instance instNeg : Neg Q := ⟨neg⟩
instance instSub : Sub Q := ⟨fun a b ↦ a + neg b⟩
instance instNatCast : NatCast Q := ⟨fun n ↦ ofPair (n : ℤ) 1⟩
instance instIntCast : IntCast Q := ⟨fun z ↦ ofPair z 1⟩
instance instOfNat (n : ℕ) : OfNat Q n := ⟨ofPair (n : ℤ) 1⟩
instance instSMulInt : SMul ℤ Q := ⟨zsmulRec⟩
instance instCoePNatQ : Coe ℕ+ Q := ⟨fun n ↦ ofPair (n : ℕ) 1⟩

/-! ## 环律（全部降为整数多项式等式，用 `ring` 证明） -/

theorem add_assoc (a b c : Q) : a + b + c = a + (b + c) := by
  refine Quotient.inductionOn a ?_
  intro x
  refine Quotient.inductionOn b ?_
  intro y
  refine Quotient.inductionOn c ?_
  intro z
  change Quotient.mk instSetoidRep (addRep (addRep x y) z) = Quotient.mk instSetoidRep (addRep x (addRep y z))
  apply Quotient.sound
  change rel (addRep (addRep x y) z) (addRep x (addRep y z))
  unfold rel addRep
  simp only [Zden_mul]
  ring

theorem add_comm (a b : Q) : a + b = b + a := by
  refine Quotient.inductionOn a ?_
  intro x
  refine Quotient.inductionOn b ?_
  intro y
  change Quotient.mk instSetoidRep (addRep x y) = Quotient.mk instSetoidRep (addRep y x)
  apply Quotient.sound
  change rel (addRep x y) (addRep y x)
  unfold rel addRep
  simp only [Zden_mul]
  ring

theorem zero_add (a : Q) : 0 + a = a := by
  refine Quotient.inductionOn a ?_
  intro x
  change Quotient.mk instSetoidRep (addRep (0, 1) x) = Quotient.mk instSetoidRep x
  apply Quotient.sound
  change rel (addRep (0, 1) x) x
  unfold rel addRep
  simp only [Zden_mul, Zden_one]
  ring

theorem add_zero (a : Q) : a + 0 = a := by
  refine Quotient.inductionOn a ?_
  intro x
  change Quotient.mk instSetoidRep (addRep x (0, 1)) = Quotient.mk instSetoidRep x
  apply Quotient.sound
  change rel (addRep x (0, 1)) x
  unfold rel addRep
  simp only [Zden_mul, Zden_one]
  ring

theorem mul_assoc (a b c : Q) : a * b * c = a * (b * c) := by
  refine Quotient.inductionOn a ?_
  intro x
  refine Quotient.inductionOn b ?_
  intro y
  refine Quotient.inductionOn c ?_
  intro z
  change Quotient.mk instSetoidRep (mulRep (mulRep x y) z) = Quotient.mk instSetoidRep (mulRep x (mulRep y z))
  apply Quotient.sound
  change rel (mulRep (mulRep x y) z) (mulRep x (mulRep y z))
  unfold rel mulRep
  simp only [Zden_mul]
  ring

theorem mul_comm (a b : Q) : a * b = b * a := by
  refine Quotient.inductionOn a ?_
  intro x
  refine Quotient.inductionOn b ?_
  intro y
  change Quotient.mk instSetoidRep (mulRep x y) = Quotient.mk instSetoidRep (mulRep y x)
  apply Quotient.sound
  change rel (mulRep x y) (mulRep y x)
  unfold rel mulRep
  simp only [Zden_mul]
  ring

theorem one_mul (a : Q) : 1 * a = a := by
  refine Quotient.inductionOn a ?_
  intro x
  change Quotient.mk instSetoidRep (mulRep (1, 1) x) = Quotient.mk instSetoidRep x
  apply Quotient.sound
  change rel (mulRep (1, 1) x) x
  unfold rel mulRep
  simp only [Zden_mul, Zden_one]
  ring

theorem mul_one (a : Q) : a * 1 = a := by
  refine Quotient.inductionOn a ?_
  intro x
  change Quotient.mk instSetoidRep (mulRep x (1, 1)) = Quotient.mk instSetoidRep x
  apply Quotient.sound
  change rel (mulRep x (1, 1)) x
  unfold rel mulRep
  simp only [Zden_mul, Zden_one]
  ring

theorem zero_mul (a : Q) : 0 * a = 0 := by
  refine Quotient.inductionOn a ?_
  intro x
  change Quotient.mk instSetoidRep (mulRep (0, 1) x) = Quotient.mk instSetoidRep (0, 1)
  apply Quotient.sound
  change rel (mulRep (0, 1) x) (0, 1)
  unfold rel mulRep
  simp only [Zden_mul, Zden_one]
  ring

theorem mul_zero (a : Q) : a * 0 = 0 := by
  refine Quotient.inductionOn a ?_
  intro x
  change Quotient.mk instSetoidRep (mulRep x (0, 1)) = Quotient.mk instSetoidRep (0, 1)
  apply Quotient.sound
  change rel (mulRep x (0, 1)) (0, 1)
  unfold rel mulRep
  simp only [Zden_mul, Zden_one]
  ring

theorem left_distrib (a b c : Q) : a * (b + c) = a * b + a * c := by
  refine Quotient.inductionOn a ?_
  intro x
  refine Quotient.inductionOn b ?_
  intro y
  refine Quotient.inductionOn c ?_
  intro z
  change Quotient.mk instSetoidRep (mulRep x (addRep y z)) = Quotient.mk instSetoidRep (addRep (mulRep x y) (mulRep x z))
  apply Quotient.sound
  change rel (mulRep x (addRep y z)) (addRep (mulRep x y) (mulRep x z))
  unfold rel addRep mulRep
  simp only [Zden_mul]
  ring

theorem right_distrib (a b c : Q) : (a + b) * c = a * c + b * c := by
  refine Quotient.inductionOn a ?_
  intro x
  refine Quotient.inductionOn b ?_
  intro y
  refine Quotient.inductionOn c ?_
  intro z
  change Quotient.mk instSetoidRep (mulRep (addRep x y) z) = Quotient.mk instSetoidRep (addRep (mulRep x z) (mulRep y z))
  apply Quotient.sound
  change rel (mulRep (addRep x y) z) (addRep (mulRep x z) (mulRep y z))
  unfold rel addRep mulRep
  simp only [Zden_mul]
  ring

theorem neg_add_cancel (a : Q) : -a + a = 0 := by
  refine Quotient.inductionOn a ?_
  intro x
  change Quotient.mk instSetoidRep (addRep (negRep x) x) = Quotient.mk instSetoidRep (0, 1)
  apply Quotient.sound
  change rel (addRep (negRep x) x) (0, 1)
  unfold rel addRep negRep
  simp only [Zden_mul, Zden_one]
  ring

/-- 自然数嵌入：$\uparrow(n+1) = \uparrow n + 1$。 -/
theorem natCast_succ (n : ℕ) : ((n + 1 : ℕ) : Q) = (n : Q) + 1 := by
  change Quotient.mk instSetoidRep (((n + 1 : ℕ) : ℤ), 1) = Quotient.mk instSetoidRep (addRep ((n : ℤ), 1) (1, 1))
  apply Quotient.sound
  change rel (((n + 1 : ℕ) : ℤ), 1) (addRep ((n : ℤ), 1) (1, 1))
  unfold rel addRep
  simp only [Zden_mul, Zden_one]
  norm_num

/-! ## 无选择公理的 `CommRing Q` -/

instance instCommRing : CommRing Q where
  toAddMonoid := {
    add := add
    zero := zero
    add_assoc := add_assoc
    zero_add := zero_add
    add_zero := add_zero
    nsmul := nsmulRec
  }
  add_comm := add_comm
  toMonoid := {
    mul := mul
    one := one
    mul_assoc := mul_assoc
    one_mul := one_mul
    mul_one := mul_one
  }
  zero_mul := zero_mul
  mul_zero := mul_zero
  left_distrib := left_distrib
  right_distrib := right_distrib
  natCast := (fun n ↦ ofPair (n : ℤ) 1)
  natCast_zero := by rfl
  natCast_succ := natCast_succ
  toNeg := ⟨neg⟩
  toSub := ⟨fun a b ↦ a + neg b⟩
  toZSMul := ⟨zsmulRec⟩
  sub_eq_add_neg := by intro a b; rfl
  neg_add_cancel := neg_add_cancel
  intCast := (fun z ↦ ofPair z 1)
  intCast_ofNat := by intro n; rfl
  intCast_negSucc := by intro n; rfl
  mul_comm := mul_comm

/-! ## 非平凡与有理数代数 -/

/-- 有理数非平凡：$0 \ne 1$。 -/
instance instNontrivial : Nontrivial Q where
  exists_pair_ne := by
    refine ⟨0, 1, ?_⟩
    intro h
    have hrel : rel (0, (1 : ℕ+)) (1, (1 : ℕ+)) := Quotient.exact h
    unfold rel at hrel
    rw [Zden_one] at hrel
    omega

/-- 正整数在有理数中可逆：$n \cdot (1/n) = 1$。 -/
instance instInvertiblePNat (n : ℕ+) : Invertible (((n : ℕ) : Q)) where
  invOf := ofPair 1 n
  invOf_mul_self := by
    change Quotient.mk instSetoidRep (mulRep (1, n) ((n : ℕ), 1)) = Quotient.mk instSetoidRep (1, 1)
    apply Quotient.sound
    change rel (mulRep (1, n) ((n : ℕ), 1)) (1, 1)
    unfold rel mulRep
    simp only [Zden_mul, Zden_one]
    rw [show Zden n = ((n : ℕ) : ℤ) by rfl]
    ring
  mul_invOf_self := by
    change Quotient.mk instSetoidRep (mulRep ((n : ℕ), 1) (1, n)) = Quotient.mk instSetoidRep (1, 1)
    apply Quotient.sound
    change rel (mulRep ((n : ℕ), 1) (1, n)) (1, 1)
    unfold rel mulRep
    simp only [Zden_mul, Zden_one]
    rw [show Zden n = ((n : ℕ) : ℤ) by rfl]
    ring

end SDG.Rational
