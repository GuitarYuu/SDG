import SDG.DifferentialForms.Currents
import SDG.DifferentialForms.StokesCup

/-!
# Hⁿ 商层 cup 组装

de Rham 上同调环的商层乘法。约定：`Hⁿ` 的底是 `cocycles (n+1)`（项目
偏移，`deRhamSetoid n` 定义于其上），故商层 cup 的度数映射为
`Hⁿ × H^m → H^{n+m+1}`（底度 `(n+1)+(m+1)` 经 `cochainLenCast` 统一）。

1. `cocycleCupZ`：底类型 cup（上循环 × 上循环 → 上循环，保上闭链）；
2. `cocycleCupZ_sound`：良定义性（差 ∈ Bⁿ 因子经 witness 引理吸收）；
3. `deRhamCup`：商层乘法（`Quotient.map₂`）+ 双线性。

原料全部来自主线：`cupProduct`（Algebra）、分次 Leibniz 的 cast 桥
形式（StokesCup）、`deRhamSetoid`/`deRhamCon`（Currents）。
全部无选择公理。
-/

namespace SDG.DifferentialForms

section CupCohomologyQuotient

variable {R : Type u} [CommRing R] {X : Type u}

/-- 同型等式的度数 cast 一致性：两个 `m = n` 等式给出的 cast 点态相等
（展开后只差证明项，proof irrelevance 直接 rfl）。 -/
lemma cochainLenCast_congr {m n : ℕ} (h₁ h₂ : m = n) (c : Cochain R X m) :
    cochainLenCast h₁ c = cochainLenCast h₂ c := by
  funext σ
  rfl

/-- 度数 cast 保加法。 -/
lemma cochainLenCast_add {m n : ℕ} (h : m = n) (c₁ c₂ : Cochain R X m) :
    cochainLenCast h (c₁ + c₂) = cochainLenCast h c₁ + cochainLenCast h c₂ := by
  funext σ
  rfl

/-- 度数 cast 保减法。 -/
lemma cochainLenCast_sub {m n : ℕ} (h : m = n) (c₁ c₂ : Cochain R X m) :
    cochainLenCast h (c₁ - c₂) = cochainLenCast h c₁ - cochainLenCast h c₂ := by
  funext σ
  rfl

/-- 度数 cast 保数乘。 -/
lemma cochainLenCast_smul {m n : ℕ} (h : m = n) (c : R) (x : Cochain R X m) :
    cochainLenCast h (c • x) = c • cochainLenCast h x := by
  funext σ
  rfl

/-- cocycle 子模成员性质即 ∂c = 0（carrier 定义直接 rfl 展开）。 -/
lemma cocycles_property {n : ℕ} (a : cocycles (R := R) (X := X) (n := n)) :
    coboundary (a : Cochain R X n) = 0 := a.property

/-- 底类型上的 cup：上循环 × 上循环 → 上循环（度 `(n+1)+(m+1)` 经 cast
统一到 `(n+m+1)+1`；保上闭链由 `cupProduct_isCocycle`）。 -/
def cocycleCupZ {n m : ℕ}
    (a : cocycles (R := R) (X := X) (n := n + 1))
    (b : cocycles (R := R) (X := X) (n := m + 1)) :
    cocycles (R := R) (X := X) (n := (n + m + 1) + 1) :=
  ⟨cochainLenCast (show n + 1 + (m + 1) = (n + m + 1) + 1 from by omega)
      (cupProduct (a : Cochain R X (n + 1)) (b : Cochain R X (m + 1))),
    by
      show coboundary (cochainLenCast (show n + 1 + (m + 1) = (n + m + 1) + 1 from by omega)
          (cupProduct (a : Cochain R X (n + 1)) (b : Cochain R X (m + 1)))) = 0
      have hcoc := cupProduct_isCocycle
        (α := (a : Cochain R X (n + 1))) (β := (b : Cochain R X (m + 1)))
        (cocycles_property a) (cocycles_property b)
      rw [coboundary_cochainLenCast, hcoc, cochainLenCast_zero]⟩

/-- 底类型 cup 点态。 -/
lemma cocycleCupZ_apply {n m : ℕ}
    (a : cocycles (R := R) (X := X) (n := n + 1))
    (b : cocycles (R := R) (X := X) (n := m + 1))
    (σ : SimplexPts X (n + m + 1)) :
    cocycleCupZ a b
      = cochainLenCast (show n + 1 + (m + 1) = (n + m + 1) + 1 from by omega)
          (cupProduct (a : Cochain R X (n + 1)) (b : Cochain R X (m + 1))) := rfl

/-- cup 对左因子的减法分配（点态 ring）。 -/
lemma cup_sub_left {p q : ℕ} (α α' : Cochain R X p) (β : Cochain R X q) :
    cupProduct (α - α') β = cupProduct α β - cupProduct α' β := by
  funext σ
  simp only [cupProduct_apply, Pi.sub_apply]
  ring

/-- cup 对右因子的减法分配（点态 ring）。 -/
lemma cup_sub_right {p q : ℕ} (α : Cochain R X p) (β β' : Cochain R X q) :
    cupProduct α (β - β') = cupProduct α β - cupProduct α β' := by
  funext σ
  simp only [cupProduct_apply, Pi.sub_apply]
  ring

/-- **左差吸收（等式版）**：`cast(∂w ⌣ b) = ∂(cast(w ⌣ b))`——分次
Leibniz + ∂b = 0 的第二项消去（度数句法经 cast congr 桥）。 -/
lemma coboundary_cast_cup_coboundary_left {n m : ℕ} (w : Cochain R X n)
    (b : cocycles (R := R) (X := X) (n := m + 1)) :
    cochainLenCast (show n + 1 + (m + 1) = (n + m + 1) + 1 from by omega)
        (cupProduct (coboundary w) (b : Cochain R X (m + 1)))
      = coboundary (cochainLenCast (show n + (m + 1) = n + m + 1 from by omega)
          (cupProduct w (b : Cochain R X (m + 1)))) := by
  rw [coboundary_cochainLenCast]
  have hleb := coboundary_cupProduct (α := w) (β := (b : Cochain R X (m + 1)))
  rw [cocycles_property b, cup_zero_right, cochainLenCast_zero, smul_zero,
    add_zero] at hleb
  rw [hleb]
  rfl

/-- 左差吸收的成员形式。 -/
lemma cast_cup_coboundary_left_mem {n m : ℕ} (w : Cochain R X n)
    (b : cocycles (R := R) (X := X) (n := m + 1)) :
    cochainLenCast (show n + 1 + (m + 1) = (n + m + 1) + 1 from by omega)
        (cupProduct (coboundary w) (b : Cochain R X (m + 1)))
      ∈ coboundaries (R := R) (X := X) (n + m + 1) := by
  rw [mem_coboundaries]
  exact ⟨cochainLenCast (show n + (m + 1) = n + m + 1 from by omega)
    (cupProduct w (b : Cochain R X (m + 1))),
    (coboundary_cast_cup_coboundary_left w b).symm⟩

/-- **右差吸收（等式版）**：`cast(α ⌣ ∂w) = (-1)^{n+1} · ∂(cast(α ⌣ w))`
——分次 Leibniz + ∂α = 0 的第一项消去（对称符号两侧各乘一次）。 -/
lemma coboundary_cast_cup_coboundary_right {n m : ℕ}
    (α : cocycles (R := R) (X := X) (n := n + 1)) (w : Cochain R X m) :
    cochainLenCast (show n + 1 + (m + 1) = (n + m + 1) + 1 from by omega)
        (cupProduct (α : Cochain R X (n + 1)) (coboundary w))
      = (-1 : R)^((n+1 : ℕ)) • coboundary (cochainLenCast
          (show (n + 1) + m = n + m + 1 from by omega)
          (cupProduct (α : Cochain R X (n + 1)) w)) := by
  rw [coboundary_cochainLenCast]
  have hY := coboundary_cupProduct
    (α := (α : Cochain R X (n + 1))) (β := w)
  rw [cocycles_property α, cup_zero_left, cochainLenCast_zero, zero_add] at hY
  rw [hY, cochainLenCast_smul, smul_smul,
    show ((-1 : R)^((n+1 : ℕ)) * (-1 : R)^((n+1 : ℕ)) = 1) from by
    rw [← mul_pow, show ((-1 : R) * (-1 : R)) = 1 from by ring, one_pow], one_smul]
  rfl

/-- 右差吸收的成员形式（±∂ 形式仍是上边缘：差一个数乘）。 -/
lemma cast_cup_coboundary_right_mem {n m : ℕ}
    (α : cocycles (R := R) (X := X) (n := n + 1)) (w : Cochain R X m) :
    cochainLenCast (show n + 1 + (m + 1) = (n + m + 1) + 1 from by omega)
        (cupProduct (α : Cochain R X (n + 1)) (coboundary w))
      ∈ coboundaries (R := R) (X := X) (n + m + 1) := by
  rw [mem_coboundaries]
  refine ⟨(-1 : R)^((n+1 : ℕ)) • cochainLenCast
    (show (n + 1) + m = n + m + 1 from by omega)
    (cupProduct (α : Cochain R X (n + 1)) w), ?_⟩
  rw [← coboundaryLinear_apply, map_smul, coboundaryLinear_apply]
  exact (coboundary_cast_cup_coboundary_right α w).symm

/-- **良定义性（左因子）**：右因子同类固定时，左因子的类代表元替换
不改变底类型 cup 的类（左差 = ∂w 经左差吸收吸收）。 -/
lemma cocycleCupZ_sound_left {n m : ℕ}
    {a a' : cocycles (R := R) (X := X) (n := n + 1)}
    (b : cocycles (R := R) (X := X) (n := m + 1))
    (h₁ : (a : Cochain R X (n + 1)) - (a' : Cochain R X (n + 1))
      ∈ coboundaries (R := R) (X := X) n) :
    (cocycleCupZ a b : Cochain R X ((n + m + 1) + 1))
        - (cocycleCupZ a' b : Cochain R X ((n + m + 1) + 1))
      ∈ coboundaries (R := R) (X := X) (n + m + 1) := by
  rcases mem_coboundaries.mp h₁ with ⟨w, hw⟩
  have heq : ((cocycleCupZ a b : Cochain R X ((n + m + 1) + 1))
      - (cocycleCupZ a' b : Cochain R X ((n + m + 1) + 1)))
    = cochainLenCast (show n + 1 + (m + 1) = (n + m + 1) + 1 from by omega)
        (cupProduct (coboundary w) (b : Cochain R X (m + 1))) := by
    show (cochainLenCast (show n + 1 + (m + 1) = (n + m + 1) + 1 from by omega)
        (cupProduct (a : Cochain R X (n + 1)) (b : Cochain R X (m + 1)))
      - cochainLenCast (show n + 1 + (m + 1) = (n + m + 1) + 1 from by omega)
        (cupProduct (a' : Cochain R X (n + 1)) (b : Cochain R X (m + 1))))
      = cochainLenCast (show n + 1 + (m + 1) = (n + m + 1) + 1 from by omega)
        (cupProduct (coboundary w) (b : Cochain R X (m + 1)))
    rw [← cochainLenCast_sub, ← cup_sub_left, ← hw]
  rw [heq]
  exact cast_cup_coboundary_left_mem w b

/-- **良定义性（右因子）**：左因子同类固定时，右因子的类代表元替换
不改变底类型 cup 的类（右差 = ∂w 经右差吸收吸收）。 -/
lemma cocycleCupZ_sound_right {n m : ℕ}
    (a : cocycles (R := R) (X := X) (n := n + 1))
    {b b' : cocycles (R := R) (X := X) (n := m + 1)}
    (h₂ : (b : Cochain R X (m + 1)) - (b' : Cochain R X (m + 1))
      ∈ coboundaries (R := R) (X := X) m) :
    (cocycleCupZ a b : Cochain R X ((n + m + 1) + 1))
        - (cocycleCupZ a b' : Cochain R X ((n + m + 1) + 1))
      ∈ coboundaries (R := R) (X := X) (n + m + 1) := by
  rcases mem_coboundaries.mp h₂ with ⟨w, hw⟩
  have heq : ((cocycleCupZ a b : Cochain R X ((n + m + 1) + 1))
      - (cocycleCupZ a b' : Cochain R X ((n + m + 1) + 1)))
    = cochainLenCast (show n + 1 + (m + 1) = (n + m + 1) + 1 from by omega)
        (cupProduct (a : Cochain R X (n + 1)) (coboundary w)) := by
    show (cochainLenCast (show n + 1 + (m + 1) = (n + m + 1) + 1 from by omega)
        (cupProduct (a : Cochain R X (n + 1)) (b : Cochain R X (m + 1)))
      - cochainLenCast (show n + 1 + (m + 1) = (n + m + 1) + 1 from by omega)
        (cupProduct (a : Cochain R X (n + 1)) (b' : Cochain R X (m + 1))))
      = cochainLenCast (show n + 1 + (m + 1) = (n + m + 1) + 1 from by omega)
        (cupProduct (a : Cochain R X (n + 1)) (coboundary w))
    rw [← cochainLenCast_sub, ← cup_sub_right, ← hw]
  rw [heq]
  exact cast_cup_coboundary_right_mem a w

/-- **良定义性（双因子）**：底类型 cup 沿 deRhamSetoid 关系适定。 -/
theorem cocycleCupZ_sound {n m : ℕ}
    {a a' : cocycles (R := R) (X := X) (n := n + 1)}
    {b b' : cocycles (R := R) (X := X) (n := m + 1)}
    (h₁ : (a : Cochain R X (n + 1)) - (a' : Cochain R X (n + 1))
      ∈ coboundaries (R := R) (X := X) n)
    (h₂ : (b : Cochain R X (m + 1)) - (b' : Cochain R X (m + 1))
      ∈ coboundaries (R := R) (X := X) m) :
    (cocycleCupZ a b : Cochain R X ((n + m + 1) + 1))
        - (cocycleCupZ a' b' : Cochain R X ((n + m + 1) + 1))
      ∈ coboundaries (R := R) (X := X) (n + m + 1) := by
  have hsplit : ((cocycleCupZ a b : Cochain R X ((n + m + 1) + 1))
      - (cocycleCupZ a' b' : Cochain R X ((n + m + 1) + 1))
    = ((cocycleCupZ a b : Cochain R X ((n + m + 1) + 1))
        - (cocycleCupZ a' b : Cochain R X ((n + m + 1) + 1)))
      + ((cocycleCupZ a' b : Cochain R X ((n + m + 1) + 1))
        - (cocycleCupZ a' b' : Cochain R X ((n + m + 1) + 1)))) := by abel
  rw [hsplit]
  exact add_mem (cocycleCupZ_sound_left b h₁) (cocycleCupZ_sound_right a' h₂)

/-- **商层 cup**：`Hⁿ × H^m → H^{n+m+1}`（Quotient.map₂ 提升底类型
cocycleCupZ）。 -/
def deRhamCup (n m : ℕ) :
    deRhamCohomology (R := R) (X := X) n →
      deRhamCohomology (R := R) (X := X) m →
        deRhamCohomology (R := R) (X := X) (n + m + 1) :=
  Quotient.map₂ (fun (a : cocycles (R := R) (X := X) (n := n + 1))
      (b : cocycles (R := R) (X := X) (n := m + 1)) => cocycleCupZ a b)
    (fun _a₁ _b₁ h₁ _a₂ _b₂ h₂ => cocycleCupZ_sound h₁ h₂)

/-- 上积保持上闭链的类级便捷形式（供 deRhamClass 陈述）。 -/
theorem cupClass {n m : ℕ} {α : Cochain R X (n + 1)} {β : Cochain R X (m + 1)}
    (hα : IsCocycle α) (hβ : IsCocycle β) :
    IsCocycle (cochainLenCast (show (n : ℕ) + 1 + (m + 1) = (n + m + 1) + 1 from by omega)
      (cupProduct α β)) :=
  by
    have H : (n : ℕ) + 1 + (m + 1) = (n + m + 1) + 1 := by omega
    show coboundary (cochainLenCast H (cupProduct α β)) = 0
    rw [coboundary_cochainLenCast,
      cupProduct_isCocycle (α := α) (β := β) hα hβ, cochainLenCast_zero]

/-- 商层 cup 在类上的点态形式。 -/
theorem deRhamCup_apply {n m : ℕ} {α : Cochain R X (n + 1)} {β : Cochain R X (m + 1)}
    (hα : IsCocycle α) (hβ : IsCocycle β) :
    deRhamCup (R := R) (X := X) n m (deRhamClass hα) (deRhamClass hβ)
      = deRhamClass (cupClass hα hβ) := rfl

end CupCohomologyQuotient

end SDG.DifferentialForms
