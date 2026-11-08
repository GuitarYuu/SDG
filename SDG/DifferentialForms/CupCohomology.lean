import SDG.DifferentialForms.Currents
import SDG.DifferentialForms.StokesCup
import SDG.DifferentialForms.CupAssoc
import SDG.DifferentialForms.CohomologyModule

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

/-- 度数 cast 的复合律：先沿 `hab` 再沿 `hbc` 的两次 cast 等于沿复合
等式的一次 cast（`Fin.cast` 的 def 级复合：两层 `⟨val, _⟩` 塌缩，
pointwise rfl）。 -/
lemma cochainLenCast_trans {a b c : ℕ} (hab : a = b) (hbc : b = c)
    (W : Cochain R X a) :
    cochainLenCast hbc (cochainLenCast hab W) = cochainLenCast (hab.trans hbc) W := by
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

section DegreeTransport

/-- cocycles 的度数 transport：沿 `Fin.cast`-式 cochainLenCast 把
`cocycles (n+1)` 的元素搬到 `cocycles (m+1)`（∂ 与 cast 交换 +
cast 零）。 -/
def cocyclesCast {n m : ℕ} (H : n = m) (a : cocycles (R := R) (X := X) (n := n + 1)) :
    cocycles (R := R) (X := X) (n := m + 1) :=
  ⟨cochainLenCast (show n + 1 = m + 1 from by rw [H]) (a : Cochain R X (n + 1)),
    by
      show coboundary _ = 0
      rw [coboundary_cochainLenCast, cocycles_property a, cochainLenCast_zero]⟩

/-- 底 transport 点态。 -/
lemma cocyclesCast_apply {n m : ℕ} (H : n = m)
    (a : cocycles (R := R) (X := X) (n := n + 1)) :
    (cocyclesCast H a : Cochain R X (m + 1))
      = cochainLenCast (show n + 1 = m + 1 from by rw [H]) (a : Cochain R X (n + 1)) := rfl

/-- **H 层度数 transport**：`Hⁿ → H^m`（沿度数等式 `n = m`）。
底映射沿 cochainLenCast，上边缘差被 cast 保（`coboundary_cochainLenCast`
的差吸收：cast(∂w) = ∂(cast w)）。 -/
def deRhamCohomologyCast {n m : ℕ} (H : n = m) :
    deRhamCohomology (R := R) (X := X) n →
      deRhamCohomology (R := R) (X := X) m :=
    Quotient.map (sa := (deRhamCon (R := R) (X := X) n).toSetoid)
      (sb := (deRhamCon (R := R) (X := X) m).toSetoid)
      (fun a : cocycles (R := R) (X := X) (n := n + 1) => cocyclesCast H a)
      (fun a₁ b₁ h => by
        have h' : (a₁ : Cochain R X (n + 1)) - (b₁ : Cochain R X (n + 1))
            ∈ coboundaries (R := R) (X := X) n := h
        rw [mem_coboundaries] at h'
        obtain ⟨w, hw⟩ := h'
        show ((cocyclesCast H a₁ : Cochain R X (m + 1))
          - (cocyclesCast H b₁ : Cochain R X (m + 1))) ∈ coboundaries (R := R) (X := X) m
        rw [cocyclesCast_apply, cocyclesCast_apply, ← cochainLenCast_sub, ← hw,
          mem_coboundaries]
        exact ⟨cochainLenCast (show n = m from by rw [H]) w, by
          rw [coboundary_cochainLenCast]⟩)

/-- H 层 transport 点态（类形式）。 -/
lemma deRhamCohomologyCast_apply {n m : ℕ} (H : n = m) {α : Cochain R X (n + 1)}
    (hα : IsCocycle α) :
    deRhamCohomologyCast H (deRhamClass hα)
      = deRhamClass (by
          have hC : IsCocycle (cochainLenCast (show n + 1 = m + 1 from by rw [H]) α) :=
            by show coboundary _ = 0
               rw [coboundary_cochainLenCast, hα, cochainLenCast_zero]
          exact hC) := rfl

/-- H 层 transport 的恒等性：`H = rfl` 时 cast 是恒等映射
（第五十二接力点：Quotient.inductionOn 路线收口）。 -/
theorem deRhamCohomologyCast_rfl {n : ℕ}
    (x : deRhamCohomology (R := R) (X := X) n) :
    deRhamCohomologyCast (R := R) (X := X) (rfl : n = n) x = x :=
  Quotient.inductionOn x (fun _a => rfl)

end DegreeTransport

/-- cup 对左因子 cast 的交换：cast 后作 cup = 作 cup 后 cast（度数
沿 omega 等式提升）。证明：两因子的槽函数等式分别作为显式函数等式
have（点态 `Fin.ext` + def 级值展开；`congr 1` 的乘法分量顺序不可预测，
故不用 congr-bullet 结构）。 -/
lemma cup_cast_left {p p' q : ℕ} (h : p = p') (c₁ : Cochain R X p)
    (c₂ : Cochain R X q) :
    cupProduct (cochainLenCast h c₁) c₂
      = cochainLenCast (show p + q = p' + q from by omega) (cupProduct c₁ c₂) := by
  funext σ
  rw [cochainLenCast_apply, cupProduct_apply, cochainLenCast_apply, cupProduct_apply]
  have hL : (fun k : Fin (p + 1) =>
        σ (cupLeft p' q (Fin.cast (show p + 1 = p' + 1 from by rw [h]) k)))
      = (fun k : Fin (p + 1) =>
        σ (Fin.cast (show p + q + 1 = p' + q + 1 from by omega) (cupLeft p q k))) := by
    funext k
    exact congrArg σ (Fin.ext (by simp only [cupLeft, Fin.val_cast, Fin.val_castAdd]))
  have hR : (fun k : Fin (q + 1) => σ (cupRight p' q k))
      = (fun k : Fin (q + 1) =>
        σ (Fin.cast (show p + q + 1 = p' + q + 1 from by omega) (cupRight p q k))) := by
    funext k
    exact congrArg σ (Fin.ext
      (by simp only [cupRight, Fin.val_cast, Fin.val_natAdd]; omega))
  rw [congrArg c₁ hL, congrArg c₂ hR]

/-- cup 对右因子 cast 的交换（组件顺序鲁棒的证明结构，见
`cup_cast_left` 注记）。 -/
lemma cup_cast_right {p q q' : ℕ} (h : q = q') (c₁ : Cochain R X p)
    (c₂ : Cochain R X q) :
    cupProduct c₁ (cochainLenCast h c₂)
      = cochainLenCast (show p + q = p + q' from by omega) (cupProduct c₁ c₂) := by
  funext σ
  rw [cochainLenCast_apply, cupProduct_apply, cochainLenCast_apply, cupProduct_apply]
  have hL : (fun k : Fin (p + 1) => σ (cupLeft p q' k))
      = (fun k : Fin (p + 1) =>
        σ (Fin.cast (show p + q + 1 = p + q' + 1 from by omega) (cupLeft p q k))) := by
    funext k
    exact congrArg σ (Fin.ext (by simp only [cupLeft, Fin.val_cast, Fin.val_castAdd]))
  have hR : (fun k : Fin (q + 1) =>
        σ (cupRight p q' (Fin.cast (show q + 1 = q' + 1 from by rw [h]) k)))
      = (fun k : Fin (q + 1) =>
        σ (Fin.cast (show p + q + 1 = p + q' + 1 from by omega) (cupRight p q k))) := by
    funext k
    exact congrArg σ (Fin.ext (by simp only [cupRight, Fin.val_cast, Fin.val_natAdd]))
  rw [congrArg c₁ hL, congrArg c₂ hR]

/-- **结合律的 cast 形式化**：`(α ⌣ β) ⌣ γ = cast(α ⌣ (β ⌣ γ))`
（cupProduct_assoc 的 cochainLenCast 桥装；cast 方向：源度
`p + (q + r)`，目标度 `(p + q) + r`；两 rw 后两侧只差证明项，rw 的
尾随 rfl 自动闭合）。 -/
lemma cup_assoc_cast {p q r : ℕ} (α : Cochain R X p) (β : Cochain R X q)
    (γ : Cochain R X r) :
    cupProduct (cupProduct α β) γ
      = cochainLenCast (show p + (q + r) = (p + q) + r from by omega)
          (cupProduct α (cupProduct β γ)) := by
  funext σ
  rw [cochainLenCast_apply, cupProduct_assoc_apply]

/-- **三因子上闭链 cup 的 cast-树一致性**：`cocycleCupZ (cocycleCupZ α β) γ`
与 `cocycleCupZ α (cocycleCupZ β γ)` 的底层 Cochain（经 H 层度数运输后）
相等——商层 cup 结合律的 Cochain 层核心。证明：两条 cast 路线各自经
`cup_cast_left/right` 吸收因子 cast、`cochainLenCast_trans` 折叠成单次
cast、`cup_assoc_cast` 换结合括号，最后两条复合等式的 cast 经
`cochainLenCast_congr`（proof irrelevance）合一。 -/
lemma cupCocycleZ_assoc_tree {n m k : ℕ} (α : Cochain R X (n + 1))
    (β : Cochain R X (m + 1)) (γ : Cochain R X (k + 1)) :
    cochainLenCast
        (show (n + (m + k + 1) + 1) + 1 = ((n + m + 1) + k + 1) + 1 from by omega)
        (cochainLenCast
          (show n + 1 + ((m + k + 1) + 1) = (n + (m + k + 1) + 1) + 1 from by omega)
          (cupProduct α
            (cochainLenCast (show m + 1 + (k + 1) = (m + k + 1) + 1 from by omega)
              (cupProduct β γ))))
      = cochainLenCast
          (show (n + m + 1) + 1 + (k + 1) = ((n + m + 1) + k + 1) + 1 from by omega)
          (cupProduct (cochainLenCast (show n + 1 + (m + 1) = (n + m + 1) + 1 from by omega)
              (cupProduct α β))
            γ) := by
  rw [cup_cast_right (show m + 1 + (k + 1) = (m + k + 1) + 1 from by omega) α
    (cupProduct β γ),
    cochainLenCast_trans, cochainLenCast_trans,
    cup_cast_left (show n + 1 + (m + 1) = (n + m + 1) + 1 from by omega)
      (cupProduct α β) γ,
    cochainLenCast_trans, cup_assoc_cast α β γ, cochainLenCast_trans]
  -- 两侧各为单次 cast 包同一个三因子 cup，只差复合等式的证明项
  --（def 展开后 λ 体 proof-irrelevant），rw 的尾随 rfl 自动闭合。

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

/-! ### 商层双线性

`deRhamCup` 对商加法的双线性：加法左/右分配、零吸收、负相容。
底层原料：`cup_add_left/right`、`cup_zero_left/right`（Algebra）、
`cochainLenCast_add/zero`（本文件）、类投影的 `rfl` 展开
（`AddCon.toQuotient` 的加法/零透明）。全部无选择公理。 -/

/-- 上循环对加法封闭（∂ 的加法性经 `coboundaryLinear`）。 -/
theorem isCocycle_add {n : ℕ} {α β : Cochain R X n}
    (hα : IsCocycle α) (hβ : IsCocycle β) : IsCocycle (α + β) := by
  show coboundary (α + β) = 0
  rw [← coboundaryLinear_apply, LinearMap.map_add, coboundaryLinear_apply,
    coboundaryLinear_apply, hα, hβ, add_zero]

/-- 上循环对零封闭。 -/
theorem isCocycle_zero {n : ℕ} : IsCocycle (0 : Cochain R X n) := by
  show coboundary (0 : Cochain R X n) = 0
  rw [← coboundaryLinear_apply, coboundaryLinear.map_zero]

/-- 上循环对取负封闭。 -/
theorem isCocycle_neg {n : ℕ} {α : Cochain R X n} (hα : IsCocycle α) :
    IsCocycle (-α) := by
  show coboundary (-α) = 0
  rw [← coboundaryLinear_apply, LinearMap.map_neg, coboundaryLinear_apply, hα, neg_zero]

/-- 底层 Cochain 相等则类相等（`deRhamClass` 的值只依赖底链，
proof irrelevance）。 -/
theorem deRhamClass_congr {n : ℕ} {c₁ c₂ : Cochain R X (n + 1)}
    (h₁ : IsCocycle c₁) (h₂ : IsCocycle c₂) (h : c₁ = c₂) :
    deRhamClass (R := R) (X := X) h₁ = deRhamClass h₂ := by
  cases h
  rfl

/-- 类加法收进单个类（`AddCon.toQuotient` 的加法透明）。 -/
theorem deRhamClass_add {n : ℕ} {α β : Cochain R X (n + 1)}
    (hα : IsCocycle α) (hβ : IsCocycle β) :
    deRhamClass hα + deRhamClass hβ
      = deRhamClass (isCocycle_add hα hβ) := rfl

/-- 零类（`Hⁿ` 的加法单位元 = 零上循环的类）。 -/
theorem deRhamClass_zero {n : ℕ} : (0 : deRhamCohomology (R := R) (X := X) n)
    = deRhamClass (R := R) (X := X) (α := (0 : Cochain R X (n + 1)))
        isCocycle_zero := rfl

/-- **商层 cup 左分配**：`([α] + [α']) ⌣ [β] = [α]⌣[β] + [α']⌣[β]`。 -/
theorem deRhamCup_add_left {n m : ℕ} {α α' : Cochain R X (n + 1)}
    {β : Cochain R X (m + 1)}
    (hα : IsCocycle α) (hα' : IsCocycle α') (hβ : IsCocycle β) :
    deRhamCup (R := R) (X := X) n m (deRhamClass hα + deRhamClass hα')
        (deRhamClass hβ)
      = deRhamCup (R := R) (X := X) n m (deRhamClass hα) (deRhamClass hβ)
        + deRhamCup (R := R) (X := X) n m (deRhamClass hα') (deRhamClass hβ) := by
  rw [deRhamClass_add hα hα', deRhamCup_apply (isCocycle_add hα hα') hβ,
    deRhamCup_apply hα hβ, deRhamCup_apply hα' hβ,
    deRhamClass_add (cupClass hα hβ) (cupClass hα' hβ)]
  exact deRhamClass_congr _ _ (by rw [← cochainLenCast_add, ← cup_add_left])

/-- **商层 cup 右分配**：`[α] ⌣ ([β] + [β']) = [α]⌣[β] + [α]⌣[β']`。 -/
theorem deRhamCup_add_right {n m : ℕ} {α : Cochain R X (n + 1)}
    {β β' : Cochain R X (m + 1)}
    (hα : IsCocycle α) (hβ : IsCocycle β) (hβ' : IsCocycle β') :
    deRhamCup (R := R) (X := X) n m (deRhamClass hα)
        (deRhamClass hβ + deRhamClass hβ')
      = deRhamCup (R := R) (X := X) n m (deRhamClass hα) (deRhamClass hβ)
        + deRhamCup (R := R) (X := X) n m (deRhamClass hα) (deRhamClass hβ') := by
  rw [deRhamClass_add hβ hβ', deRhamCup_apply hα (isCocycle_add hβ hβ'),
    deRhamCup_apply hα hβ, deRhamCup_apply hα hβ',
    deRhamClass_add (cupClass hα hβ) (cupClass hα hβ')]
  exact deRhamClass_congr _ _ (by rw [← cochainLenCast_add, ← cup_add_right])

/-- **商层 cup 左零吸收**：`0 ⌣ [β] = 0`。 -/
theorem deRhamCup_zero_left {n m : ℕ} {β : Cochain R X (m + 1)}
    (hβ : IsCocycle β) :
    deRhamCup (R := R) (X := X) n m 0 (deRhamClass hβ) = 0 := by
  rw [deRhamClass_zero, deRhamCup_apply isCocycle_zero hβ, deRhamClass_zero]
  exact deRhamClass_congr _ _ (by rw [cup_zero_left, cochainLenCast_zero])

/-- **商层 cup 右零吸收**：`[α] ⌣ 0 = 0`。 -/
theorem deRhamCup_zero_right {n m : ℕ} {α : Cochain R X (n + 1)}
    (hα : IsCocycle α) :
    deRhamCup (R := R) (X := X) n m (deRhamClass hα) 0 = 0 := by
  rw [deRhamClass_zero, deRhamCup_apply hα isCocycle_zero, deRhamClass_zero]
  exact deRhamClass_congr _ _ (by rw [cup_zero_right, cochainLenCast_zero])

/-- **商层 cup 左负相容**（群律后承：`add_left` + `zero_left`）：
`(-[α]) ⌣ [β] = -([α]⌣[β])`。 -/
theorem deRhamCup_neg_left {n m : ℕ} {α : Cochain R X (n + 1)}
    {β : Cochain R X (m + 1)}
    (hα : IsCocycle α) (hβ : IsCocycle β) :
    deRhamCup (R := R) (X := X) n m (-deRhamClass hα) (deRhamClass hβ)
      = -deRhamCup (R := R) (X := X) n m (deRhamClass hα) (deRhamClass hβ) := by
  have hsum : deRhamCup (R := R) (X := X) n m
      (deRhamClass hα + deRhamClass (isCocycle_neg hα)) (deRhamClass hβ)
      = deRhamCup (R := R) (X := X) n m (deRhamClass hα) (deRhamClass hβ)
        + deRhamCup (R := R) (X := X) n m (-deRhamClass hα) (deRhamClass hβ) :=
    deRhamCup_add_left hα (isCocycle_neg hα) hβ
  have hzero : deRhamClass hα + deRhamClass (isCocycle_neg hα) = 0 := by
    rw [deRhamClass_add hα (isCocycle_neg hα)]
    exact deRhamClass_congr (isCocycle_add hα (isCocycle_neg hα)) isCocycle_zero
      (by show (α + -α : Cochain R X (n+1)) = 0
          rw [add_neg_cancel])
  rw [hzero, deRhamCup_zero_left hβ] at hsum
  exact eq_neg_of_add_eq_zero_right hsum.symm

/-- **商层 cup 右负相容**（群律后承）：`[α] ⌣ (-[β]) = -([α]⌣[β])`。 -/
theorem deRhamCup_neg_right {n m : ℕ} {α : Cochain R X (n + 1)}
    {β : Cochain R X (m + 1)}
    (hα : IsCocycle α) (hβ : IsCocycle β) :
    deRhamCup (R := R) (X := X) n m (deRhamClass hα) (-deRhamClass hβ)
      = -deRhamCup (R := R) (X := X) n m (deRhamClass hα) (deRhamClass hβ) := by
  have hsum : deRhamCup (R := R) (X := X) n m (deRhamClass hα)
      (deRhamClass hβ + deRhamClass (isCocycle_neg hβ))
      = deRhamCup (R := R) (X := X) n m (deRhamClass hα) (deRhamClass hβ)
        + deRhamCup (R := R) (X := X) n m (deRhamClass hα) (-deRhamClass hβ) :=
    deRhamCup_add_right hα hβ (isCocycle_neg hβ)
  have hzero : deRhamClass hβ + deRhamClass (isCocycle_neg hβ) = 0 := by
    rw [deRhamClass_add hβ (isCocycle_neg hβ)]
    exact deRhamClass_congr (isCocycle_add hβ (isCocycle_neg hβ)) isCocycle_zero
      (by show (β + -β : Cochain R X (m+1)) = 0
          rw [add_neg_cancel])
  rw [hzero, deRhamCup_zero_right hα] at hsum
  exact eq_neg_of_add_eq_zero_right hsum.symm

/-! #### 商层 cup 的数乘相容

`Hⁿ` 的 `Module R` 结构（`CohomologyModule`）与商层 cup 的相容性——
de Rham 上同调环作为 R-代数的最后一块商层拼图。底层原料：
`cup_smul_left/right`（Algebra）、`cochainLenCast_smul`（本文件）、
`deRhamClass_smul`（CohomologyModule）。 -/

/-- **商层 cup 左数乘相容**：`(r•[α]) ⌣ [β] = r•([α]⌣[β])`。 -/
theorem deRhamCup_smul_left {n m : ℕ} (r : R) {α : Cochain R X (n + 1)}
    {β : Cochain R X (m + 1)}
    (hα : IsCocycle α) (hβ : IsCocycle β) :
    deRhamCup (R := R) (X := X) n m (r • deRhamClass hα) (deRhamClass hβ)
      = r • deRhamCup (R := R) (X := X) n m (deRhamClass hα) (deRhamClass hβ) := by
  rw [deRhamClass_smul, deRhamCup_apply (isCocycle_smul r hα) hβ,
    deRhamCup_apply hα hβ, deRhamClass_smul]
  exact deRhamClass_congr _ _ (by rw [cup_smul_left, cochainLenCast_smul])

/-- **商层 cup 右数乘相容**：`[α] ⌣ (r•[β]) = r•([α]⌣[β])`。 -/
theorem deRhamCup_smul_right {n m : ℕ} (r : R) {α : Cochain R X (n + 1)}
    {β : Cochain R X (m + 1)}
    (hα : IsCocycle α) (hβ : IsCocycle β) :
    deRhamCup (R := R) (X := X) n m (deRhamClass hα) (r • deRhamClass hβ)
      = r • deRhamCup (R := R) (X := X) n m (deRhamClass hα) (deRhamClass hβ) := by
  rw [deRhamClass_smul, deRhamCup_apply hα (isCocycle_smul r hβ),
    deRhamCup_apply hα hβ, deRhamClass_smul]
  exact deRhamClass_congr _ _ (by rw [cup_smul_right, cochainLenCast_smul])

/-! #### 商层 cup 结合律

de Rham 上同调环乘法结合律的商层组装。两侧的 H 度数句法不同
（`n + (m + k + 1) + 1` vs `(n + m + 1) + k + 1`），左侧经
`deRhamCohomologyCast` 运输到右侧度数——这正是该运输引理的
设计用途（第四十二接力点）。底层核心：`cupCocycleZ_assoc_tree`。 -/

/-- **商层 cup 结合律**：`([α]⌣[β])⌣[γ] = [α]⌣([β]⌣[γ])`（左侧经
`deRhamCohomologyCast` 从度数 `n + (m + k + 1) + 1` 运输到
`(n + m + 1) + k + 1`）。 -/
theorem deRhamCup_assoc {n m k : ℕ}
    {α : Cochain R X (n + 1)} {β : Cochain R X (m + 1)} {γ : Cochain R X (k + 1)}
    (hα : IsCocycle α) (hβ : IsCocycle β) (hγ : IsCocycle γ) :
    deRhamCohomologyCast (R := R) (X := X)
        (show n + (m + k + 1) + 1 = (n + m + 1) + k + 1 from by omega)
        (deRhamCup (R := R) (X := X) n (m + k + 1) (deRhamClass hα)
          (deRhamCup (R := R) (X := X) m k (deRhamClass hβ) (deRhamClass hγ)))
      = deRhamCup (R := R) (X := X) (n + m + 1) k
          (deRhamCup (R := R) (X := X) n m (deRhamClass hα) (deRhamClass hβ))
          (deRhamClass hγ) := by
  rw [deRhamCup_apply hβ hγ, deRhamCup_apply hα (cupClass hβ hγ),
    deRhamCohomologyCast_apply
      (show n + (m + k + 1) + 1 = (n + m + 1) + k + 1 from by omega)
      (cupClass hα (cupClass hβ hγ)),
    deRhamCup_apply hα hβ, deRhamCup_apply (cupClass hα hβ) hγ]
  exact deRhamClass_congr _ _ (cupCocycleZ_assoc_tree α β γ)

/-! ### 商层 cup 单位律（传播形式）

度数约定 `Hⁿ ← Cochain (n+1)` 下，单位（常值 1 的 0-上链）不单独成类——
单位律按「与 𝟙 作 cup 不改变类」陈述。右方向免度数 cast
（`(n+1)+0 ≡ n+1` 由 `Nat.add` 对第二变元递归的定义等价）；左方向需
度数 cast（`0+(n+1)` 非定义等价）+ 双 cast 塌缩（`funext σ; rfl`，
`cochainLenCast_trans` 同款点态论证）。全部无选择公理。 -/

/-- 与常值 1 的 0-上链作 cup 后仍为上循环（左，度数 cast 形）。 -/
theorem isCocycle_cupUnit_left {n : ℕ} {α : Cochain R X (n + 1)} (hα : IsCocycle α) :
    IsCocycle (cochainLenCast (show 0 + (n + 1) = n + 1 from by omega)
      (cupProduct (cochainOfFun (fun _ : X => (1 : R))) α)) := by
  have hOne : coboundary (cochainOfFun (fun _ : X => (1 : R))) = 0 :=
    cochainOfFun_one_isCocycle
  show coboundary (cochainLenCast (show 0 + (n + 1) = n + 1 from by omega)
      (cupProduct (cochainOfFun (fun _ : X => (1 : R))) α)) = 0
  rw [coboundary_cochainLenCast,
    cupProduct_isCocycle (cochainOfFun (fun _ : X => (1 : R))) α hOne hα,
    cochainLenCast_zero]

/-- 与常值 1 的 0-上链作 cup 后仍为上循环（右，免 cast）。 -/
theorem isCocycle_cupUnit_right {n : ℕ} {α : Cochain R X (n + 1)} (hα : IsCocycle α) :
    IsCocycle (cupProduct α (cochainOfFun (fun _ : X => (1 : R)))) := by
  have hOne : coboundary (cochainOfFun (fun _ : X => (1 : R))) = 0 :=
    cochainOfFun_one_isCocycle
  exact cupProduct_isCocycle α _ hα hOne

/-- **类层面左单位律（传播形式）**：与常值 1 的 0-上链作 cup 不改变类
——`[𝟙]∪[α] = [α]`（𝟙 是度 0 上循环，ℕ 度数索引下不单独成类）。 -/
theorem deRhamCup_unit_left {n : ℕ} {α : Cochain R X (n + 1)} (hα : IsCocycle α) :
    deRhamClass (n := n) (isCocycle_cupUnit_left hα) = deRhamClass hα := by
  refine deRhamClass_eq (isCocycle_cupUnit_left hα) hα ?_
  have hid : cochainLenCast (show 0 + (n + 1) = n + 1 from by omega)
      (cochainLenCast (show (n + 1 : ℕ) = 0 + (n + 1) from by omega) α) = α := by
    funext σ
    rfl
  show (cochainLenCast (show 0 + (n + 1) = n + 1 from by omega)
      (cupProduct (cochainOfFun (fun _ : X => (1 : R))) α) - α : Cochain R X (n + 1))
    ∈ coboundaries (R := R) (X := X) n
  rw [cupProduct_unit_left α, hid, sub_self]
  exact zero_mem (coboundaries (R := R) (X := X) n)

/-- **类层面右单位律（传播形式）**：与常值 1 的 0-上链作 cup 不改变类
——`[α]∪[𝟙] = [α]`。 -/
theorem deRhamCup_unit_right {n : ℕ} {α : Cochain R X (n + 1)} (hα : IsCocycle α) :
    deRhamClass (n := n) (isCocycle_cupUnit_right hα) = deRhamClass hα := by
  refine deRhamClass_eq (isCocycle_cupUnit_right hα) hα ?_
  show (cupProduct α (cochainOfFun (fun _ : X => (1 : R))) - α : Cochain R X (n + 1))
    ∈ coboundaries (R := R) (X := X) n
  rw [cupProduct_unit_right α, sub_self]
  exact zero_mem (coboundaries (R := R) (X := X) n)

/-! ### 商层 cup 的 (1,1) 反交换（shuffle-cup 阶梯第一级）

数学：对 1-上闭链 α β，`h(σ) := −α(σ)·β(σ)` 满足链级恒等式
`∂h = α∪β + β∪α`（δh = −α₁₂β₁₂ + α₀₂β₀₂ − α₀₁β₀₁ = α₀₁β₁₂ + α₁₂β₀₁，
用两次闭链条件 α₀₂ = α₁₂ + α₀₁、β₀₂ = β₁₂ + β₀₁）⟹ 和类为零 ⟹
`[α]∪[β] = −[β]∪[α]`。工程：finSum 展开后的 Fin 系数幂 `(−1)^(↑i)`
需 val-rfl 改写（∂²=₀ 战役记录的「Fin 系数幂墙」）。 -/

/-- (1,1) 面引理：cupLeft 1 1 的顶点选择 = 第 2 个余面（(σ₀,σ₁)）。 -/
theorem cupLeft_one_one_eq (σ : SimplexPts X 2) :
    (fun k : Fin 2 => σ (cupLeft 1 1 k)) = coFace σ (2 : Fin 3) := by
  funext k
  refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun j => Fin.elim0 j) k') k
  · rfl
  · rfl

/-- (1,1) 面引理：cupRight 1 1 的顶点选择 = 第 0 个余面（(σ₁,σ₂)）。 -/
theorem cupRight_one_one_eq (σ : SimplexPts X 2) :
    (fun k : Fin 2 => σ (cupRight 1 1 k)) = coFace σ (0 : Fin 3) := by
  funext k
  refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun j => Fin.elim0 j) k') k
  · rfl
  · rfl

/-- **cup 的 (1,1) 反交换链级恒等式**：对 1-上闭链 α β，
`∂h = α∪β + β∪α`，其中 `h(σ) := −α(σ)·β(σ)`（点态）。 -/
theorem coboundary_cup_add_cup {α β : Cochain R X 1}
    (hα : coboundary α = 0) (hβ : coboundary β = 0) :
    coboundary (fun τ : SimplexPts X 1 => -(α τ * β τ))
      = cupProduct α β + cupProduct β α := by
  funext σ
  have hασ' : α (coFace σ (0 : Fin 3)) - α (coFace σ (1 : Fin 3))
      + α (coFace σ (2 : Fin 3)) = 0 := by
    have h2 := congrFun hα σ
    rw [coboundary_apply, finSum_three] at h2
    rw [show ((0 : Fin 3) : ℕ) = 0 from rfl, show ((1 : Fin 3) : ℕ) = 1 from rfl,
        show ((2 : Fin 3) : ℕ) = 2 from rfl] at h2
    simp only [pow_zero, pow_one, pow_two, Pi.zero_apply] at h2
    linear_combination (norm := ring_nf) h2
  have hβσ' : β (coFace σ (0 : Fin 3)) - β (coFace σ (1 : Fin 3))
      + β (coFace σ (2 : Fin 3)) = 0 := by
    have h2 := congrFun hβ σ
    rw [coboundary_apply, finSum_three] at h2
    rw [show ((0 : Fin 3) : ℕ) = 0 from rfl, show ((1 : Fin 3) : ℕ) = 1 from rfl,
        show ((2 : Fin 3) : ℕ) = 2 from rfl] at h2
    simp only [pow_zero, pow_one, pow_two, Pi.zero_apply] at h2
    linear_combination (norm := ring_nf) h2
  have eα : α (coFace σ (1 : Fin 3)) = α (coFace σ (2 : Fin 3)) + α (coFace σ (0 : Fin 3)) := by
    linear_combination (norm := ring_nf) -hασ'
  have eβ : β (coFace σ (1 : Fin 3)) = β (coFace σ (2 : Fin 3)) + β (coFace σ (0 : Fin 3)) := by
    linear_combination (norm := ring_nf) -hβσ'
  show finSum R 3 (fun i : Fin 3 => (-1 : R) ^ (i : ℕ) * -(α (coFace σ i) * β (coFace σ i)))
    = α (fun k : Fin 2 => σ (cupLeft 1 1 k)) * β (fun k : Fin 2 => σ (cupRight 1 1 k))
      + β (fun k : Fin 2 => σ (cupLeft 1 1 k)) * α (fun k : Fin 2 => σ (cupRight 1 1 k))
  rw [cupLeft_one_one_eq, cupRight_one_one_eq, finSum_three,
    show ((0 : Fin 3) : ℕ) = 0 from rfl, show ((1 : Fin 3) : ℕ) = 1 from rfl,
    show ((2 : Fin 3) : ℕ) = 2 from rfl, eα, eβ]
  ring

/-- **⭐ 商层 cup 的 (1,1) 反交换**：`[α]∪[β] = −[β]∪[α]`（deRhamCup 0 0 :
H⁰×H⁰ → H¹——经典 H¹ 上积的反对称性，shuffle-cup 阶梯第一级）。
证明：链级 `∂h = α∪β + β∪α` ⟹ 和类为零（h 为上边缘见证）⟹ 反交换。 -/
theorem deRhamCup_antisymm_zero {α β : Cochain R X 1} (hα : IsCocycle α)
    (hβ : IsCocycle β) :
    deRhamCup 0 0 (deRhamClass hα) (deRhamClass hβ)
      = -deRhamCup 0 0 (deRhamClass hβ) (deRhamClass hα) := by
  have hsum : deRhamCup 0 0 (deRhamClass hα) (deRhamClass hβ)
      + deRhamCup 0 0 (deRhamClass hβ) (deRhamClass hα) = 0 := by
    rw [deRhamCup_apply hα hβ, deRhamCup_apply hβ hα,
      deRhamClass_add (cupClass hα hβ) (cupClass hβ hα), deRhamClass_zero]
    refine deRhamClass_eq _ isCocycle_zero ?_
    refine ⟨fun τ : SimplexPts X 1 => -(α τ * β τ), ?_⟩
    rw [sub_zero]
    funext σ
    rw [Pi.add_apply, cochainLenCast_apply, cochainLenCast_apply]
    exact congrFun (coboundary_cup_add_cup hα hβ) σ
  exact eq_neg_of_add_eq_zero_left hsum

/-! ### 商层 cup 的 (0,q) 交换（传播形式，shuffle-cup 阶梯第二级）

数学：0-上闭链 f 与任意上闭链 β 的 cup 交换——链级差恒为零：
`(f∪β − β∪f)(σ) = (f(σ₀) − f(σ_last))·β(σ) = 0`
（d₀f = 0 在对角边 (σ₀,σ_last) 上直接收口，无需 β 闭、无需归纳）。
工程：cast-证明显式参数化（Nat.zero_add / Nat.add_zero 命名引理，
保证证明项全局同一、rw 可匹配）；对角边经桥引理
`coboundary_cochainZero_eq_d0` 直读 d₀-形（避开 coFace 的 succAbove
管道）；hfx/hfy 的 σ₀/σ_last 项序不可对易，linear_combination 补号。 -/

/-- **桥引理：一般 0-上链的余边界即 d₀**（`f ↦ f ∘ (单点元组)` 的
d₀——与 cochainOfFun-版互补，覆盖任意 0-上链）。 -/
theorem coboundary_cochainZero_eq_d0 (f : Cochain R X 0) :
    coboundary f = d0 (fun x => f (fun _ : Fin 1 => x)) := by
  funext σ
  rw [coboundary_apply, finSum_two, d0]
  have e0 : coFace σ (0 : Fin 2) = (fun _ : Fin 1 => σ 1) := by
    funext k; refine Fin.cases ?_ (fun j => Fin.elim0 j) k; rfl
  have e1 : coFace σ (1 : Fin 2) = (fun _ : Fin 1 => σ 0) := by
    funext k; refine Fin.cases ?_ (fun j => Fin.elim0 j) k; rfl
  rw [e0, e1]
  rw [show ((0 : Fin 2) : ℕ) = 0 from rfl, show ((1 : Fin 2) : ℕ) = 1 from rfl]
  simp only [pow_zero, pow_one]
  ring

/-- (0,q) 交换的 IsCocycle 助手（左）。 -/
theorem isCocycle_cupZero_left {r : ℕ} (f : Cochain R X 0) (hf : coboundary f = 0)
    {β : Cochain R X (r + 1)} (hβ : IsCocycle β) (H₁ : 0 + (r + 1) = r + 1) :
    IsCocycle (cochainLenCast H₁ (cupProduct f β)) := by
  show coboundary (cochainLenCast H₁ (cupProduct f β)) = 0
  rw [coboundary_cochainLenCast, cupProduct_isCocycle f β hf hβ, cochainLenCast_zero]

/-- (0,q) 交换的 IsCocycle 助手（右）。 -/
theorem isCocycle_cupZero_right {r : ℕ} (f : Cochain R X 0) (hf : coboundary f = 0)
    {β : Cochain R X (r + 1)} (hβ : IsCocycle β) (H₂ : (r + 1) + 0 = r + 1) :
    IsCocycle (cochainLenCast H₂ (cupProduct β f)) := by
  show coboundary (cochainLenCast H₂ (cupProduct β f)) = 0
  rw [coboundary_cochainLenCast, cupProduct_isCocycle β f hβ hf, cochainLenCast_zero]

/-- (0,q) 交换的链级恒等式：链级差恒为零（对角边论证）。 -/
theorem cup_zero_cocycle_comm {r : ℕ} (f : Cochain R X 0) (hf : coboundary f = 0)
    (β : Cochain R X (r + 1)) (H₁ : 0 + (r + 1) = r + 1) (H₂ : (r + 1) + 0 = r + 1) :
    cochainLenCast H₁ (cupProduct f β) = cochainLenCast H₂ (cupProduct β f) := by
  funext σ
  show (cupProduct f β) (fun k : Fin (0 + (r + 1) + 1) =>
      σ (Fin.cast (show 0 + (r + 1) + 1 = (r + 1) + 1 from by rw [H₁]) k))
    = cupProduct β f σ
  rw [cupProduct_apply, cupProduct_apply]
  -- 左 f-元组（带 Fin.cast 包装）= (σ₀) 单点元组
  have e0 : (fun k : Fin 1 => σ (Fin.cast (show 0 + (r + 1) + 1 = (r + 1) + 1 from by
        rw [H₁]) (cupLeft 0 (r + 1) k))) = (fun _ : Fin 1 => σ 0) := by
    funext k
    apply congrArg σ
    apply Fin.ext
    show (Fin.cast (show 0 + (r + 1) + 1 = (r + 1) + 1 from by rw [H₁])
        (cupLeft 0 (r + 1) k)).val = (0 : Fin (r + 2)).val
    rw [Fin.val_cast]
    refine Fin.cases ?_ (fun j => Fin.elim0 j) k
    rfl
  -- 左 β-元组（带包装）= σ 本身
  have eB : (fun k : Fin (r + 2) => σ (Fin.cast (show 0 + (r + 1) + 1 = (r + 1) + 1 from by
        rw [H₁]) (cupRight 0 (r + 1) k))) = σ := by
    funext k
    apply congrArg σ
    apply Fin.ext
    show (Fin.cast (show 0 + (r + 1) + 1 = (r + 1) + 1 from by rw [H₁])
        (cupRight 0 (r + 1) k)).val = k.val
    show (Fin.cast (show 0 + ((r + 1) + 1) = 0 + (r + 1) + 1 from by omega)
        (Fin.natAdd 0 k)).val = k.val
    rw [Fin.val_cast, Fin.val_natAdd, Nat.zero_add]
  -- 右 β-元组 = σ 本身
  have eB2 : (fun k : Fin (r + 2) => σ (cupLeft (r + 1) 0 k)) = σ := by
    funext k
    apply congrArg σ
    apply Fin.ext
    show (cupLeft (r + 1) 0 k).val = k.val
    rfl
  -- 右 f-元组 = (σ_last) 单点元组
  have e1 : (fun k : Fin 1 => σ (cupRight (r + 1) 0 k)) =
      (fun _ : Fin 1 => σ (Fin.last (r + 1))) := by
    funext k
    apply congrArg σ
    apply Fin.ext
    show (Fin.cast (show (r + 1) + 1 + 0 = (r + 1) + 0 + 1 from by omega)
        (Fin.natAdd (r + 1) k)).val = (Fin.last (r + 1)).val
    rw [Fin.val_cast, Fin.val_natAdd, Fin.val_last]
    refine Fin.cases ?_ (fun j => Fin.elim0 j) k
    rfl
  rw [e0, eB, eB2, e1]
  -- 对角边论证：d₀f = 0 在 (σ₀, σ_last) 上（hf 点态 + 桥引理传递）
  have hd := congrFun (coboundary_cochainZero_eq_d0 f)
      (fun k : Fin 2 => if k = 0 then σ 0 else σ (Fin.last (r + 1)))
  rw [d0] at hd
  have hfy : f (fun _ : Fin 1 => σ (Fin.last (r + 1)))
      - f (fun _ : Fin 1 => σ 0) = 0 :=
    hd.symm.trans (congrFun hf _)
  have hfx : f (fun _ : Fin 1 => σ 0)
      - f (fun _ : Fin 1 => σ (Fin.last (r + 1))) = 0 := by
    linear_combination (norm := ring_nf) -hfy
  linear_combination (norm := ring_nf) hfx * (β σ)

/-- **⭐ 商层 cup 的 (0,q) 交换（传播形式）**：0-上闭链 f 与任意上闭链 β
的 cup 交换（链级差恒为零——d₀f = 0 在对角边 (σ₀,σ_last) 上直接收口）。 -/
theorem deRhamCup_comm_zero {r : ℕ} (f : Cochain R X 0) (hf : coboundary f = 0)
    {β : Cochain R X (r + 1)} (hβ : IsCocycle β) :
    deRhamClass (n := r) (isCocycle_cupZero_left f hf hβ (Nat.zero_add (r + 1)))
      = deRhamClass (n := r) (isCocycle_cupZero_right f hf hβ (Nat.add_zero (r + 1))) := by
  have H₁ : 0 + (r + 1) = r + 1 := Nat.zero_add (r + 1)
  have H₂ : (r + 1) + 0 = r + 1 := Nat.add_zero (r + 1)
  refine deRhamClass_eq (isCocycle_cupZero_left f hf hβ H₁)
    (isCocycle_cupZero_right f hf hβ H₂) ?_
  refine ⟨0, ?_⟩
  rw [← coboundaryLinear_apply, coboundaryLinear.map_zero,
    cup_zero_cocycle_comm f hf β H₁ H₂, sub_self]

/-! ### 商层 cup 的 (1,2) 反交换同伦（shuffle-cup 阶梯第三级）

数学：对 1-上闭链 α、2-上闭链 β，h(τ) := −α(τ₀,τ₂)·β(τ)（α 取跳边
(τ₀,τ₂)——头 (τ₀) + 尾 (τ₂) 跳过中段 τ₁）满足链级恒等式
∂h = α∪β − β∪α（经典度数 (1,2)，分级符号 (−1)² = +1）。
数值验证：s = −1 唯一（一般 φ-cocycle 网格全点态）。工程：Fin 3-元组
需三层 Fin.cases 嵌套；h 的 α-跳边经 skipEdge-面引理 ×4 与四面体四面对齐。 -/

/-- (1,2) 面引理：h 的 α-跳边在四面体的四个面上的一致性（每面一条）。 -/
theorem skipEdge_face0 (σ : SimplexPts X 3) :
    (fun k : Fin 2 => if k = 0 then (coFace σ (0 : Fin 4)) 0 else (coFace σ (0 : Fin 4)) 2)
      = (fun k : Fin 2 => if k = 0 then σ 1 else σ 3) := by
  funext k
  refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun j => Fin.elim0 j) k') k
  · rfl
  · rfl

theorem skipEdge_face1 (σ : SimplexPts X 3) :
    (fun k : Fin 2 => if k = 0 then (coFace σ (1 : Fin 4)) 0 else (coFace σ (1 : Fin 4)) 2)
      = (fun k : Fin 2 => if k = 0 then σ 0 else σ 3) := by
  funext k
  refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun j => Fin.elim0 j) k') k
  · rfl
  · rfl

theorem skipEdge_face2 (σ : SimplexPts X 3) :
    (fun k : Fin 2 => if k = 0 then (coFace σ (2 : Fin 4)) 0 else (coFace σ (2 : Fin 4)) 2)
      = (fun k : Fin 2 => if k = 0 then σ 0 else σ 3) := by
  funext k
  refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun j => Fin.elim0 j) k') k
  · rfl
  · rfl

theorem skipEdge_face3 (σ : SimplexPts X 3) :
    (fun k : Fin 2 => if k = 0 then (coFace σ (3 : Fin 4)) 0 else (coFace σ (3 : Fin 4)) 2)
      = (fun k : Fin 2 => if k = 0 then σ 0 else σ 2) := by
  funext k
  refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun j => Fin.elim0 j) k') k
  · rfl
  · rfl

/-- **cup 的 (1,2) 反交换同伦链级恒等式**：对 1-上闭链 α、2-上闭链 β，
`∂h = α∪β − β∪α`，其中 `h(τ) := −α(τ₀,τ₂)·β(τ)`（α 取跳边）。 -/
theorem coboundary_cupSkip_12 (α : Cochain R X 1) (β : Cochain R X 2)
    (hα : coboundary α = 0) (hβ : coboundary β = 0) :
    coboundary (fun τ : SimplexPts X 2 =>
        -(α (fun k : Fin 2 => if k = 0 then τ 0 else τ 2) * β τ))
      = cupProduct α β - cupProduct β α := by
  funext σ
  -- β-面桥引理：coFace σ i 元组 = if-形元组（×4）
  have bB0 : β (coFace σ (0 : Fin 4)) = β (fun k : Fin 3 => if k = 0 then σ 1
      else if k = 1 then σ 2 else σ 3) := by
    apply congrArg β
    funext k
    refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun k'' => Fin.cases ?_ (fun j => Fin.elim0 j) k'') k') k
    · rfl
    · rfl
    · rfl
  have bB1 : β (coFace σ (1 : Fin 4)) = β (fun k : Fin 3 => if k = 0 then σ 0
      else if k = 1 then σ 2 else σ 3) := by
    apply congrArg β
    funext k
    refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun k'' => Fin.cases ?_ (fun j => Fin.elim0 j) k'') k') k
    · rfl
    · rfl
    · rfl
  have bB2 : β (coFace σ (2 : Fin 4)) = β (fun k : Fin 3 => if k = 0 then σ 0
      else if k = 1 then σ 1 else σ 3) := by
    apply congrArg β
    funext k
    refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun k'' => Fin.cases ?_ (fun j => Fin.elim0 j) k'') k') k
    · rfl
    · rfl
    · rfl
  have bB3 : β (coFace σ (3 : Fin 4)) = β (fun k : Fin 3 => if k = 0 then σ 0
      else if k = 1 then σ 1 else σ 2) := by
    apply congrArg β
    funext k
    refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun k'' => Fin.cases ?_ (fun j => Fin.elim0 j) k'') k') k
    · rfl
    · rfl
    · rfl
  -- cup-元组桥引理（×4）：cupLeft/cupRight 元组 = if-形元组
  have eL : (fun k : Fin 2 => σ (cupLeft 1 2 k)) = (fun k : Fin 2 =>
      if k = 0 then σ 0 else σ 1) := by
    funext k
    refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun j => Fin.elim0 j) k') k
    · rfl
    · rfl
  have eR : (fun k : Fin 3 => σ (cupRight 1 2 k)) = (fun k : Fin 3 =>
      if k = 0 then σ 1 else if k = 1 then σ 2 else σ 3) := by
    funext k
    refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun k'' => Fin.cases ?_ (fun j => Fin.elim0 j) k'') k') k
    · rfl
    · rfl
    · rfl
  have eL2 : (fun k : Fin 3 => σ (cupLeft 2 1 k)) = (fun k : Fin 3 =>
      if k = 0 then σ 0 else if k = 1 then σ 1 else σ 2) := by
    funext k
    refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun k'' => Fin.cases ?_ (fun j => Fin.elim0 j) k'') k') k
    · rfl
    · rfl
    · rfl
  have eR2 : (fun k : Fin 2 => σ (cupRight 2 1 k)) = (fun k : Fin 2 =>
      if k = 0 then σ 2 else σ 3) := by
    funext k
    refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun j => Fin.elim0 j) k') k
    · rfl
    · rfl
  -- δβ-关系的 if-形代入式（经 coFace-桥 + h4 线性组合）
  have hβrelsub : β (fun k : Fin 3 => if k = 0 then σ 0 else if k = 1 then σ 2 else σ 3)
      = β (fun k : Fin 3 => if k = 0 then σ 1 else if k = 1 then σ 2 else σ 3)
        + β (fun k : Fin 3 => if k = 0 then σ 0 else if k = 1 then σ 1 else σ 3)
        - β (fun k : Fin 3 => if k = 0 then σ 0 else if k = 1 then σ 1 else σ 2) := by
    have h4 := congrFun hβ σ
    rw [coboundary_apply, finSum_four] at h4
    rw [show ((0 : Fin 4) : ℕ) = 0 from rfl, show ((1 : Fin 4) : ℕ) = 1 from rfl,
        show ((2 : Fin 4) : ℕ) = 2 from rfl, show ((3 : Fin 4) : ℕ) = 3 from rfl] at h4
    simp only [pow_zero, pow_one, pow_two, Pi.zero_apply] at h4
    rw [bB0, bB1, bB2, bB3] at h4
    linear_combination (norm := ring_nf) -h4
  have hα012 : α (fun k : Fin 2 => if k = 0 then σ 0 else σ 2)
      = α (fun k : Fin 2 => if k = 0 then σ 1 else σ 2)
        + α (fun k : Fin 2 => if k = 0 then σ 0 else σ 1) := by
    have h2 := congrFun hα (coFace σ (3 : Fin 4))
    rw [coboundary_apply, finSum_three] at h2
    have e0 : coFace (coFace σ (3 : Fin 4)) (0 : Fin 3) =
        (fun k : Fin 2 => if k = 0 then σ 1 else σ 2) := by
      funext k; refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun j => Fin.elim0 j) k') k
      · rfl
      · rfl
    have e1 : coFace (coFace σ (3 : Fin 4)) (1 : Fin 3) =
        (fun k : Fin 2 => if k = 0 then σ 0 else σ 2) := by
      funext k; refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun j => Fin.elim0 j) k') k
      · rfl
      · rfl
    have e2 : coFace (coFace σ (3 : Fin 4)) (2 : Fin 3) =
        (fun k : Fin 2 => if k = 0 then σ 0 else σ 1) := by
      funext k; refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun j => Fin.elim0 j) k') k
      · rfl
      · rfl
    rw [e0, e1, e2, show ((0 : Fin 3) : ℕ) = 0 from rfl,
        show ((1 : Fin 3) : ℕ) = 1 from rfl, show ((2 : Fin 3) : ℕ) = 2 from rfl] at h2
    simp only [pow_zero, pow_one, pow_two, Pi.zero_apply] at h2
    linear_combination (norm := ring_nf) -h2
  have hα023 : α (fun k : Fin 2 => if k = 0 then σ 0 else σ 3)
      = α (fun k : Fin 2 => if k = 0 then σ 0 else σ 2)
        + α (fun k : Fin 2 => if k = 0 then σ 2 else σ 3) := by
    have h2 := congrFun hα (coFace σ (1 : Fin 4))
    rw [coboundary_apply, finSum_three] at h2
    have e0 : coFace (coFace σ (1 : Fin 4)) (0 : Fin 3) =
        (fun k : Fin 2 => if k = 0 then σ 2 else σ 3) := by
      funext k; refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun j => Fin.elim0 j) k') k
      · rfl
      · rfl
    have e1 : coFace (coFace σ (1 : Fin 4)) (1 : Fin 3) =
        (fun k : Fin 2 => if k = 0 then σ 0 else σ 3) := by
      funext k; refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun j => Fin.elim0 j) k') k
      · rfl
      · rfl
    have e2 : coFace (coFace σ (1 : Fin 4)) (2 : Fin 3) =
        (fun k : Fin 2 => if k = 0 then σ 0 else σ 2) := by
      funext k; refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun j => Fin.elim0 j) k') k
      · rfl
      · rfl
    rw [e0, e1, e2, show ((0 : Fin 3) : ℕ) = 0 from rfl,
        show ((1 : Fin 3) : ℕ) = 1 from rfl, show ((2 : Fin 3) : ℕ) = 2 from rfl] at h2
    simp only [pow_zero, pow_one, pow_two, Pi.zero_apply] at h2
    linear_combination (norm := ring_nf) -h2
  have hα123 : α (fun k : Fin 2 => if k = 0 then σ 1 else σ 3)
      = α (fun k : Fin 2 => if k = 0 then σ 1 else σ 2)
        + α (fun k : Fin 2 => if k = 0 then σ 2 else σ 3) := by
    have h2 := congrFun hα (coFace σ (0 : Fin 4))
    rw [coboundary_apply, finSum_three] at h2
    have e0 : coFace (coFace σ (0 : Fin 4)) (0 : Fin 3) =
        (fun k : Fin 2 => if k = 0 then σ 2 else σ 3) := by
      funext k; refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun j => Fin.elim0 j) k') k
      · rfl
      · rfl
    have e1 : coFace (coFace σ (0 : Fin 4)) (1 : Fin 3) =
        (fun k : Fin 2 => if k = 0 then σ 1 else σ 3) := by
      funext k; refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun j => Fin.elim0 j) k') k
      · rfl
      · rfl
    have e2 : coFace (coFace σ (0 : Fin 4)) (2 : Fin 3) =
        (fun k : Fin 2 => if k = 0 then σ 1 else σ 2) := by
      funext k; refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun j => Fin.elim0 j) k') k
      · rfl
      · rfl
    rw [e0, e1, e2, show ((0 : Fin 3) : ℕ) = 0 from rfl,
        show ((1 : Fin 3) : ℕ) = 1 from rfl, show ((2 : Fin 3) : ℕ) = 2 from rfl] at h2
    simp only [pow_zero, pow_one, pow_two, Pi.zero_apply] at h2
    linear_combination (norm := ring_nf) -h2
  -- β-四面关系（δβ-点态）
  have hβσ : β (coFace σ (1 : Fin 4))
      = β (coFace σ (0 : Fin 4)) + β (coFace σ (2 : Fin 4))
        - β (coFace σ (3 : Fin 4)) := by
    have h4 := congrFun hβ σ
    rw [coboundary_apply, finSum_four] at h4
    rw [show ((0 : Fin 4) : ℕ) = 0 from rfl, show ((1 : Fin 4) : ℕ) = 1 from rfl,
        show ((2 : Fin 4) : ℕ) = 2 from rfl, show ((3 : Fin 4) : ℕ) = 3 from rfl] at h4
    simp only [pow_zero, pow_one, pow_two, Pi.zero_apply] at h4
    linear_combination (norm := ring_nf) -h4
  show finSum R 4 (fun i : Fin 4 => (-1 : R) ^ (i : ℕ) *
      -(α (fun k : Fin 2 => if k = 0 then (coFace σ i) 0 else (coFace σ i) 2)
        * β (coFace σ i)))
    = (cupProduct α β - cupProduct β α) σ
  rw [Pi.sub_apply, cupProduct_apply, cupProduct_apply, finSum_four,
    show ((0 : Fin 4) : ℕ) = 0 from rfl, show ((1 : Fin 4) : ℕ) = 1 from rfl,
    show ((2 : Fin 4) : ℕ) = 2 from rfl, show ((3 : Fin 4) : ℕ) = 3 from rfl,
    skipEdge_face0, skipEdge_face1, skipEdge_face2, skipEdge_face3,
    eL, eR, eL2, eR2,
    hα023, hα012, hα123,
    bB0, bB1, bB2, bB3,
    hβrelsub]
  simp only [pow_zero, pow_one]
  ring

-- ======== shuffle-cup (2,1) anticommutativity homotopy (rung 4) ========

/-- (2,1) 面引理：face₀ = (σ₁,σ₂,σ₃) 的 (0,1)-边 = (σ₁,σ₂)。 -/
theorem edge01_face0 (σ : SimplexPts X 3) :
    (fun k : Fin 2 => if k = 0 then (coFace σ (0 : Fin 4)) 0 else (coFace σ (0 : Fin 4)) 1)
      = (fun k : Fin 2 => if k = 0 then σ 1 else σ 2) := by
  funext k
  refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun j => Fin.elim0 j) k') k
  · rfl
  · rfl

/-- (2,1) 面引理：face₀ 的 (1,2)-边 = (σ₂,σ₃)。 -/
theorem edge12_face0 (σ : SimplexPts X 3) :
    (fun k : Fin 2 => if k = 0 then (coFace σ (0 : Fin 4)) 1 else (coFace σ (0 : Fin 4)) 2)
      = (fun k : Fin 2 => if k = 0 then σ 2 else σ 3) := by
  funext k
  refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun j => Fin.elim0 j) k') k
  · rfl
  · rfl

/-- (2,1) 面引理：face₁ = (σ₀,σ₂,σ₃) 的 (0,1)-边 = (σ₀,σ₂)。 -/
theorem edge01_face1 (σ : SimplexPts X 3) :
    (fun k : Fin 2 => if k = 0 then (coFace σ (1 : Fin 4)) 0 else (coFace σ (1 : Fin 4)) 1)
      = (fun k : Fin 2 => if k = 0 then σ 0 else σ 2) := by
  funext k
  refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun j => Fin.elim0 j) k') k
  · rfl
  · rfl

/-- (2,1) 面引理：face₁ 的 (1,2)-边 = (σ₂,σ₃)。 -/
theorem edge12_face1 (σ : SimplexPts X 3) :
    (fun k : Fin 2 => if k = 0 then (coFace σ (1 : Fin 4)) 1 else (coFace σ (1 : Fin 4)) 2)
      = (fun k : Fin 2 => if k = 0 then σ 2 else σ 3) := by
  funext k
  refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun j => Fin.elim0 j) k') k
  · rfl
  · rfl

/-- (2,1) 面引理：face₂ = (σ₀,σ₁,σ₃) 的 (0,1)-边 = (σ₀,σ₁)。 -/
theorem edge01_face2 (σ : SimplexPts X 3) :
    (fun k : Fin 2 => if k = 0 then (coFace σ (2 : Fin 4)) 0 else (coFace σ (2 : Fin 4)) 1)
      = (fun k : Fin 2 => if k = 0 then σ 0 else σ 1) := by
  funext k
  refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun j => Fin.elim0 j) k') k
  · rfl
  · rfl

/-- (2,1) 面引理：face₂ 的 (1,2)-边 = (σ₁,σ₃)。 -/
theorem edge12_face2 (σ : SimplexPts X 3) :
    (fun k : Fin 2 => if k = 0 then (coFace σ (2 : Fin 4)) 1 else (coFace σ (2 : Fin 4)) 2)
      = (fun k : Fin 2 => if k = 0 then σ 1 else σ 3) := by
  funext k
  refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun j => Fin.elim0 j) k') k
  · rfl
  · rfl

/-- (2,1) 面引理：face₃ = (σ₀,σ₁,σ₂) 的 (0,1)-边 = (σ₀,σ₁)。 -/
theorem edge01_face3 (σ : SimplexPts X 3) :
    (fun k : Fin 2 => if k = 0 then (coFace σ (3 : Fin 4)) 0 else (coFace σ (3 : Fin 4)) 1)
      = (fun k : Fin 2 => if k = 0 then σ 0 else σ 1) := by
  funext k
  refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun j => Fin.elim0 j) k') k
  · rfl
  · rfl

/-- (2,1) 面引理：face₃ 的 (1,2)-边 = (σ₁,σ₂)。 -/
theorem edge12_face3 (σ : SimplexPts X 3) :
    (fun k : Fin 2 => if k = 0 then (coFace σ (3 : Fin 4)) 1 else (coFace σ (3 : Fin 4)) 2)
      = (fun k : Fin 2 => if k = 0 then σ 1 else σ 2) := by
  funext k
  refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun j => Fin.elim0 j) k') k
  · rfl
  · rfl

/-- (2,1) cup-元组桥：cupLeft 2 1 元组 = (σ₀,σ₁,σ₂)。 -/
theorem cupL21 (σ : SimplexPts X 3) :
    (fun k : Fin 3 => σ (cupLeft 2 1 k))
      = (fun k : Fin 3 => if k = 0 then σ 0 else if k = 1 then σ 1 else σ 2) := by
  funext k
  refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun k'' => Fin.cases ?_ (fun j => Fin.elim0 j) k'') k') k
  · rfl
  · rfl
  · rfl

/-- (2,1) cup-元组桥：cupRight 2 1 元组 = (σ₂,σ₃)。 -/
theorem cupR21 (σ : SimplexPts X 3) :
    (fun k : Fin 2 => σ (cupRight 2 1 k))
      = (fun k : Fin 2 => if k = 0 then σ 2 else σ 3) := by
  funext k
  refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun j => Fin.elim0 j) k') k
  · rfl
  · rfl

/-- (2,1) cup-元组桥：cupLeft 1 2 元组 = (σ₀,σ₁)。 -/
theorem cupL12 (σ : SimplexPts X 3) :
    (fun k : Fin 2 => σ (cupLeft 1 2 k))
      = (fun k : Fin 2 => if k = 0 then σ 0 else σ 1) := by
  funext k
  refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun j => Fin.elim0 j) k') k
  · rfl
  · rfl

/-- (2,1) cup-元组桥：cupRight 1 2 元组 = (σ₁,σ₂,σ₃)。 -/
theorem cupR12 (σ : SimplexPts X 3) :
    (fun k : Fin 3 => σ (cupRight 1 2 k))
      = (fun k : Fin 3 => if k = 0 then σ 1 else if k = 1 then σ 2 else σ 3) := by
  funext k
  refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun k'' => Fin.cases ?_ (fun j => Fin.elim0 j) k'') k') k
  · rfl
  · rfl
  · rfl

/-- (2,1) α-面桥：coFace σ 0 元组 = if-形元组（元组等价形，rw 可匹配）。 -/
theorem alphaFace0 (σ : SimplexPts X 3) :
    (coFace σ (0 : Fin 4))
      = (fun k : Fin 3 => if k = 0 then σ 1 else if k = 1 then σ 2 else σ 3) := by
  funext k
  refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun k'' => Fin.cases ?_ (fun j => Fin.elim0 j) k'') k') k
  · rfl
  · rfl
  · rfl

/-- (2,1) α-面桥：coFace σ 1 元组 = if-形元组。 -/
theorem alphaFace1 (σ : SimplexPts X 3) :
    (coFace σ (1 : Fin 4))
      = (fun k : Fin 3 => if k = 0 then σ 0 else if k = 1 then σ 2 else σ 3) := by
  funext k
  refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun k'' => Fin.cases ?_ (fun j => Fin.elim0 j) k'') k') k
  · rfl
  · rfl
  · rfl

/-- (2,1) α-面桥：coFace σ 2 元组 = if-形元组。 -/
theorem alphaFace2 (σ : SimplexPts X 3) :
    (coFace σ (2 : Fin 4))
      = (fun k : Fin 3 => if k = 0 then σ 0 else if k = 1 then σ 1 else σ 3) := by
  funext k
  refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun k'' => Fin.cases ?_ (fun j => Fin.elim0 j) k'') k') k
  · rfl
  · rfl
  · rfl

/-- (2,1) α-面桥：coFace σ 3 元组 = if-形元组。 -/
theorem alphaFace3 (σ : SimplexPts X 3) :
    (coFace σ (3 : Fin 4))
      = (fun k : Fin 3 => if k = 0 then σ 0 else if k = 1 then σ 1 else σ 2) := by
  funext k
  refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun k'' => Fin.cases ?_ (fun j => Fin.elim0 j) k'') k') k
  · rfl
  · rfl
  · rfl

/-- **cup 的 (2,1) 交换同伦链级恒等式**：对 2-上闭链 α、1-上闭链 β，
`∂h = α∪β − β∪α`，其中 `h(τ) := α(τ)·(β(τ₀,τ₁) + β(τ₁,τ₂))`
（Steenrod ⋃₁ 的 (2,1)-特例：全 α 扫掠 × β 前向边对）。 -/
theorem coboundary_cupSweep_21 (α : Cochain R X 2) (β : Cochain R X 1)
    (hα : coboundary α = 0) (hβ : coboundary β = 0) :
    coboundary (fun τ : SimplexPts X 2 =>
        α τ * (β (fun k : Fin 2 => if k = 0 then τ 0 else τ 1)
          + β (fun k : Fin 2 => if k = 0 then τ 1 else τ 2)))
      = cupProduct α β - cupProduct β α := by
  funext σ
  -- δβ-边关系 1（δβ 点态于 coFace σ 3 = (σ₀,σ₁,σ₂)）：β(σ₁,σ₂) = β(σ₀,σ₂) − β(σ₀,σ₁)
  have hβ12 : β (fun k : Fin 2 => if k = 0 then σ 1 else σ 2)
      = β (fun k : Fin 2 => if k = 0 then σ 0 else σ 2)
        - β (fun k : Fin 2 => if k = 0 then σ 0 else σ 1) := by
    have h3 := congrFun hβ (coFace σ (3 : Fin 4))
    rw [coboundary_apply, finSum_three] at h3
    rw [show ((0 : Fin 3) : ℕ) = 0 from rfl, show ((1 : Fin 3) : ℕ) = 1 from rfl,
        show ((2 : Fin 3) : ℕ) = 2 from rfl] at h3
    simp only [pow_zero, pow_one, pow_two, Pi.zero_apply] at h3
    have e0 : coFace (coFace σ (3 : Fin 4)) (0 : Fin 3)
        = (fun k : Fin 2 => if k = 0 then σ 1 else σ 2) := by
      funext k; refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun j => Fin.elim0 j) k') k
      · rfl
      · rfl
    have e1 : coFace (coFace σ (3 : Fin 4)) (1 : Fin 3)
        = (fun k : Fin 2 => if k = 0 then σ 0 else σ 2) := by
      funext k; refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun j => Fin.elim0 j) k') k
      · rfl
      · rfl
    have e2 : coFace (coFace σ (3 : Fin 4)) (2 : Fin 3)
        = (fun k : Fin 2 => if k = 0 then σ 0 else σ 1) := by
      funext k; refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun j => Fin.elim0 j) k') k
      · rfl
      · rfl
    rw [e0, e1, e2] at h3
    linear_combination (norm := ring_nf) h3
  -- δβ-边关系 2（δβ 点态于 coFace σ 1 = (σ₀,σ₂,σ₃)）：β(σ₂,σ₃) = β(σ₀,σ₃) − β(σ₀,σ₂)
  have hβ23 : β (fun k : Fin 2 => if k = 0 then σ 2 else σ 3)
      = β (fun k : Fin 2 => if k = 0 then σ 0 else σ 3)
        - β (fun k : Fin 2 => if k = 0 then σ 0 else σ 2) := by
    have h3 := congrFun hβ (coFace σ (1 : Fin 4))
    rw [coboundary_apply, finSum_three] at h3
    rw [show ((0 : Fin 3) : ℕ) = 0 from rfl, show ((1 : Fin 3) : ℕ) = 1 from rfl,
        show ((2 : Fin 3) : ℕ) = 2 from rfl] at h3
    simp only [pow_zero, pow_one, pow_two, Pi.zero_apply] at h3
    have e0 : coFace (coFace σ (1 : Fin 4)) (0 : Fin 3)
        = (fun k : Fin 2 => if k = 0 then σ 2 else σ 3) := by
      funext k; refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun j => Fin.elim0 j) k') k
      · rfl
      · rfl
    have e1 : coFace (coFace σ (1 : Fin 4)) (1 : Fin 3)
        = (fun k : Fin 2 => if k = 0 then σ 0 else σ 3) := by
      funext k; refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun j => Fin.elim0 j) k') k
      · rfl
      · rfl
    have e2 : coFace (coFace σ (1 : Fin 4)) (2 : Fin 3)
        = (fun k : Fin 2 => if k = 0 then σ 0 else σ 2) := by
      funext k; refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun j => Fin.elim0 j) k') k
      · rfl
      · rfl
    rw [e0, e1, e2] at h3
    linear_combination (norm := ring_nf) h3
  -- δβ-边关系 3（δβ 点态于 coFace σ 2 = (σ₀,σ₁,σ₃)）：β(σ₁,σ₃) = β(σ₀,σ₃) − β(σ₀,σ₁)
  have hβ13 : β (fun k : Fin 2 => if k = 0 then σ 1 else σ 3)
      = β (fun k : Fin 2 => if k = 0 then σ 0 else σ 3)
        - β (fun k : Fin 2 => if k = 0 then σ 0 else σ 1) := by
    have h3 := congrFun hβ (coFace σ (2 : Fin 4))
    rw [coboundary_apply, finSum_three] at h3
    rw [show ((0 : Fin 3) : ℕ) = 0 from rfl, show ((1 : Fin 3) : ℕ) = 1 from rfl,
        show ((2 : Fin 3) : ℕ) = 2 from rfl] at h3
    simp only [pow_zero, pow_one, pow_two, Pi.zero_apply] at h3
    have e0 : coFace (coFace σ (2 : Fin 4)) (0 : Fin 3)
        = (fun k : Fin 2 => if k = 0 then σ 1 else σ 3) := by
      funext k; refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun j => Fin.elim0 j) k') k
      · rfl
      · rfl
    have e1 : coFace (coFace σ (2 : Fin 4)) (1 : Fin 3)
        = (fun k : Fin 2 => if k = 0 then σ 0 else σ 3) := by
      funext k; refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun j => Fin.elim0 j) k') k
      · rfl
      · rfl
    have e2 : coFace (coFace σ (2 : Fin 4)) (2 : Fin 3)
        = (fun k : Fin 2 => if k = 0 then σ 0 else σ 1) := by
      funext k; refine Fin.cases ?_ (fun k' => Fin.cases ?_ (fun j => Fin.elim0 j) k') k
      · rfl
      · rfl
    rw [e0, e1, e2] at h3
    linear_combination (norm := ring_nf) h3
  -- δα(σ) = 0（if-形原子；α-面桥消 coFace-形）
  have hαD : α (fun k : Fin 3 => if k = 0 then σ 1 else if k = 1 then σ 2 else σ 3)
      - α (fun k : Fin 3 => if k = 0 then σ 0 else if k = 1 then σ 2 else σ 3)
      + α (fun k : Fin 3 => if k = 0 then σ 0 else if k = 1 then σ 1 else σ 3)
      - α (fun k : Fin 3 => if k = 0 then σ 0 else if k = 1 then σ 1 else σ 2) = 0 := by
    have h4 := congrFun hα σ
    rw [coboundary_apply, finSum_four] at h4
    rw [show ((0 : Fin 4) : ℕ) = 0 from rfl, show ((1 : Fin 4) : ℕ) = 1 from rfl,
        show ((2 : Fin 4) : ℕ) = 2 from rfl, show ((3 : Fin 4) : ℕ) = 3 from rfl] at h4
    simp only [pow_zero, pow_one, pow_two, Pi.zero_apply] at h4
    rw [alphaFace0, alphaFace1, alphaFace2, alphaFace3] at h4
    linear_combination (norm := ring_nf) h4
  show finSum R 4 (fun i : Fin 4 => (-1 : R) ^ (i : ℕ) *
      (α (coFace σ i)
      * (β (fun k : Fin 2 => if k = 0 then (coFace σ i) 0 else (coFace σ i) 1)
        + β (fun k : Fin 2 => if k = 0 then (coFace σ i) 1 else (coFace σ i) 2))))
    = (cupProduct α β - cupProduct β α) σ
  rw [Pi.sub_apply, cupProduct_apply, cupProduct_apply, finSum_four,
    show ((0 : Fin 4) : ℕ) = 0 from rfl, show ((1 : Fin 4) : ℕ) = 1 from rfl,
    show ((2 : Fin 4) : ℕ) = 2 from rfl, show ((3 : Fin 4) : ℕ) = 3 from rfl,
    edge01_face0, edge12_face0, edge01_face1, edge12_face1,
    edge01_face2, edge12_face2, edge01_face3, edge12_face3,
    cupL21, cupR21, cupL12, cupR12,
    alphaFace0, alphaFace1, alphaFace2, alphaFace3,
    hβ23, hβ12, hβ13]
  simp only [pow_zero, pow_one]
  linear_combination (norm := ring_nf)
    (β (fun k : Fin 2 => if k = 0 then σ 0 else σ 3)) • hαD

end CupCohomologyQuotient

end SDG.DifferentialForms
