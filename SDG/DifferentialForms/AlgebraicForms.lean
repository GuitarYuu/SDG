import SDG.LieBracket
import SDG.DifferentialForms.Core

/-!
# 代数形式层与 Koszul 外微分（场变元）

F 线的外微分第三层：**场变元代数形式**——变元是全局向量场
`TangentVectorField`（每点有定义），Koszul 公式的外微分**零 transport
依赖**（不需要切向量的平行搬运/联络；对比点态形式层的
ScratchStokesTan T5 障碍）。

输入件全部主线就绪：`directionalDerivative`（Core，KL 公理）、
`lieBracket`（LieBracket.lean，Property W 路线 Kock I.9）、向量场
的 Zero/Add/SMul/Module 结构（TangentBundle）。

本文件交付 M2（def 层）：向量场对函数的作用 `fieldDeriv`（KL 刻画 +
乘积法则）、0-形式外微分 `algD0`、1-形式 `AlgForm1` 及其 Koszul
外微分 `algD1`。性质层（反对称/Leibniz/d²=0）见 M3/M4 里程碑。

全部无选择公理。
-/

namespace SDG.DifferentialForms

open TangentVectorField

section AlgebraicForms

variable {R : Type u} [IsKockLawvere_one R] {X : Type u}

/-! ### 向量场对函数的作用 -/

/-- **向量场对函数的方向导数场**：`ξ(f)(x) := f 沿切向量 ξ(x) 的
KL 导数`。 -/
def fieldDeriv (ξ : TangentVectorField R X) (f : X → R) : X → R :=
  fun x => directionalDerivative f (TangentVectorField.toFiber ξ x)

/-- **KL 刻画**：`f` 沿 ξ 自己的积分曲线展开——
`f(ξ(x)(d)) = f(x) + ξ(f)(x) · d`。 -/
theorem fieldDeriv_spec (ξ : TangentVectorField R X) (f : X → R) (x : X) (d : D R) :
    f (ξ.1 x d) = f x + fieldDeriv ξ f x * (d : R) :=
  directionalDerivative_spec f (TangentVectorField.toFiber ξ x) d

/-- **场导子的乘积法则**（KL 唯一性：沿积分曲线展开 + `d² = 0` 消
二阶项，导数由一阶系数唯一决定）。 -/
theorem fieldDeriv_mul (ξ : TangentVectorField R X) (f g : X → R) :
    fieldDeriv ξ (f * g) = f * fieldDeriv ξ g + g * fieldDeriv ξ f := by
  funext x
  have key : ∀ d : D R, (f * g) (ξ.1 x d)
      = (f * g) x + (f * fieldDeriv ξ g + g * fieldDeriv ξ f) x * (d : R) := by
    intro d
    have hf := fieldDeriv_spec ξ f x d
    have hg := fieldDeriv_spec ξ g x d
    have hd2 : (d : R) * (d : R) = 0 := D.mul_eq_zero R d
    calc (f * g) (ξ.1 x d) = f (ξ.1 x d) * g (ξ.1 x d) := rfl
      _ = (f x + fieldDeriv ξ f x * (d : R)) * (g x + fieldDeriv ξ g x * (d : R)) := by
          rw [hf, hg]
      _ = f x * g x + fieldDeriv ξ f x * g x * (d : R)
            + f x * fieldDeriv ξ g x * (d : R) := by
          rw [add_mul, mul_add, mul_add, mul_mul_mul_comm, hd2, mul_zero, add_zero]
          ring
      _ = (f * g) x + (f * fieldDeriv ξ g + g * fieldDeriv ξ f) x * (d : R) := by
          show f x * g x + fieldDeriv ξ f x * g x * (d : R)
              + f x * fieldDeriv ξ g x * (d : R)
            = f x * g x + (f x * fieldDeriv ξ g x + g x * fieldDeriv ξ f x) * (d : R)
          ring
  have h : ∀ d : D R, (f * g) (ξ.1 x d)
      = (f * g) (ξ.1 x 0) + (f * fieldDeriv ξ g + g * fieldDeriv ξ f) x * (d : R) := by
    intro d
    rw [show ξ.1 x 0 = x from ξ.2 x]
    exact key d
  -- KL 唯一性：一阶系数由展开式唯一决定（注意 KL 数据必须内联——have 会丢 body）
  exact ((IsKockLawvere_one.isKockLawvere_one (R := R)
    (fun d : D R => (f * g) ((TangentVectorField.toFiber ξ x).1 d))).property.right _ h).symm

/-! ### 0-形式与 1-形式的外微分 -/

/-- **0-形式的外微分**：`d₀ f := ξ ↦ ξ(f)`（方向导数场）。 -/
def algD0 (f : X → R) (ξ : TangentVectorField R X) : X → R :=
  fieldDeriv ξ f

/-- 1-形式（场变元）：向量场 → 函数。`abbrev`（reducible）：Pi 型的
Add/SMul 实例直接透传，`ω₁ + ω₂`、`c • ω` 逐点可用。 -/
abbrev AlgForm1 (R : Type u) [IsKockLawvere_one R] (X : Type u) :=
  TangentVectorField R X → (X → R)

/-- **1-形式的 Koszul 外微分**：
`(dω)(ξ, η) = ξ(ω η) - η(ω ξ) - ω([ξ, η])`（逐点函数；
`[·,·]` 为 Property W 路线的李括号）。 -/
def algD1 [Microlinear R X] [PropertyW R X]
    (ω : AlgForm1 R X) (ξ η : TangentVectorField R X) : X → R :=
  fieldDeriv ξ (ω η) - fieldDeriv η (ω ξ) - ω (lieBracket ξ η)

/-- 0-形式外微分的点态展开。 -/
theorem algD0_apply (f : X → R) (ξ : TangentVectorField R X) (x : X) :
    algD0 f ξ x = directionalDerivative f (TangentVectorField.toFiber ξ x) := rfl

/-- 1-形式 Koszul 外微分的点态展开。 -/
theorem algD1_apply [Microlinear R X] [PropertyW R X]
    (ω : AlgForm1 R X) (ξ η : TangentVectorField R X) (x : X) :
    algD1 ω ξ η x
      = directionalDerivative (ω η) (TangentVectorField.toFiber ξ x)
        - directionalDerivative (ω ξ) (TangentVectorField.toFiber η x)
        - ω (lieBracket ξ η) x := rfl

/-- 0-形式外微分与场导子一致（定义桥梁）。 -/
theorem algD0_eq_fieldDeriv (f : X → R) (ξ : TangentVectorField R X) :
    algD0 f ξ = fieldDeriv ξ f := rfl

/-! ### M3：分次 Leibniz（函数数乘下的 1-形式外微分）-/

/-- 1-形式按函数数乘（逐点）：`(f ⬝ ω)(ξ) = f · (ω ξ)`。 -/
def algSMul (f : X → R) (ω : AlgForm1 R X) : AlgForm1 R X :=
  fun ξ => f * ω ξ

/-- `algSMul` 的求值展开（定义桥梁）。 -/
theorem algSMul_apply (f : X → R) (ω : AlgForm1 R X)
    (ξ : TangentVectorField R X) (x : X) :
    algSMul f ω ξ x = f x * ω ξ x := rfl

/-- **分次 Leibniz（函数数乘，1-形式 Koszul 外微分）**：
`d(f·ω)(ξ, η) = (ξf)·ω(η) - (ηf)·ω(ξ) + f·dω(ξ, η)`——
即 `d(fω) = df·ω + f·dω` 的求值形式（`df` 即 0-形式外微分 `algD0`）。

证明：乘积法则 `fieldDeriv_mul` 展开前两项，第三项由 `algSMul` 定义直接
提出 `f`，逐点重排为 Leibniz 形。 -/
theorem algD1_algSMul [Microlinear R X] [PropertyW R X]
    (f : X → R) (ω : AlgForm1 R X) (ξ η : TangentVectorField R X) :
    algD1 (algSMul f ω) ξ η
      = (fun x => fieldDeriv ξ f x * ω η x - fieldDeriv η f x * ω ξ x)
        + f * algD1 ω ξ η := by
  funext x
  have hp1 : fieldDeriv ξ ((algSMul f ω) η) x
      = f x * fieldDeriv ξ (ω η) x + ω η x * fieldDeriv ξ f x :=
    congrFun (fieldDeriv_mul ξ f (ω η)) x
  have hp2 : fieldDeriv η ((algSMul f ω) ξ) x
      = f x * fieldDeriv η (ω ξ) x + ω ξ x * fieldDeriv η f x :=
    congrFun (fieldDeriv_mul η f (ω ξ)) x
  show fieldDeriv ξ ((algSMul f ω) η) x - fieldDeriv η ((algSMul f ω) ξ) x
      - (algSMul f ω) (lieBracket ξ η) x
    = (fieldDeriv ξ f x * ω η x - fieldDeriv η f x * ω ξ x)
      + f x * (fieldDeriv ξ (ω η) x - fieldDeriv η (ω ξ) x
        - ω (lieBracket ξ η) x)
  rw [hp1, hp2]
  show f x * fieldDeriv ξ (ω η) x + ω η x * fieldDeriv ξ f x
      - (f x * fieldDeriv η (ω ξ) x + ω ξ x * fieldDeriv η f x)
      - f x * ω (lieBracket ξ η) x
    = (fieldDeriv ξ f x * ω η x - fieldDeriv η f x * ω ξ x)
      + f x * (fieldDeriv ξ (ω η) x - fieldDeriv η (ω ξ) x
        - ω (lieBracket ξ η) x)
  ring

/-- 0-形式版本的同一恒等式（`algD0` 记法）：外微分的乘积法则——
`d₀(f·ω) = f·d₀ω + ω·d₀f` 的场求值形。 -/
theorem algD0_mul (f g : X → R) (ξ : TangentVectorField R X) :
    algD0 (f * g) ξ = f * algD0 g ξ + g * algD0 f ξ :=
  fieldDeriv_mul ξ f g

/-! ### 场导子的线性性（KL 唯一性直推）-/

/-- **场导子的加法性**：`ξ(f + g) = ξf + ξg`（KL 唯一性：两条
展开式的系数相加）。 -/
theorem fieldDeriv_add (ξ : TangentVectorField R X) (f g : X → R) :
    fieldDeriv ξ (f + g) = fieldDeriv ξ f + fieldDeriv ξ g := by
  funext x
  have key : ∀ d : D R, (f + g) (ξ.1 x d)
      = (f + g) (ξ.1 x 0) + (fieldDeriv ξ f x + fieldDeriv ξ g x) * (d : R) := by
    intro d
    have hf := fieldDeriv_spec ξ f x d
    have hg := fieldDeriv_spec ξ g x d
    rw [show ξ.1 x 0 = x from ξ.2 x]
    show f (ξ.1 x d) + g (ξ.1 x d)
      = f x + g x + (fieldDeriv ξ f x + fieldDeriv ξ g x) * (d : R)
    rw [hf, hg]
    ring
  exact ((IsKockLawvere_one.isKockLawvere_one (R := R)
    (fun d : D R => (f + g) ((TangentVectorField.toFiber ξ x).1 d))).property.right _ key).symm

/-- **场导子的数乘性**：`ξ(c·f) = c·ξf`。 -/
theorem fieldDeriv_smul (ξ : TangentVectorField R X) (c : R) (f : X → R) :
    fieldDeriv ξ (c • f) = c • fieldDeriv ξ f := by
  funext x
  have key : ∀ d : D R, (c • f) (ξ.1 x d)
      = (c • f) (ξ.1 x 0) + (c * fieldDeriv ξ f x) * (d : R) := by
    intro d
    have hf := fieldDeriv_spec ξ f x d
    rw [show ξ.1 x 0 = x from ξ.2 x]
    show c * f (ξ.1 x d) = c * f x + c * fieldDeriv ξ f x * (d : R)
    rw [hf]
    ring
  exact ((IsKockLawvere_one.isKockLawvere_one (R := R)
    (fun d : D R => (c • f) ((TangentVectorField.toFiber ξ x).1 d))).property.right _ key).symm

/-! ### M3 续：algD 的线性性（复空间 Ω̂⁰ → Ω̂¹ → Ω̂² 是 R-线性映射）-/

/-- 0-形式外微分的加法性。 -/
theorem algD0_add (f g : X → R) (ξ : TangentVectorField R X) :
    algD0 (f + g) ξ = algD0 f ξ + algD0 g ξ :=
  fieldDeriv_add ξ f g

/-- 0-形式外微分的数乘性。 -/
theorem algD0_smul (c : R) (f : X → R) (ξ : TangentVectorField R X) :
    algD0 (c • f) ξ = c • algD0 f ξ :=
  fieldDeriv_smul ξ c f

/-- **1-形式 Koszul 外微分的加法性**：`d(ω₁ + ω₂) = dω₁ + dω₂`
（场导子加法性 + 逐点 ring）。 -/
theorem algD1_add [Microlinear R X] [PropertyW R X]
    (ω₁ ω₂ : AlgForm1 R X) (ξ η : TangentVectorField R X) :
    algD1 (ω₁ + ω₂) ξ η = algD1 ω₁ ξ η + algD1 ω₂ ξ η := by
  funext x
  simp only [algD1, Pi.add_apply, Pi.sub_apply, fieldDeriv_add]
  ring

/-- **1-形式 Koszul 外微分的数乘性**：`d(c·ω) = c·dω`。 -/
theorem algD1_smul [Microlinear R X] [PropertyW R X]
    (c : R) (ω : AlgForm1 R X) (ξ η : TangentVectorField R X) :
    algD1 (c • ω) ξ η = c • algD1 ω ξ η := by
  funext x
  simp only [algD1, Pi.smul_apply, Pi.sub_apply, fieldDeriv_smul, smul_eq_mul]
  ring

/-- **场导子的取负**：`ξ(−f) = −ξf`（KL 唯一性）。 -/
theorem fieldDeriv_neg (ξ : TangentVectorField R X) (f : X → R) :
    fieldDeriv ξ (-f) = -fieldDeriv ξ f := by
  funext x
  have key : ∀ d : D R, (-f) (ξ.1 x d)
      = (-f) (ξ.1 x 0) + (-fieldDeriv ξ f x) * (d : R) := by
    intro d
    have hf := fieldDeriv_spec ξ f x d
    rw [show ξ.1 x 0 = x from ξ.2 x]
    show -f (ξ.1 x d) = -f x + -fieldDeriv ξ f x * (d : R)
    rw [hf]; ring
  exact ((IsKockLawvere_one.isKockLawvere_one (R := R)
    (fun d : D R => (-f) ((TangentVectorField.toFiber ξ x).1 d))).property.right _ key).symm

/-- **场导子的减法**：`ξ(f − g) = ξf − ξg`。 -/
theorem fieldDeriv_sub (ξ : TangentVectorField R X) (f g : X → R) :
    fieldDeriv ξ (f - g) = fieldDeriv ξ f - fieldDeriv ξ g := by
  have h : (f - g) = f + (-g) := by funext x; exact sub_eq_add_neg (f x) (g x)
  rw [h, fieldDeriv_add, fieldDeriv_neg]
  exact (sub_eq_add_neg _ _).symm

/-! ### M4 核心：导子交换公式与 0-形式层的 d² = 0 -/

/-- **KL 零化子引理**：零化整个 `D` 的环元素为零——KL 公理的
唯一性子句用于零映射的直接推论（第五十二接力点）。 -/
theorem kl_zero_map_coeff [IsKockLawvere_one R] :
    (IsKockLawvere_one.isKockLawvere_one (fun _ : D R => (0 : R))).1 = 0 :=
  ((IsKockLawvere_one.isKockLawvere_one (fun _ : D R => (0 : R))).2.2
    (0 : R) (fun e => by show (0 : R) = (0 : R) + (0 : R) * (e : R); ring)).symm

theorem kl_annihilator_eq_zero [IsKockLawvere_one R] {c : R}
    (h : ∀ d : D R, c * (d : R) = 0) : c = 0 := by
  obtain ⟨b, hbs, hbu⟩ := IsKockLawvere_one.isKockLawvere_one
    (fun _ : D R => (0 : R))
  have h0 : (0 : R) = b := hbu 0 (fun d => by
    show (0 : R) = (0 : R) + (0 : R) * (d : R)
    ring)
  have hc : c = b := hbu c (fun d => by
    show (0 : R) = (0 : R) + c * (d : R)
    rw [h d]
    ring)
  exact hc.trans h0.symm

/-- **R 自身满足 Property W**（第五十二接力点；KL 公理的定理级
推论，零新公理）：轴退化的 `τ : D×D → R` 唯一经 `d₁·d₂` 因子化。

存在性：对 `d ↦ τ(d,e)` 与 `e ↦ a(e)` 各用一次 KL；轴条件 +
KL 唯一性（`d ↦ τ(d,0)` 的系数既是 `a 0` 又是 `0`）给出 `a 0 = 0`。
唯一性：差函数 `h` 经 KL 是仿射的（系数 `c`）且在 `D·D` 像上为零；
固定 `d₀` 后 `e ↦ h(d₀·e)` 既是零映射又是系数 `c·d₀` 的仿射映射——
同一函数的 KL 系数相等 ⟹ `c·d₀ = 0` 对每个 `d₀` ⟹ 零化子引理。
（全部构造性：KL 数据走子类型投影，不引入 Classical.choice。） -/
instance instPropertyW_self : PropertyW R R where
  propertyW τ hRA hLA := by
    set a : D R → R :=
      fun e => (IsKockLawvere_one.isKockLawvere_one (fun d : D R => τ d e)).1 with hAdef
    have ha : ∀ e d : D R, τ d e = τ 0 e + a e * (d : R) := by
      intro e d
      exact (IsKockLawvere_one.isKockLawvere_one (fun d : D R => τ d e)).2.1 d
    obtain ⟨b, hbs, -⟩ := IsKockLawvere_one.isKockLawvere_one a
    have ha0 : a 0 = 0 := by
      obtain ⟨â, -, âuniq⟩ := IsKockLawvere_one.isKockLawvere_one (fun d : D R => τ d 0)
      have h0spec : ∀ d : D R, τ d 0 = τ 0 0 + (0 : R) * (d : R) := by
        intro d
        rw [hRA d]
        ring
      exact (((âuniq 0 h0spec).trans (âuniq (a 0) (ha 0)).symm)).symm
    have hfac : ∀ d₁ d₂ : D R, τ d₁ d₂ = τ 0 0 + b * ((d₁ : R) * (d₂ : R)) := by
      intro d₁ d₂
      rw [ha d₂ d₁, hLA d₂, hbs d₂, ha0]
      ring
    refine ⟨fun t => τ 0 0 + b * (t : R), ?_, ?_⟩
    · exact fun d₁ d₂ => (hfac d₁ d₂).symm
    · intro y hy
      obtain ⟨c, hcs, -⟩ := IsKockLawvere_one.isKockLawvere_one
        (fun t : D R => y t - (τ 0 0 + b * (t : R)))
      have hzero0 : y 0 - (τ 0 0 + b * ((0 : D R) : R)) = 0 := by
        have e1 := hy 0 0
        rw [D.mul_zero_zero] at e1
        show y 0 - (τ 0 0 + b * ((0 : D R) : R)) = 0
        rw [show ((0 : D R) : R) = 0 from rfl, mul_zero, add_zero, e1]
        ring
      have hdiff0 : ∀ d₁ d₂ : D R,
          y (D.mul R d₁ d₂) - (τ 0 0 + b * ((D.mul R d₁ d₂ : D R) : R)) = 0 := by
        intro d₁ d₂
        have e1 := hy d₁ d₂
        show y (D.mul R d₁ d₂) - (τ 0 0 + b * ((D.mul R d₁ d₂ : D R) : R)) = 0
        rw [e1, D.coe_mul, hfac]
        ring
      have hcd : ∀ d₀ : D R, c * (d₀ : R) = 0 := by
        intro d₀
        have hz : ∀ e : D R,
            y (D.mul R d₀ e) - (τ 0 0 + b * ((D.mul R d₀ e : D R) : R)) = 0 :=
          hdiff0 d₀
        have e0 : ∀ e : D R,
            y (D.mul R d₀ e) - (τ 0 0 + b * ((D.mul R d₀ e : D R) : R))
            = (c * (d₀ : R)) * (e : R) := by
          intro e
          have hk := hcs (D.mul R d₀ e)
          rw [hzero0, D.coe_mul] at hk
          rw [D.coe_mul, hk]
          ring
        have hEqFun : (fun e : D R =>
              y (D.mul R d₀ e) - (τ 0 0 + b * ((D.mul R d₀ e : D R) : R)))
            = (fun e : D R => (c * (d₀ : R)) * (e : R)) :=
          funext e0
        have hEqZero : (fun e : D R =>
              y (D.mul R d₀ e) - (τ 0 0 + b * ((D.mul R d₀ e : D R) : R)))
            = (fun _ : D R => (0 : R)) :=
          funext hz
        have hproj : ∀ (f₁ f₂ : D R → R), f₁ = f₂ →
            (IsKockLawvere_one.isKockLawvere_one f₁).1
              = (IsKockLawvere_one.isKockLawvere_one f₂).1 :=
          fun _ _ hf => congrArg (fun f => (IsKockLawvere_one.isKockLawvere_one f).1) hf
        have hkc : (IsKockLawvere_one.isKockLawvere_one
              (fun e : D R => (c * (d₀ : R)) * (e : R))).1 = c * (d₀ : R) :=
          ((IsKockLawvere_one.isKockLawvere_one
            (fun e : D R => (c * (d₀ : R)) * (e : R))).2.2
            (c * (d₀ : R)) (fun e => by
              show (c * (d₀ : R)) * (e : R)
                = (c * (d₀ : R)) * ((0 : D R) : R) + (c * (d₀ : R)) * (e : R)
              rw [show ((0 : D R) : R) = 0 from rfl, mul_zero, zero_add])).symm
        calc c * (d₀ : R)
            = (IsKockLawvere_one.isKockLawvere_one
                (fun e : D R => (c * (d₀ : R)) * (e : R))).1 := hkc.symm
          _ = (IsKockLawvere_one.isKockLawvere_one
                (fun _ : D R => (0 : R))).1 := by
                rw [← hproj _ _ hEqFun, hproj _ _ hEqZero]
          _ = 0 := kl_zero_map_coeff
      have hcz : c = 0 := kl_annihilator_eq_zero hcd
      funext t
      have ht := hcs t
      rw [hzero0, hcz] at ht
      have ht2 : y t - (τ 0 0 + b * (t : R)) = 0 := by simpa using ht
      exact sub_eq_zero.mp ht2

/-- **交换子轨道的四步 KL 展开**（导子交换公式的计算核心）：
`f` 沿 `ξ_d → η_e → ξ_{-d} → η_{-e}` 无穷小轨道的展开是**精确**仿射式。
高阶单项（`d²e`、`de²`、`d²e²`）在交换环中全含重复字母，由
`d² = e² = 0` 恒为零消去，只剩一阶系数 `ξ(ηf) − η(ξf)` 乘 `de`。
（第五十二接力点：第四十九/五十一接力点记录的"三阶残差"是记账
错误——`d·e·d = d²·e = 0` 由交换律直接消去。） -/
theorem fieldDeriv_commutator_expansion (ξ η : TangentVectorField R X) (f : X → R)
    (x : X) (d e : D R) :
    f (transformationCommutator ξ η d e x)
      = f x + (fieldDeriv ξ (fieldDeriv η f) x
          - fieldDeriv η (fieldDeriv ξ f) x) * ((d : R) * (e : R)) := by
  have hd2 : (d : R) * (d : R) = 0 := D.mul_eq_zero R d
  have he2 : (e : R) * (e : R) = 0 := D.mul_eq_zero R e
  have hd2p : (d : R) ^ 2 = 0 := by rw [pow_two]; exact hd2
  have he2p : (e : R) ^ 2 = 0 := by rw [pow_two]; exact he2
  -- 沿轨道的 KL 刻画（每步一阶，参数都在 D 中）
  have h1 : f (ξ.1 x d) = f x + fieldDeriv ξ f x * (d : R) := fieldDeriv_spec ξ f x d
  have h2 : f (η.1 (ξ.1 x d) e)
      = f (ξ.1 x d) + fieldDeriv η f (ξ.1 x d) * (e : R) :=
    fieldDeriv_spec η f (ξ.1 x d) e
  have h3 : fieldDeriv η f (ξ.1 x d)
      = fieldDeriv η f x + fieldDeriv ξ (fieldDeriv η f) x * (d : R) :=
    fieldDeriv_spec ξ (fieldDeriv η f) x d
  have h5 : fieldDeriv ξ f (η.1 (ξ.1 x d) e)
      = fieldDeriv ξ f (ξ.1 x d)
        + fieldDeriv η (fieldDeriv ξ f) (ξ.1 x d) * (e : R) :=
    fieldDeriv_spec η (fieldDeriv ξ f) (ξ.1 x d) e
  have h6 : fieldDeriv ξ f (ξ.1 x d)
      = fieldDeriv ξ f x + fieldDeriv ξ (fieldDeriv ξ f) x * (d : R) :=
    fieldDeriv_spec ξ (fieldDeriv ξ f) x d
  have h7 : fieldDeriv η (fieldDeriv ξ f) (ξ.1 x d)
      = fieldDeriv η (fieldDeriv ξ f) x
        + fieldDeriv ξ (fieldDeriv η (fieldDeriv ξ f)) x * (d : R) :=
    fieldDeriv_spec ξ (fieldDeriv η (fieldDeriv ξ f)) x d
  have h10 : fieldDeriv η f (η.1 (ξ.1 x d) e)
      = fieldDeriv η f (ξ.1 x d)
        + fieldDeriv η (fieldDeriv η f) (ξ.1 x d) * (e : R) :=
    fieldDeriv_spec η (fieldDeriv η f) (ξ.1 x d) e
  have h11 : fieldDeriv η (fieldDeriv η f) (ξ.1 x d)
      = fieldDeriv η (fieldDeriv η f) x
        + fieldDeriv ξ (fieldDeriv η (fieldDeriv η f)) x * (d : R) :=
    fieldDeriv_spec ξ (fieldDeriv η (fieldDeriv η f)) x d
  have h12 : fieldDeriv ξ (fieldDeriv η f) (η.1 (ξ.1 x d) e)
      = fieldDeriv ξ (fieldDeriv η f) (ξ.1 x d)
        + fieldDeriv η (fieldDeriv ξ (fieldDeriv η f)) (ξ.1 x d) * (e : R) :=
    fieldDeriv_spec η (fieldDeriv ξ (fieldDeriv η f)) (ξ.1 x d) e
  have h13 : fieldDeriv ξ (fieldDeriv η f) (ξ.1 x d)
      = fieldDeriv ξ (fieldDeriv η f) x
        + fieldDeriv ξ (fieldDeriv ξ (fieldDeriv η f)) x * (d : R) :=
    fieldDeriv_spec ξ (fieldDeriv ξ (fieldDeriv η f)) x d
  have h14 : fieldDeriv η (fieldDeriv ξ (fieldDeriv η f)) (ξ.1 x d)
      = fieldDeriv η (fieldDeriv ξ (fieldDeriv η f)) x
        + fieldDeriv ξ (fieldDeriv η (fieldDeriv ξ (fieldDeriv η f))) x * (d : R) :=
    fieldDeriv_spec ξ (fieldDeriv η (fieldDeriv ξ (fieldDeriv η f))) x d
  have hnegd : ((-(d : D R) : D R) : R) = -(d : R) := rfl
  have hnege : ((-(e : D R) : D R) : R) = -(e : R) := rfl
  -- 第二步（x₂）与第三步（x₃）的已化简形式
  have hx2 : f (η.1 (ξ.1 x d) e)
      = f x + fieldDeriv ξ f x * (d : R) + fieldDeriv η f x * (e : R)
        + fieldDeriv ξ (fieldDeriv η f) x * ((d : R) * (e : R)) := by
    rw [h2, h1, h3]; ring
  have hx3 : f (ξ.1 (η.1 (ξ.1 x d) e) (-d))
      = f x + fieldDeriv η f x * (e : R)
        + (fieldDeriv ξ (fieldDeriv η f) x
          - fieldDeriv η (fieldDeriv ξ f) x) * ((d : R) * (e : R)) := by
    have h4' := fieldDeriv_spec ξ f (η.1 (ξ.1 x d) e) (-d)
    rw [h4', hx2, h5, h6, h7, hnegd]
    ring_nf
    rw [hd2p]
    ring
  -- 第四步（x₄ = 交换子轨道终点）
  have h8' := fieldDeriv_spec η f (ξ.1 (η.1 (ξ.1 x d) e) (-d)) (-e)
  have h9' := fieldDeriv_spec ξ (fieldDeriv η f) (η.1 (ξ.1 x d) e) (-d)
  rw [transformationCommutator_apply, h8', h9', h12, h13, h14, h10, h11, hx3, h3,
    hnegd, hnege]
  ring_nf
  rw [hd2p, he2p]
  ring

/-- **导子交换公式**（Kock I.9 的算子形式，Koszul d² 的核心）：
`[ξ,η](f) = ξ(ηf) − η(ξf)`。

证明：映射 `T(d₁,d₂) := f(交换子轨道 x (d₁,d₂))` 两轴退化，Property W
给出唯一因子化。两个候选：① `f ∘ [ξ,η]-轨道`（`lieBracket_spec`）；
② 系数 `ξ(ηf) − η(ξf)` 的仿射函数（四步展开引理）。因子化唯一性
给出二者相等，再对 ① 用 KL 唯一性读出系数即得。零新公理。 -/
theorem fieldDeriv_lieBracket [Microlinear R X] [PropertyW R X]
    (ξ η : TangentVectorField R X) (f : X → R) :
    fieldDeriv (lieBracket ξ η) f
      = fieldDeriv ξ (fieldDeriv η f) - fieldDeriv η (fieldDeriv ξ f) := by
  funext x
  show (IsKockLawvere_one.isKockLawvere_one
      (fun t : D R => f ((lieBracket ξ η).1 x t))).1
    = fieldDeriv ξ (fieldDeriv η f) x - fieldDeriv η (fieldDeriv ξ f) x
  -- W-因子化：两轴退化（单轴为零时交换子是恒等变换）
  have hRA : ∀ d₁ : D R, f (transformationCommutator ξ η d₁ 0 x)
      = f (transformationCommutator ξ η 0 0 x) := fun d₁ => by
    rw [transformationCommutator_zero_right, transformationCommutator_zero_zero]
  have hLA : ∀ d₂ : D R, f (transformationCommutator ξ η 0 d₂ x)
      = f (transformationCommutator ξ η 0 0 x) := fun d₂ => by
    rw [transformationCommutator_zero_left, transformationCommutator_zero_zero]
  obtain ⟨t₀, hspec0, huniq0⟩ := PropertyW.propertyW (R := R) (M := R)
    (fun d₁ d₂ => f (transformationCommutator ξ η d₁ d₂ x)) hRA hLA
  -- 候选 1：括号场轨道复合 f（lieBracket_spec 给出因子化）
  have hw1 : ∀ d₁ d₂ : D R,
      (fun t : D R => f ((lieBracket ξ η).1 x t)) (D.mul R d₁ d₂)
        = f (transformationCommutator ξ η d₁ d₂ x) := by
    intro d₁ d₂
    show f ((lieBracket ξ η).1 x (D.mul R d₁ d₂))
      = f (transformationCommutator ξ η d₁ d₂ x)
    rw [lieBracket_spec ξ η x d₁ d₂]
    rfl
  -- 候选 2：仿射函数（四步展开给出因子化）
  have hw2 : ∀ d₁ d₂ : D R,
      (fun t : D R => f x + (fieldDeriv ξ (fieldDeriv η f) x
          - fieldDeriv η (fieldDeriv ξ f) x) * (t : R)) (D.mul R d₁ d₂)
        = f (transformationCommutator ξ η d₁ d₂ x) := by
    intro d₁ d₂
    show f x + (fieldDeriv ξ (fieldDeriv η f) x
          - fieldDeriv η (fieldDeriv ξ f) x) * ((D.mul R d₁ d₂ : D R) : R)
      = f (transformationCommutator ξ η d₁ d₂ x)
    rw [D.coe_mul]
    exact (fieldDeriv_commutator_expansion ξ η f x d₁ d₂).symm
  -- 因子化唯一性 ⟹ 两候选作为 D 上的函数相等
  have hEq : (fun t : D R => f ((lieBracket ξ η).1 x t))
      = (fun t : D R => f x + (fieldDeriv ξ (fieldDeriv η f) x
          - fieldDeriv η (fieldDeriv ξ f) x) * (t : R)) :=
    (huniq0 _ hw1).trans (huniq0 _ hw2).symm
  -- 对候选 1 用 KL 唯一性读出系数：仿射系数唯一 ⟹ 就是 ξ(ηf) − η(ξf)
  obtain ⟨b, hbs, hbu⟩ := IsKockLawvere_one.isKockLawvere_one
    (fun t : D R => f ((lieBracket ξ η).1 x t))
  have hbase : f ((lieBracket ξ η).1 x 0) = f x := by
    rw [lieBracket_basePoint]
  have hCeq : (fieldDeriv ξ (fieldDeriv η f) x
      - fieldDeriv η (fieldDeriv ξ f) x) = b := by
    apply hbu
    intro t
    show f ((lieBracket ξ η).1 x t)
      = f ((lieBracket ξ η).1 x 0)
        + (fieldDeriv ξ (fieldDeriv η f) x
          - fieldDeriv η (fieldDeriv ξ f) x) * (t : R)
    rw [congrFun hEq t, hbase]
  exact hCeq.symm

/-- **0-形式层的 d² = 0**：`d(d f) = 0`——由导子交换公式，
`d(d₀f)(ξ,η) = ξ(ηf) − η(ξf) − [ξ,η](f) = 0`。 -/
theorem algD_d2_zero_form [Microlinear R X] [PropertyW R X]
    (f : X → R) (ξ η : TangentVectorField R X) :
    algD1 (algD0 f) ξ η = 0 := by
  funext x
  simp only [algD1, Pi.zero_apply, Pi.sub_apply]
  have h1 : fieldDeriv ξ (algD0 f η) x = fieldDeriv ξ (fieldDeriv η f) x := rfl
  have h2 : fieldDeriv η (algD0 f ξ) x = fieldDeriv η (fieldDeriv ξ f) x := rfl
  have h3 : algD0 f (lieBracket ξ η) x = fieldDeriv (lieBracket ξ η) f x := rfl
  rw [h1, h2, h3, fieldDeriv_lieBracket]
  simp only [Pi.sub_apply]
  ring

/-! ### M1 完成：Jacobi 恒等式（函数作用层面）-/

/-- **Jacobi 恒等式**（作用于函数的层面）：
`[[ξ,η],ζ](f) + [[η,ζ],ξ](f) + [[ζ,ξ],η](f) = 0` 对任意 `f`。

证明：导子交换公式（第五十二接力点）把三项全部展开为六项二阶复合
场导数，逐点配对反号相消——纯 ring 计算。这是 1-形式层 Koszul d²=0
的前置件。 -/
theorem fieldDeriv_jacobi [Microlinear R X] [PropertyW R X]
    (ξ η ζ : TangentVectorField R X) (f : X → R) :
    fieldDeriv (lieBracket (lieBracket ξ η) ζ) f
      + fieldDeriv (lieBracket (lieBracket η ζ) ξ) f
      + fieldDeriv (lieBracket (lieBracket ζ ξ) η) f = 0 := by
  funext x
  simp only [Pi.add_apply, Pi.zero_apply, fieldDeriv_lieBracket, fieldDeriv_sub,
    Pi.sub_apply]
  ring

/-! ### M1 收官：李括号是导子 -/

/-- **李括号是导子**：`[ξ,η](f·g) = [ξ,η](f)·g + f·[ξ,η](g)`——
交换子公式 + 乘积法则展开，交叉项两两相消。 -/
theorem fieldDeriv_lieBracket_mul [Microlinear R X] [PropertyW R X]
    (ξ η : TangentVectorField R X) (f g : X → R) :
    fieldDeriv (lieBracket ξ η) (f * g)
      = fieldDeriv (lieBracket ξ η) f * g + f * fieldDeriv (lieBracket ξ η) g := by
  funext x
  have hηfg : fieldDeriv η (f * g) = f * fieldDeriv η g + g * fieldDeriv η f :=
    fieldDeriv_mul η f g
  have hξfg : fieldDeriv ξ (f * g) = f * fieldDeriv ξ g + g * fieldDeriv ξ f :=
    fieldDeriv_mul ξ f g
  rw [fieldDeriv_lieBracket, hηfg, hξfg, fieldDeriv_add ξ, fieldDeriv_add η,
    fieldDeriv_mul ξ f (fieldDeriv η g), fieldDeriv_mul ξ g (fieldDeriv η f),
    fieldDeriv_mul η f (fieldDeriv ξ g), fieldDeriv_mul η g (fieldDeriv ξ f),
    fieldDeriv_lieBracket, fieldDeriv_lieBracket]
  simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply]
  ring

/-! ### 2-形式层与 Koszul 外微分（第二层）-/

/-- 2-形式（场变元）：场对 → 函数。 -/
abbrev AlgForm2 (R : Type u) [IsKockLawvere_one R] (X : Type u) :=
  TangentVectorField R X → TangentVectorField R X → (X → R)

/-- **2-形式输入的 Koszul 外微分**（p = 2 顶点公式）：
`(dα)(ξ₀,ξ₁,ξ₂) = ξ₀(α(ξ₁,ξ₂)) − ξ₁(α(ξ₀,ξ₂)) + ξ₂(α(ξ₀,ξ₁))
  − α([ξ₀,ξ₁],ξ₂) + α([ξ₀,ξ₂],ξ₁) − α([ξ₁,ξ₂],ξ₀)`。
（与 `algD1` 的 Koszul 约定一致：p = 1 时给出同一公式。） -/
def algD2 [Microlinear R X] [PropertyW R X] (α : AlgForm2 R X) :
    TangentVectorField R X → TangentVectorField R X → TangentVectorField R X → (X → R) :=
  fun ξ₀ ξ₁ ξ₂ =>
    fieldDeriv ξ₀ (α ξ₁ ξ₂) - fieldDeriv ξ₁ (α ξ₀ ξ₂) + fieldDeriv ξ₂ (α ξ₀ ξ₁)
      - α (lieBracket ξ₀ ξ₁) ξ₂ + α (lieBracket ξ₀ ξ₂) ξ₁ - α (lieBracket ξ₁ ξ₂) ξ₀

/-- `algD2` 的点态展开。 -/
theorem algD2_apply [Microlinear R X] [PropertyW R X] (α : AlgForm2 R X)
    (ξ₀ ξ₁ ξ₂ : TangentVectorField R X) (x : X) :
    algD2 α ξ₀ ξ₁ ξ₂ x
      = fieldDeriv ξ₀ (α ξ₁ ξ₂) x - fieldDeriv ξ₁ (α ξ₀ ξ₂) x + fieldDeriv ξ₂ (α ξ₀ ξ₁) x
        - α (lieBracket ξ₀ ξ₁) ξ₂ x + α (lieBracket ξ₀ ξ₂) ξ₁ x
        - α (lieBracket ξ₁ ξ₂) ξ₀ x := rfl

/-- `algD2` 对形式变元的加法性。 -/
theorem algD2_add [Microlinear R X] [PropertyW R X] (α₁ α₂ : AlgForm2 R X)
    (ξ₀ ξ₁ ξ₂ : TangentVectorField R X) :
    algD2 (α₁ + α₂) ξ₀ ξ₁ ξ₂ = algD2 α₁ ξ₀ ξ₁ ξ₂ + algD2 α₂ ξ₀ ξ₁ ξ₂ := by
  funext x
  simp only [algD2, Pi.add_apply, Pi.sub_apply, fieldDeriv_add]
  ring

/-- `algD2` 对形式变元的数乘性。 -/
theorem algD2_smul [Microlinear R X] [PropertyW R X] (c : R) (α : AlgForm2 R X)
    (ξ₀ ξ₁ ξ₂ : TangentVectorField R X) :
    algD2 (c • α) ξ₀ ξ₁ ξ₂ = c • algD2 α ξ₀ ξ₁ ξ₂ := by
  funext x
  simp only [algD2, Pi.smul_apply, Pi.sub_apply, fieldDeriv_smul, smul_eq_mul,
    Pi.add_apply]
  ring

end AlgebraicForms

end SDG.DifferentialForms

#print axioms SDG.DifferentialForms.fieldDeriv_mul
#print axioms SDG.DifferentialForms.algD1
#print axioms SDG.DifferentialForms.algD1_apply
