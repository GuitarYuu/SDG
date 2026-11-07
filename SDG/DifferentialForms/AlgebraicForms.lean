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

/-! ### 微线性解锁：导数的可加性与缩放（第五十五接力点）-/

/-- **KL-D(2) 对角引理**：轴上仿射（系数 `c₀`、`c₁`，公共基点 `b`）的
`D(2) → R` 函数在对角线上取值为 `b + (c₀ + c₁)·d`。

证明：显式仿射映射与 `F` 都是同一轴数据的 `D(2)`-扩张，由 R 自身的
微线性（`Microlinear R R`，即 KL 全 schema——Kock Axiom 1''，库内
`IsKockLawvereDkn` 的推论）的唯一性相等，对角求值后交叉项
`c₁·d·d = 0` 消去。**注意**：切片论证不可用（`D(2)` 内固定第二坐标
的切片不是完整的 `D`），唯一可走的是扩张唯一性。 -/
theorem kl_diag_add [Microlinear R R]
    (F : Dn R 2 → R) (b c₀ c₁ : R)
    (h0 : ∀ d : D R, F (Dn.embed R 0 d) = b + c₀ * (d : R))
    (h1 : ∀ d : D R, F (Dn.embed R 1 d) = b + c₁ * (d : R)) :
    ∀ d : D R, F (Dn.diag R d) = b + (c₀ + c₁) * (d : R) := by
  set G : Dn R 2 → R :=
    fun u => b + c₀ * (u.1 (0 : Fin 2)) + c₁ * (u.1 (1 : Fin 2)) with hGdef
  have hc00 : ∀ d : D R, (Dn.embed R 0 d).1 (0 : Fin 2) = (d : R) := by
    intro d; simp [Dn.embed]
  have hc01 : ∀ d : D R, (Dn.embed R 0 d).1 (1 : Fin 2) = 0 := by
    intro d; simp [Dn.embed]
  have hc10 : ∀ d : D R, (Dn.embed R 1 d).1 (0 : Fin 2) = 0 := by
    intro d; simp [Dn.embed]
  have hc11 : ∀ d : D R, (Dn.embed R 1 d).1 (1 : Fin 2) = (d : R) := by
    intro d; simp [Dn.embed]
  have hcd : ∀ (j : Fin 2) (d : D R), (Dn.diag R d).1 j = (d : R) := by
    intro j d; simp [Dn.diag]
  have hbase : (fun d : D R => F (Dn.embed R 0 d)) 0
      = (fun d : D R => F (Dn.embed R 1 d)) 0 := by
    show F (Dn.embed R 0 0) = F (Dn.embed R 1 0)
    rw [h0, h1]
    show b + c₀ * ((0 : D R) : R) = b + c₁ * ((0 : D R) : R)
    rw [show ((0 : D R) : R) = 0 from rfl, mul_zero, mul_zero]
  have haxisF : Dn.restrict' R F
      = mkFiberProduct2 R (fun d : D R => F (Dn.embed R 0 d))
        (fun d : D R => F (Dn.embed R 1 d)) hbase := by
    apply Subtype.ext
    funext i d
    by_cases hi : i = 0
    · subst i
      rfl
    · have hi1 : i = 1 := fin_two_eq_one_of_ne_zero hi
      subst i
      rfl
  have haxisG : Dn.restrict' R G
      = mkFiberProduct2 R (fun d : D R => F (Dn.embed R 0 d))
        (fun d : D R => F (Dn.embed R 1 d)) hbase := by
    apply Subtype.ext
    funext i d
    by_cases hi : i = 0
    · subst i
      show b + c₀ * (Dn.embed R 0 d).1 (0 : Fin 2) + c₁ * (Dn.embed R 0 d).1 (1 : Fin 2)
        = F (Dn.embed R 0 d)
      rw [hc00, hc01, h0 d]
      ring
    · have hi1 : i = 1 := fin_two_eq_one_of_ne_zero hi
      subst i
      show b + c₀ * (Dn.embed R 1 d).1 (0 : Fin 2) + c₁ * (Dn.embed R 1 d).1 (1 : Fin 2)
        = F (Dn.embed R 1 d)
      rw [hc10, hc11, h1 d]
      ring
  obtain ⟨G', hspec', huniq'⟩ := Microlinear.microlinear (R := R) (X := R) (n := 2)
    (mkFiberProduct2 R (fun d : D R => F (Dn.embed R 0 d))
      (fun d : D R => F (Dn.embed R 1 d)) hbase)
  have hFG : F = G := (huniq' F haxisF).trans (huniq' G haxisG).symm
  intro d
  rw [hFG]
  show b + c₀ * (Dn.diag R d).1 (0 : Fin 2) + c₁ * (Dn.diag R d).1 (1 : Fin 2)
    = b + (c₀ + c₁) * (d : R)
  rw [hcd 0 d, hcd 1 d]
  ring

/-- **导数沿切纤维加法的可加性**（MicrolinearD2 障碍的突破）：
`d(g)(v + w) = d(g)(v) + d(g)(w)`。

证明：和轨道是 `D(2)`-扩张 `E₂` 的对角求值；`g ∘ E₂` 的轴-KL 系数
即 `d(g)(v)`、`d(g)(w)`（KL 唯一性对齐），由 `kl_diag_add` 得对角
仿射式，再与 canonical KL 展开联立、零化子引理收尾。前提
`[Microlinear R R]` = KL 全 schema（Kock Axiom 1''）。 -/
theorem directionalDeriv_tangentAdd [Microlinear R X] [Microlinear R R]
    (g : X → R) {x : X} (v w : TangentFiber R X x) :
    directionalDerivative g (v + w) = directionalDerivative g v + directionalDerivative g w := by
  obtain ⟨E₂, hspecE, huniqE⟩ := Microlinear.microlinear (R := R) (X := X) (n := 2)
    (mkFiberProduct2 R v.1 w.1 (v.2.trans w.2.symm))
  have hax0 : ∀ d : D R, E₂ (Dn.embed R 0 d) = v.1 d := by
    intro d
    show E₂ (Dn.embed R 0 d) = v.1 d
    have h := congrArg (fun t : TangentFiberProduct R X 2 => t.1 (0 : Fin 2) d) hspecE
    simpa [Dn.restrict', Dn.restrict, mkFiberProduct2] using h
  have hax1 : ∀ d : D R, E₂ (Dn.embed R 1 d) = w.1 d := by
    intro d
    show E₂ (Dn.embed R 1 d) = w.1 d
    have h := congrArg (fun t : TangentFiberProduct R X 2 => t.1 (1 : Fin 2) d) hspecE
    simpa [Dn.restrict', Dn.restrict, mkFiberProduct2] using h
  have haxv : ∀ d : D R, g (E₂ (Dn.embed R 0 d))
      = g x + directionalDerivative g v * (d : R) := by
    intro d
    rw [hax0]
    exact directionalDerivative_spec g v d
  have haxw : ∀ d : D R, g (E₂ (Dn.embed R 1 d))
      = g x + directionalDerivative g w * (d : R) := by
    intro d
    rw [hax1]
    exact directionalDerivative_spec g w d
  have hdiag := kl_diag_add (F := fun u : Dn R 2 => g (E₂ u))
    (g x) (directionalDerivative g v) (directionalDerivative g w) haxv haxw
  have hjoin : ∀ d : D R,
      (directionalDerivative g (v + w) - (directionalDerivative g v
        + directionalDerivative g w)) * (d : R) = 0 := by
    intro d
    have h1 := directionalDerivative_spec g (v + w) d
    have h2 : g ((v + w).1 d)
        = g x + (directionalDerivative g v + directionalDerivative g w) * (d : R) := by
      have hid : (v + w).1 d = E₂ (Dn.diag R d) := by
        show tangentAdd R v.1 w.1 (v.2.trans w.2.symm) d = E₂ (Dn.diag R d)
        show (Microlinear.microlinear (n := 2)
            (mkFiberProduct2 R v.1 w.1 (v.2.trans w.2.symm))).1 (Dn.diag R d)
          = E₂ (Dn.diag R d)
        exact congrArg (fun t => t (Dn.diag R d))
          (huniqE _ (Microlinear.microlinear (n := 2)
            (mkFiberProduct2 R v.1 w.1 (v.2.trans w.2.symm))).2.1)
      rw [hid, hdiag d]
    rw [h2] at h1
    have h3 : (directionalDerivative g v + directionalDerivative g w) * (d : R)
        = directionalDerivative g (v + w) * (d : R) := add_left_cancel h1
    rw [sub_mul, h3, sub_self]
  exact sub_eq_zero.mp (kl_annihilator_eq_zero hjoin)

/-- **场和的导数可加性**（可加性墙的推论）：
`(φ + ψ)(g) = φ(g) + ψ(g)`。 -/
theorem fieldDeriv_add_fields [Microlinear R X] [Microlinear R R]
    (φ ψ : TangentVectorField R X) (g : X → R) :
    fieldDeriv (φ + ψ) g = fieldDeriv φ g + fieldDeriv ψ g := by
  funext x
  show directionalDerivative g (toFiber (φ + ψ) x)
    = directionalDerivative g (toFiber φ x) + directionalDerivative g (toFiber ψ x)
  rw [toFiber_add]
  exact directionalDeriv_tangentAdd g (toFiber φ x) (toFiber ψ x)

/-- **R-标量缩放场的导数**：`(c·ξ)(g) = c·ξ(g)`（同
`fieldDeriv_smul_field` 的模板，把 `f x` 换成常数 `c`）。 -/
theorem fieldDeriv_smulR_field (c : R) (ξ : TangentVectorField R X) (g : X → R) :
    fieldDeriv (c • ξ) g = c • fieldDeriv ξ g := by
  funext x
  simp only [Pi.smul_apply]
  show directionalDerivative g (toFiber (c • ξ) x) = c * fieldDeriv ξ g x
  have hspec : ∀ d : D R, g ((c • ξ).1 x d) = g x + fieldDeriv (c • ξ) g x * (d : R) :=
    fieldDeriv_spec (c • ξ) g x
  have hξ : ∀ d : D R, g (ξ.1 x d) = g x + fieldDeriv ξ g x * (d : R) :=
    fieldDeriv_spec ξ g x
  have hstep : ∀ d : D R, g ((c • ξ).1 x d)
      = g x + (c * fieldDeriv ξ g x) * (d : R) := by
    intro d
    have hd : ((c • d : D R) : R) = c * (d : R) := rfl
    calc g ((c • ξ).1 x d) = g (ξ.1 x (c • d)) := rfl
      _ = g x + fieldDeriv ξ g x * ((c • d : D R) : R) := hξ (c • d)
      _ = g x + (c * fieldDeriv ξ g x) * (d : R) := by rw [hd]; ring
  have hjoin : ∀ d : D R,
      (fieldDeriv (c • ξ) g x - c * fieldDeriv ξ g x) * (d : R) = 0 := by
    intro d
    have h1 := hspec d
    rw [hstep d] at h1
    have h3 : (c * fieldDeriv ξ g x) * (d : R) = fieldDeriv (c • ξ) g x * (d : R) :=
      add_left_cancel h1
    rw [sub_mul, h3, sub_self]
  have hpt : directionalDerivative g (toFiber (c • ξ) x) = c * fieldDeriv ξ g x :=
    sub_eq_zero.mp (kl_annihilator_eq_zero hjoin)
  rw [hpt]

/-- **缩放场的导数**（只需 KL-1）：`(f·ξ)(g) = f·ξ(g)`——
缩放场在 `x` 处的轨道是 ξ-轨道在参数 `f(x)·d`（仍属 D），代入
ξ-KL 展开后系数即 `f·ξ(g)`，零化子引理收尾。 -/
theorem fieldDeriv_smul_field (f : X → R) (ξ : TangentVectorField R X) (g : X → R) :
    fieldDeriv (f • ξ) g = f * fieldDeriv ξ g := by
  funext x
  simp only [Pi.mul_apply]
  show directionalDerivative g (toFiber (f • ξ) x) = f x * fieldDeriv ξ g x
  have hspec : ∀ d : D R, g ((f • ξ).1 x d) = g x + fieldDeriv (f • ξ) g x * (d : R) :=
    fieldDeriv_spec (f • ξ) g x
  have hξ : ∀ d : D R, g (ξ.1 x d) = g x + fieldDeriv ξ g x * (d : R) :=
    fieldDeriv_spec ξ g x
  have hstep : ∀ d : D R, g ((f • ξ).1 x d)
      = g x + (f x * fieldDeriv ξ g x) * (d : R) := by
    intro d
    have hd : ((f x • d : D R) : R) = f x * (d : R) := rfl
    calc g ((f • ξ).1 x d) = g (ξ.1 x (f x • d)) := rfl
      _ = g x + fieldDeriv ξ g x * ((f x • d : D R) : R) := hξ (f x • d)
      _ = g x + (f x * fieldDeriv ξ g x) * (d : R) := by rw [hd]; ring
  have hjoin : ∀ d : D R,
      (fieldDeriv (f • ξ) g x - f x * fieldDeriv ξ g x) * (d : R) = 0 := by
    intro d
    have h1 := hspec d
    rw [hstep d] at h1
    have h3 : (f x * fieldDeriv ξ g x) * (d : R) = fieldDeriv (f • ξ) g x * (d : R) :=
      add_left_cancel h1
    rw [sub_mul, h3, sub_self]
  have hpt : directionalDerivative g (toFiber (f • ξ) x) = f x * fieldDeriv ξ g x :=
    sub_eq_zero.mp (kl_annihilator_eq_zero hjoin)
  rw [hpt]

/-- **C∞(X)-线性（函数作用层面，仅 KL-1）**：
`[f·ξ,η](g) = f·[ξ,η](g) − η(f)·ξ(g)`——
第五十二接力点交换子公式 + 缩放场引理 + 乘积法则的纯组装。 -/
theorem fieldDeriv_lieBracket_smul_field [Microlinear R X] [PropertyW R X]
    (f : X → R) (ξ η : TangentVectorField R X) (g : X → R) :
    fieldDeriv (lieBracket (f • ξ) η) g
      = f * fieldDeriv (lieBracket ξ η) g - fieldDeriv η f * fieldDeriv ξ g := by
  funext x
  rw [fieldDeriv_lieBracket (f • ξ) η g, fieldDeriv_smul_field f ξ (fieldDeriv η g),
    fieldDeriv_smul_field f ξ g, fieldDeriv_mul η f (fieldDeriv ξ g),
    fieldDeriv_lieBracket ξ η g]
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply]
  ring

/-! ### d² = 0（1-形式层，好形式类）-/

/-- 场层：(−1)·φ + φ = 0（Module 纤维律直推）。 -/
theorem field_add_neg_smul [Microlinear R X] (φ : TangentVectorField R X) :
    (-1 : R) • φ + φ = 0 := by
  have hfib : ∀ x : X, toFiber ((-1 : R) • φ + φ) x = toFiber (0 : TangentVectorField R X) x := by
    intro x
    rw [toFiber_add, toFiber_smulR, toFiber_zero]
    have h1 : ((-1 : R) + 1) • toFiber φ x
        = (-1 : R) • toFiber φ x + (1 : R) • toFiber φ x :=
      add_smul (-1 : R) 1 (toFiber φ x)
    rw [show ((-1 : R) + 1) = 0 from by ring, zero_smul, one_smul] at h1
    exact h1.symm
  apply Subtype.ext
  funext x d
  have h := congrArg (fun t : TangentFiber R X x => t.1 d) (hfib x)
  exact h

/-- 场值形式的 −1-线性（可加性 + 零推出）。 -/
theorem algForm1_neg_smul [Microlinear R X] (ω : AlgForm1 R X)
    (hadd : ∀ φ ψ : TangentVectorField R X, ω (φ + ψ) = ω φ + ω ψ)
    (hzero : ω 0 = 0) (φ : TangentVectorField R X) :
    ω ((-1 : R) • φ) = -ω φ := by
  have h1 : ω ((-1 : R) • φ + φ) = ω ((-1 : R) • φ) + ω φ := hadd _ _
  rw [field_add_neg_smul φ, hzero] at h1
  exact eq_neg_of_add_eq_zero_left h1.symm

/-- **W-引理：括号对 −1 缩放的齐次性**：`[(−1)·φ, η] = (−1)·[φ, η]`。

证明：`((−1)·φ)` 的轨道是 φ-轨道在参数 `−d`，故交换子
`K((−1)·φ,η)(d,e) = K(φ,η)(−d,e)`（轨道复合逐点同形）；两侧变换
`t_{[(−1)φ],η}` 与 `t_{[φ,η]}∘(参数取负)` 都是 `K((−1)·φ,η)` 的
Property W 因子化，唯一性相等。 -/
theorem lieBracket_neg_smul_left [Microlinear R X] [PropertyW R X]
    (φ η : TangentVectorField R X) :
    lieBracket ((-1 : R) • φ) η = (-1 : R) • lieBracket φ η := by
  apply Subtype.ext
  funext x
  funext d
  show lieBracketTransform ((-1 : R) • φ) η d x
    = lieBracketTransform φ η ((-1 : R) • d) x
  obtain ⟨t'', hspec'', huniq''⟩ := PropertyW.propertyW (R := R) (M := X → X)
    (fun d₁ d₂ => transformationCommutator ((-1 : R) • φ) η d₁ d₂)
    (fun d₁ => transformationCommutator_rightAxis ((-1 : R) • φ) η d₁)
    (fun d₂ => transformationCommutator_leftAxis ((-1 : R) • φ) η d₂)
  have hK : ∀ d₁ d₂ : D R,
      lieBracketTransform ((-1 : R) • φ) η (D.mul R d₁ d₂)
        = transformationCommutator ((-1 : R) • φ) η d₁ d₂ :=
    fun d₁ d₂ => lieBracketTransform_spec ((-1 : R) • φ) η d₁ d₂
  have hK2 : ∀ d₁ d₂ : D R,
      (fun δ : D R => lieBracketTransform φ η ((-1 : R) • δ)) (D.mul R d₁ d₂)
        = transformationCommutator ((-1 : R) • φ) η d₁ d₂ := by
    intro d₁ d₂
    show lieBracketTransform φ η ((-1 : R) • (D.mul R d₁ d₂))
      = transformationCommutator ((-1 : R) • φ) η d₁ d₂
    have hsplit : ((-1 : R) • (D.mul R d₁ d₂) : D R) = D.mul R (-d₁) d₂ := by
      apply Subtype.ext
      show (-1 : R) * ((d₁ : R) * (d₂ : R)) = -(d₁ : R) * (d₂ : R)
      ring
    rw [hsplit, lieBracketTransform_spec φ η (-d₁) d₂]
    show (fun x' : X => η.1 (φ.1 (η.1 (φ.1 x' (-d₁)) d₂) (-(-d₁))) (-d₂))
      = (fun x' : X => η.1 (((-1 : R) • φ).1 (η.1 (((-1 : R) • φ).1 x' d₁) d₂) (-d₁)) (-d₂))
    have hs : ∀ (y : X) (d' : D R), ((-1 : R) • φ).1 y d' = φ.1 y (-d') := by
      intro y d'
      show (φ.1 y) ((-1 : R) • d') = φ.1 y (-d')
      rw [D.neg_one_smul]
    simp only [hs]
  have hw1 : lieBracketTransform ((-1 : R) • φ) η = t'' := huniq'' _ hK
  have hw2 : (fun δ : D R => lieBracketTransform φ η ((-1 : R) • δ)) = t'' := huniq'' _ hK2
  rw [hw1, ← hw2]

/-- **d² = 0（1-形式层，好形式类）**：对与函数作用相容的 1-形式 ω
（场可加 `hadd`、零保持 `hzero`、三体折叠 `hfold`——凡三个场的
函数作用之和为零则 ω-值之和为零），Koszul 外微分的平方为零。

证明：`d(dω)` 的 Koszul 展开中六个二阶导数项对与三个 ω-复合项对
自动相消（纯 ring），剩余 `ω([[ξ₀,ξ₁],ξ₂]) − ω([[ξ₀,ξ₂],ξ₁])
+ ω([[ξ₁,ξ₂],ξ₀]])`——第二项经 ω-负线性（`algForm1_neg_smul`）与
括号对 −1 缩放的齐次性（`lieBracket_neg_smul_left`，内层反对称）
化为 `+ω([[ξ₂,ξ₀],ξ₁]])`，三项恰为函数层 Jacobi（`fieldDeriv_jacobi`）
的三场组合，由 `hfold` 收尾。 -/
theorem algD_d2_one_form [Microlinear R X] [PropertyW R X] [Microlinear R R]
    (ω : AlgForm1 R X)
    (hadd : ∀ φ ψ : TangentVectorField R X, ω (φ + ψ) = ω φ + ω ψ)
    (hzero : ω 0 = 0)
    (hfold : ∀ φ₁ φ₂ φ₃ : TangentVectorField R X,
      (∀ g : X → R, fieldDeriv φ₁ g + fieldDeriv φ₂ g + fieldDeriv φ₃ g = 0) →
      ω φ₁ + ω φ₂ + ω φ₃ = 0)
    (ξ₀ ξ₁ ξ₂ : TangentVectorField R X) :
    algD2 (algD1 ω) ξ₀ ξ₁ ξ₂ = 0 := by
  funext x
  have hneg := algForm1_neg_smul ω hadd hzero
  have hswap : lieBracket (lieBracket ξ₂ ξ₀) ξ₁
      = (-1 : R) • lieBracket (lieBracket ξ₀ ξ₂) ξ₁ := by
    rw [lieBracket_antisymm ξ₀ ξ₂, lieBracket_neg_smul_left]
  have hJ := fieldDeriv_jacobi ξ₀ ξ₁ ξ₂
  have hswap2 : lieBracket (lieBracket ξ₀ ξ₂) ξ₁
      = (-1 : R) • lieBracket (lieBracket ξ₂ ξ₀) ξ₁ := by
    rw [lieBracket_antisymm ξ₂ ξ₀, lieBracket_neg_smul_left]
  have hfold3 := hfold (lieBracket (lieBracket ξ₀ ξ₁) ξ₂)
    ((-1 : R) • lieBracket (lieBracket ξ₀ ξ₂) ξ₁) (lieBracket (lieBracket ξ₁ ξ₂) ξ₀) (by
      intro g
      have hfs : fieldDeriv ((-1 : R) • lieBracket (lieBracket ξ₀ ξ₂) ξ₁) g
          = fieldDeriv (lieBracket (lieBracket ξ₂ ξ₀) ξ₁) g := by
        rw [hswap2, fieldDeriv_smulR_field, fieldDeriv_smulR_field, smul_smul,
        show ((-1 : R) * (-1) : R) = 1 from by ring, one_smul]
      rw [hfs]
      linear_combination (norm := ring_nf) (hJ g))
  show algD2 (algD1 ω) ξ₀ ξ₁ ξ₂ x = 0
  have hpair : algD2 (algD1 ω) ξ₀ ξ₁ ξ₂ x
      = ω (lieBracket (lieBracket ξ₀ ξ₁) ξ₂) x
        + ω ((-1 : R) • lieBracket (lieBracket ξ₀ ξ₂) ξ₁) x
        + ω (lieBracket (lieBracket ξ₁ ξ₂) ξ₀) x := by
    simp only [algD2, algD1, Pi.zero_apply]
    rw [fieldDeriv_sub ξ₀, fieldDeriv_sub ξ₀, fieldDeriv_sub ξ₁, fieldDeriv_sub ξ₁,
      fieldDeriv_sub ξ₂, fieldDeriv_sub ξ₂,
      fieldDeriv_lieBracket ξ₀ ξ₁ (ω ξ₂), fieldDeriv_lieBracket ξ₀ ξ₂ (ω ξ₁),
      fieldDeriv_lieBracket ξ₁ ξ₂ (ω ξ₀)]
    simp only [Pi.sub_apply, Pi.add_apply, Pi.zero_apply]
    have hnegx : -ω (lieBracket (lieBracket ξ₀ ξ₂) ξ₁) x
        = ω ((-1 : R) • lieBracket (lieBracket ξ₀ ξ₂) ξ₁) x := by
      have h2 := congrFun (hneg (lieBracket (lieBracket ξ₀ ξ₂) ξ₁)) x
      simp only [Pi.neg_apply] at h2
      exact h2.symm
    ring_nf
    simp only [sub_eq_add_neg]
    rw [hnegx]
    ring
  rw [hpair]
  have hfold3x := congrFun hfold3 x
  simp only [Pi.add_apply, Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at hfold3x
  exact hfold3x

/-! ### 好形式类的实例化：精确形式与完整 d² 链（第五十七接力点）-/

/-- **零场的导数为零**。 -/
theorem fieldDeriv_zero_field (g : X → R) :
    fieldDeriv (0 : TangentVectorField R X) g = 0 := by
  funext x
  show directionalDerivative g (toFiber (0 : TangentVectorField R X) x) = 0
  rw [toFiber_zero]
  exact directionalDerivative_zero g x

/-- **ω 尊重函数作用相等**（好形式假设三件套的推论）：
若两场的函数作用逐函数相等，则 ω-值相等——
三场组 `(φ, (−1)·χ, 0)` 的函数作用和为零，hfold 给出
`ω φ − ω χ = 0`。 -/
theorem algForm1_congr_action [Microlinear R X] (ω : AlgForm1 R X)
    (hadd : ∀ φ ψ : TangentVectorField R X, ω (φ + ψ) = ω φ + ω ψ)
    (hzero : ω 0 = 0)
    (hfold : ∀ φ₁ φ₂ φ₃ : TangentVectorField R X,
      (∀ g : X → R, fieldDeriv φ₁ g + fieldDeriv φ₂ g + fieldDeriv φ₃ g = 0) →
      ω φ₁ + ω φ₂ + ω φ₃ = 0)
    (hneg : ∀ φ : TangentVectorField R X, ω ((-1 : R) • φ) = -ω φ)
    (φ χ : TangentVectorField R X)
    (h : ∀ g : X → R, fieldDeriv φ g = fieldDeriv χ g) :
    ω φ = ω χ := by
  funext x
  have h3 := hfold φ ((-1 : R) • χ) 0 (by
    intro g
    show fieldDeriv φ g + fieldDeriv ((-1 : R) • χ) g
      + fieldDeriv (0 : TangentVectorField R X) g = 0
    rw [h g, fieldDeriv_smulR_field (-1 : R) χ g, fieldDeriv_zero_field g]
    funext z
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.zero_apply, smul_eq_mul]
    ring)
  have h3x := congrFun h3 x
  simp only [Pi.add_apply, Pi.zero_apply] at h3x
  have hnegx := congrFun (hneg χ) x
  simp only [Pi.neg_apply] at hnegx
  have hzx := congrFun hzero x
  simp only [Pi.zero_apply] at hzx
  rw [hnegx, hzx, add_zero] at h3x
  have hfin : ω φ x = -(-ω χ x) := eq_neg_of_add_eq_zero_left h3x
  rw [hfin, neg_neg]

/-- **d₀f 满足好形式假设·可加性**（fieldDeriv_add_fields 直推）。 -/
theorem algForm1_good_d0_add [Microlinear R X] [Microlinear R R] (f : X → R)
    (φ ψ : TangentVectorField R X) :
    algD0 f (φ + ψ) = algD0 f φ + algD0 f ψ := by
  show fieldDeriv (φ + ψ) f = fieldDeriv φ f + fieldDeriv ψ f
  exact fieldDeriv_add_fields φ ψ f

/-- **d₀f 满足好形式假设·零保持**。 -/
theorem algForm1_good_d0_zero (f : X → R) :
    algD0 f 0 = 0 := by
  funext x
  show fieldDeriv (0 : TangentVectorField R X) f x = 0
  show directionalDerivative f (toFiber (0 : TangentVectorField R X) x) = 0
  rw [toFiber_zero]
  exact directionalDerivative_zero f x

/-- **d₀f 满足好形式假设·三体折叠**（hfold-假设取 `g := f` 直接）。 -/
theorem algForm1_good_d0_hfold (f : X → R)
    (φ₁ φ₂ φ₃ : TangentVectorField R X)
    (h : ∀ g : X → R, fieldDeriv φ₁ g + fieldDeriv φ₂ g + fieldDeriv φ₃ g = 0) :
    algD0 f φ₁ + algD0 f φ₂ + algD0 f φ₃ = 0 := by
  show fieldDeriv φ₁ f + fieldDeriv φ₂ f + fieldDeriv φ₃ f = 0
  exact h f

/-- **⭐ 完整 d² 链（精确形式）**：`d²(d₀f) = 0`——零假设、零选择公理。
`d₀f` 的好形式三假设由上面三条引理直接供给，`algD_d2_one_form` 收官。 -/
theorem algD_d2_exact [Microlinear R X] [PropertyW R X] [Microlinear R R]
    (f : X → R) (ξ₀ ξ₁ ξ₂ : TangentVectorField R X) :
    algD2 (algD1 (algD0 f)) ξ₀ ξ₁ ξ₂ = 0 :=
  algD_d2_one_form (algD0 f) (algForm1_good_d0_add f) (algForm1_good_d0_zero f)
    (algForm1_good_d0_hfold f) ξ₀ ξ₁ ξ₂

/-! ### 场变元楔积（1-形式×1-形式）与分次 Leibniz 核心情形（第五十八接力点）-/

/-- **1-形式×1-形式的楔积**：`(α∧ω)(ξ,η) = α(ξ)·ω(η) − α(η)·ω(ξ)`——
`d₀f ∧ ω` 为特例。 -/
def wedge11 (α ω : AlgForm1 R X) : AlgForm2 R X :=
  fun ξ η => fun x => α ξ x * ω η x - α η x * ω ξ x

/-- wedge11 的点态展开。 -/
theorem wedge11_apply (α ω : AlgForm1 R X) (ξ η : TangentVectorField R X) (x : X) :
    wedge11 α ω ξ η x = α ξ x * ω η x - α η x * ω ξ x := rfl

/-- **楔积的反对称性**。 -/
theorem wedge11_antisymm (α ω : AlgForm1 R X) (ξ η : TangentVectorField R X) :
    wedge11 α ω ξ η = -wedge11 α ω η ξ := by
  funext x
  show α ξ x * ω η x - α η x * ω ξ x
    = -(α η x * ω ξ x - α ξ x * ω η x)
  ring

/-- 楔积对左变元的加法性。 -/
theorem wedge11_add_left (α α' ω : AlgForm1 R X) :
    wedge11 (α + α') ω = wedge11 α ω + wedge11 α' ω := by
  funext ξ η x
  simp only [wedge11, Pi.add_apply]
  show (α ξ x + α' ξ x) * ω η x - (α η x + α' η x) * ω ξ x
    = (α ξ x * ω η x - α η x * ω ξ x) + (α' ξ x * ω η x - α' η x * ω ξ x)
  ring

/-- 楔积对左变元的数乘性。 -/
theorem wedge11_smul_left (c : R) (α ω : AlgForm1 R X) :
    wedge11 (c • α) ω = c • wedge11 α ω := by
  funext ξ η x
  simp only [wedge11, Pi.smul_apply, Pi.smul_apply, smul_eq_mul]
  show c * α ξ x * ω η x - c * α η x * ω ξ x
    = c * (α ξ x * ω η x - α η x * ω ξ x)
  ring

/-- **⭐ 分次 Leibniz（核心情形：0-形式×1-形式）**：
`d(f·ω) = f·dω + d₀f∧ω`——一般 p×q 分次 Leibniz 的生成元。 -/
theorem algD1_algSMul_wedge [Microlinear R X] [PropertyW R X]
    (f : X → R) (ω : AlgForm1 R X) :
    algD1 (algSMul f ω) = f • algD1 ω + wedge11 (algD0 f) ω := by
  funext ξ η x
  show fieldDeriv ξ (f * ω η) x - fieldDeriv η (f * ω ξ) x - f x * ω (lieBracket ξ η) x
    = f x * (fieldDeriv ξ (ω η) x - fieldDeriv η (ω ξ) x - ω (lieBracket ξ η) x)
      + (fieldDeriv ξ f x * ω η x - fieldDeriv η f x * ω ξ x)
  rw [fieldDeriv_mul ξ f (ω η), fieldDeriv_mul η f (ω ξ)]
  simp only [Pi.add_apply, Pi.mul_apply]
  ring

/-! ### 分次 Leibniz 完整情形（1×1）：d(α∧ω) = dα∧ω − α∧dω（第五十八接力点续）-/

/-- **2-形式×1-形式的插入**：`(β∧ω)(ξ₀,ξ₁,ξ₂) = β(ξ₀,ξ₁)·ω(ξ₂)
− β(ξ₀,ξ₂)·ω(ξ₁) + β(ξ₁,ξ₂)·ω(ξ₀)`。 -/
def wedge21 (β : AlgForm2 R X) (ω : AlgForm1 R X) :
    TangentVectorField R X → TangentVectorField R X → TangentVectorField R X → (X → R) :=
  fun ξ₀ ξ₁ ξ₂ => fun x =>
    β ξ₀ ξ₁ x * ω ξ₂ x - β ξ₀ ξ₂ x * ω ξ₁ x + β ξ₁ ξ₂ x * ω ξ₀ x

/-- **1-形式×2-形式的插入**：`(α∧β)(ξ₀,ξ₁,ξ₂) = α(ξ₀)·β(ξ₁,ξ₂)
− α(ξ₁)·β(ξ₀,ξ₂) + α(ξ₂)·β(ξ₀,ξ₁)`。 -/
def wedge12 (α : AlgForm1 R X) (β : AlgForm2 R X) :
    TangentVectorField R X → TangentVectorField R X → TangentVectorField R X → (X → R) :=
  fun ξ₀ ξ₁ ξ₂ => fun x =>
    α ξ₀ x * β ξ₁ ξ₂ x - α ξ₁ x * β ξ₀ ξ₂ x + α ξ₂ x * β ξ₀ ξ₁ x

/-- **⭐ 分次 Leibniz（1×1 完整情形）**：
`d(α∧ω) = dα∧ω − α∧dω`——Koszul 三顶点展开后 **18 对项全部由
纯 ring 配对相消**（α-括号项与 ω-括号项各自与 wedge-插入项配对，
无需场层 Jacobi）。工程要点：wedge11-体的 λ-参数先经 rfl-桥统一为
β-形（`α ξ₁ * ω ξ₂` 的 Π-层），`fieldDeriv_sub/mul` 显式实例化
（rw 在 λ-绑定下实例化元变量失败的老坑）。 -/
theorem d_wedge11 [Microlinear R X] [PropertyW R X] [Microlinear R R]
    (α ω : AlgForm1 R X) :
    algD2 (wedge11 α ω) = wedge21 (algD1 α) ω - wedge12 α (algD1 ω) := by
  funext ξ₀ ξ₁ ξ₂ x
  have hpair : algD2 (wedge11 α ω) ξ₀ ξ₁ ξ₂ x
      = wedge21 (algD1 α) ω ξ₀ ξ₁ ξ₂ x - wedge12 α (algD1 ω) ξ₀ ξ₁ ξ₂ x := by
    have hb1 : wedge11 α ω ξ₁ ξ₂
        = α ξ₁ * ω ξ₂ - α ξ₂ * ω ξ₁ := rfl
    have hb2 : wedge11 α ω ξ₀ ξ₂
        = α ξ₀ * ω ξ₂ - α ξ₂ * ω ξ₀ := rfl
    have hb3 : wedge11 α ω ξ₀ ξ₁
        = α ξ₀ * ω ξ₁ - α ξ₁ * ω ξ₀ := rfl
    have hb4 : wedge11 α ω (lieBracket ξ₀ ξ₁) ξ₂
        = α (lieBracket ξ₀ ξ₁) * ω ξ₂ - α ξ₂ * ω (lieBracket ξ₀ ξ₁) := rfl
    have hb5 : wedge11 α ω (lieBracket ξ₀ ξ₂) ξ₁
        = α (lieBracket ξ₀ ξ₂) * ω ξ₁ - α ξ₁ * ω (lieBracket ξ₀ ξ₂) := rfl
    have hb6 : wedge11 α ω (lieBracket ξ₁ ξ₂) ξ₀
        = α (lieBracket ξ₁ ξ₂) * ω ξ₀ - α ξ₀ * ω (lieBracket ξ₁ ξ₂) := rfl
    show algD2 (wedge11 α ω) ξ₀ ξ₁ ξ₂ x = _
    simp only [algD2, hb1, hb2, hb3, hb4, hb5, hb6, Pi.zero_apply]
    rw [fieldDeriv_sub ξ₀ (α ξ₁ * ω ξ₂) (α ξ₂ * ω ξ₁),
      fieldDeriv_sub ξ₁ (α ξ₀ * ω ξ₂) (α ξ₂ * ω ξ₀),
      fieldDeriv_sub ξ₂ (α ξ₀ * ω ξ₁) (α ξ₁ * ω ξ₀),
      fieldDeriv_mul ξ₀ (α ξ₁) (ω ξ₂), fieldDeriv_mul ξ₀ (α ξ₂) (ω ξ₁),
      fieldDeriv_mul ξ₁ (α ξ₀) (ω ξ₂), fieldDeriv_mul ξ₁ (α ξ₂) (ω ξ₀),
      fieldDeriv_mul ξ₂ (α ξ₀) (ω ξ₁), fieldDeriv_mul ξ₂ (α ξ₁) (ω ξ₀)]
    simp only [algD1, Pi.zero_apply, wedge21, wedge12, Pi.mul_apply, Pi.sub_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hpair]
  simp only [Pi.sub_apply]

/-! ### 3-形式层与交错化算子（第五十九接力点）-/

/-- 3-形式（场变元）。 -/
abbrev AlgForm3 (R : Type u) [IsKockLawvere_one R] (X : Type u) :=
  TangentVectorField R X → TangentVectorField R X → TangentVectorField R X → (X → R)

/-- **Koszul 4-顶点外微分**（p = 3；符号约定与 algD1/algD2 一致：
第一和 `Σ(−1)ⁱ ξᵢ(α(rest))`、第二和 `Σ_{i<j}(−1)^{i+j}
α([ξᵢ,ξⱼ],rest-rest)`）。 -/
def algD3 [Microlinear R X] [PropertyW R X] (α : AlgForm3 R X) :
    TangentVectorField R X → TangentVectorField R X → TangentVectorField R X →
    TangentVectorField R X → (X → R) :=
  fun ξ₀ ξ₁ ξ₂ ξ₃ => fun x =>
    fieldDeriv ξ₀ (α ξ₁ ξ₂ ξ₃) x - fieldDeriv ξ₁ (α ξ₀ ξ₂ ξ₃) x
      + fieldDeriv ξ₂ (α ξ₀ ξ₁ ξ₃) x - fieldDeriv ξ₃ (α ξ₀ ξ₁ ξ₂) x
      - α (lieBracket ξ₀ ξ₁) ξ₂ ξ₃ x + α (lieBracket ξ₀ ξ₂) ξ₁ ξ₃ x
      - α (lieBracket ξ₀ ξ₃) ξ₁ ξ₂ x
      - α (lieBracket ξ₁ ξ₂) ξ₀ ξ₃ x + α (lieBracket ξ₁ ξ₃) ξ₀ ξ₂ x
      - α (lieBracket ξ₂ ξ₃) ξ₀ ξ₁ x

/-- algD3 的点态展开。 -/
theorem algD3_apply [Microlinear R X] [PropertyW R X] (α : AlgForm3 R X)
    (ξ₀ ξ₁ ξ₂ ξ₃ : TangentVectorField R X) (x : X) :
    algD3 α ξ₀ ξ₁ ξ₂ ξ₃ x
      = fieldDeriv ξ₀ (α ξ₁ ξ₂ ξ₃) x - fieldDeriv ξ₁ (α ξ₀ ξ₂ ξ₃) x
        + fieldDeriv ξ₂ (α ξ₀ ξ₁ ξ₃) x - fieldDeriv ξ₃ (α ξ₀ ξ₁ ξ₂) x
        - α (lieBracket ξ₀ ξ₁) ξ₂ ξ₃ x + α (lieBracket ξ₀ ξ₂) ξ₁ ξ₃ x
        - α (lieBracket ξ₀ ξ₃) ξ₁ ξ₂ x
        - α (lieBracket ξ₁ ξ₂) ξ₀ ξ₃ x + α (lieBracket ξ₁ ξ₃) ξ₀ ξ₂ x
        - α (lieBracket ξ₂ ξ₃) ξ₀ ξ₁ x := rfl

/-- algD3 对形式变元的加法性。 -/
theorem algD3_add [Microlinear R X] [PropertyW R X] (α₁ α₂ : AlgForm3 R X)
    (ξ₀ ξ₁ ξ₂ ξ₃ : TangentVectorField R X) :
    algD3 (α₁ + α₂) ξ₀ ξ₁ ξ₂ ξ₃ = algD3 α₁ ξ₀ ξ₁ ξ₂ ξ₃ + algD3 α₂ ξ₀ ξ₁ ξ₂ ξ₃ := by
  funext x
  simp only [algD3, Pi.add_apply, Pi.sub_apply, fieldDeriv_add]
  ring

/-- algD3 对形式变元的数乘性。 -/
theorem algD3_smul [Microlinear R X] [PropertyW R X] (c : R) (α : AlgForm3 R X)
    (ξ₀ ξ₁ ξ₂ ξ₃ : TangentVectorField R X) :
    algD3 (c • α) ξ₀ ξ₁ ξ₂ ξ₃ = c • algD3 α ξ₀ ξ₁ ξ₂ ξ₃ := by
  funext x
  simp only [algD3, Pi.smul_apply, Pi.sub_apply, fieldDeriv_smul, smul_eq_mul,
    Pi.add_apply]
  ring

/-- **1-形式张量积**：`(α⊗ω)(ξ,η) = α(ξ)·ω(η)`（不交错）。 -/
def algTens2 (α ω : AlgForm1 R X) : AlgForm2 R X :=
  fun ξ η => fun x => α ξ x * ω η x

/-- **alt2：2-变元交错化算子**（swap-反序和：
`alt2(β)(ξ,η) = β(ξ,η) − β(η,ξ)`——E3 置换引擎的 permSum 在 q = 2
的具体化，全部置换 = 恒等与对换）。 -/
def alt2 (β : AlgForm2 R X) : AlgForm2 R X :=
  fun ξ η => fun x => β ξ η x - β η ξ x

/-- **楔积 = 交错化张量积**（q = 2 定理）：`α∧ω = alt2(α⊗ω)`——
连接经典楔积的交错化定义。 -/
theorem wedge11_eq_alt2 (α ω : AlgForm1 R X) :
    wedge11 α ω = alt2 (algTens2 α ω) := by
  funext ξ η x
  show α ξ x * ω η x - α η x * ω ξ x = _
  rfl

/-- alt2 的输出是反对称的。 -/
theorem alt2_antisymm (β : AlgForm2 R X) (ξ η : TangentVectorField R X) :
    alt2 β ξ η = -alt2 β η ξ := by
  funext x
  show β ξ η x - β η ξ x = -(β η ξ x - β ξ η x)
  ring

/-- **alt2 是投影的倍数**：`alt2(alt2 β) = 2·alt2 β`——
（除以 2! 需 2 可逆，这里保留倍数形式，与 E2c 的 `h2 : ∃ y, y*2 = 1`
假设接口相容）。 -/
theorem alt2_idem (β : AlgForm2 R X) :
    alt2 (alt2 β) = (2 : R) • alt2 β := by
  funext ξ η x
  simp only [alt2, Pi.smul_apply]
  show (β ξ η x - β η ξ x) - (β η ξ x - β ξ η x)
    = 2 * (β ξ η x - β η ξ x)
  ring

/-! ### 各层级零引理与三阶链（第六十接力点）-/

/-- **零函数的场导数为零**（KL 唯一性）。 -/
theorem fieldDeriv_zero_fun (ξ : TangentVectorField R X) :
    fieldDeriv ξ (0 : X → R) = 0 := by
  funext x
  have key : ∀ d : D R, (0 : X → R) (ξ.1 x d)
      = (0 : X → R) (ξ.1 x 0) + (0 : R) * ((d : D R) : R) := by
    intro d
    show (0 : R) = (0 : R) + (0 : R) * ((d : D R) : R)
    ring
  exact ((IsKockLawvere_one.isKockLawvere_one (R := R)
    (fun d : D R => (0 : X → R) ((TangentVectorField.toFiber ξ x).1 d))).property.right _ key).symm

/-- algD1 的零输入。 -/
theorem algD1_zero [Microlinear R X] [PropertyW R X] :
    algD1 (0 : AlgForm1 R X) = (0 : AlgForm2 R X) := by
  funext ξ η x
  simp only [algD1, Pi.zero_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply,
    Pi.add_apply, fieldDeriv_zero_fun]
  ring

/-- algD2 的零输入。 -/
theorem algD2_zero [Microlinear R X] [PropertyW R X] :
    algD2 (0 : AlgForm2 R X) = (0 : AlgForm3 R X) := by
  funext ξ₀ ξ₁ ξ₂ x
  simp only [algD2, Pi.zero_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply,
    Pi.add_apply, fieldDeriv_zero_fun]
  ring

/-- algD3 的零输入。 -/
theorem algD3_zero [Microlinear R X] [PropertyW R X] :
    algD3 (0 : AlgForm3 R X) = 0 := by
  funext ξ₀ ξ₁ ξ₂ ξ₃ x
  simp only [algD3, Pi.zero_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply,
    Pi.add_apply, fieldDeriv_zero_fun]
  ring

/-- **⭐ 三阶链（精确形式）**：`d³(d₀f) = 0`——`d²(d₀f) = 0`
（第五十六接力点）与各层级零引理的推论：
`d(d²(d₀f)) = d(0) = 0`。 -/
theorem algD_d3_exact [Microlinear R X] [PropertyW R X] [Microlinear R R]
    (f : X → R) (ξ₀ ξ₁ ξ₂ ξ₃ : TangentVectorField R X) :
    algD3 (algD2 (algD1 (algD0 f))) ξ₀ ξ₁ ξ₂ ξ₃ = 0 := by
  have h0 : algD1 (algD0 f) = (0 : AlgForm2 R X) := by
    funext φ η
    exact algD_d2_zero_form f φ η
  have h1 : algD2 (algD1 (algD0 f)) = (0 : AlgForm3 R X) := by
    rw [h0]
    exact algD2_zero
  rw [h1]
  exact congrArg (fun F => F ξ₀ ξ₁ ξ₂ ξ₃) algD3_zero

end AlgebraicForms

end SDG.DifferentialForms

#print axioms SDG.DifferentialForms.fieldDeriv_mul
#print axioms SDG.DifferentialForms.algD1
#print axioms SDG.DifferentialForms.algD1_apply
