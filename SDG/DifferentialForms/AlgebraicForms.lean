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

end AlgebraicForms

end SDG.DifferentialForms

#print axioms SDG.DifferentialForms.fieldDeriv_mul
#print axioms SDG.DifferentialForms.algD1
#print axioms SDG.DifferentialForms.algD1_apply
