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

/-- 1-形式（场变元）：向量场 → 函数。 -/
def AlgForm1 (R : Type u) [IsKockLawvere_one R] (X : Type u) :=
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

end AlgebraicForms

end SDG.DifferentialForms

#print axioms SDG.DifferentialForms.fieldDeriv_mul
#print axioms SDG.DifferentialForms.algD1
#print axioms SDG.DifferentialForms.algD1_apply
