import SDG.DifferentialForms.Algebra

import SDG.Integration
/-!
# (R) 链与分次交换律（已迁移）

本文件的全部内容（(R) permSum 右复合重排链、CastBridge、GradCommSlot、
GradComm 分次交换律组装、formLenCast 形级度数重标记与 wedgeAny_grad_comm）
已迁入 `SDG/DifferentialForms/Algebra.lean` 尾部（同名 section），进入主线
构建树。本 stub 仅为保留模块名（AuditR.lean 等审计文件的 import 目标）。
-/

namespace SDG.DifferentialForms

section FTC

/-- **FTC 代数核心**：积分的原函数性质的平移形——
`x ↦ ∫_a^x g' + g(a)` 的导数为 `g'`。由 `sderiv_integralR` +
`sderiv_add` + `sderiv_const` 直接组装。 -/
theorem sderiv_integralR_add_const {R : Type u} [SDG.Integration.IsIntegration R]
    (g : R → R) (a x : R) :
    sderiv (fun x => SDG.Integration.integralR (sderiv g) a x + g a) x
      = sderiv g x := by
  rw [sderiv_add, SDG.Integration.sderiv_integralR, sderiv_const]
  ring

end FTC

section FTC_UI

/-- **微积分基本定理（UnitInterval 版）**：
`∫_0^1 G' = G(1) - G(0)`——由积分公理的原函数唯一性：
`K := G - G 0` 满足 `K 0 = 0` 与 `K' = G'`，故 `K = primitive G'`，
而 `integral` 的定义本就是 Newton-Leibniz 形。 -/
theorem integral_ftc_UI {R : Type u} [SDG.Integration.IsIntegration R]
    (G : SDG.Order.UnitInterval R → R) :
    SDG.Integration.integral (SDG.Integration.sderiv_I G) 0 1
      = G 1 - G 0 := by
  have hK : SDG.Integration.primitive (SDG.Integration.sderiv_I G)
      = fun t => G t - G 0 := by
    symm
    exact SDG.Integration.primitive_unique (fun x => SDG.Integration.sderiv_I G x)
      (fun x => G x - G 0)
      (by show G 0 - G 0 = 0; ring)
      (by intro x
          rw [SDG.Integration.sderiv_I_sub G (fun _ => G 0) x,
            SDG.Integration.sderiv_I_const]
          ring)
  rw [SDG.Integration.integral, hK]
  show (G 1 - G 0) - (G 0 - G 0) = G 1 - G 0
  ring

end FTC_UI


end SDG.DifferentialForms
