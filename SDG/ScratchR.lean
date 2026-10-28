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

end SDG.DifferentialForms
