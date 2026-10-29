import SDG.DifferentialForms
import SDG.Integration

/-! 全库核心定理 axiom 批量审计（第四十四接力点体检轮）。
预期：全部 `[propext, Quot.sound]`，零 Classical.choice / sorryAx。 -/

-- Algebra：分次交换律引擎
#print axioms SDG.DifferentialForms.sign_mul
#print axioms SDG.DifferentialForms.wedgeAnyFun_grad_comm
#print axioms SDG.DifferentialForms.wedgeAny_grad_comm
#print axioms SDG.DifferentialForms.cup_add_left
#print axioms SDG.DifferentialForms.cup_smul_left

-- StokesCup：分次 Leibniz + 上同调性 + 单位律
#print axioms SDG.DifferentialForms.coboundary_cup_product
#print axioms SDG.DifferentialForms.coboundary_cupProduct
#print axioms SDG.DifferentialForms.cupProduct_isCocycle
#print axioms SDG.DifferentialForms.cupProduct_unit_left
#print axioms SDG.DifferentialForms.cupProduct_unit_right
#print axioms SDG.DifferentialForms.coboundary_cupProduct_unit_right

-- CupAssoc：结合律 + 单位元
#print axioms SDG.DifferentialForms.cupProduct_assoc
#print axioms SDG.DifferentialForms.cupProduct_one_left
#print axioms SDG.DifferentialForms.cupProduct_one_right

-- Currents：电流层 + 配对
#print axioms SDG.DifferentialForms.currentBoundary_currentBoundary
#print axioms SDG.DifferentialForms.chainCurrent_boundary_apply
#print axioms SDG.DifferentialForms.pairing_class_well_defined
#print axioms SDG.DifferentialForms.deRhamClass_eq
#print axioms SDG.DifferentialForms.cochainOfFun_one_isCocycle
#print axioms SDG.DifferentialForms.deRhamPairing_add_left
#print axioms SDG.DifferentialForms.deRhamPairing_add_right

-- CupCohomology：商层 cup 全套
#print axioms SDG.DifferentialForms.cocycleCupZ_sound
#print axioms SDG.DifferentialForms.deRhamCup_apply
#print axioms SDG.DifferentialForms.deRhamCup_add_left
#print axioms SDG.DifferentialForms.deRhamCup_add_right
#print axioms SDG.DifferentialForms.deRhamCup_zero_left
#print axioms SDG.DifferentialForms.deRhamCup_zero_right
#print axioms SDG.DifferentialForms.deRhamCup_neg_left
#print axioms SDG.DifferentialForms.deRhamCup_neg_right
#print axioms SDG.DifferentialForms.deRhamCup_smul_left
#print axioms SDG.DifferentialForms.deRhamCup_smul_right

-- CohomologyModule：双侧模结构 + 配对 R-双线性
#print axioms SDG.DifferentialForms.instModuleDeRhamCohomology
#print axioms SDG.DifferentialForms.instModuleCurrentHomology
#print axioms SDG.DifferentialForms.deRhamClass_smul
#print axioms SDG.DifferentialForms.currentClass_smul
#print axioms SDG.DifferentialForms.deRhamPairing_smul_left
#print axioms SDG.DifferentialForms.deRhamPairing_smul_right

-- Integration：单变量积分核心
#print axioms SDG.Integration.sderiv_I_spec
#print axioms SDG.Integration.primitive_unique
