import SDG.DifferentialForms.Core
import SDG.DifferentialForms.Algebra
import SDG.DifferentialForms.Simplicial
import SDG.DifferentialForms.Currents
import SDG.DifferentialForms.CupAssoc

/-!
# SDG.DifferentialForms

微分形式模块的汇总入口。基础切向量组、兼容的核心 API 和严格的
逐点交错多线性形式均定义在 `SDG.DifferentialForms.Core` 中。
形式代数、单形与 de Rham 上链代数在 `Algebra`，单形面算子在 `Simplicial`，
电流（currents）层：拓扑/紧支撑结构与电流空间在 `Currents`，
上积结合律在 `CupAssoc`。
-/
