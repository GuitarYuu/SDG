import SDG.NoChoice
import SDG.Infinitesimal
import SDG.Microlinear
import SDG.TangentBundle
import SDG.LieBracket
import SDG.DifferentialForms
import SDG.Derivative
import SDG.Taylor
import SDG.KockLawvereDkn
import SDG.WeilAlgebra
import SDG.Rational
import SDG.Order
import SDG.Integration

/-!
# SDG.Basic

综合微分几何 (Synthetic Differential Geometry, SDG) 基础（汇总导入）。

本模块把原先单文件的 SDG 基础拆分为多个主题文件：

* `SDG.Infinitesimal` — 无穷小量集合 $D$、$n$ 维无穷小邻域 $D(n)$、$D^n$，
  以及「存在且唯一」编码 `ExistsUnique'`；
* `SDG.Microlinear` — 微线性对象 `Microlinear` 与典范映射 $\Phi_n$；
* `SDG.TangentBundle` — 切从、切向量运算（加法/数乘/零）及切纤维上的 $R$-模结构；
* `SDG.LieBracket` — Property W、向量场无穷小变换的交换子，以及由此定义的李括号；
* `SDG.DifferentialForms` — 微分形式核心：同基点切向量组、齐次/交错/规范化形式，
  以及 $0$-形式的外微分；
* `SDG.Derivative` — Kock-Lawvere 公理、合成导数 `sderiv`、微商消去律、
  偏导数与混合偏导数及其交换律（Schwarz 定理）；
* `SDG.Taylor` — $D_k$ 上的 Kock-Lawvere 公理（Axiom 1'）与 Taylor 公式；
* `SDG.KockLawvereDkn` — $D_k(n)$ 上的 Kock-Lawvere 公理（Axiom 1'' 的 $k$ 阶
  版本）：每个 $f : D_k(n) \to R$ 唯一地是总次数 $\le k$ 的多项式；
* `SDG.Rational` — **无选择公理的有理数**：从整数商构造 $\mathbb{Q}$，
  得到无选择公理的 `CommRing` 与 `NontrivialRatCommAlgebra`（SDG 基环的实例）。
  （Mathlib 的 `Rat.commRing` 依赖 `Classical.choice`，故本项目自建。）
* `SDG.Order` — **序结构**：光滑直线 $R$ 上的非严格序 `≤`（有序交换环），
  以及 SDG 特有的无穷小量公理（$d \in D$ 非负则 $d = 0$，即无穷小量不参与序）；
* `SDG.Integration` — **积分公理**：每个 $f : R \to R$ 有唯一原函数
  $g$（$g(0)=0$ 且 $g' = f$），据此定义原函数 `primitive f` 与定积分
  $\int_a^b f$，并证明微积分基本定理与线性性/区间可加性。
-/
