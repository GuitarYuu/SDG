# 论文可行性分析

## 1. 是否已有相关形式化？

### 已知的 SDG / 微分几何形式化项目
（2026-11-07 核实：已通读 Brasca–Clemente 原文 arXiv:2603.17457v3 全文 32 页）

| 项目 | 证明助手 | 范围 | 与本项目的关系 |
|---|---|---|---|
| **Brasca–Clemente，《Synthetic Differential Geometry in Lean》**（arXiv:2603.17457v3，2026-10-19，已过同行评审） | Lean 4 + mathlib | **SDG 基础微积分**：Dₖ、KL 公理（Koc06 公理 1 与 1′）、导数 ∂ 与消去引理、Leibniz/链式/幂法则、**单变量 Taylor（Thm 4.2.3）与多变量 Taylor（Thm 5.2.4，主定理）**、偏导交换 ∂ᵢ∂ⱼ=∂ⱼ∂ᵢ（Prop 5.1.4） | **直接相关、必须引用**。只做 Taylor 展开侧；全文**无**微分形式、外微分 d、d²=0、楔积、李括号、电流、上同调、积分公理、微线性（逐节核对） |
| SynthLean（Nawrocki et al., CPP 2026） | Lean 4 | 合成数学推理框架 | 相邻领域，非 SDG de Rham |
| Mathlib 的经典微分几何 | Lean 4 | 流形、切丛、微分形式、Stokes | **不同框架**——经典路线（局部坐标+拓扑），非合成路线 |
| Fermat (Coq)、Agda/HoTT SDG | Coq/Agda | SDG 基础探索（KL、微线性） | 研究原型，未涉及 de Rham 复形 |

> **Brasca–Clemente 的工程方法**（对照）：显式添加**唯一选择公理**
> `axiom axiom_unique_choice`（Koc06 II.3.4 在 topos 内成立、Lean 需显式加入）；
> Damiano Testa 的 choice-linter；**fork mathlib** 改写 1.6 万+ 条声明为
> choice-free（Rat.instField、`Fintype (Fin n)` 等）。他们把 smooth topos /
> well-adapted models 留给 "forthcoming work"——该赛道已占，本项目不竞争。
>
> **本项目对照优势**：零 fork（Fin 专用构造性替身 `FinPerm`/`finSum`/`finProd`）、
> **不引入唯一选择公理**（KL 数据化 + 子类型投影）——111 条核心声明 axiom
> 足迹为 `[propext, Quot.sound]`，严格小于他们的
> `[propext, Quot.sound, axiom_unique_choice]`。诚实注记：他们的 KL 假设
> （∃! 形式）本身比我们的数据化 KL 稍弱，在 topos 内部二者等价
> （呼应其 Remark 4.1.2），论文中应写明。

### 发表的空白点（核实后修正）

1. ~~"首个 Lean 4 SDG 形式化"~~ ——已被 Brasca–Clemente 占据（Taylor 微积分侧）。
   **本项目定位改为：把 Lean 4 的 SDG 形式化从 Taylor 微积分推进到 de Rham 复形。**
2. **首个** 微分形式 + Koszul 外微分 + **d²=0** 的 SDG 形式化（两层：单纯层+场变元层；场变元层含 0/1/2-形式三层 d²=0 与三阶链 d³）——他们全文未涉及
3. **首个** SDG 李括号形式化（Property W 因子化路线、反对称、交换子公式、Jacobi）——他们连向量场对象都没有
4. **首个** SDG 电流层与 Stokes 配对、Hⁿ/Hₙ 同调群、cup 积——他们未涉及
5. **微线性理论**（Microlinear R R ⇒ KL 全 schema、方向导数沿切向量和可加）——他们不需要也未发展
6. **积分层**（FTC、分部积分）——他们连 Kock 积分公理都未引入
7. 更小公理足迹 + 不 fork mathlib 的构造性方法论（与他们的 fork 路线形成方法论对照）

---

## 2. 适合发什么论文？

### 目标期刊/会议

| 级别 | 期刊/会议 | 匹配度 | 理由 |
|---|---|---|---|
| **顶会** | CPP (Certified Programs and Proofs) | ⭐⭐⭐ | 形式化证明的正确赛道 |
| **顶会** | ITP (Interactive Theorem Proving) | ⭐⭐⭐ | 形式化数学的标准出口；SDG 是新领域 |
| **期刊** | Mathematical Structures in Computer Science | ⭐⭐ | SDG+类型论交叉 |
| **期刊** | Journal of Formalized Reasoning | ⭐⭐ | 开放获取 |
| **arXiv** | cs.LO / math.CT | 预印本 | 先挂 arXiv |

### 推荐论文主题

**Option A（推荐）：de Rham 复形形式化论文**

> "The de Rham Complex in Synthetic Differential Geometry: A Choice-Free
> Formalization in Lean 4"
> 覆盖 微分形式 → Koszul d → d²=0（两层）→ 李括号 → 电流层 → 上同调
> 卖点：把 SDG 形式化从 Brasca–Clemente 的 Taylor 微积分推进到 de Rham 链；
> 零选择公理（连唯一选择也不用）；111 条审计；微线性与李括号理论
> 页数：20-30 页

**Option B：聚焦 d²=0 技术论文**

> "Constructive Proofs of d²=0 for de Rham Complexes in SDG"
> 聚焦两层（单纯+场变元）d²=0 的证明策略与工程经验
> 页数：15-20 页

**Option C：聚焦无选择公理方法论**

> "Formalizing Mathematics Without the Axiom of Choice: A Case Study in SDG"
> 聚焦 NoChoice 审计范式与 choice-free 替身设计
> 页数：12-18 页

---

## 3. 作者排序与贡献保证

### 贡献分配（基于 git 记录）

| 贡献者 | 角色 | 代码量 | 提交数 | 核心贡献 |
|---|---|---|---|---|
| **caojiarong** | 奠基者 | ~6,700 行 (35%) | 19 | 基础设施：NoChoice 审计框架、KL 公理、无穷小对象、微线性、切丛模结构、Core 逐点形式层、d₀、FinSumProd |
| **GuitarYuu** | 完成者/核心贡献者 | ~12,300 行 (65%) | 111+16 | 核心定理：∂²=0 全层、cup 积全套、分次 Leibniz/交换律、Hⁿ/Hₙ 同调群、Module R、Stokes 配对、**场变元代数层**（李括号配套+Koszul 外微分+d²=0 两层闭环+楔积+可加性突破）、FTC+分部积分、AuditSweep |

### 推荐排序

**Option A（一作 GuitarYuu，二作 caojiarong）**——推荐

理由：核心理论闭环（d²=0 两层）由 GuitarYuu 完成；全部 111 提交由
GuitarYuu 贡献；论文撰写由 GuitarYuu 承担；caojiarong 的基础设施
贡献通过正文引用与致谢充分体现。

**Option B（共同一作）**

如果 caojiarong 参与论文修订和审稿回应，可升级为共同一作。

### 贡献保证机制

1. **Git 记录**：130 个提交的时间线与作者归属（不可篡改）
2. **代码归属**：每个文件的首位作者可从 git log 追溯
3. **时间戳**：暑校期间（8 月）vs 后续（10-11 月）清晰分离
4. **RESUME.md**：62 个接力点的工程日志记录每步作者
5. **Lean 的 `#print axioms`**：每条声明的依赖链可追溯到模块

---

## 4. 论文结构建议

1. Introduction
2. Mathematical Background（Kock 的 SDG 框架）
3. Why No Choice?（SDG 中选择公理的问题 + NoChoice 框架）
4. Formalization Architecture（模块图 + 层级依赖）
5. The Simplicial de Rham Complex（∂²=0 + cup 积）
6. The Field-Variable Layer（李括号 + Koszul d + d²=0）
7. Currents and Stokes Pairing
8. Audit Methodology（111 条声明的 axiom 分析）
9. Related Work
10. Conclusion

---

## 5. 时间线

| 阶段 | 内容 | 时间 |
|---|---|---|
| 1 | 整理代码 + 补文档 + 填缺口 | 1-2 周 |
| 2 | 撰写初稿 | 2-3 周 |
| 3 | 内部审阅 + 修改 | 1 周 |
| 4 | 挂 arXiv + 提交 CPP/ITP 2027 | 视截稿 |
