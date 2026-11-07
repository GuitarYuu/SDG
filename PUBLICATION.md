# 论文可行性分析

## 1. 是否已有相关形式化？

### 已知的 SDG / 微分几何形式化项目

| 项目 | 证明助手 | 范围 | 与本项目的关系 |
|---|---|---|---|
| Mathlib 的 `SmoothSpace` 系列 | Lean 4 | 经典微分几何（流形、切丛、微分形式、Stokes） | **不同框架**——经典路线（局部坐标+拓扑），非合成路线 |
| Fermat (Coq) | Coq | SDG 基础探索（KL 公理、微线性） | 研究原型，未涉及微分形式/de Rham 复形/上同调 |
| Agda/HoTT 中的 SDG | Agda/HoTT | 微线性、无穷小群 | 不同逻辑基础 |
| Isabelle 的形式化 | Isabelle/HOL | 各种分析 | 独立框架 |

> **注意**：以上列表基于 2026-11 的知识，建议投稿前用 Google Scholar
> 搜索 "Synthetic Differential Geometry" + "Lean" / "Coq" / "formalization"
> 确认是否有新出现的相关工作。

### 发表的空白点

1. **首个** Lean 4 中的 SDG 形式化（KL 公理 + 微线性 + 切丛 + 形式层全套）
2. **首个** 无选择公理的 de Rham 复形 d²=0 构造性证明（两层：单纯+场变元）
3. **首个** SDG 框架下的李括号形式化（Property W 因子化路线，Kock I.9）
4. **首个** SDG 电流层与 Stokes 配对的形式化
5. **NoChoice 审计范式**：可复用的构造性形式化方法论
6. **111 条核心声明的 axiom 审计**：全部在 [propext, Quot.sound] 内

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

**Option A（推荐）：完整 SDG 形式化论文**

> "A Constructive Formalization of Synthetic Differential Geometry in Lean 4"
> 覆盖 KL 公理 → 微线性 → 切丛 → 微分形式 → de Rham 复形 → d²=0 → 上同调
> 卖点：首个 Lean 4 SDG；无选择公理；111 条审计
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
