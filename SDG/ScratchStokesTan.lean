import SDG.DifferentialForms.Algebra

/-!
# SDG.ScratchStokesTan —— 切空间层 Stokes 基础设施（工作包 WP-C）

无选择公理约束下的五块地基：

1. **0-形式 Stokes**（T1）：`stokes_zero_form`——KL 公理的 Stokes 形式重述；
   `edgeSimplex` 把「棱 [x, x+v(d)]」编码为一维单形顶点对，`d0_edgeSimplex`
   把单纯形侧 `d0` 与切空间侧 `directionalDerivative` 显式桥接。
2. **无穷小单形与面代数**（T2）：`InfSimplex`（基点 + n 条棱切向量）、顶点曲线
   `vertex`、上闭面 `faceSucc`（删第 i ≥ 1 号顶点 = 删第 i-1 条棱，纯组合、
   无 transport）、面-棱值引理、面-顶点曲线引理与面-面复合交换表
   （`faceSucc_comp_faceSucc_le/gt`）。
3. **coFace 完全交换表**（T3）：补全 `coFace_comp_coFace`（a ≤ b 情形）缺失的
   `b < a` 情形（`coFace_comp_coFace_gt`）与覆盖全部相对位置的总表
   （`coFace_comp_coFace_total`）。
4. **d0 乘积法则**（T4）：`d0_mul`。
5. **基点搬运 transport 调研**（T5，F 里程碑前置）。

## T5 障碍的精确形式（本文件调研结论）

- **目标**：对 `v₀ v₁ : TangentFiber R X x`，定义沿 `v₀` 把 `v₁` 搬运到基点
  `v₀(s)` 的切向量 `transportVec v₀ v₁ s : TangentFiber R X (v₀.1 s)`，
  期望 `d' ↦ g(s, d')`，其中 `g : Dn R 2 → X` 是 `(v₀, v₁)` 的 n=2 微线性扩展
  （本文件 `klExtend`，边界条件 `klExtend_axis0/axis1` 已证）。
- **断裂点**：`Dn R 2 = {u : Fin 2 → R | ∀ i j, u i * u j = 0}` 是「十字形」
  一阶邻域，**严格小于** `D × D`：竖直切片 `{s} × D` 中的 `(s, d')` 满足
  `s * d' = 0` 一般不成立（模型 k[ε,δ]/(ε²,δ²) 中取 s = ε、d' = δ 即反例），
  故 `g` 在竖直切片上**无定义**；类型层面即：无法给出
  `(s : D R) → (d' : D R) → (s:R) * (d':R) = 0` 这一 `Dn.pairOf` 的成员证明。
- 换言之，n=2 微线性只提供「十字」`D(2)` 上的扩展，而 transport 需要「方块」
  `D × D` 上的扩展；`D × D` 上的函数一般是**二次**的
  （`a + b·d + c·d' + e·d·d'`），不存在 KL 型仿射唯一性。**transport 不是
  微线性的自动推论，而是附加结构（仿射联络）**。
- 本文件把可证部分全部立起：十字上的边界条件（`klExtend_axis0/axis1/zero`）、
  `(s, d') ∈ D(2) ⟺ s·d' = 0` 的显式构造（`Dn.pairOf`）、
  **条件形式 transport**（`transportVecOfPairwiseMul`：若
  `∀ d d' : D R, (d:R)*(d':R) = 0` 则搬运存在）与零向量的无条件退化搬运
  （`transportZero`）。无条件版本需要 `D × D` 层面的新公理
  （「一阶方块微线性」或等价表述），留给 F 里程碑决策。
-/

universe u

namespace SDG.DifferentialForms

/-! ## T1：0-形式 Stokes -/

section StokesTangent

/-- **0-形式 Stokes**：`df` 沿无穷小棱 `[x, x+v(d)]` 的积分 = `f` 在边界端点的
取值差。这是 KL 公理的 Stokes 形式重述：`f (v.1 d) - f x = df(x)(v) · d`。 -/
lemma stokes_zero_form {R : Type u} [IsKockLawvere_one R] {X : Type u} (f : X → R)
    {x : X} (v : TangentFiber R X x) (d : D R) :
    f (v.1 d) - f x = directionalDerivative f (x := x) v * (d : R) := by
  rw [directionalDerivative_spec f v d]
  ring

/-- **棱单形**：顶点为 `x`（0 号，常值曲线）与 `x + v(d)`（1 号，沿切向量 `v`
走参数 `d`）的一维单形顶点对。 -/
def edgeSimplex {R : Type u} [CommRing R] {X : Type u} {x : X}
    (v : TangentFiber R X x) (d : D R) : SimplexPts X 1 :=
  Fin.cases x (fun _ : Fin 1 => v.1 d)

lemma edgeSimplex_zero {R : Type u} [CommRing R] {X : Type u} {x : X}
    (v : TangentFiber R X x) (d : D R) : edgeSimplex v d 0 = x := rfl

lemma edgeSimplex_one {R : Type u} [CommRing R] {X : Type u} {x : X}
    (v : TangentFiber R X x) (d : D R) : edgeSimplex v d 1 = v.1 d := by
  have h1 : (1 : Fin 2) = Fin.succ (0 : Fin 1) := rfl
  simp only [edgeSimplex, h1, Fin.cases_succ]

/-- 棱单形上 0-形式余边界的取值：`d0 f [x, x+v(d)] = f (v.1 d) - f x`。 -/
lemma d0_edgeSimplex_eq {R : Type u} [IsKockLawvere_one R] {X : Type u} (f : X → R)
    {x : X} (v : TangentFiber R X x) (d : D R) :
    d0 f (edgeSimplex v d) = f (v.1 d) - f x := by
  rw [d0_apply, edgeSimplex_one, edgeSimplex_zero]

/-- **单纯形侧与切空间侧的桥**：沿棱 `[x, x+v(d)]` 的 0-形式余边界等于
方向导数乘棱参数：`d0 f [x, x+v(d)] = df(x)(v) · d`。 -/
lemma d0_edgeSimplex {R : Type u} [IsKockLawvere_one R] {X : Type u} (f : X → R)
    {x : X} (v : TangentFiber R X x) (d : D R) :
    d0 f (edgeSimplex v d) = directionalDerivative f (x := x) v * (d : R) := by
  rw [d0_edgeSimplex_eq, stokes_zero_form]

/-! ## T2：无穷小单形与面代数 -/

/-- **无穷小 n-单形**：基点 `base` 加 n 条棱切向量（Kock《Synthetic Differential
Geometry》定义 14.1 的「公共基点切向量组」编码）。

第 `j`（≥ 1）号顶点即第 `j-1` 条棱的切向量曲线的终点 `edge (j-1) (d)`；
0 号顶点是基点本身。0 号顶点所在的面的顶点会被替换（需要 transport），另行处理。 -/
structure InfSimplex (R : Type u) [CommRing R] (X : Type u) (n : ℕ) where
  base : X
  edge : Fin n → TangentFiber R X base

/-- 顶点曲线：0 号顶点为常值曲线 `s.base`；第 `j.succ` 号顶点为第 `j` 条棱的
切向量曲线 `d ↦ (s.edge j).1 d`（沿棱离开基点的参数化点）。

**取舍说明**：直接取切向量曲线本身，而非 `tangentAdd R (tangentZero R base)
(edge j)`——二者经 `AddCommMonoid (TangentFiber …)` 的 `zero_add` 一致
（见 `InfSimplex.vertex_succ_tangentAdd`），直接定义省去一次 n=2 微线性展开。 -/
def InfSimplex.vertex {R : Type u} [CommRing R] {X : Type u} {n : ℕ}
    (s : InfSimplex R X n) : Fin (n + 1) → D R → X :=
  Fin.cases (fun _ : D R => s.base) (fun j : Fin n => (s.edge j).1)

lemma InfSimplex.vertex_zero {R : Type u} [CommRing R] {X : Type u} {n : ℕ}
    (s : InfSimplex R X n) :
    s.vertex 0 = fun _ : D R => s.base := rfl

lemma InfSimplex.vertex_succ {R : Type u} [CommRing R] {X : Type u} {n : ℕ}
    (s : InfSimplex R X n) (j : Fin n) :
    s.vertex j.succ = (s.edge j).1 := rfl

/-- 顶点曲线在 0 处取基点：`s.vertex i 0 = s.base`（0 号顶点平凡，
第 `j.succ` 号顶点由切向量的基点条件给出）。 -/
lemma InfSimplex.vertex_basePoint {R : Type u} [CommRing R] {X : Type u} {n : ℕ}
    (s : InfSimplex R X n) (i : Fin (n + 1)) :
    s.vertex i 0 = s.base := by
  revert i
  apply Fin.cases
  · rw [InfSimplex.vertex_zero]
  · intro j
    rw [InfSimplex.vertex_succ]
    exact (s.edge j).2

/-- 第 `j.succ` 号顶点曲线与「零切向量 + 棱切向量」的 `tangentAdd` 编码一致
（经 `AddCommMonoid (TangentFiber R X s.base)` 的 `zero_add`）。 -/
lemma InfSimplex.vertex_succ_tangentAdd {R : Type u} [CommRing R] {X : Type u}
    [Microlinear R X] {n : ℕ} (s : InfSimplex R X n) (j : Fin n) :
    s.vertex j.succ
      = tangentAdd R (tangentZero R s.base) (s.edge j).1
          ((tangentZero_basePoint R s.base).trans (s.edge j).2.symm) := by
  rw [InfSimplex.vertex_succ]
  exact (congrArg Subtype.val (zero_add (s.edge j))).symm

/-- **上闭面**（i ≥ 1 的面）：删除第 `i` 号顶点（即第 `i-1` 条棱），基点不变。
第 `k` 条棱是原单形的第 `succAbove (i-1) k` 条棱（纯组合重排，无 transport）。 -/
def InfSimplex.faceSucc {R : Type u} [CommRing R] {X : Type u} {n : ℕ}
    (s : InfSimplex R X (n + 1)) (i : Fin (n + 1)) (hi : 0 < (i : ℕ)) :
    InfSimplex R X n where
  base := s.base
  edge := fun k =>
    s.edge (Fin.succAbove (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin (n + 1)) k)

/-- 面的第 `k` 条棱在 `k < i-1` 时是原单形的第 `k` 条棱。 -/
lemma InfSimplex.faceSucc_edge_lt {R : Type u} [CommRing R] {X : Type u} {n : ℕ}
    (s : InfSimplex R X (n + 1)) {i : Fin (n + 1)} (hi : 0 < (i : ℕ))
    {k : Fin n} (hk : (k : ℕ) < (i : ℕ) - 1) :
    (s.faceSucc i hi).edge k = s.edge (⟨(k : ℕ), by have := k.isLt; omega⟩ : Fin (n + 1)) := by
  refine congrArg s.edge (Fin.ext ?_)
  have hv := succAbove_val (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin (n + 1)) k
  simp only [hv, if_pos hk]

/-- 面的第 `k` 条棱在 `k ≥ i-1` 时是原单形的第 `k+1` 条棱。 -/
lemma InfSimplex.faceSucc_edge_ge {R : Type u} [CommRing R] {X : Type u} {n : ℕ}
    (s : InfSimplex R X (n + 1)) {i : Fin (n + 1)} (hi : 0 < (i : ℕ))
    {k : Fin n} (hk : (i : ℕ) - 1 ≤ (k : ℕ)) :
    (s.faceSucc i hi).edge k
      = s.edge (⟨(k : ℕ) + 1, by have := k.isLt; omega⟩ : Fin (n + 1)) := by
  refine congrArg s.edge (Fin.ext ?_)
  have hv := succAbove_val (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin (n + 1)) k
  simp only [hv, if_neg (by omega : ¬((k : ℕ) < (i : ℕ) - 1))]

/-- 面的 0 号顶点 = 原单形的 0 号顶点（常值 `base` 曲线）。 -/
lemma InfSimplex.faceSucc_vertex_zero {R : Type u} [CommRing R] {X : Type u} {n : ℕ}
    (s : InfSimplex R X (n + 1)) {i : Fin (n + 1)} (hi : 0 < (i : ℕ)) :
    (s.faceSucc i hi).vertex 0 = s.vertex 0 := rfl

/-- 面的第 `j.succ` 号顶点 = 原单形第 `succAbove (i-1) j` 条棱对应的顶点。 -/
lemma InfSimplex.faceSucc_vertex_succ {R : Type u} [CommRing R] {X : Type u} {n : ℕ}
    (s : InfSimplex R X (n + 1)) {i : Fin (n + 1)} (hi : 0 < (i : ℕ)) (j : Fin n) :
    (s.faceSucc i hi).vertex j.succ
      = s.vertex ((⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin (n + 1)).succAbove j).succ := by
  rw [InfSimplex.vertex_succ, InfSimplex.vertex_succ]
  rfl

/-- **面-面复合表（a ≤ b 情形）**：对 `s : InfSimplex R X (n+2)`，先删顶点 `a`
再删顶点 `b`，等于先删顶点 `c` 再删顶点 `d`，其中 `(c:ℕ) = (b:ℕ)+1`（`b`
删除后在原单形中的后继顶点）、`(d:ℕ) = (a:ℕ)`。仿 `coFace_comp_coFace`。 -/
lemma InfSimplex.faceSucc_comp_faceSucc_le {R : Type u} [CommRing R] {X : Type u} {n : ℕ}
    (s : InfSimplex R X (n + 2)) {a : Fin (n + 2)} (ha : 0 < (a : ℕ))
    {b : Fin (n + 1)} (hb : 0 < (b : ℕ))
    {c : Fin (n + 2)} (hcb : (c : ℕ) = (b : ℕ) + 1)
    {d : Fin (n + 1)} (hda : (d : ℕ) = (a : ℕ))
    (hab : (a : ℕ) ≤ (b : ℕ)) :
    (s.faceSucc a ha).faceSucc b hb
      = (s.faceSucc c (by have := hb; have := hcb; omega)).faceSucc d
          (by have := ha; have := hda; omega) := by
  refine congrArg (InfSimplex.mk s.base) (funext fun k => ?_)
  refine congrArg s.edge (Fin.ext ?_)
  have eB : ((⟨(b : ℕ) - 1, by have := b.isLt; have := hb; omega⟩ : Fin (n + 1)) : ℕ)
      = (b : ℕ) - 1 := rfl
  have eA : ((⟨(a : ℕ) - 1, by have := a.isLt; have := ha; omega⟩ : Fin (n + 2)) : ℕ)
      = (a : ℕ) - 1 := rfl
  have eD : ((⟨(d : ℕ) - 1, by have := d.isLt; have := hda; omega⟩ : Fin (n + 1)) : ℕ)
      = (d : ℕ) - 1 := rfl
  have eC : ((⟨(c : ℕ) - 1, by have := c.isLt; have := hcb; omega⟩ : Fin (n + 2)) : ℕ)
      = (c : ℕ) - 1 := rfl
  rw [succAbove_val, succAbove_val, succAbove_val, succAbove_val, eB, eA, eD, eC]
  by_cases h1 : (k : ℕ) < (b : ℕ) - 1
  · rw [if_pos h1]
    by_cases h2 : (k : ℕ) < (a : ℕ) - 1
    · rw [if_pos h2, if_pos (show (k : ℕ) < (d : ℕ) - 1 by have := hda; omega),
        if_pos (show (k : ℕ) < (c : ℕ) - 1 by have := hcb; have := h1; omega)]
    · rw [if_neg h2, if_neg (show ¬((k : ℕ) < (d : ℕ) - 1) by have := hda; have := h2; omega),
        if_pos (show (k : ℕ) + 1 < (c : ℕ) - 1 by have := hcb; have := h1; omega)]
  · rw [if_neg h1,
      if_neg (show ¬((k : ℕ) + 1 < (a : ℕ) - 1) by have := h1; have := hab; omega),
      if_neg (show ¬((k : ℕ) < (d : ℕ) - 1) by have := hda; have := h1; have := hab; omega),
      if_neg (show ¬((k : ℕ) + 1 < (c : ℕ) - 1) by have := hcb; have := h1; omega)]

/-- **面-面复合表（b < a 情形）**：对 `s : InfSimplex R X (n+2)`，先删顶点 `a`
再删顶点 `b`，等于先删顶点 `c` 再删顶点 `d`，其中 `(c:ℕ) = (b:ℕ)`
（`b` 不受删除影响）、`(d:ℕ) = (a:ℕ)-1`（`a` 在删除 `b` 后前移一位）。 -/
lemma InfSimplex.faceSucc_comp_faceSucc_gt {R : Type u} [CommRing R] {X : Type u} {n : ℕ}
    (s : InfSimplex R X (n + 2)) {a : Fin (n + 2)} (ha : 0 < (a : ℕ))
    {b : Fin (n + 1)} (hb : 0 < (b : ℕ))
    {c : Fin (n + 2)} (hcb : (c : ℕ) = (b : ℕ))
    {d : Fin (n + 1)} (hda : (d : ℕ) = (a : ℕ) - 1)
    (hba : (b : ℕ) < (a : ℕ)) :
    (s.faceSucc a ha).faceSucc b hb
      = (s.faceSucc c (by have := hb; have := hcb; omega)).faceSucc d
          (by have := ha; have := hba; have := hda; omega) := by
  refine congrArg (InfSimplex.mk s.base) (funext fun k => ?_)
  refine congrArg s.edge (Fin.ext ?_)
  have eB : ((⟨(b : ℕ) - 1, by have := b.isLt; have := hb; omega⟩ : Fin (n + 1)) : ℕ)
      = (b : ℕ) - 1 := rfl
  have eA : ((⟨(a : ℕ) - 1, by have := a.isLt; have := ha; omega⟩ : Fin (n + 2)) : ℕ)
      = (a : ℕ) - 1 := rfl
  have eD : ((⟨(d : ℕ) - 1, by have := d.isLt; have := hda; omega⟩ : Fin (n + 1)) : ℕ)
      = (d : ℕ) - 1 := rfl
  have eC : ((⟨(c : ℕ) - 1, by have := c.isLt; have := hcb; omega⟩ : Fin (n + 2)) : ℕ)
      = (c : ℕ) - 1 := rfl
  rw [succAbove_val, succAbove_val, succAbove_val, succAbove_val, eB, eA, eD, eC]
  by_cases h1 : (k : ℕ) < (b : ℕ) - 1
  · by_cases h2 : (k : ℕ) + 1 < (a : ℕ) - 1
    · rw [if_pos h1, if_pos (show (k : ℕ) < (a : ℕ) - 1 by have := hba; have := h1; omega),
        if_pos (show (k : ℕ) < (d : ℕ) - 1 by have := hda; have := h2; omega),
        if_pos (show (k : ℕ) < (c : ℕ) - 1 by have := hcb; have := h1; omega)]
    · exfalso
      have := hba
      omega
  · by_cases h2 : (k : ℕ) + 1 < (a : ℕ) - 1
    · rw [if_neg h1, if_pos (show (k : ℕ) + 1 < (a : ℕ) - 1 by exact h2),
        if_pos (show (k : ℕ) < (d : ℕ) - 1 by have := hda; have := h2; omega),
        if_neg (show ¬((k : ℕ) < (c : ℕ) - 1) by have := hcb; have := h1; omega)]
    · rw [if_neg h1,
        if_neg (show ¬((k : ℕ) + 1 < (a : ℕ) - 1) by exact h2),
        if_neg (show ¬((k : ℕ) < (d : ℕ) - 1) by have := hda; have := h2; omega),
        if_neg (show ¬((k : ℕ) + 1 < (c : ℕ) - 1) by have := hcb; have := h1; omega)]

/-! ## T3：coFace 完全交换表 -/

/-- **coFace 复合交换表（b < a 情形）**：先删顶点 `a` 再删顶点 `b`，等于先删
顶点 `b` 再删顶点 `a-1`。与已有的 `coFace_comp_coFace`（a ≤ b 情形：
先 `a` 后 `b` = 先 `b+1` 后 `a`）合起来覆盖全部 `(a, b)` 相对位置。 -/
lemma coFace_comp_coFace_gt {n : ℕ} (σ : Fin (n + 3) → X) {a : Fin (n + 3)}
    {b : Fin (n + 2)} (hba : (b : ℕ) < (a : ℕ)) :
    coFace (coFace σ a) b
      = coFace (coFace σ (⟨(b : ℕ), by have := b.isLt; omega⟩ : Fin (n + 3)))
          (⟨(a : ℕ) - 1, by have := a.isLt; omega⟩ : Fin (n + 2)) := by
  funext k
  show σ (a.succAbove (b.succAbove k))
      = σ ((⟨(b : ℕ), by have := b.isLt; omega⟩ : Fin (n + 3)).succAbove
          ((⟨(a : ℕ) - 1, by have := a.isLt; omega⟩ : Fin (n + 2)).succAbove k))
  apply congrArg σ
  apply Fin.ext
  have eA : ((⟨(a : ℕ) - 1, by have := a.isLt; omega⟩ : Fin (n + 2)) : ℕ) = (a : ℕ) - 1 := rfl
  rw [succAbove_val, succAbove_val, succAbove_val, succAbove_val, eA]
  by_cases h1 : (k : ℕ) < (b : ℕ)
  · by_cases h2 : (k : ℕ) + 1 < (a : ℕ)
    · rw [if_pos h1, if_pos (show (k : ℕ) < (a : ℕ) by have := h1; have := hba; omega),
        if_pos (show (k : ℕ) < (a : ℕ) - 1 by have := h2; omega), if_pos h1]
    · exfalso
      have := hba
      omega
  · by_cases h2 : (k : ℕ) + 1 < (a : ℕ)
    · rw [if_neg h1, if_pos (show (k : ℕ) + 1 < (a : ℕ) by exact h2),
        if_pos (show (k : ℕ) < (a : ℕ) - 1 by have := h2; omega), if_neg h1]
    · rw [if_neg h1, if_neg (show ¬((k : ℕ) + 1 < (a : ℕ)) by exact h2),
        if_neg (show ¬((k : ℕ) < (a : ℕ) - 1) by have := h2; omega),
        if_neg (show ¬((k : ℕ) + 1 < (b : ℕ)) by have := h1; omega)]

/-- **coFace 复合交换总表**：对任意 `a : Fin (n+3)`、`b : Fin (n+2)`，两次取面
的交换形式按 `(a:ℕ) ≤ (b:ℕ)` 或 `(b:ℕ) < (a:ℕ)` 二选一给出，重排指标以存在量词
打包（覆盖全部相对位置；两分支分别由 `coFace_comp_coFace` 与
`coFace_comp_coFace_gt` 提供）。 -/
lemma coFace_comp_coFace_total {n : ℕ} (σ : Fin (n + 3) → X) (a : Fin (n + 3))
    (b : Fin (n + 2)) :
    (((a : ℕ) ≤ (b : ℕ) → ∃ c : Fin (n + 3), ∃ d : Fin (n + 2),
        (c : ℕ) = (b : ℕ) + 1 ∧ (d : ℕ) = (a : ℕ) ∧
          coFace (coFace σ a) b = coFace (coFace σ c) d)
      ∧ ((b : ℕ) < (a : ℕ) → ∃ c : Fin (n + 3), ∃ d : Fin (n + 2),
        (c : ℕ) = (b : ℕ) ∧ (d : ℕ) = (a : ℕ) - 1 ∧
          coFace (coFace σ a) b = coFace (coFace σ c) d)) := by
  refine ⟨fun hab => ⟨⟨(b : ℕ) + 1, by have := b.isLt; omega⟩,
    ⟨(a : ℕ), by have := a.isLt; have := hab; omega⟩, rfl, rfl, coFace_comp_coFace σ hab⟩,
    fun hba => ⟨⟨(b : ℕ), by have := b.isLt; omega⟩,
    ⟨(a : ℕ) - 1, by have := a.isLt; omega⟩, rfl, rfl, coFace_comp_coFace_gt σ hba⟩⟩

/-! ## T4：d0 乘积法则 -/

/-- **0-形式余边界的乘积法则（T4 规定形状）**：与上游已有的 `d0_mul`
（Algebra.lean，两项和的顺序相反）等价；按 WP-C 的形状重述并给出独立证明。 -/
lemma d0_mul' {R : Type u} [CommRing R] {X : Type u} (f g : X → R)
    (σ : SimplexPts X 1) :
    d0 (fun x => f x * g x) σ = f (σ 1) * d0 g σ + g (σ 0) * d0 f σ := by
  simp only [d0_apply]
  ring

/-! ## T5：基点搬运 transport（F 里程碑前置调研） -/

/-- **KL 扩展**：同基点两条切向量 `(v₀, v₁)` 经 n=2 微线性得到的
`D(2) → X` 映射 `g`——唯一满足 `g(d, 0) = v₀(d)`、`g(0, d') = v₁(d')` 的扩展。
**注意**：`g` 只在「十字」`D(2)` 上有定义，竖直切片 `(s, d')`（`s·d' ≠ 0` 时）
不在 `D(2)` 中——这正是无条件 transport 的障碍（见文件头注释）。 -/
def klExtend {R : Type u} [CommRing R] {X : Type u} [Microlinear R X] {x : X}
    (v₀ v₁ : TangentFiber R X x) : Dn R 2 → X :=
  (Microlinear.microlinear (n := 2)
    (mkFiberProduct2 R v₀.1 v₁.1 (v₀.2.trans v₁.2.symm))).1

/-- `klExtend` 的扩展性质：沿坐标嵌入与 `(v₀, v₁)` 一致。 -/
lemma klExtend_spec {R : Type u} [CommRing R] {X : Type u} [Microlinear R X] {x : X}
    (v₀ v₁ : TangentFiber R X x) :
    Dn.restrict' R (klExtend v₀ v₁)
      = mkFiberProduct2 R v₀.1 v₁.1 (v₀.2.trans v₁.2.symm) :=
  (Microlinear.microlinear (n := 2)
    (mkFiberProduct2 R v₀.1 v₁.1 (v₀.2.trans v₁.2.symm))).2.1

/-- `klExtend` 在水平轴上的边界条件：`g(e₀(d)) = v₀(d)`。 -/
lemma klExtend_axis0 {R : Type u} [CommRing R] {X : Type u} [Microlinear R X] {x : X}
    (v₀ v₁ : TangentFiber R X x) (d : D R) :
    klExtend v₀ v₁ (Dn.embed R (0 : Fin 2) d) = v₀.1 d := by
  have hval : Dn.restrict R (klExtend v₀ v₁)
      = fun i : Fin 2 => if i = 0 then v₀.1 else v₁.1 := by
    simpa [Dn.restrict', mkFiberProduct2] using
      congrArg Subtype.val (klExtend_spec v₀ v₁)
  exact congrFun (congrFun hval (0 : Fin 2)) d

/-- `klExtend` 在竖直轴上的边界条件：`g(e₁(d')) = v₁(d')`。 -/
lemma klExtend_axis1 {R : Type u} [CommRing R] {X : Type u} [Microlinear R X] {x : X}
    (v₀ v₁ : TangentFiber R X x) (d : D R) :
    klExtend v₀ v₁ (Dn.embed R (1 : Fin 2) d) = v₁.1 d := by
  have hval : Dn.restrict R (klExtend v₀ v₁)
      = fun i : Fin 2 => if i = 0 then v₀.1 else v₁.1 := by
    simpa [Dn.restrict', mkFiberProduct2] using
      congrArg Subtype.val (klExtend_spec v₀ v₁)
  exact congrFun (congrFun hval (1 : Fin 2)) d

/-- `klExtend` 保持基点：`g(0) = x`。 -/
lemma klExtend_zero {R : Type u} [CommRing R] {X : Type u} [Microlinear R X] {x : X}
    (v₀ v₁ : TangentFiber R X x) : klExtend v₀ v₁ 0 = x := by
  have h := klExtend_axis0 v₀ v₁ (0 : D R)
  rw [Dn.embed_zero] at h
  rw [h]
  exact v₀.2

/-- 把两条无穷小量打包为 `D(2)` 的元素：`(s, d') ∈ D(2)` 当且仅当
`(s:R) * (d':R) = 0`。**这正是 T5 transport 的断裂点**：一般模型中
`D × D ⊄ D(2)`（如 k[ε,δ]/(ε²,δ²) 中 ε·δ ≠ 0），故此构造带前提 `h`。 -/
def Dn.pairOf (R) [CommRing R] (s d' : D R) (h : (s : R) * (d' : R) = 0) : Dn R 2 :=
  Dn.ofPairwise R (fun i : Fin 2 ↦ if i = 0 then (s : R) else (d' : R)) (by
    intro i j
    by_cases hi : (i : Fin 2) = 0 <;> by_cases hj : (j : Fin 2) = 0 <;>
      simp [hi, hj, h]
    · exact D.mul_eq_zero R s
    · rw [mul_comm]
      exact h
    · exact D.mul_eq_zero R d')

/-- 零切向量的无条件搬运（退化情形）：沿 `v₀` 搬运零向量 = 常值曲线
`d' ↦ v₀(s)`。不需要任何附加公理。 -/
def transportZero {R : Type u} [CommRing R] {X : Type u} {x : X}
    (v₀ : TangentFiber R X x) (s : D R) : TangentFiber R X (v₀.1 s) :=
  ⟨fun _ => v₀.1 s, rfl⟩

/-- **T5 主结果（条件形式）**：若任意两条无穷小量相乘为零（即 `D × D ⊆ D(2)`，
一般 SDG 模型中**不**成立），则沿 `v₀` 的搬运存在：
`transportVecOfPairwiseMul v₀ v₁ hmul s : TangentFiber R X (v₀.1 s)`，
由 `klExtend` 在「打包点」`(s, d')` 处取值。无条件版本需要 `D × D` 层面的
微线性/KL 公理（超出 n=2 KL 的表达范围），留给 F 里程碑决策。 -/
def transportVecOfPairwiseMul {R : Type u} [CommRing R] {X : Type u} [Microlinear R X]
    {x : X} (v₀ v₁ : TangentFiber R X x)
    (hmul : ∀ d d' : D R, (d : R) * (d' : R) = 0) (s : D R) :
    TangentFiber R X (v₀.1 s) :=
  ⟨fun d' => klExtend v₀ v₁ (Dn.pairOf R s d' (hmul s d')), by
    show klExtend v₀ v₁ (Dn.pairOf R s (0 : D R) (hmul s (0 : D R))) = v₀.1 s
    have hpair : Dn.pairOf R s (0 : D R) (hmul s (0 : D R))
        = Dn.embed R (0 : Fin 2) s := by
      apply Subtype.ext
      funext i
      by_cases hi : (i : Fin 2) = 0
      · simp [Dn.pairOf, Dn.embed, Dn.ofPairwise, Function.update, hi]
      · simp [Dn.pairOf, Dn.embed, Dn.ofPairwise, Function.update, hi, zero_coeDk]
    rw [hpair]
    exact klExtend_axis0 v₀ v₁ s⟩

end StokesTangent

/-! ## 审计：新证公开项的公理依赖 -/

#print axioms edgeSimplex_zero
#print axioms edgeSimplex_one
#print axioms stokes_zero_form
#print axioms d0_edgeSimplex_eq
#print axioms d0_edgeSimplex
#print axioms InfSimplex.vertex_zero
#print axioms InfSimplex.vertex_succ
#print axioms InfSimplex.vertex_basePoint
#print axioms InfSimplex.vertex_succ_tangentAdd
#print axioms InfSimplex.faceSucc_edge_lt
#print axioms InfSimplex.faceSucc_edge_ge
#print axioms InfSimplex.faceSucc_vertex_zero
#print axioms InfSimplex.faceSucc_vertex_succ
#print axioms InfSimplex.faceSucc_comp_faceSucc_le
#print axioms InfSimplex.faceSucc_comp_faceSucc_gt
#print axioms coFace_comp_coFace_gt
#print axioms coFace_comp_coFace_total
#print axioms d0_mul
#print axioms d0_mul'
#print axioms klExtend
#print axioms klExtend_spec
#print axioms klExtend_axis0
#print axioms klExtend_axis1
#print axioms klExtend_zero
#print axioms Dn.pairOf
#print axioms transportZero
#print axioms transportVecOfPairwiseMul

end SDG.DifferentialForms
