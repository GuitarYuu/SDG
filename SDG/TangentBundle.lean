import SDG.NoChoice
import SDG.Microlinear

/-!
# SDG.TangentBundle

切从 (tangent bundle) 及其纤维上的 $R$-模结构。

对微线性空间 $X$，**切从**是 $X^D$：从无穷小区间 $D$ 到 $X$ 的映射。
本模块建立 $D(2)$/$D(3)$ 的坐标基础设施、切向量加法/数乘/零、
基点兼容性引理，以及切纤维 $T_x X$ 上的 $R$-模实例。
-/


/-! ## 切从及其纤维上的 R-模结构

对微线性空间 $X$，**切从**（tangent bundle）是 $X^D$：从无穷小区间 $D$ 到 $X$ 的映射。
纤维 $X^D_x$（在基点 $x = v(0)$ 上）带有自然的 $R$-模结构：

* **加法**：$v_1 + v_2 := d \mapsto g(d, d)$，其中 $g : D(2) \to X$ 是微线性给出的
  纤维积元素 $(v_1, v_2) \in X^D \times_X X^D$ 的唯一扩展；
* **标量乘法**：$(\alpha \cdot v)(d) := v(\alpha d)$；
* **零向量**：$0_x := d \mapsto x$。

这些操作保持基点，从而构成每条纤维上的 $R$-模结构（nLab: Proposition 2.2）。 -/


/-- **切向量加法**：$v_1 + v_2 := d \mapsto g(d, d)$，其中 $g : D(2) \to X$
是微线性给出的 $(v_1, v_2)$ 的唯一扩展。 -/
def tangentAdd (R) [CommRing R] {X : Type*} [Microlinear R X]
    (v1 v2 : D R → X) (h : v1 0 = v2 0) : D R → X :=
  fun d ↦ (Microlinear.microlinear (n := 2) (mkFiberProduct2 R v1 v2 h)).1 (Dn.diag R d)


/-- **标量乘法**：$(\alpha \cdot v)(d) := v(\alpha d)$。 -/
def tangentSMul (R) [CommRing R] {X : Type*}
    (α : R) (v : D R → X) : D R → X :=
  fun d ↦ v (α • d)


/-- **零切向量**（常函数）：基点为 $x$ 的零向量 $d \mapsto x$。 -/
def tangentZero (R) [CommRing R] {X : Type*} (x : X) : D R → X :=
  fun _ ↦ x


/-! ### 基点兼容性：模结构不改变纤维 -/

/-- 零切向量的基点就是 $x$：$0_x(0) = x$。 -/
lemma tangentZero_basePoint (R) [CommRing R] {X : Type*} (x : X) :
    tangentZero R x 0 = x := rfl


/-- $0$ 在数乘下的像仍是 $0$：$\alpha \cdot 0 = 0$。 -/
lemma D.smul_zero (R) [CommRing R] (α : R) :
    α • (0 : D R) = 0 := by
  apply Subtype.ext
  simp


/-- $1$ 在数乘下是恒等：$1 \cdot d = d$。 -/
lemma D.one_smul (R) [CommRing R] (d : D R) :
    (1 : R) • d = d := by
  apply Subtype.ext
  simp


/-- $0$ 乘任意元素得 $0$：$0 \cdot d = 0$。 -/
lemma D.zero_smul (R) [CommRing R] (d : D R) :
    (0 : R) • d = 0 := by
  apply Subtype.ext
  simp


/-- 数乘保持基点：$(\alpha \cdot v)(0) = v(0)$。 -/
lemma tangentSMul_basePoint (R) [CommRing R] {X : Type*}
    (α : R) (v : D R → X) :
    tangentSMul R α v 0 = v 0 := by
  unfold tangentSMul
  congr 1
  exact D.smul_zero R α


/-- 对角映射在 $0$ 处退化为坐标嵌入：$\Delta(0) = e_0(0)$。 -/
lemma Dn.diag_zero (R) [CommRing R] :
    Dn.diag R 0 = 0 := by
  apply Subtype.ext
  funext k
  dsimp [Dn.diag, Dn.embed]


/-- 加法保持基点：$(v_1 + v_2)(0) = v_1(0)$。 -/
lemma tangentAdd_basePoint (R) [CommRing R] {X : Type*} [Microlinear R X]
    (v1 v2 : D R → X) (h : v1 0 = v2 0) :
    tangentAdd R v1 v2 h 0 = v1 0 := by
  unfold tangentAdd
  rw [Dn.diag_zero R]
  let g : Dn R 2 → X := (Microlinear.microlinear (n := 2) (mkFiberProduct2 R v1 v2 h)).1
  have hg : Dn.restrict' R g = mkFiberProduct2 R v1 v2 h :=
    (Microlinear.microlinear (n := 2) (mkFiberProduct2 R v1 v2 h)).2.1
  have hv : Dn.restrict R g = (mkFiberProduct2 R v1 v2 h).1 := by
    simpa [Dn.restrict'] using congrArg Subtype.val hg
  have hpoint : g 0 = v1 0 := by
    simpa [Dn.restrict, mkFiberProduct2] using congrFun (congrFun hv 0) 0
  exact hpoint


/-! ### 切纤维上的 $R$-模实例 -/

/-- 基点 $x$ 处的切纤维 $T_x X$：满足 $v(0) = x$ 的切向量。 -/
def TangentFiber (R) [CommRing R] (X : Type u) (x : X) : Type u :=
  { v : D R → X // v 0 = x }


/-- 切纤维 $T_x X$ 的零元 $0_x$（常切向量）。 -/
instance instZeroTangentFiber (R) [CommRing R] {X : Type u} (x : X) :
    Zero (TangentFiber R X x) where
  zero := ⟨tangentZero R x, tangentZero_basePoint R x⟩


/-- 切纤维上的切向量加法（同基点，由 $n=2$ 微线性给出）。 -/
instance instAddTangentFiber (R) [CommRing R] {X : Type u} [Microlinear R X]
    (x : X) : Add (TangentFiber R X x) where
  add v1 v2 := ⟨tangentAdd R v1.1 v2.1 (v1.2.trans v2.2.symm), by
    rw [tangentAdd_basePoint]
    exact v1.2⟩


/-- 切纤维上的标量乘法（逐点 $v(\alpha d)$）。 -/
instance instSMulTangentFiber (R) [CommRing R] {X : Type u} (x : X) :
    SMul R (TangentFiber R X x) where
  smul α v := ⟨tangentSMul R α v.1, by
    rw [tangentSMul_basePoint]
    exact v.2⟩


/-- 切纤维 $T_x X$ 的加法交换幺半群结构。

零元是常切向量 $0_x$，加法是切向量加法（由 $n=2$ 微线性给出）。
结合律、交换律与单位元均由微线性给出的扩展唯一性真实证明（无 `sorry`）。 -/
instance instAddCommMonoidTangentFiber (R) [CommRing R] {X : Type u}
    [Microlinear R X] (x : X) : AddCommMonoid (TangentFiber R X x) where
  toZero := inferInstance
  toAdd := inferInstance
  add_assoc := by
    intro a b c
    apply Subtype.ext
    funext d
    -- 展开加法为 tangentAdd
    change (tangentAdd R (a + b).1 c.1 ((a + b).2.trans c.2.symm)) d =
           (tangentAdd R a.1 (b + c).1 (a.2.trans (b + c).2.symm)) d
    unfold tangentAdd
    -- 各扩展
    let p_abc : TangentFiberProduct R X 3 :=
      mkFiberProduct3 R a.1 b.1 c.1 (a.2.trans b.2.symm) (b.2.trans c.2.symm)
    let F : Dn R 3 → X := (Microlinear.microlinear (n := 3) p_abc).1
    have hF : Dn.restrict' R F = p_abc := (Microlinear.microlinear (n := 3) p_abc).2.1
    let p_ab : TangentFiberProduct R X 2 := mkFiberProduct2 R a.1 b.1 (a.2.trans b.2.symm)
    let g_ab : Dn R 2 → X := (Microlinear.microlinear (n := 2) p_ab).1
    have hg_ab : Dn.restrict' R g_ab = p_ab := (Microlinear.microlinear (n := 2) p_ab).2.1
    let p_bc : TangentFiberProduct R X 2 := mkFiberProduct2 R b.1 c.1 (b.2.trans c.2.symm)
    let g_bc : Dn R 2 → X := (Microlinear.microlinear (n := 2) p_bc).1
    have hg_bc : Dn.restrict' R g_bc = p_bc := (Microlinear.microlinear (n := 2) p_bc).2.1
    let vab : D R → X := (a + b).1
    let vbc : D R → X := (b + c).1
    let vab_bp : vab 0 = x := (a + b).2
    let vbc_bp : vbc 0 = x := (b + c).2
    let p_abc' : TangentFiberProduct R X 2 := mkFiberProduct2 R vab c.1 (vab_bp.trans c.2.symm)
    let g_abc : Dn R 2 → X := (Microlinear.microlinear (n := 2) p_abc').1
    have hg_abc : Dn.restrict' R g_abc = p_abc' := (Microlinear.microlinear (n := 2) p_abc').2.1
    let p_bca : TangentFiberProduct R X 2 := mkFiberProduct2 R a.1 vbc (a.2.trans vbc_bp.symm)
    let g_bca : Dn R 2 → X := (Microlinear.microlinear (n := 2) p_bca).1
    have hg_bca : Dn.restrict' R g_bca = p_bca := (Microlinear.microlinear (n := 2) p_bca).2.1
    change g_abc (Dn.diag R d) = g_bca (Dn.diag R d)
    -- Lemma A：F ∘ emb3_0 = g_ab（沿前两坐标的拉回）
    have lemmaA : ∀ x : Dn R 2, F (Dn.emb3_0 R x) = g_ab x := by
      intro x
      have hH : Dn.restrict' R (fun y ↦ F (Dn.emb3_0 R y)) = p_ab := by
        apply Subtype.ext
        funext i
        funext e
        dsimp [Dn.restrict', Dn.restrict, p_ab, mkFiberProduct2]
        by_cases hi : i = 0
        · subst i
          rw [Dn.emb3_0_embed0 R e]
          have hFa : F (Dn.embed R (0 : Fin 3) e) = a.1 e := by
            have hv := congrFun (congrFun (congrArg Subtype.val hF) (0 : Fin 3)) e
            simpa [Dn.restrict', Dn.restrict, p_abc, mkFiberProduct3] using hv
          exact hFa
        · have hi1 : i = (1 : Fin 2) := fin_two_eq_one_of_ne_zero hi
          subst i
          rw [Dn.emb3_0_embed1 R e]
          have hFb : F (Dn.embed R (1 : Fin 3) e) = b.1 e := by
            have hv := congrFun (congrFun (congrArg Subtype.val hF) (1 : Fin 3)) e
            simpa [Dn.restrict', Dn.restrict, p_abc, mkFiberProduct3] using hv
          exact hFb
      have hFun : (fun y ↦ F (Dn.emb3_0 R y)) = g_ab :=
        (Microlinear.microlinear (n := 2) p_ab).2.2 (fun y ↦ F (Dn.emb3_0 R y)) hH
      exact congrFun hFun x
    -- Lemma B：F ∘ emb3_2 = g_bc（沿后两坐标的拉回）
    have lemmaB : ∀ x : Dn R 2, F (Dn.emb3_2 R x) = g_bc x := by
      intro x
      have hH : Dn.restrict' R (fun y ↦ F (Dn.emb3_2 R y)) = p_bc := by
        apply Subtype.ext
        funext i
        funext e
        dsimp [Dn.restrict', Dn.restrict, p_bc, mkFiberProduct2]
        by_cases hi : i = 0
        · subst i
          rw [Dn.emb3_2_embed0 R e]
          have hFb : F (Dn.embed R (1 : Fin 3) e) = b.1 e := by
            have hv := congrFun (congrFun (congrArg Subtype.val hF) (1 : Fin 3)) e
            simpa [Dn.restrict', Dn.restrict, p_abc, mkFiberProduct3] using hv
          exact hFb
        · have hi1 : i = (1 : Fin 2) := fin_two_eq_one_of_ne_zero hi
          subst i
          rw [Dn.emb3_2_embed1 R e]
          have hFc : F (Dn.embed R (2 : Fin 3) e) = c.1 e := by
            have hv := congrFun (congrFun (congrArg Subtype.val hF) (2 : Fin 3)) e
            simpa [Dn.restrict', Dn.restrict, p_abc, mkFiberProduct3] using hv
          exact hFc
      have hFun : (fun y ↦ F (Dn.emb3_2 R y)) = g_bc :=
        (Microlinear.microlinear (n := 2) p_bc).2.2 (fun y ↦ F (Dn.emb3_2 R y)) hH
      exact congrFun hFun x
    -- 三元数据 (vab, vab, c)
    let p3 : TangentFiberProduct R X 3 := mkFiberProduct3 R vab vab c.1 rfl (vab_bp.trans c.2.symm)
    -- F ∘ squash01 是 p3 的扩展
    have hFsq : Dn.restrict' R (fun y ↦ F (Dn.squash01 R y)) = p3 := by
      apply Subtype.ext
      funext i
      funext e
      dsimp [Dn.restrict', Dn.restrict, p3, mkFiberProduct3]
      by_cases hi0 : i = 0
      · subst i
        rw [Dn.squash01_embed0 R e]
        rw [lemmaA (Dn.diag R e)]
        rfl
      · by_cases hi1 : i = 1
        · subst i
          rw [Dn.squash01_embed1 R e]
          rw [lemmaA (Dn.diag R e)]
          rfl
        · have hi2 : i = (2 : Fin 3) := fin_three_eq_two_of_ne_zero_ne_one hi0 hi1
          subst i
          rw [Dn.squash01_embed2 R e]
          have hFc : F (Dn.embed R (2 : Fin 3) e) = c.1 e := by
            have hv := congrFun (congrFun (congrArg Subtype.val hF) (2 : Fin 3)) e
            simpa [Dn.restrict', Dn.restrict, p_abc, mkFiberProduct3] using hv
          exact hFc
    -- g_abc ∘ alpha 也是 p3 的扩展
    have hGal : Dn.restrict' R (fun y ↦ g_abc (Dn.alpha R y)) = p3 := by
      apply Subtype.ext
      funext i
      funext e
      dsimp [Dn.restrict', Dn.restrict, p3, mkFiberProduct3]
      by_cases hi0 : i = 0
      · subst i
        rw [Dn.alpha_embed0 R e]
        have hg0 : g_abc (Dn.embed R (0 : Fin 2) e) = vab e := by
          have hv := congrFun (congrFun (congrArg Subtype.val hg_abc) (0 : Fin 2)) e
          simpa [Dn.restrict', Dn.restrict, p_abc', mkFiberProduct2] using hv
        exact hg0
      · by_cases hi1 : i = 1
        · subst i
          rw [Dn.alpha_embed1 R e]
          have hg0 : g_abc (Dn.embed R (0 : Fin 2) e) = vab e := by
            have hv := congrFun (congrFun (congrArg Subtype.val hg_abc) (0 : Fin 2)) e
            simpa [Dn.restrict', Dn.restrict, p_abc', mkFiberProduct2] using hv
          exact hg0
        · have hi2 : i = (2 : Fin 3) := fin_three_eq_two_of_ne_zero_ne_one hi0 hi1
          subst i
          rw [Dn.alpha_embed2 R e]
          have hg2 : g_abc (Dn.embed R (1 : Fin 2) e) = c.1 e := by
            have hv := congrFun (congrFun (congrArg Subtype.val hg_abc) (1 : Fin 2)) e
            simpa [Dn.restrict', Dn.restrict, p_abc', mkFiberProduct2] using hv
          exact hg2
    -- 唯一性：F ∘ squash01 = g_abc ∘ alpha（都是 p3 的扩展）
    have hEq1 : (fun y ↦ F (Dn.squash01 R y)) = (Microlinear.microlinear (n := 3) p3).1 :=
      (Microlinear.microlinear (n := 3) p3).2.2 (fun y ↦ F (Dn.squash01 R y)) hFsq
    have hEq1' : (fun y ↦ g_abc (Dn.alpha R y)) = (Microlinear.microlinear (n := 3) p3).1 :=
      (Microlinear.microlinear (n := 3) p3).2.2 (fun y ↦ g_abc (Dn.alpha R y)) hGal
    -- 左结合：g_abc (diag d) = F (diag3 d)
    have hleft : g_abc (Dn.diag R d) = F (Dn.diag3 R d) := by
      rw [← Dn.alpha_mk02 R d, ← Dn.squash01_mk02 R d]
      change (fun y ↦ g_abc (Dn.alpha R y)) (Dn.mk02 R d) =
             (fun y ↦ F (Dn.squash01 R y)) (Dn.mk02 R d)
      rw [hEq1', hEq1]
    -- 三元数据 (a, vbc, vbc)
    let p3' : TangentFiberProduct R X 3 := mkFiberProduct3 R a.1 vbc vbc (a.2.trans vbc_bp.symm) rfl
    -- F ∘ squash12 是 p3' 的扩展
    have hFsq2 : Dn.restrict' R (fun y ↦ F (Dn.squash12 R y)) = p3' := by
      apply Subtype.ext
      funext i
      funext e
      dsimp [Dn.restrict', Dn.restrict, p3', mkFiberProduct3]
      by_cases hi0 : i = 0
      · subst i
        rw [Dn.squash12_embed0 R e]
        have hFa : F (Dn.embed R (0 : Fin 3) e) = a.1 e := by
          have hv := congrFun (congrFun (congrArg Subtype.val hF) (0 : Fin 3)) e
          simpa [Dn.restrict', Dn.restrict, p_abc, mkFiberProduct3] using hv
        exact hFa
      · by_cases hi1 : i = 1
        · subst i
          rw [Dn.squash12_embed1 R e]
          rw [lemmaB (Dn.diag R e)]
          rfl
        · have hi2 : i = (2 : Fin 3) := fin_three_eq_two_of_ne_zero_ne_one hi0 hi1
          subst i
          rw [Dn.squash12_embed2 R e]
          rw [lemmaB (Dn.diag R e)]
          rfl
    -- g_bca ∘ beta 也是 p3' 的扩展
    have hGbe : Dn.restrict' R (fun y ↦ g_bca (Dn.beta R y)) = p3' := by
      apply Subtype.ext
      funext i
      funext e
      dsimp [Dn.restrict', Dn.restrict, p3', mkFiberProduct3]
      by_cases hi0 : i = 0
      · subst i
        rw [Dn.beta_embed0 R e]
        have hg0 : g_bca (Dn.embed R (0 : Fin 2) e) = a.1 e := by
          have hv := congrFun (congrFun (congrArg Subtype.val hg_bca) (0 : Fin 2)) e
          simpa [Dn.restrict', Dn.restrict, p_bca, mkFiberProduct2] using hv
        exact hg0
      · by_cases hi1 : i = 1
        · subst i
          rw [Dn.beta_embed1 R e]
          have hg1 : g_bca (Dn.embed R (1 : Fin 2) e) = vbc e := by
            have hv := congrFun (congrFun (congrArg Subtype.val hg_bca) (1 : Fin 2)) e
            simpa [Dn.restrict', Dn.restrict, p_bca, mkFiberProduct2] using hv
          exact hg1
        · have hi2 : i = (2 : Fin 3) := fin_three_eq_two_of_ne_zero_ne_one hi0 hi1
          subst i
          rw [Dn.beta_embed2 R e]
          have hg1 : g_bca (Dn.embed R (1 : Fin 2) e) = vbc e := by
            have hv := congrFun (congrFun (congrArg Subtype.val hg_bca) (1 : Fin 2)) e
            simpa [Dn.restrict', Dn.restrict, p_bca, mkFiberProduct2] using hv
          exact hg1
    -- 唯一性：F ∘ squash12 = g_bca ∘ beta（都是 p3' 的扩展）
    have hEq2 : (fun y ↦ F (Dn.squash12 R y)) = (Microlinear.microlinear (n := 3) p3').1 :=
      (Microlinear.microlinear (n := 3) p3').2.2 (fun y ↦ F (Dn.squash12 R y)) hFsq2
    have hEq2' : (fun y ↦ g_bca (Dn.beta R y)) = (Microlinear.microlinear (n := 3) p3').1 :=
      (Microlinear.microlinear (n := 3) p3').2.2 (fun y ↦ g_bca (Dn.beta R y)) hGbe
    -- 右结合：g_bca (diag d) = F (diag3 d)
    have hright : g_bca (Dn.diag R d) = F (Dn.diag3 R d) := by
      rw [← Dn.beta_mk02 R d, ← Dn.squash12_mk02 R d]
      change (fun y ↦ g_bca (Dn.beta R y)) (Dn.mk02 R d) =
             (fun y ↦ F (Dn.squash12 R y)) (Dn.mk02 R d)
      rw [hEq2', hEq2]
    exact hleft.trans hright.symm
  add_comm := by
    intro v1 v2
    apply Subtype.ext
    funext d
    -- 设 g 是 (v1,v2) 的唯一扩展，g' 是 (v2,v1) 的唯一扩展
    let p : TangentFiberProduct R X 2 := mkFiberProduct2 R v1.1 v2.1 (v1.2.trans v2.2.symm)
    let g : Dn R 2 → X := (Microlinear.microlinear (n := 2) p).1
    let p' : TangentFiberProduct R X 2 := mkFiberProduct2 R v2.1 v1.1 (v2.2.trans v1.2.symm)
    let g' : Dn R 2 → X := (Microlinear.microlinear (n := 2) p').1
    have hg : Dn.restrict' R g = p := (Microlinear.microlinear (n := 2) p).2.1
    have hg' : Dn.restrict' R g' = p' := (Microlinear.microlinear (n := 2) p').2.1
    -- 展开目标（v1+v2 的加法 = tangentAdd，再等于唯一扩展在 (d,d) 处的值）
    change g (Dn.diag R d) = g' (Dn.diag R d)
    -- 先证 g' ∘ swap 是 (v1,v2) 的扩展
    have hH : Dn.restrict' R (fun x ↦ g' (Dn.swap R x)) = p := by
      apply Subtype.ext
      funext i
      funext e
      dsimp [Dn.restrict', Dn.restrict]
      by_cases hi : i = 0
      · subst i
        rw [Dn.swap_embed_0 R e]
        have hg'1 : g' (Dn.embed R 1 e) = v1.1 e := by
          have hv := congrFun (congrFun (congrArg Subtype.val hg') 1) e
          simpa [Dn.restrict', Dn.restrict, p', mkFiberProduct2] using hv
        rw [hg'1]
        simp [p, mkFiberProduct2]
      · have hi1 : i = (1 : Fin 2) := fin_two_eq_one_of_ne_zero hi
        subst i
        rw [Dn.swap_embed_1 R e]
        have hg'0 : g' (Dn.embed R 0 e) = v2.1 e := by
          have hv := congrFun (congrFun (congrArg Subtype.val hg') 0) e
          simpa [Dn.restrict', Dn.restrict, p', mkFiberProduct2] using hv
        rw [hg'0]
        simp [p, mkFiberProduct2]
    -- 由唯一性：g' ∘ swap = g
    have hgswap : (fun x ↦ g' (Dn.swap R x)) = g :=
      (Microlinear.microlinear (n := 2) p).2.2 (fun x ↦ g' (Dn.swap R x)) hH
    -- g (diag d) = (g' ∘ swap)(diag d) = g' (swap(diag d)) = g' (diag d)
    rw [← hgswap]
    congr 1
  zero_add := by
    intro a
    apply Subtype.ext
    funext d
    -- 展开目标：(0 + a) d = tangentAdd (0_x) a 在 d 处的值 = a.1 d
    change (tangentAdd R (tangentZero R x) a.1 a.2.symm) d = a.1 d
    unfold tangentAdd
    let p : TangentFiberProduct R X 2 := mkFiberProduct2 R (tangentZero R x) a.1 a.2.symm
    let g : Dn R 2 → X := (Microlinear.microlinear (n := 2) p).1
    have hg : Dn.restrict' R g = p := (Microlinear.microlinear (n := 2) p).2.1
    change g (Dn.diag R d) = a.1 d
    -- 构造 hT(z) = a.1 (0*z₀ + 1*z₁) = a.1 z₁，验证它是 (0_x, a) 的扩展
    let hT : Dn R 2 → X := fun z ↦ a.1 (Dn.linComb R 0 1 z)
    have hH : Dn.restrict' R hT = p := by
      apply Subtype.ext
      funext i
      funext e
      dsimp [Dn.restrict', Dn.restrict, p, mkFiberProduct2]
      by_cases hi : i = 0
      · subst i
        dsimp [hT]
        rw [Dn.linComb_embed_0 R 0 1 e]
        rw [D.zero_smul R e]
        simp [tangentZero, a.2]
      · have hi1 : i = (1 : Fin 2) := fin_two_eq_one_of_ne_zero hi
        subst i
        dsimp [hT]
        rw [Dn.linComb_embed_1 R 0 1 e]
        rw [D.one_smul R e]
    -- 由唯一性：hT = g
    have hgT : hT = g := (Microlinear.microlinear (n := 2) p).2.2 hT hH
    -- g (diag d) = hT (diag d) = a.1 ((0+1) • d) = a.1 (1 • d) = a.1 d
    rw [← hgT]
    dsimp [hT]
    rw [Dn.linComb_diag R 0 1 d]
    rw [zero_add]
    rw [D.one_smul R d]
  add_zero := by
    intro a
    apply Subtype.ext
    funext d
    -- 展开目标：(a + 0) d = tangentAdd a (0_x) 在 d 处的值 = a.1 d
    change tangentAdd R a.1 (tangentZero R x) a.2 d = a.1 d
    unfold tangentAdd
    let p : TangentFiberProduct R X 2 := mkFiberProduct2 R a.1 (tangentZero R x) a.2
    let g : Dn R 2 → X := (Microlinear.microlinear (n := 2) p).1
    have hg : Dn.restrict' R g = p := (Microlinear.microlinear (n := 2) p).2.1
    change g (Dn.diag R d) = a.1 d
    -- 构造 hT(z) = a.1 (1*z₀ + 0*z₁) = a.1 z₀，验证它是 (a, 0_x) 的扩展
    let hT : Dn R 2 → X := fun z ↦ a.1 (Dn.linComb R 1 0 z)
    have hH : Dn.restrict' R hT = p := by
      apply Subtype.ext
      funext i
      funext e
      dsimp [Dn.restrict', Dn.restrict, p, mkFiberProduct2]
      by_cases hi : i = 0
      · subst i
        dsimp [hT]
        rw [Dn.linComb_embed_0 R 1 0 e]
        rw [D.one_smul R e]
      · have hi1 : i = (1 : Fin 2) := fin_two_eq_one_of_ne_zero hi
        subst i
        dsimp [hT]
        rw [Dn.linComb_embed_1 R 1 0 e]
        rw [D.zero_smul R e]
        simp [tangentZero, a.2]
    -- 由唯一性：hT = g
    have hgT : hT = g := (Microlinear.microlinear (n := 2) p).2.2 hT hH
    -- g (diag d) = hT (diag d) = a.1 ((1+0) • d) = a.1 (1 • d) = a.1 d
    rw [← hgT]
    dsimp [hT]
    rw [Dn.linComb_diag R 1 0 d]
    rw [add_zero]
    rw [D.one_smul R d]
  nsmul := nsmulRec
  nsmul_zero := by
    intro a
    rfl
  nsmul_succ := by
    intro n a
    rfl


/-- 切纤维 $T_x X$ 上的 $R$-模结构。

数乘 $(\alpha \cdot v)(d) = v(\alpha d)$；各模公理（分配律、单位元、结合性）
均由微线性给出的扩展唯一性真实证明（无 `sorry`）。 -/
instance instModuleTangentFiber (R) [CommRing R] {X : Type u}
    [Microlinear R X] (x : X) : Module R (TangentFiber R X x) where
  toSMul := inferInstance
  smul_zero := by
    intro a
    apply Subtype.ext
    funext d
    change tangentSMul R a (tangentZero R x) d = tangentZero R x d
    -- (a • 0) 与 0 在每点都取值 x（零切向量是常函数 x）
    simp [tangentSMul, tangentZero]
  smul_add := by
    intro a v w
    apply Subtype.ext
    funext d
    -- 设 g 是 (v,w) 的唯一扩展，g' 是 (a•v, a•w) 的唯一扩展
    let p : TangentFiberProduct R X 2 := mkFiberProduct2 R v.1 w.1 (v.2.trans w.2.symm)
    let g : Dn R 2 → X := (Microlinear.microlinear (n := 2) p).1
    let p' : TangentFiberProduct R X 2 :=
      mkFiberProduct2 R (a • v).1 (a • w).1 ((a • v).2.trans (a • w).2.symm)
    let g' : Dn R 2 → X := (Microlinear.microlinear (n := 2) p').1
    have hg : Dn.restrict' R g = p := (Microlinear.microlinear (n := 2) p).2.1
    have hg' : Dn.restrict' R g' = p' := (Microlinear.microlinear (n := 2) p').2.1
    -- 展开目标：a•(v+w) 与 a•v+a•w 在 d 处的值
    change g (Dn.diag R (a • d)) = g' (Dn.diag R d)
    -- 先证 g ∘ (a·) 是 (a•v, a•w) 的扩展
    have hH : Dn.restrict' R (fun x ↦ g (a • x)) = p' := by
      apply Subtype.ext
      funext i
      funext e
      dsimp [Dn.restrict', Dn.restrict]
      by_cases hi : i = 0
      · subst i
        rw [Dn.embed_smul R a 0 e]
        have hg0 : g (Dn.embed R 0 (a • e)) = v.1 (a • e) := by
          have hv := congrFun (congrFun (congrArg Subtype.val hg) 0) (a • e)
          simpa [Dn.restrict', Dn.restrict, p, mkFiberProduct2] using hv
        rw [hg0]
        rfl
      · have hi1 : i = (1 : Fin 2) := fin_two_eq_one_of_ne_zero hi
        subst i
        rw [Dn.embed_smul R a 1 e]
        have hg1 : g (Dn.embed R 1 (a • e)) = w.1 (a • e) := by
          have hv := congrFun (congrFun (congrArg Subtype.val hg) 1) (a • e)
          simpa [Dn.restrict', Dn.restrict, p, mkFiberProduct2] using hv
        rw [hg1]
        rfl
    -- 由唯一性：g ∘ (a·) = g'
    have hgscale : (fun x ↦ g (a • x)) = g' :=
      (Microlinear.microlinear (n := 2) p').2.2 (fun x ↦ g (a • x)) hH
    -- g (diag (a•d)) = (g ∘ (a·))(diag d) = g (a • diag d) = g (diag (a•d))
    rw [← hgscale]
    congr 1
  add_smul := by
    intro a b v
    apply Subtype.ext
    funext d
    -- 设 g' 是 (a•v, b•v) 的唯一扩展
    let p' : TangentFiberProduct R X 2 :=
      mkFiberProduct2 R (a • v).1 (b • v).1 ((a • v).2.trans (b • v).2.symm)
    let g' : Dn R 2 → X := (Microlinear.microlinear (n := 2) p').1
    have hg' : Dn.restrict' R g' = p' := (Microlinear.microlinear (n := 2) p').2.1
    -- 展开目标：((a+b)•v)(d) 与 (a•v+b•v)(d)
    change v.1 ((a + b) • d) = g' (Dn.diag R d)
    -- 先证 ψ := fun x ↦ v (a x0 + b x1) 是 (a•v, b•v) 的扩展
    have hH : Dn.restrict' R (fun x ↦ v.1 (Dn.linComb R a b x)) = p' := by
      apply Subtype.ext
      funext i
      funext e
      dsimp [Dn.restrict', Dn.restrict]
      by_cases hi : i = 0
      · subst i
        rw [Dn.linComb_embed_0 R a b e]
        rfl
      · have hi1 : i = (1 : Fin 2) := fin_two_eq_one_of_ne_zero hi
        subst i
        rw [Dn.linComb_embed_1 R a b e]
        rfl
    -- 由唯一性：ψ = g'
    have hpsi : (fun x ↦ v.1 (Dn.linComb R a b x)) = g' :=
      (Microlinear.microlinear (n := 2) p').2.2 (fun x ↦ v.1 (Dn.linComb R a b x)) hH
    -- v ((a+b)•d) = ψ(diag d) = g' (diag d)
    rw [← hpsi]
    simp [Dn.linComb_diag]
  zero_smul := by
    intro v
    apply Subtype.ext
    funext d
    change tangentSMul R 0 v.1 d = tangentZero R x d
    rw [tangentSMul]
    rw [tangentZero]
    -- 目标：v.1 (0 • d) = x
    rw [show (0 : R) • d = (0 : D R) by
      apply Subtype.ext
      simp]
    exact v.2
  one_smul := by
    intro v
    apply Subtype.ext
    funext d
    change tangentSMul R 1 v.1 d = v.1 d
    -- (1 • v)(d) = v(1•d) = v(d)
    simp [tangentSMul]
  mul_smul := by
    intro a b v
    apply Subtype.ext
    funext d
    change tangentSMul R (a * b) v.1 d = tangentSMul R a (tangentSMul R b v.1) d
    -- 目标：v.1 ((a*b) • d) = v.1 (b • (a • d))
    have h : (a * b) • d = b • (a • d) := by
      apply Subtype.ext
      change (a * b) • d.1 = b • (a • d.1)
      rw [mul_comm, mul_smul]
    simp [tangentSMul, h]


/-! ## 切映射 (Tangent Map)

对映射 $f : X \to Y$，其**切映射**（pushforward）在每点 $x$ 给出
$R$-模同态 $T_x f : T_x X \to T_{f(x)} Y$，$v \mapsto f \circ v$。

* **加法保持**：$(v+w)(d) = g(d,d)$，其中 $g$ 是 $(v,w)$ 的唯一扩展。复合 $f \circ g$
  沿两坐标方向分别为 $f \circ v$ 与 $f \circ w$，故 $f \circ g$ 是 $(f \circ v, f \circ w)$
  的扩展；由 $Y$ 的微线性唯一性，$f \circ g = g_{fv,fw}$，从而
  $$f \circ (v+w) = f \circ g \circ \Delta = f \circ v + f \circ w.$$
* **数乘保持**：$f((\alpha \cdot v)(d)) = f(v(\alpha d)) = (\alpha \cdot (f \circ v))(d)$，逐点成立。

因此切映射对**任意**映射 $f$ 都是 $R$-模同态（无需 $f$ 微线性）——「存在唯一扩展」
由 $X, Y$ 的微线性保证，而复合 $f \circ g$ 自动给出扩展。 -/

/-- **切映射**（pushforward）：$T_x f(v) := f \circ v$，基点 $x$ 映到 $f(x)$。 -/
def tangentMapAt (R) [CommRing R] {X Y : Type u} (f : X → Y) {x : X} :
    TangentFiber R X x → TangentFiber R Y (f x) :=
  fun v ↦ ⟨fun d ↦ f (v.1 d), by
    dsimp
    rw [v.2]
  ⟩

/-- 切映射保持基点：$T_x f(v)(0) = f(x)$。 -/
lemma tangentMapAt_basePoint (R) [CommRing R] {X Y : Type u} (f : X → Y) {x : X}
    (v : TangentFiber R X x) :
    (tangentMapAt R f v).1 0 = f x := by
  dsimp [tangentMapAt]
  rw [v.2]

/-- 切映射保持加法：$T_x f(v + w) = T_x f(v) + T_x f(w)$。 -/
lemma tangentMapAt_add (R) [CommRing R] {X Y : Type u} [Microlinear R X] [Microlinear R Y]
    (f : X → Y) {x : X} (v w : TangentFiber R X x) :
    tangentMapAt R f (v + w) = tangentMapAt R f v + tangentMapAt R f w := by
  apply Subtype.ext
  funext d
  -- 展开两边的加法
  change f ((v + w).1 d) = (tangentMapAt R f v + tangentMapAt R f w).1 d
  unfold tangentMapAt
  change f (tangentAdd R v.1 w.1 (v.2.trans w.2.symm) d) =
    tangentAdd R (fun e ↦ f (v.1 e)) (fun e ↦ f (w.1 e))
      ((tangentMapAt R f v).2.trans (tangentMapAt R f w).2.symm) d
  unfold tangentAdd
  -- 设 g 是 (v,w) 的唯一扩展，g' 是 (f∘v, f∘w) 的唯一扩展
  let p : TangentFiberProduct R X 2 := mkFiberProduct2 R v.1 w.1 (v.2.trans w.2.symm)
  let g : Dn R 2 → X := (Microlinear.microlinear (n := 2) p).1
  have hg : Dn.restrict' R g = p := (Microlinear.microlinear (n := 2) p).2.1
  let p' : TangentFiberProduct R Y 2 :=
    mkFiberProduct2 R (fun e ↦ f (v.1 e)) (fun e ↦ f (w.1 e))
      ((tangentMapAt R f v).2.trans (tangentMapAt R f w).2.symm)
  let g' : Dn R 2 → Y := (Microlinear.microlinear (n := 2) p').1
  have hg' : Dn.restrict' R g' = p' := (Microlinear.microlinear (n := 2) p').2.1
  change f (g (Dn.diag R d)) = g' (Dn.diag R d)
  -- f ∘ g 是 (f∘v, f∘w) 的扩展
  have hH : Dn.restrict' R (fun y ↦ f (g y)) = p' := by
    apply Subtype.ext
    funext i
    funext e
    dsimp [Dn.restrict', Dn.restrict, p', mkFiberProduct2]
    by_cases hi : i = 0
    · subst i
      have hg0 : g (Dn.embed R (0 : Fin 2) e) = v.1 e := by
        have hv := congrFun (congrFun (congrArg Subtype.val hg) (0 : Fin 2)) e
        simpa [Dn.restrict', Dn.restrict, p, mkFiberProduct2] using hv
      rw [hg0]
      simp
    · have hi1 : i = (1 : Fin 2) := fin_two_eq_one_of_ne_zero hi
      subst i
      have hg1 : g (Dn.embed R (1 : Fin 2) e) = w.1 e := by
        have hv := congrFun (congrFun (congrArg Subtype.val hg) (1 : Fin 2)) e
        simpa [Dn.restrict', Dn.restrict, p, mkFiberProduct2] using hv
      rw [hg1]
      simp
  -- 由唯一性：f ∘ g = g'
  have hFun : (fun y ↦ f (g y)) = g' :=
    (Microlinear.microlinear (n := 2) p').2.2 (fun y ↦ f (g y)) hH
  exact congrFun hFun (Dn.diag R d)

/-- 切映射保持数乘：$T_x f(\alpha \cdot v) = \alpha \cdot T_x f(v)$。 -/
lemma tangentMapAt_smul (R) [CommRing R] {X Y : Type u} (f : X → Y) {x : X}
    (α : R) (v : TangentFiber R X x) :
    tangentMapAt R f (α • v) = α • tangentMapAt R f v := by
  apply Subtype.ext
  funext d
  -- 展开两边的数乘（逐点）：f((α•v)(d)) = f(v(α•d))，α•(f∘v)(d) = f(v(α•d))
  change f ((α • v).1 d) = (α • tangentMapAt R f v).1 d
  change f (v.1 (α • d)) = f (v.1 (α • d))
  rfl

/-- 切映射是 $R$-模同态：
$T_x f : T_x X \to T_{f(x)} Y$ 保持加法与数乘。 -/
def tangentMapAtLinear (R) [CommRing R] {X Y : Type u} [Microlinear R X] [Microlinear R Y]
    (f : X → Y) {x : X} : TangentFiber R X x →ₗ[R] TangentFiber R Y (f x) where
  toFun := tangentMapAt R f
  map_add' := tangentMapAt_add R f
  map_smul' := tangentMapAt_smul R f


/-! ## 切向量场 (Tangent Vector Fields)

在 SDG 中，微线性空间 $X$ 上的**切向量场**（vector field）是切从 $TX = X^D$
的一个截面：为每个点 $x : X$ 指派一个基点在该点的切向量。

切从投影为 $\pi : TX \to X$，$\pi(v) := v(0)$（把切向量映到其基点）。
向量场 $\xi$ 是它的右逆：$\pi \circ \xi = \mathrm{id}_X$，
即对每个 $x$ 有 $\xi(x)(0) = x$（基点条件）。等价地，$\xi(x)$ 位于基点 $x$ 处的
切纤维 $T_x X$ 中。 -/

/-- **切向量场**（向量场）：切从 $TX = X^D$ 的一个截面。

即映射 $\xi : X \to X^D$，满足基点条件 $\xi(x)(0) = x$ 对所有 $x : X$；
等价地 $\xi(x) \in T_x X$（位于基点 $x$ 处的切纤维中）。 -/
def TangentVectorField (R) [CommRing R] (X) :=
  { ξ : X → D R → X // ∀ x : X, ξ x 0 = x }

namespace TangentVectorField

/-- 向量场在点 $x$ 处给出的切向量以 $x$ 为基点：$\xi(x)(0) = x$。 -/
lemma basePoint {R X} [CommRing R] (ξ : TangentVectorField R X) (x : X) :
    ξ.1 x 0 = x :=
  ξ.2 x

/-- 向量场在点 $x$ 处取值于切纤维 $T_x X$。 -/
def toFiber {R X} [CommRing R] (ξ : TangentVectorField R X) (x : X) : TangentFiber R X x :=
  ⟨ξ.1 x, ξ.2 x⟩

/-- **无穷小平移合成律**：向量场 $\xi$ 给出 $X$ 上的无穷小平移
$\xi_d(x) := \xi(x)(d)$。对 $u \in D(2)$，记 $d_1 := u_0$、$d_2 := u_1$
（则 $d_1 d_2 = 0$，从而 $d_1 + d_2 \in D$），有
$$\xi_{d_1} \circ \xi_{d_2} = \xi_{d_1 + d_2},$$
即「先沿 $d_2$ 平移、再沿 $d_1$ 平移」等于「沿 $d_1 + d_2$ 平移」。

**证明**：映射 $\alpha(u) := \xi(x)(u_0 + u_1)$ 与
$\beta(u) := \xi(\xi(x)(u_1))(u_0)$ 沿两坐标轴的限制都是 $d \mapsto \xi(x)(d)$
（前者因 $u_0 + u_1$ 沿坐标轴化为 $d$；后者因基点条件 $\xi(y)(0) = y$）；
由微线性唯一性 $\alpha = \beta$，在 $u$ 处求值即得。 -/
theorem translation_compose {R X} [CommRing R] [Microlinear R X]
    (ξ : TangentVectorField R X) (x : X) (u : Dn R 2) :
    ξ.1 (ξ.1 x (Dn.comp1 R u)) (Dn.comp0 R u) = ξ.1 x (Dn.add01 R u) := by
  -- α(u) := ξ(x)(u_0 + u_1)，β(u) := ξ(ξ(x)(u_1))(u_0)
  let α : Dn R 2 → X := fun w ↦ ξ.1 x (Dn.add01 R w)
  let β : Dn R 2 → X := fun w ↦ ξ.1 (ξ.1 x (Dn.comp1 R w)) (Dn.comp0 R w)
  change β u = α u
  -- 公共的纤维积数据：两坐标方向都是切向量 ξ(x)
  let v : TangentFiberProduct R X 2 :=
    ⟨fun _ : Fin 2 ↦ ξ.1 x, by intro i j; rfl⟩
  -- α 沿两坐标轴的限制都是 d ↦ ξ(x)(d)
  have hα : Dn.restrict' R α = v := by
    apply Subtype.ext
    funext i d
    dsimp [Dn.restrict', Dn.restrict, v]
    by_cases hi : i = 0
    · subst i
      dsimp [α]
      simp [Dn.add01_embed0]
    · have hi1 : i = (1 : Fin 2) := fin_two_eq_one_of_ne_zero hi
      subst i
      dsimp [α]
      simp [Dn.add01_embed1]
  -- β 沿两坐标轴的限制也是 d ↦ ξ(x)(d)
  have hβ : Dn.restrict' R β = v := by
    apply Subtype.ext
    funext i d
    dsimp [Dn.restrict', Dn.restrict, v]
    by_cases hi : i = 0
    · subst i
      -- β(e_0(d)) = ξ(ξ(x)(0))(d) = ξ(x)(d)
      dsimp [β]
      simp [Dn.comp1_embed0, Dn.comp0_embed0, ξ.2]
    · have hi1 : i = (1 : Fin 2) := fin_two_eq_one_of_ne_zero hi
      subst i
      -- β(e_1(d)) = ξ(ξ(x)(d))(0) = ξ(x)(d)
      dsimp [β]
      simp [Dn.comp1_embed1, Dn.comp0_embed1, ξ.2]
  -- 由微线性唯一性：α = β
  have hEq : α = β := by
    calc
      α = (Microlinear.microlinear (n := 2) v).1 := (Microlinear.microlinear (n := 2) v).2.2 α hα
      _ = β := ((Microlinear.microlinear (n := 2) v).2.2 β hβ).symm
  exact (congrFun hEq u).symm

/-- 无穷小平移合成律（函数形式）：
$(\xi_{d_1} \circ \xi_{d_2}) = \xi_{d_1 + d_2}$。 -/
theorem translation_compose_fun {R X} [CommRing R] [Microlinear R X]
    (ξ : TangentVectorField R X) (u : Dn R 2) :
    (ξ.1 · (Dn.comp0 R u)) ∘ (ξ.1 · (Dn.comp1 R u)) = (ξ.1 · (Dn.add01 R u)) := by
  funext x
  exact translation_compose ξ x u

/-- **无穷小平移的可逆性**：对 $d \in D$，向量场 $\xi$ 的无穷小平移
$\xi_d(x) := \xi(x)(d)$（即 $(\xi.1 \cdot d)$）是**可逆**的，其逆为
$\xi_{-d}$（即 $(\xi.1 \cdot (-d))$）：
$$\xi_{-d} \circ \xi_d = \mathrm{id}, \qquad \xi_d \circ \xi_{-d} = \mathrm{id}.$$

**注意**：这里给出的是**显式的逆**，而不仅仅是「双射」。在不承认选择公理时，
「双射」（单射 + 满射）并不足以构造逆映射（从满射取原像需要选择公理）；
逆由 $\xi_{-d}$ 显式给出，全程无需选择。

由合成律（取 $u = (d, -d) \in D(2)$，其中 $d \cdot (-d) = 0$，故 $d + (-d) \in D$）：
$$\xi_d \circ \xi_{-d} = \xi_{d + (-d)} = \xi_0 = \mathrm{id},$$
同理另一方向。 -/
theorem infTranslation_invertible {R X} [CommRing R] [Microlinear R X]
    (ξ : TangentVectorField R X) (d : D R) :
    Function.LeftInverse (ξ.1 · (-d)) (ξ.1 · d) ∧
      Function.RightInverse (ξ.1 · (-d)) (ξ.1 · d) := by
  constructor
  · -- ξ_{-d} ∘ ξ_d = id（合成律，取 u = (d, -d)）
    intro x
    change ξ.1 (ξ.1 x d) (-d) = x
    have hu := translation_compose ξ x (Dn.swap R (Dn.mkDiagNeg R d))
    simpa [Dn.comp0_swap, Dn.comp1_swap, Dn.add01_swap,
      Dn.comp0_mkDiagNeg, Dn.comp1_mkDiagNeg, Dn.add01_mkDiagNeg, ξ.2] using hu
  · -- ξ_d ∘ ξ_{-d} = id
    intro x
    change ξ.1 (ξ.1 x (-d)) d = x
    have hu := translation_compose ξ x (Dn.mkDiagNeg R d)
    simpa [Dn.comp0_mkDiagNeg, Dn.comp1_mkDiagNeg, Dn.add01_mkDiagNeg, ξ.2] using hu


/-! ### 向量场空间上的 $R^X$-模与 $R$-模

向量场 $\xi : X \to X^D$（每点指定一个切向量）构成一个 $R^X$-模
（$R^X$ 是 $X$ 上的函数环）：逐点地
$$(\xi + \eta)(x) := \xi(x) + \eta(x), \qquad (f \cdot \xi)(x) := f(x) \cdot \xi(x),$$
其中 $+$ 与 $\cdot$ 是切纤维 $T_x X$ 内的加法与数乘。取常值函数
$f := a$ 即得 $R$-模结构。 -/

/-- 零向量场：每点 $x$ 取该点的零切向量 $0_x$。 -/
instance instZeroTangentVectorField (R) [CommRing R] {X : Type u} :
    Zero (TangentVectorField R X) where
  zero := ⟨fun x ↦ (0 : TangentFiber R X x).1, by
    intro x
    exact (0 : TangentFiber R X x).2⟩

/-- 向量场的逐点加法（纤维内加法）：$(\xi + \eta)(x) := \xi(x) + \eta(x)$。 -/
instance instAddTangentVectorField (R) [CommRing R] {X : Type u} [Microlinear R X] :
    Add (TangentVectorField R X) where
  add ξ η := ⟨fun x ↦ (toFiber ξ x + toFiber η x).1, by
    intro x
    exact (toFiber ξ x + toFiber η x).2⟩

/-- 向量场按函数 $f : X \to R$ 的数乘（逐点）：$(f \cdot \xi)(x) := f(x)\cdot\xi(x)$。 -/
instance instSMulTangentVectorField (R) [CommRing R] {X : Type u} :
    SMul (X → R) (TangentVectorField R X) where
  smul f ξ := ⟨fun x ↦ (f x • toFiber ξ x).1, by
    intro x
    exact (f x • toFiber ξ x).2⟩

/-- 向量场按标量 $a \in R$ 的数乘（逐点，即按常值函数作用）：$(a \cdot \xi)(x) := a\cdot\xi(x)$。 -/
instance instSMulTangentVectorFieldR (R) [CommRing R] {X : Type u} :
    SMul R (TangentVectorField R X) where
  smul a ξ := ⟨fun x ↦ (a • toFiber ξ x).1, by
    intro x
    exact (a • toFiber ξ x).2⟩

/-- 零向量场在点 $x$ 的纤维值就是零切向量。 -/
@[simp]
lemma toFiber_zero (R) [CommRing R] {X : Type u} (x : X) :
    toFiber (0 : TangentVectorField R X) x = 0 := by
  apply Subtype.ext
  rfl

/-- 向量场加法逐点对应纤维内加法。 -/
@[simp]
lemma toFiber_add (R) [CommRing R] {X : Type u} [Microlinear R X]
    (ξ η : TangentVectorField R X) (x : X) :
    toFiber (ξ + η) x = toFiber ξ x + toFiber η x := by
  apply Subtype.ext
  rfl

/-- 向量场按函数数乘逐点对应纤维内数乘。 -/
@[simp]
lemma toFiber_smul (R) [CommRing R] {X : Type u} (f : X → R) (ξ : TangentVectorField R X) (x : X) :
    toFiber (f • ξ) x = f x • toFiber ξ x := by
  apply Subtype.ext
  rfl

/-- 向量场按标量数乘逐点对应纤维内数乘。 -/
@[simp]
lemma toFiber_smulR (R) [CommRing R] {X : Type u} (a : R) (ξ : TangentVectorField R X) (x : X) :
    toFiber (a • ξ) x = a • toFiber ξ x := by
  apply Subtype.ext
  rfl

/-- 向量场构成加法交换幺半群（逐点、由纤维给出）。 -/
instance instAddCommMonoidTangentVectorField (R) [CommRing R] {X : Type u} [Microlinear R X] :
    AddCommMonoid (TangentVectorField R X) where
  toZero := inferInstance
  toAdd := inferInstance
  add_assoc := by
    intro a b c
    apply Subtype.ext
    funext x
    change (toFiber (a + b) x + toFiber c x).1 = (toFiber a x + toFiber (b + c) x).1
    rw [toFiber_add]
    exact congrArg Subtype.val (add_assoc (toFiber a x) (toFiber b x) (toFiber c x))
  add_comm := by
    intro a b
    apply Subtype.ext
    funext x
    change (toFiber (a + b) x).1 = (toFiber (b + a) x).1
    rw [toFiber_add]
    exact congrArg Subtype.val (add_comm (toFiber a x) (toFiber b x))
  zero_add := by
    intro a
    apply Subtype.ext
    funext x
    change (toFiber (0 + a) x).1 = (toFiber a x).1
    rw [toFiber_add, toFiber_zero]
    exact congrArg Subtype.val (zero_add (toFiber a x))
  add_zero := by
    intro a
    apply Subtype.ext
    funext x
    change (toFiber (a + 0) x).1 = (toFiber a x).1
    rw [toFiber_add, toFiber_zero]
    exact congrArg Subtype.val (add_zero (toFiber a x))
  nsmul := nsmulRec
  nsmul_zero := by intro a; rfl
  nsmul_succ := by intro n a; rfl

/-- 向量场构成 $R^X$-模：加法逐点、数乘按函数逐点。 -/
instance instModuleTangentVectorField (R) [CommRing R] {X : Type u} [Microlinear R X] :
    Module (X → R) (TangentVectorField R X) where
  toSMul := inferInstance
  smul_zero := by
    intro f
    apply Subtype.ext
    funext x
    change (f x • toFiber (0 : TangentVectorField R X) x).1 =
      (toFiber (0 : TangentVectorField R X) x).1
    rw [toFiber_zero]
    exact congrArg Subtype.val (smul_zero (A := TangentFiber R X x) (f x))
  smul_add := by
    intro f a b
    apply Subtype.ext
    funext x
    change (f x • toFiber (a + b) x).1 = (toFiber (f • a) x + toFiber (f • b) x).1
    rw [toFiber_add, toFiber_smul, toFiber_smul]
    exact congrArg Subtype.val (smul_add (f x) (toFiber a x) (toFiber b x))
  add_smul := by
    intro f g a
    apply Subtype.ext
    funext x
    change ((f x + g x) • toFiber a x).1 = (toFiber (f • a) x + toFiber (g • a) x).1
    rw [toFiber_smul, toFiber_smul]
    exact congrArg Subtype.val (add_smul (f x) (g x) (toFiber a x))
  zero_smul := by
    intro a
    apply Subtype.ext
    funext x
    change (toFiber ((0 : X → R) • a) x).1 = (toFiber (0 : TangentVectorField R X) x).1
    rw [toFiber_smul, toFiber_zero]
    exact congrArg Subtype.val (zero_smul (M₀ := R) (A := TangentFiber R X x) (toFiber a x))
  one_smul := by
    intro a
    apply Subtype.ext
    funext x
    change (toFiber ((1 : X → R) • a) x).1 = (toFiber a x).1
    rw [toFiber_smul]
    exact congrArg Subtype.val (one_smul R (toFiber a x))
  mul_smul := by
    intro f g a
    apply Subtype.ext
    funext x
    change ((f x * g x) • toFiber a x).1 = (f x • toFiber (g • a) x).1
    rw [toFiber_smul]
    exact congrArg Subtype.val (mul_smul (f x) (g x) (toFiber a x))

/-- 向量场构成 $R$-模（逐点、由纤维给出）。 -/
instance instModuleTangentVectorFieldR (R) [CommRing R] {X : Type u} [Microlinear R X] :
    Module R (TangentVectorField R X) where
  toSMul := inferInstance
  smul_zero := by
    intro a
    apply Subtype.ext
    funext x
    change (a • toFiber (0 : TangentVectorField R X) x).1 =
      (toFiber (0 : TangentVectorField R X) x).1
    rw [toFiber_zero]
    exact congrArg Subtype.val (smul_zero (A := TangentFiber R X x) a)
  smul_add := by
    intro a u v
    apply Subtype.ext
    funext x
    change (a • toFiber (u + v) x).1 = (toFiber (a • u) x + toFiber (a • v) x).1
    rw [toFiber_add, toFiber_smulR, toFiber_smulR]
    exact congrArg Subtype.val (smul_add a (toFiber u x) (toFiber v x))
  add_smul := by
    intro a b v
    apply Subtype.ext
    funext x
    change ((a + b) • toFiber v x).1 = (toFiber (a • v) x + toFiber (b • v) x).1
    rw [toFiber_smulR, toFiber_smulR]
    exact congrArg Subtype.val (add_smul a b (toFiber v x))
  zero_smul := by
    intro v
    apply Subtype.ext
    funext x
    change (toFiber ((0 : R) • v) x).1 = (toFiber (0 : TangentVectorField R X) x).1
    rw [toFiber_smulR, toFiber_zero]
    exact congrArg Subtype.val (zero_smul (M₀ := R) (A := TangentFiber R X x) (toFiber v x))
  one_smul := by
    intro v
    apply Subtype.ext
    funext x
    change (toFiber ((1 : R) • v) x).1 = (toFiber v x).1
    rw [toFiber_smulR]
    exact congrArg Subtype.val (one_smul R (toFiber v x))
  mul_smul := by
    intro a b v
    apply Subtype.ext
    funext x
    change ((a * b) • toFiber v x).1 = (a • toFiber (b • v) x).1
    rw [toFiber_smulR]
    exact congrArg Subtype.val (mul_smul a b (toFiber v x))

end TangentVectorField
