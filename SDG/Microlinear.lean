import SDG.NoChoice
import SDG.Infinitesimal
import SDG.KockLawvereDkn

/-!
# SDG.Microlinear

微线性空间 (Microlinear Spaces)。

在 SDG 中，「微线性」刻画了这样一类空间 $X$：其切空间具有 $R$-线性结构，
使得大多数微分几何构造可以在其上执行。这是通过要求「把 $D(n)$ 上的函数
拉回到各坐标方向的 $D$ 上」是一个双射来实现的（nLab「微线性空间」定义的具体形式）。

主要内容：
* 坐标嵌入 $e_i : D \to D(n)$；
* 切向量族在基点上的纤维积 `TangentFiberProduct`；
* 典范映射 $\Phi_n$（`Dn.restrict`/`Dn.restrict'`）；
* 微线性对象 `Microlinear`。
-/

/-! ## 微线性对象 (Microlinear Spaces)

在 SDG 中，「微线性」刻画了这样一类空间 $X$：其切空间具有 $R$-线性结构，
使得大多数微分几何构造可以在其上执行。这是通过要求「把 $D(n)$ 上的函数
拉回到各坐标方向的 $D$ 上」是一个双射来实现的（nLab「微线性空间」定义的具体形式）。

具体地，对每个 $n \in \mathbb{N}$，考察典范映射
$$\Phi_n : X^{D(n)} \longrightarrow \left\{ (v_1, \ldots, v_n) \in (X^D)^n \;\middle|\; v_1(0) = \cdots = v_n(0) \right\}, \quad g \mapsto (g \circ e_1, \ldots, g \circ e_n),$$
其中 $e_i : D \to D(n)$ 把 $d$ 放到第 $i$ 个坐标、其余为 $0$。

$X$ 是**微线性**的（`Microlinear R X`），如果每个 $\Phi_n$ 都是双射，即
$$X^{D(n)} \cong X^D \times_X \cdots \times_X X^D$$
（$X^D$ 在基点上的 $n$ 重纤维积）。当 $X = R$ 时，这正是 Kock-Lawvere 公理的 $n$ 维版本。 -/


/-- **微线性对象**：$X$ 是微线性的，若对每个 $n \in \mathbb{N}$（$n \neq 0$）和每个
「在基点上有相同取值」的切向量族 $v \in X^D \times_X \cdots \times_X X^D$，
存在唯一一个 $g : D(n) \to X$ 使得 $\Phi_n(g) = v$（即 $g \circ e_i = v_i$ 对所有 $i$）。

等价地说，典范映射 $\Phi_n : X^{D(n)} \to X^D \times_X \cdots \times_X X^D$ 是双射，
即 $X^{D(n)} \cong X^D \times_X \cdots \times_X X^D$（在基点上的纤维积）。
「存在且唯一」用 `ExistsUnique'` 编码来表达。

**注意**：只要求 $n \neq 0$ 的情形（`[NeZero n]`）。因为 $D(0)$ 是单点，对非平凡的
$R$（如 $\mathbb{Q}$），$D(0) \to R \cong R$ 非单点，故 $n = 0$ 的微线性条件不成立。 -/
class Microlinear (R) [CommRing R] (X) where
  microlinear {n : ℕ} [NeZero n] (v : TangentFiberProduct R X n) :
    ExistsUnique' fun (g : Dn R n → X) ↦ Dn.restrict' R g = v


/-! ## 微线性在 Π-类型下的保持 (Closure under Π-types)

微线性空间在若干重要的构造下封闭，其中最重要的是：**任意指标集上的 Π-类型
（依赖函数空间）保持微线性**。

具体地，设 $Y : I \to \mathsf{Type}$ 是一族类型。若每个纤维 $Y_i$ 都是微线性的，
则整个依赖函数空间 $\prod_{i : I} Y_i$ 也是微线性的。这一结果覆盖了：
* **任意重积**（取 $Y_i := X$ 常值族），特别是 $A \to X$（函数空间/指数对象）；
* 有限积（可借助与 $\text{Bool}$ 索引族的等价化归到 Π-类型）。

**证明思路**（不依赖选择公理）：`ExistsUnique'` 是携带数据的子类型（不是 `∃`，
取 `.1` 即可得唯一扩展而不做任何选择）。对每个指标 $i$，把切向量族 $v$ 逐点
投影到 $Y_i$ 上得到 $v^{(i)}_k(d) := v_k(d)(i)$，由 $Y_i$ 的微线性取唯一扩展
$g_i : D(n) \to Y_i$，再逐点装配 $g(x)(i) := g_i(x)$ 即为 $\prod_i Y_i$ 上的唯一扩展。
「存在」由各 $g_i$ 的扩展性逐点得到，「唯一」由各 $g_i$ 的唯一性逐点得到。 -/

/-- 任意指标集上的 Π-类型（依赖函数空间）保持微线性：
若每个 $Y_i$ 都是微线性的，则 $\prod_{i : I} Y_i$ 也是微线性的。 -/
instance instMicrolinearPi (R) [CommRing R] {I : Type*} {Y : I → Type*}
    [hY : ∀ i, Microlinear R (Y i)] : Microlinear R ((i : I) → Y i) where
  microlinear {n : ℕ} [NeZero n] (v : TangentFiberProduct R ((i : I) → Y i) n) := by
    -- 对每个指标 i，把 v 逐点投影到 Y_i，得到 Y_i 上的纤维积数据
    let vAt : (i : I) → TangentFiberProduct R (Y i) n :=
      fun i ↦ ⟨fun k d ↦ v.1 k d i, by
        intro k l
        exact congrFun (v.property k l) i
      ⟩
    -- 对每个指标 i，取唯一扩展 g_i（ExistsUnique' 是携带数据的子类型，无选择公理）
    let gAt : (i : I) → (Dn R n → Y i) :=
      fun i ↦ ((hY i).microlinear (vAt i)).1
    -- 逐点装配 g : D(n) → ∏_i Y_i
    let g : Dn R n → (i : I) → Y i :=
      fun x i ↦ gAt i x
    refine ⟨g, ?_, ?_⟩
    · -- 存在性：Dn.restrict' R g = v（逐点即各 g_i 的扩展性）
      apply Subtype.ext
      funext k
      funext d
      funext i
      dsimp [g, gAt]
      have hri : Dn.restrict' R ((hY i).microlinear (vAt i)).1 = vAt i :=
        ((hY i).microlinear (vAt i)).property.1
      exact congrFun (congrFun (congrArg Subtype.val hri) k) d
    · -- 唯一性：由各 g_i 的唯一性逐点得到
      intro y hy
      funext x
      funext i
      dsimp [g, gAt]
      have hyi : Dn.restrict' R (fun x : Dn R n ↦ y x i) = vAt i := by
        apply Subtype.ext
        funext k
        funext d
        change y (Dn.embed R k d) i = v.1 k d i
        have hhy := congrArg Subtype.val hy
        exact congrFun (congrFun (congrFun hhy k) d) i
      have huni : (fun x : Dn R n ↦ y x i) = ((hY i).microlinear (vAt i)).1 :=
        ((hY i).microlinear (vAt i)).property.2 (fun x : Dn R n ↦ y x i) hyi
      exact congrFun huni x


/-- 二元积保持微线性：若 $X, Y$ 都微线性，则 $X \times Y$ 微线性。
这是「Π-类型保微线性」的二元版本：由于 $X \times Y$ 本身不是 Π-类型，这里用
逐点投影给出直接的构造——把切向量族 $v$ 沿两个投影分别压到 $X$、$Y$ 上，取各自
的唯一扩展 $g_X, g_Y$，再装配 $g(x) := (g_X(x), g_Y(x))$。存在与唯一均逐分量成立。 -/
instance instMicrolinearProd (R) [CommRing R] {X Y : Type*}
    [Microlinear R X] [Microlinear R Y] : Microlinear R (X × Y) where
  microlinear {n : ℕ} [NeZero n] (v : TangentFiberProduct R (X × Y) n) := by
    -- 把 v 沿两个投影分别压到 X 与 Y 上（基点一致由 v.property 传递）
    let vX : TangentFiberProduct R X n :=
      ⟨fun k d ↦ (v.1 k d).1, by
        intro k l
        exact congrArg Prod.fst (v.property k l)
      ⟩
    let vY : TangentFiberProduct R Y n :=
      ⟨fun k d ↦ (v.1 k d).2, by
        intro k l
        exact congrArg Prod.snd (v.property k l)
      ⟩
    -- 取两个分量上的唯一扩展，再装配为积上的扩展
    let gX : Dn R n → X := (Microlinear.microlinear (n := n) vX).1
    let gY : Dn R n → Y := (Microlinear.microlinear (n := n) vY).1
    let g : Dn R n → X × Y := fun x ↦ (gX x, gY x)
    refine ⟨g, ?_, ?_⟩
    · -- 存在性：Dn.restrict' R g = v（逐分量即 gX、gY 的扩展性）
      apply Subtype.ext
      funext k
      funext d
      apply Prod.ext
      · dsimp [g, gX]
        have hX : Dn.restrict' R (Microlinear.microlinear (n := n) vX).1 = vX :=
          (Microlinear.microlinear (n := n) vX).property.1
        exact congrFun (congrFun (congrArg Subtype.val hX) k) d
      · dsimp [g, gY]
        have hY : Dn.restrict' R (Microlinear.microlinear (n := n) vY).1 = vY :=
          (Microlinear.microlinear (n := n) vY).property.1
        exact congrFun (congrFun (congrArg Subtype.val hY) k) d
    · -- 唯一性：逐分量由 gX、gY 的唯一性得到
      intro y hy
      funext x
      apply Prod.ext
      · dsimp [g, gX]
        have hyX : Dn.restrict' R (fun x : Dn R n ↦ (y x).1) = vX := by
          apply Subtype.ext
          funext k
          funext d
          change (y (Dn.embed R k d)).1 = (v.1 k d).1
          have hhy := congrArg Subtype.val hy
          exact congrArg Prod.fst (congrFun (congrFun hhy k) d)
        have huniX : (fun x : Dn R n ↦ (y x).1) = (Microlinear.microlinear (n := n) vX).1 :=
          (Microlinear.microlinear (n := n) vX).property.2 (fun x : Dn R n ↦ (y x).1) hyX
        exact congrFun huniX x
      · dsimp [g, gY]
        have hyY : Dn.restrict' R (fun x : Dn R n ↦ (y x).2) = vY := by
          apply Subtype.ext
          funext k
          funext d
          change (y (Dn.embed R k d)).2 = (v.1 k d).2
          have hhy := congrArg Subtype.val hy
          exact congrArg Prod.snd (congrFun (congrFun hhy k) d)
        have huniY : (fun x : Dn R n ↦ (y x).2) = (Microlinear.microlinear (n := n) vY).1 :=
          (Microlinear.microlinear (n := n) vY).property.2 (fun x : Dn R n ↦ (y x).2) hyY
        exact congrFun huniY x

/-! ## KL 公理蕴含 $R$ 微线性（Prop I.6.4 的 $k$ 阶推广）

`IsKockLawvereDkn`（Axiom 1'' 的 $k$ 阶版本，见 `SDG.KockLawvereDkn`）蕴含
$R$ 自身微线性：对每个 $n \ge 1$ 与每个基点一致的切向量族 $v$，存在唯一扩展
$g : D(n) \to R$。

证明：由 `IsKockLawvere_one`（`IsKockLawvereDkn` 经 `instIsKockLawvereDk` /
`instIsKockLawvereOne` 的 $k=n=1$ 特例推出）取每个 $v_i$ 的斜率 $s_i$
（$v_i(d) = v_i(0) + s_i d$），构造扩展 $g(x) = b + \sum_i s_i x_i$（$b$ = 公共基点）。
存在性直接验证 $g \circ e_k = v_k$；唯一性由 `IsKockLawvereDknAt R 1 n` 的「$g$ 唯一
仿射」给出——仿射系数经 `polyEvalDkn_affine`/`polyEvalDkn_axis` 与 $v_i$ 的斜率
$s_i$ 对齐：常数部分在 $x = 0$ 处等于基点 $b$，线性部分用 `smul_cancel_d` 微商消去。
-/

/-- **`IsKockLawvereDkn` 蕴含 `Microlinear R R`**（Prop I.6.4 的 $k$ 阶推广）：
KL 公理（Axiom 1'' 的 $k$ 阶版本）保证 $R$ 自身对一切 $n \ge 1$ 微线性。 -/
instance microlinear_of_IsKockLawvereDkn (R : Type u) [IsKockLawvereDkn R] : Microlinear R R where
  microlinear {n : ℕ} [NeZero n] (v : TangentFiberProduct R R n) := by
    -- 公共基点
    let b : R := v.1 0 0
    -- 每个切向量 v_i : D → R 由 KL(1) 唯一仿射化
    let s : Fin n → R := fun i ↦ (IsKockLawvere_one.isKockLawvere_one (v.1 i)).1
    have hvi : ∀ i d, v.1 i d = (v.1 i) 0 + s i * d := by
      intro i d
      exact (IsKockLawvere_one.isKockLawvere_one (v.1 i)).2.1 d
    have hbase : ∀ i, (v.1 i) 0 = b := by
      intro i
      dsimp [b]
      exact v.property i 0
    -- 扩展 g(x) = b + Σ s_i x_i（求和用 `finSum`）
    let g : Dn R n → R := fun x ↦ b + finSum R n (fun i : Fin n ↦ s i * x.1 i)
    refine ⟨g, ?_, ?_⟩
    · -- 存在性：g ∘ e_k = v_k
      apply Subtype.ext
      funext k
      funext d
      change g (Dn.embed R k d) = v.1 k d
      dsimp [g]
      have hsum : finSum R n (fun i : Fin n ↦ s i * (Dn.embed R k d).1 i) = s k * (d : R) := by
        have hterm : ∀ i : Fin n, s i * (Dn.embed R k d).1 i = if i = k then s k * (d : R) else 0 := by
          intro i
          by_cases hik : i = k
          · subst i
            simp [Dn.embed, Function.update]
          · simp [Dn.embed, Function.update, hik]
        calc
          finSum R n (fun i ↦ s i * (Dn.embed R k d).1 i)
              = finSum R n (fun i ↦ if i = k then s k * (d : R) else 0) := by
                exact congrArg (fun φ : Fin n → R ↦ finSum R n φ) (funext hterm)
          _ = s k * (d : R) := finSum_eq_single R k (s k * (d : R))
      rw [hsum]
      rw [hvi k d, hbase k]
    · -- 唯一性
      intro y hy
      -- y 是仿射函数（Axiom 1'' 的 k=1 情形）
      let a : PolyCoeff R 1 n := (IsKockLawvereDkn.isKockLawvereDkn (k := 1) y).1
      have hyAff : ∀ x, y x = polyEvalDkn R 1 n a (x : Fin n → R) :=
        (IsKockLawvereDkn.isKockLawvereDkn (k := 1) y).2.1
      have hres : ∀ k d, y (Dn.embed R k d) = v.1 k d := by
        intro k d
        exact congrFun (congrFun (congrArg Subtype.val hy) k) d
      -- a 的常数部分 = b（在 x = 0 处取值）
      have hconst : polyCoeff1const R n a = b := by
        have hy0 : y 0 = b := by
          have h00 := hres 0 (0 : D R)
          dsimp [b]
          simpa [Dn.embed_zero] using h00
        have hy0' : y 0 = polyCoeff1const R n a := by
          rw [hyAff 0]
          exact polyEvalDkn_zero_const R n a
        calc
          polyCoeff1const R n a = y 0 := hy0'.symm
          _ = b := hy0
      -- a 的线性部分 = s（微商消去）
      have hlin : polyCoeff1lin R n a = s := by
        funext k
        have hsub : polyCoeff1lin R n a k - s k = 0 := by
          apply smul_cancel_d
          intro d
          have hk1 : y (Dn.embed R k d) = polyCoeff1const R n a + polyCoeff1lin R n a k * (d : R) := by
            rw [hyAff (Dn.embed R k d)]
            exact polyEvalDkn_axis R n a k d
          have hk2 : y (Dn.embed R k d) = b + s k * (d : R) := by
            rw [hres k d, hvi k d, hbase k]
          have hEq : polyCoeff1const R n a + polyCoeff1lin R n a k * (d : R) =
              b + s k * (d : R) := by
            rw [← hk1, hk2]
          rw [hconst] at hEq
          calc
            (polyCoeff1lin R n a k - s k) * (d : R)
                = polyCoeff1lin R n a k * (d : R) - s k * (d : R) := by ring
            _ = (b + polyCoeff1lin R n a k * (d : R)) - (b + s k * (d : R)) := by ring
            _ = 0 := by
              rw [hEq]
              ring
        exact sub_eq_zero.mp hsub
      -- 由常数与线性部分一致得 y = g
      funext x
      dsimp [g]
      rw [hyAff x]
      rw [polyEvalDkn_affine R n a (x : Fin n → R)]
      rw [← hconst, ← hlin]
