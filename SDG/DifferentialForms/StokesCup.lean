import SDG.DifferentialForms.Algebra

/-!
# Stokes 形式积分基础设施与 cup 的上同调性（单纯层，主线）

1. **边界积分** `boundaryIntegral` 与 Stokes 对偶（∫_σ ∂c = ∫_{∂σ} c，
   链侧 ∂² = 0 由 D2 里程碑 `coboundary_coboundary` 给出）；
2. **分次 Leibniz** `coboundary_cup_product`：主线 `cupProduct` 的
   ∂(c₁ ⌣ c₂) = ∂c₁ ⌣ c₂ + (-1)^p · c₁ ⌣ ∂c₂（补上 `Algebra.lean`
   CupProduct 节中 deferred 的定理；该节注释里的 (-1)^{p+1} 是笔误，
   正确符号为 (-1)^p）。

全部无选择公理（审计目标 `[propext, Quot.sound]`）。

工程纪律：`have` 的**类型**里不允许出现 `(by ...)`（延迟求值导致 omega
丢上下文，反例原子呈孤立 `↑↑k`）——一律前置具名 have；`have` 的**值**里
允许。 -/

namespace SDG.DifferentialForms

section StokesSimplicial

variable {R : Type u} [CommRing R] {X : Type u}

/-! ## 通用切片引理 -/

/-- 三段切片：`Fin n`（`n = a+b+1`）上的求和 = 枢轴项 `T a` + 前段 `[0,a)` + 后段 `[a+1, n)`。 -/
lemma finSum_split_mid {R : Type u} [AddCommMonoid R] {n a b : ℕ}
    (hn : n = a + b + 1) (T : Fin n → R) :
    finSum R n T
      = T (Fin.mk a (by have h2 := hn; omega))
        + (finSum R a (fun i => T (Fin.mk ((i:ℕ)) (by have h1 := i.isLt; have h2 := hn; omega)))
          + finSum R b (fun i => T (Fin.mk (a + 1 + (i:ℕ)) (by have h1 := i.isLt; have h2 := hn; omega)))) := by
  have he : n = (b:ℕ) + (a + 1) := by omega
  rw [finSum_index_congr R he T]
  rw [finSum_front R (a+1) b (fun i : Fin ((b:ℕ)+(a+1)) => T (Fin.cast he.symm i))]
  have hlt1 : ∀ i : Fin (a+1), (i:ℕ) < (b:ℕ) + (a+1) := fun i => by have := i.isLt; omega
  have hlt2 : ∀ i : Fin (a+1), (i:ℕ) < n := fun i => by have h1 := i.isLt; have h2 := he; omega
  have hlt3 : ∀ i : Fin b, (a:ℕ) + 1 + (i:ℕ) < (b:ℕ) + (a+1) := fun i => by have := i.isLt; omega
  have hlt4 : ∀ i : Fin b, (a:ℕ) + 1 + (i:ℕ) < n := fun i => by have h1 := i.isLt; have h2 := he; omega
  have hC1 : ∀ i : Fin (a+1),
      Fin.cast he.symm (Fin.mk ((i:ℕ)) (hlt1 i)) = Fin.mk ((i:ℕ)) (hlt2 i) := fun i =>
    Fin.ext (by simp only [Fin.val_cast, Fin.val_mk])
  have hC2 : ∀ i : Fin b,
      Fin.cast he.symm (Fin.mk (a + 1 + (i:ℕ)) (hlt3 i)) = Fin.mk (a + 1 + (i:ℕ)) (hlt4 i) := fun i =>
    Fin.ext (by simp only [Fin.val_cast, Fin.val_mk])
  rw [finSum_congr (R := R) (n := a+1) (fun i : Fin (a+1) => congrArg T (hC1 i)),
      finSum_congr (R := R) (n := b) (fun i : Fin b => congrArg T (hC2 i))]
  rw [finSum_last (R := R) (m := a)
    (h := fun i => T (Fin.mk ((i:ℕ)) (hlt2 i)))]
  have hAn : (a:ℕ) < n := by have h2 := hn; omega
  have hlt2a : ∀ i : Fin a, (i:ℕ) < n := fun i => by have h1 := i.isLt; have h2 := he; omega
  have hCS : ∀ i : Fin a,
      Fin.mk (((Fin.castSucc i : Fin (a+1)) : ℕ)) (hlt2 (Fin.castSucc i))
        = Fin.mk ((i:ℕ)) (hlt2a i) := fun i =>
    Fin.ext (by simp only [Fin.val_castSucc, Fin.val_mk])
  have hLA : Fin.mk (((Fin.last a : Fin (a+1)) : ℕ)) (hlt2 (Fin.last a))
      = Fin.mk a hAn :=
    Fin.ext (by simp only [Fin.val_castSucc, Fin.val_cast, Fin.val_last, Fin.val_mk])
  rw [finSum_congr (R := R) (n := a) (fun i => congrArg T (hCS i)), congrArg T hLA]
  abel

/-- 末项提取（`m+2` 直配形状，避免 `m+2` 与 `(m+1)+1` 的句法失配）。 -/
lemma finSum_last' {R : Type u} [AddCommMonoid R] (m : ℕ) (h : Fin (m+2) → R) :
    finSum R (m+2) h = finSum R (m+1) (fun i => h (Fin.castSucc i)) + h (Fin.last (m+1)) :=
  finSum_last R (m+1) h

/-- 首项提取（`n+2` 直配形状）。 -/
lemma finSum_succ' {R : Type u} [AddCommMonoid R] (n : ℕ) (f : Fin (n+2) → R) :
    finSum R (n+2) f = f (0 : Fin (n+2)) + finSum R (n+1) (fun i => f (Fin.succ i)) :=
  finSum_succ R (n+1) f

/-! ## Part 1：边界积分与 Stokes 对偶 -/

/-- n-上链 `c` 沿 (n+1)-单纯形 σ 的边界积分：`Σ_i (-1)^i c(face_i σ)`。 -/
def boundaryIntegral {n : ℕ} (c : Cochain R X n) (σ : SimplexPts X (n+1)) : R :=
  finSum R (n+2) (fun i : Fin (n+2) => (-1:R)^((i:ℕ)) * c (coFace σ i))

lemma boundaryIntegral_apply {n : ℕ} (c : Cochain R X n) (σ : SimplexPts X (n+1)) :
    boundaryIntegral c σ = finSum R (n+2) (fun i : Fin (n+2) =>
      (-1:R)^((i:ℕ)) * c (coFace σ i)) := rfl

/-- **Stokes 对偶**：∂c 在 σ 上的取值 = c 在 ∂σ 上的积分（同一公式的两种读法）。 -/
lemma stokes_duality {n : ℕ} (c : Cochain R X n) (σ : SimplexPts X (n+1)) :
    coboundary c σ = boundaryIntegral c σ := rfl

/-- **链侧 ∂² = 0**：边界积分的边界积分为零（由 D2 里程碑 `coboundary_coboundary`）。 -/
lemma boundary_of_boundary_zero {n : ℕ} (c : Cochain R X n) (σ : SimplexPts X (n+2)) :
    finSum R (n+3) (fun i : Fin (n+3) =>
      (-1:R)^((i:ℕ)) * boundaryIntegral c (coFace σ i)) = 0 :=
  congrFun (coboundary_coboundary c) σ

/-! ## Part 2：点态读值引理 -/

/-- α 块高段读值（枢轴与 β-面段）：第 `p+1` 个及以后的面上，α 的读值就是原顶点组。 -/
lemma alphaRead_high {p q : ℕ} (σ : SimplexPts X (p+q+1)) (i : Fin (p+q+2))
    (h : (p:ℕ) + 1 ≤ (i:ℕ)) :
    (fun k : Fin (p+1) => σ (i.succAbove (Fin.mk ((k:ℕ)) (by have := k.isLt; omega))))
      = (fun k : Fin (p+1) => σ (Fin.mk ((k:ℕ)) (by have := k.isLt; omega))) := by
  funext k
  have hkk : (k:ℕ) < (p:ℕ) + q + 1 := by have := k.isLt; omega
  have hkk2 : (k:ℕ) < (p:ℕ) + q + 2 := by have := k.isLt; omega
  have hmk : i.succAbove (Fin.mk ((k:ℕ)) hkk) = Fin.mk ((k:ℕ)) hkk2 := Fin.ext (by
    have hv := succAbove_val i (Fin.mk ((k:ℕ)) hkk)
    simp only [Fin.val_mk] at hv
    rw [hv, if_pos (by have := k.isLt; have := h; omega)])
  exact congrArg σ hmk

/-- α 块前段读值：与 ∂α 的面相同（经 `castLE` 嵌入）。 -/
lemma alphaRead_low {p q : ℕ} (σ : SimplexPts X (p+q+1)) (i : Fin (p+1)) :
    (fun k : Fin (p+1) => σ ((Fin.mk ((i:ℕ)) (by have := i.isLt; omega)).succAbove
        (Fin.mk ((k:ℕ)) (by have := k.isLt; omega))))
      = coFace (fun m : Fin (p+2) => σ (Fin.mk ((m:ℕ)) (by have := m.isLt; omega)))
          (Fin.castLE (by omega) i) := by
  funext k
  have hik : (i:ℕ) < (p:ℕ) + q + 2 := by have := i.isLt; omega
  have hkk : (k:ℕ) < (p:ℕ) + q + 1 := by have := k.isLt; omega
  have hLE2 : (p:ℕ) + 1 ≤ (p:ℕ) + 2 := by omega
  have hBv : ((Fin.castLE hLE2 i).succAbove k : ℕ) < (p:ℕ) + q + 2 := by
    have hv := succAbove_val (Fin.castLE hLE2 i) k
    simp only [Fin.val_mk, Fin.val_castLE] at hv
    rw [hv]
    split_ifs
    · exact Nat.lt_of_lt_of_le k.isLt (by omega)
    · omega
  have hmk : (Fin.mk ((i:ℕ)) hik).succAbove (Fin.mk ((k:ℕ)) hkk)
      = Fin.mk ((Fin.castLE hLE2 i).succAbove k : ℕ) hBv :=
    Fin.ext (by
      have hv1 := succAbove_val (Fin.mk ((i:ℕ)) hik) (Fin.mk ((k:ℕ)) hkk)
      have hv2 := succAbove_val (Fin.castLE hLE2 i) k
      simp only [Fin.val_mk, Fin.val_castLE] at hv1 hv2
      rw [hv1, hv2])
  exact congrArg σ hmk

/-- β 块前段读值：面上 β 读的是整体后移一位的顶点组 `σ_{p+1},…`。 -/
lemma betaRead_front {p q : ℕ} (σ : SimplexPts X (p+q+1)) (i : Fin (p+q+2))
    (h : (i:ℕ) ≤ (p:ℕ)) :
    (fun l : Fin (q+1) => σ (i.succAbove (Fin.mk (p + (l:ℕ)) (by have := l.isLt; omega))))
      = (fun l : Fin (q+1) => σ (Fin.mk (p + 1 + (l:ℕ)) (by have := l.isLt; omega))) := by
  funext l
  have hll : (p:ℕ) + (l:ℕ) < (p:ℕ) + q + 1 := by have := l.isLt; omega
  have hll2 : (p:ℕ) + 1 + (l:ℕ) < (p:ℕ) + q + 2 := by have := l.isLt; omega
  have hmk : i.succAbove (Fin.mk (p + (l:ℕ)) hll) = Fin.mk (p + 1 + (l:ℕ)) hll2 := Fin.ext (by
    have hv := succAbove_val i (Fin.mk (p + (l:ℕ)) hll)
    simp only [Fin.val_mk] at hv
    rw [hv, if_neg (by have := l.isLt; have := h; omega)]
    simp only [Fin.val_mk]
    omega)
  exact congrArg σ hmk

/-- β 块枢轴读值：恰为删除 σ'' 第 1 个顶点的面。 -/
lemma betaRead_pivot {p q : ℕ} (σ : SimplexPts X (p+q+1)) :
    (fun l : Fin (q+1) => σ ((Fin.mk ((p:ℕ)+1) (by omega)).succAbove
        (Fin.mk (p + (l:ℕ)) (by have := l.isLt; omega))))
      = coFace (fun m : Fin (q+2) => σ (Fin.mk (p + (m:ℕ)) (by have := m.isLt; omega)))
          (Fin.mk (1:ℕ) (by omega)) := by
  funext l
  have hP1 : (p:ℕ) + 1 < (p:ℕ) + q + 2 := by omega
  have hpl : (p:ℕ) + (l:ℕ) < (p:ℕ) + q + 1 := by have := l.isLt; omega
  have h1f : (1:ℕ) < (q:ℕ) + 2 := by omega
  have hll : (l:ℕ) < (q:ℕ) + 1 := l.isLt
  have hvv : ((Fin.mk ((p:ℕ)+1) hP1).succAbove (Fin.mk (p + (l:ℕ)) hpl) : ℕ)
      = (p:ℕ) + ((Fin.mk (1:ℕ) h1f).succAbove (Fin.mk ((l:ℕ)) hll) : ℕ) := by
    have hv1 := succAbove_val (Fin.mk ((p:ℕ)+1) hP1) (Fin.mk (p + (l:ℕ)) hpl)
    have hv2 := succAbove_val (Fin.mk (1:ℕ) h1f) (Fin.mk ((l:ℕ)) hll)
    simp only [Fin.val_mk] at hv1 hv2
    rw [hv1, hv2]
    split_ifs <;> omega
  exact congrArg σ (Fin.ext hvv)

/-- β 块后段读值：恰为 σ'' 的第 `↑i - p` 个面。 -/
lemma betaRead_back {p q : ℕ} (σ : SimplexPts X (p+q+1)) (i : Fin (p+q+2))
    (h : (p:ℕ) + 2 ≤ (i:ℕ)) :
    (fun l : Fin (q+1) => σ (i.succAbove (Fin.mk (p + (l:ℕ)) (by have := l.isLt; omega))))
      = coFace (fun m : Fin (q+2) => σ (Fin.mk (p + (m:ℕ)) (by have := m.isLt; omega)))
          (Fin.mk ((i:ℕ) - p) (by have := i.isLt; omega)) := by
  funext l
  have hip : (p:ℕ) + (l:ℕ) < (p:ℕ) + q + 1 := by have := l.isLt; omega
  have hll : (l:ℕ) < (q:ℕ) + 1 := l.isLt
  have hsub : (i:ℕ) - (p:ℕ) < (q:ℕ) + 2 := by have := i.isLt; omega
  have hvv : (i.succAbove (Fin.mk (p + (l:ℕ)) hip) : ℕ)
      = (p:ℕ) + ((Fin.mk ((i:ℕ) - (p:ℕ)) hsub).succAbove (Fin.mk ((l:ℕ)) hll) : ℕ) := by
    have hv1 := succAbove_val i (Fin.mk (p + (l:ℕ)) hip)
    have hv2 := succAbove_val (Fin.mk ((i:ℕ) - (p:ℕ)) hsub) (Fin.mk ((l:ℕ)) hll)
    simp only [Fin.val_mk] at hv1 hv2
    rw [hv1, hv2]
    split_ifs <;> omega
  exact congrArg σ (Fin.ext hvv)

/-- ∂α 的末项面 = α 的原读值（删除末顶点保持前 `p+1` 个顶点）。 -/
lemma coFaceTop_last {p q : ℕ} (σ : SimplexPts X (p+q+1)) :
    coFace (fun m : Fin (p+2) => σ (Fin.mk ((m:ℕ)) (by have := m.isLt; omega)))
        (Fin.last (p+1))
      = (fun k : Fin (p+1) => σ (Fin.mk ((k:ℕ)) (by have := k.isLt; omega))) := by
  funext k
  have hkk : (k:ℕ) < (p:ℕ) + 1 := k.isLt
  have hBv : ((Fin.last ((p:ℕ)+1)).succAbove (Fin.mk ((k:ℕ)) hkk) : ℕ) < (p:ℕ) + q + 2 := by
    have hv := succAbove_val (Fin.last ((p:ℕ)+1)) (Fin.mk ((k:ℕ)) hkk)
    simp only [Fin.val_mk, Fin.val_last] at hv
    rw [hv, if_pos (by have := k.isLt; omega)]
    omega
  have hRk : (k:ℕ) < (p:ℕ) + q + 2 := by have := k.isLt; omega
  have hvv : ((Fin.last ((p:ℕ)+1)).succAbove (Fin.mk ((k:ℕ)) hkk) : ℕ) = (k:ℕ) := by
    have hv := succAbove_val (Fin.last ((p:ℕ)+1)) (Fin.mk ((k:ℕ)) hkk)
    rw [hv, Fin.val_last, if_pos (by have := k.isLt; omega)]
  have hf : Fin.mk ((Fin.last ((p:ℕ)+1)).succAbove (Fin.mk ((k:ℕ)) hkk) : ℕ) hBv
      = Fin.mk ((k:ℕ)) hRk := Fin.ext (by rw [hvv])
  exact congrArg σ hf

/-- ∂β 的首项面 = σ₊（删除 0 号顶点保持整体后移的顶点组）。 -/
lemma coFace_zero_shift {p q : ℕ} (σ : SimplexPts X (p+q+1)) :
    coFace (fun m : Fin (q+2) => σ (Fin.mk (p + (m:ℕ)) (by have := m.isLt; omega)))
        (Fin.mk (0:ℕ) (by omega))
      = (fun l : Fin (q+1) => σ (Fin.mk (p + 1 + (l:ℕ)) (by have := l.isLt; omega))) := by
  funext l
  have h0f : (0:ℕ) < (q:ℕ) + 2 := by omega
  have hll : (l:ℕ) < (q:ℕ) + 1 := l.isLt
  have hv0 : ((Fin.mk (0:ℕ) h0f).succAbove (Fin.mk ((l:ℕ)) hll) : ℕ) = (l:ℕ) + 1 := by
    have hv := succAbove_val (Fin.mk (0:ℕ) h0f) (Fin.mk ((l:ℕ)) hll)
    simp only [Fin.val_mk] at hv
    rw [hv, if_neg (by have := l.isLt; omega)]
  have hAv : (p:ℕ) + ((Fin.mk (0:ℕ) h0f).succAbove (Fin.mk ((l:ℕ)) hll) : ℕ)
      < (p:ℕ) + q + 2 := by rw [hv0]; have := l.isLt; omega
  have hBv : (p:ℕ) + 1 + (l:ℕ) < (p:ℕ) + q + 2 := by have := l.isLt; omega
  have hfin : Fin.mk ((p:ℕ) + ((Fin.mk (0:ℕ) h0f).succAbove (Fin.mk ((l:ℕ)) hll) : ℕ)) hAv
      = Fin.mk ((p:ℕ) + 1 + (l:ℕ)) hBv := Fin.ext (by simp only [Fin.val_mk]; rw [hv0]; omega)
  exact congrArg σ hfin

/-! ## Part 3：分次 Leibniz（主线 `cupProduct` 的 deferred 定理） -/

/-- **分次 Leibniz**：∂(c₁ ⌣ c₂) = (∂c₁) ⌣ c₂ + (-1)^p · c₁ ⌣ (∂c₂)。
    符号账三情形：α-面段无净号；枢轴项与 ∂β 的 j=1 项经 (-1)^{p+1} + (-1)^p = 0 相消；
    β-面段带 (-1)^p。 -/
theorem coboundary_cup_product {p q : ℕ} (α : Cochain R X p) (β : Cochain R X q)
    (σ : SimplexPts X (p+q+1)) :
    coboundary (cupProduct α β) σ
      = coboundary α (fun m : Fin (p+2) => σ (Fin.mk ((m:ℕ)) (by have := m.isLt; omega)))
          * β (fun j : Fin (q+1) => σ (Fin.mk (p + 1 + (j:ℕ)) (by have := j.isLt; omega)))
        + (-1:R)^((p:ℕ)) * α (fun k : Fin (p+1) => σ (Fin.mk ((k:ℕ)) (by have := k.isLt; omega)))
          * coboundary β (fun l : Fin (q+2) => σ (Fin.mk (p + (l:ℕ)) (by have := l.isLt; omega))) := by
  unfold coboundary
  -- cupLeft/cupRight → mk 形式的值引理
  -- 具名 mk 证明（have 类型位置禁 by）
  have hkC : ∀ k : Fin (p+1), (k:ℕ) < (p:ℕ) + q + 1 := fun k => by have := k.isLt; omega
  have hlC : ∀ l : Fin (q+1), (p:ℕ) + (l:ℕ) < (p:ℕ) + q + 1 := fun l => by have := l.isLt; omega
  have hL : ∀ k : Fin (p+1), cupLeft p q k = Fin.mk ((k:ℕ)) (hkC k) := fun k =>
    Fin.ext (by simp only [cupLeft, Fin.val_cast, Fin.val_castAdd, Fin.val_mk])
  have hRt : ∀ l : Fin (q+1), cupRight p q l = Fin.mk (p + (l:ℕ)) (hlC l) := fun l =>
    Fin.ext (by simp only [cupRight, Fin.val_cast, Fin.val_natAdd, Fin.val_mk])
  have hiF : ∀ i : Fin (p+1), (i:ℕ) < (p:ℕ) + q + 2 := fun i => by have := i.isLt; omega
  have hsB : ∀ s : Fin q, (p:ℕ) + 1 + 1 + (s:ℕ) < (p:ℕ) + q + 2 := fun s => by have := s.isLt; omega
  have hsB2 : ∀ s : Fin q, (p:ℕ) + 2 + (s:ℕ) < (p:ℕ) + q + 2 := fun s => by have := s.isLt; omega
  have hPiv : (p:ℕ) + 1 < (p:ℕ) + q + 2 := by omega
  have h1f : (1:ℕ) < (q:ℕ) + 2 := by omega
  have hjF : ∀ j : Fin (q+1), (p:ℕ) + 1 + (j:ℕ) < (p:ℕ) + q + 2 := fun j => by have := j.isLt; omega
  have hcCup : ∀ i : Fin (p+q+2),
      (cupProduct α β) (coFace σ i)
        = α (fun k : Fin (p+1) => σ (i.succAbove (Fin.mk ((k:ℕ)) (hkC k))))
          * β (fun l : Fin (q+1) => σ (i.succAbove (Fin.mk (p + (l:ℕ)) (hlC l)))) := by
    intro i
    have h1 : (fun k : Fin (p+1) => (coFace σ i) (cupLeft p q k))
        = (fun k : Fin (p+1) => σ (i.succAbove (Fin.mk ((k:ℕ)) (hkC k)))) := by
      funext k
      rw [hL k]
      rfl
    have h2 : (fun l : Fin (q+1) => (coFace σ i) (cupRight p q l))
        = (fun l : Fin (q+1) => σ (i.succAbove (Fin.mk (p + (l:ℕ)) (hlC l)))) := by
      funext l
      rw [hRt l]
      rfl
    rw [cupProduct_apply, congrArg α h1, congrArg β h2]
  -- LHS 切片：枢轴 ⟨p+1⟩ + α-面段 + β-面段
  have hnL : (p:ℕ) + q + 2 = ((p:ℕ) + 1) + (q:ℕ) + 1 := by omega
  rw [finSum_split_mid hnL
    (fun i : Fin (p+q+2) => (-1:R)^((i:ℕ)) * (cupProduct α β) (coFace σ i))]
  -- α-面段 → (∂α 前段) ⌣ β₊
  have hF : finSum R (p+1) (fun i : Fin (p+1) =>
      (-1:R)^(((Fin.mk ((i:ℕ)) (hiF i) : Fin (p+q+2)) : ℕ))
        * (cupProduct α β) (coFace σ (Fin.mk ((i:ℕ)) (hiF i))))
      = (finSum R (p+1) (fun i : Fin (p+1) =>
          (-1:R)^(((Fin.castSucc i : Fin ((p:ℕ)+2)) : ℕ))
            * α (coFace (fun m : Fin (p+2) =>
              σ (Fin.mk ((m:ℕ)) (by have := m.isLt; omega))) (Fin.castSucc i))))
        * β (fun j : Fin (q+1) => σ (Fin.mk (p + 1 + (j:ℕ)) (hjF j))) := by
    rw [← finSum_mul_right]
    refine finSum_congr (R := R) (n := p+1) (fun i => ?_)
    have eP : (Fin.val (Fin.mk ((i:ℕ)) (hiF i)))
        = ((Fin.castSucc i : Fin ((p:ℕ)+2)) : ℕ) := rfl
    rw [congrArg (fun c : ℕ => (-1:R)^c) eP, hcCup (Fin.mk ((i:ℕ)) (hiF i)),
      congrArg α (alphaRead_low σ i),
      congrArg β (betaRead_front σ (Fin.mk ((i:ℕ)) (hiF i)) (by simp only [Fin.val_mk]; have := i.isLt; omega))]
    have hcc : Fin.castLE (by have := i.isLt; omega) i = Fin.castSucc i :=
      Fin.ext (by simp only [Fin.val_castLE, Fin.val_castSucc])
    rw [hcc, mul_assoc]
  -- 枢轴项
  have hP : (-1:R)^(((Fin.mk ((p:ℕ)+1) hPiv : Fin (p+q+2)) : ℕ))
      * (cupProduct α β) (coFace σ (Fin.mk ((p:ℕ)+1) hPiv))
      = (-1:R)^((p:ℕ)+1) * α (fun k : Fin (p+1) => σ (Fin.mk ((k:ℕ)) (by have := k.isLt; omega)))
        * β (coFace (fun m : Fin (q+2) => σ (Fin.mk (p + (m:ℕ)) (by have := m.isLt; omega)))
          (Fin.mk (1:ℕ) h1f)) := by
    rw [hcCup (Fin.mk ((p:ℕ)+1) hPiv),
      congrArg α (alphaRead_high σ (Fin.mk ((p:ℕ)+1) hPiv) (by rw [Fin.val_mk])),
      congrArg β (betaRead_pivot σ)]
    have ePiv : ((Fin.mk ((p:ℕ)+1) hPiv : Fin (p+q+2)) : ℕ) = (p:ℕ) + 1 := rfl
    rw [ePiv]
    ring
  -- β-面段
  have hB : finSum R (q:ℕ) (fun s : Fin q =>
      (-1:R)^(((Fin.mk ((p:ℕ)+1+1+(s:ℕ)) (hsB s) : Fin (p+q+2)) : ℕ))
        * (cupProduct α β) (coFace σ (Fin.mk ((p:ℕ)+1+1+(s:ℕ)) (hsB s))))
      = (-1:R)^((p:ℕ)) * α (fun k : Fin (p+1) => σ (Fin.mk ((k:ℕ)) (by have := k.isLt; omega)))
        * finSum R (q:ℕ) (fun j : Fin q =>
          (-1:R)^((j:ℕ)+2) * β (coFace (fun m : Fin (q+2) =>
              σ (Fin.mk (p + (m:ℕ)) (by have := m.isLt; omega)))
            (Fin.succ (Fin.succ j)))) := by
    rw [← finSum_mul_left]
    refine finSum_congr (R := R) (n := q) (fun s => ?_)
    have hss : (p:ℕ) + 2 + (s:ℕ) < (p:ℕ) + q + 2 := hsB2 s
    have eMk : (Fin.mk ((p:ℕ)+1+1+(s:ℕ)) (hsB s) : Fin (p+q+2))
        = Fin.mk ((p:ℕ)+2+(s:ℕ)) hss :=
      Fin.ext (by simp only [Fin.val_mk])
    rw [eMk]
    have eP : (Fin.val (Fin.mk ((p:ℕ)+2+(s:ℕ)) hss)) = (p:ℕ)+2+(s:ℕ) := rfl
    rw [congrArg (fun c : ℕ => (-1:R)^c) eP, hcCup (Fin.mk ((p:ℕ)+2+(s:ℕ)) hss),
      congrArg α (alphaRead_high σ (Fin.mk ((p:ℕ)+2+(s:ℕ)) hss) (by simp only [Fin.val_mk]; have := s.isLt; omega))]
    have hexp : ((p:ℕ) + 2 + (s:ℕ)) = (p:ℕ) + ((s:ℕ) + 2) := by omega
    conv_lhs =>
      lhs
      rhs
      rw [hexp]
    rw [pow_add]
    rw [congrArg β (betaRead_back σ (Fin.mk ((p:ℕ)+2+(s:ℕ)) hss) (by simp only [Fin.val_mk]; have := s.isLt; omega))]
    have hface : (Fin.mk ((p:ℕ)+2+(s:ℕ) - (p:ℕ)) (by have := s.isLt; omega) : Fin (q+2))
        = Fin.succ (Fin.succ s) := Fin.ext (by
          simp only [Fin.val_mk, Fin.val_succ]; omega)
    rw [hface]
    ring
  rw [hF, hP, hB]
  -- RHS 的 ∂α 块末项剥取（p+2 直配）
  rw [finSum_last' (p:ℕ) (fun i : Fin ((p:ℕ)+2) =>
    (-1:R)^((i:ℕ)) * α (coFace (fun m : Fin (p+2) =>
      σ (Fin.mk ((m:ℕ)) (by have := m.isLt; omega))) i))]
  -- RHS 的 ∂β 块双重首项剥取
  rw [finSum_succ' (q:ℕ) (fun i : Fin ((q:ℕ)+2) =>
    (-1:R)^((i:ℕ)) * β (coFace (fun l : Fin (q+2) =>
      σ (Fin.mk (p + (l:ℕ)) (by have := l.isLt; omega))) i))]
  rw [finSum_succ (R := R) (n := (q:ℕ)) (f := fun j : Fin (q+1) =>
    (-1:R)^((Fin.succ j : ℕ)) * β (coFace (fun l : Fin (q+2) =>
      σ (Fin.mk (p + (l:ℕ)) (by have := l.isLt; omega))) (Fin.succ j)))]
  -- ∂α 末项、∂β 首项/次项的读值改写
  have hDAlast : (-1:R)^(((Fin.last ((p:ℕ)+1) : Fin ((p:ℕ)+2)) : ℕ))
      * α (coFace (fun m : Fin (p+2) => σ (Fin.mk ((m:ℕ)) (by have := m.isLt; omega)))
        (Fin.last ((p:ℕ)+1)))
      = (-1:R)^((p:ℕ)+1) * α (fun k : Fin (p+1) => σ (Fin.mk ((k:ℕ)) (by have := k.isLt; omega))) := by
    rw [congrArg α (coFaceTop_last σ), Fin.val_last]
  have hz0 : coFace (fun l : Fin (q+2) => σ (Fin.mk (p + (l:ℕ)) (by have := l.isLt; omega)))
      (0 : Fin ((q:ℕ)+2))
    = (fun j : Fin (q+1) => σ (Fin.mk (p + 1 + (j:ℕ)) (by have := j.isLt; omega))) := by
    have e0 : ((0 : Fin ((q:ℕ)+2)) : Fin ((q:ℕ)+2)) = Fin.mk (0:ℕ) (by omega) := rfl
    rw [e0, coFace_zero_shift σ]
  have hDB0 : (-1:R)^(((0 : Fin ((q:ℕ)+2)) : ℕ))
      * β (coFace (fun l : Fin (q+2) => σ (Fin.mk (p + (l:ℕ)) (by have := l.isLt; omega)))
        (0 : Fin ((q:ℕ)+2)))
      = β (fun j : Fin (q+1) => σ (Fin.mk (p + 1 + (j:ℕ)) (by have := j.isLt; omega))) := by
    have hz2 : (((0 : Fin ((q:ℕ)+2)) : Fin ((q:ℕ)+2)) : ℕ) = 0 := rfl
    rw [hz2, pow_zero, one_mul, congrArg β hz0]
  have hs : (Fin.succ ((0 : Fin (q+1)) : Fin (q+1))) = Fin.mk (1:ℕ) h1f :=
    Fin.ext (by simp only [Fin.val_succ, Fin.val_zero, Fin.val_mk])
  have hDB1 : (-1:R)^((Fin.succ ((0 : Fin (q+1))) : ℕ))
      * β (coFace (fun l : Fin (q+2) => σ (Fin.mk (p + (l:ℕ)) (by have := l.isLt; omega)))
        (Fin.succ ((0 : Fin (q+1)))))
      = (-1:R)^1 * β (coFace (fun m : Fin (q+2) => σ (Fin.mk (p + (m:ℕ)) (by have := m.isLt; omega)))
        (Fin.mk (1:ℕ) h1f)) := by
    rw [hs]
  have hDBrest : ∀ j : Fin q,
      (-1:R)^((Fin.succ (Fin.succ j) : ℕ))
        * β (coFace (fun l : Fin (q+2) => σ (Fin.mk (p + (l:ℕ)) (by have := l.isLt; omega)))
          (Fin.succ (Fin.succ j)))
      = (-1:R)^((j:ℕ)+2) * β (coFace (fun m : Fin (q+2) => σ (Fin.mk (p + (m:ℕ)) (by have := m.isLt; omega)))
        (Fin.succ (Fin.succ j))) := by
    intro j
    have hv : (Fin.succ (Fin.succ j) : ℕ) = (j:ℕ) + 2 := rfl
    rw [hv]
  rw [finSum_congr (R := R) (n := q) (fun j => hDBrest j), hDAlast, hDB0, hDB1]
  -- 符号拼装收尾
  have hpow1 : (-1:R)^((p:ℕ)+1) = (-1:R)^((p:ℕ)) * (-1:R) := by
    rw [pow_succ]
  rw [hpow1]
  ring

end StokesSimplicial

/-! ## Part 5：cup 积在上同调上的良定义性

由函数版分次 Leibniz 直接推出：上积把上闭链对映为上闭链；把一个因子换成
上边缘（另一个因子为上闭链）只改变上积一个上边缘——即
`[α] ⌣ [β] := [α ⌣ β]` 良定义。 -/

section CupCohomology

variable {R : Type u} [CommRing R] {X : Type u}

/-- 上链度数重标记（`h : m = n`；顶点经 `Fin.cast` 值恒等复合）。 -/
def cochainLenCast {m n : ℕ} (h : m = n) (c : Cochain R X m) : Cochain R X n :=
  fun σ => c (fun k => σ (Fin.cast (show m + 1 = n + 1 from by rw [h]) k))

lemma cochainLenCast_apply {m n : ℕ} (h : m = n) (c : Cochain R X m)
    (σ : SimplexPts X n) :
    cochainLenCast h c σ
      = c (fun k => σ (Fin.cast (show m + 1 = n + 1 from by rw [h]) k)) := rfl

lemma cochainLenCast_zero {m n : ℕ} (h : m = n) :
    cochainLenCast h (0 : Cochain R X m) = 0 := by
  funext σ
  rfl

/-- 度数 cast 与 coboundary 交换。 -/
lemma coboundary_cochainLenCast {m n : ℕ} (h : m = n) (c : Cochain R X m) :
    coboundary (cochainLenCast h c)
      = cochainLenCast (show m + 1 = n + 1 from by rw [h]) (coboundary c) := by
  subst h
  rfl

lemma cupLeft_val {p q : ℕ} (k : Fin (p + 1)) :
    ((cupLeft p q k : Fin (p + q + 1)) : ℕ) = (k : ℕ) := by
  simp [cupLeft]

lemma cupRight_val {p q : ℕ} (k : Fin (q + 1)) :
    ((cupRight p q k : Fin (p + q + 1)) : ℕ) = p + (k : ℕ) := by
  simp [cupRight]

/-- **函数版分次 Leibniz**：∂(c₁ ⌀ c₂) = (∂c₁) ⌀ c₂ + (-1)^p · c₁ ⌀ (∂c₂)
    作为 Cochain 的等式（点态主定理 `coboundary_cup_product` 的 funext 包装；
    度数经 `cochainLenCast` 桥接）。 -/
theorem coboundary_cupProduct {p q : ℕ} (α : Cochain R X p) (β : Cochain R X q) :
    coboundary (cupProduct α β)
      = cochainLenCast (show p + 1 + q = p + q + 1 from by omega)
          (cupProduct (coboundary α) β)
        + (-1:R)^((p:ℕ)) • cochainLenCast (show p + (q + 1) = p + q + 1 from by omega)
          (cupProduct α (coboundary β)) := by
  funext σ
  have b1 : ∀ m : Fin ((p:ℕ)+2),
      (fun k => σ (Fin.cast (show p + 1 + q + 1 = p + q + 1 + 1 from by omega) k))
          (cupLeft ((p:ℕ)+1) q m)
        = σ (Fin.mk ((m:ℕ)) (by have := m.isLt; omega)) := by
    intro m
    apply congrArg σ
    apply Fin.ext
    simp only [Fin.val_cast, cupLeft_val, Fin.val_mk]
  have b2 : ∀ j : Fin (q+1),
      (fun k => σ (Fin.cast (show p + 1 + q + 1 = p + q + 1 + 1 from by omega) k))
          (cupRight ((p:ℕ)+1) q j)
        = σ (Fin.mk (p + 1 + (j:ℕ)) (by have := j.isLt; omega)) := by
    intro j
    apply congrArg σ
    apply Fin.ext
    simp only [Fin.val_cast, cupRight_val, Fin.val_mk]
  have b3 : ∀ k : Fin (p+1),
      (fun l => σ (Fin.cast (show p + (q + 1) + 1 = p + q + 1 + 1 from by omega) l))
          (cupLeft p (q+1) k)
        = σ (Fin.mk ((k:ℕ)) (by have := k.isLt; omega)) := by
    intro k
    apply congrArg σ
    apply Fin.ext
    simp only [Fin.val_cast, cupLeft_val, Fin.val_mk]
  have b4 : ∀ l : Fin ((q:ℕ)+2),
      (fun k => σ (Fin.cast (show p + (q + 1) + 1 = p + q + 1 + 1 from by omega) k))
          (cupRight p (q+1) l)
        = σ (Fin.mk (p + (l:ℕ)) (by have := l.isLt; omega)) := by
    intro l
    apply congrArg σ
    apply Fin.ext
    simp only [Fin.val_cast, cupRight_val, Fin.val_mk]
  rw [coboundary_cup_product α β σ, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    cochainLenCast_apply, cochainLenCast_apply, cupProduct_apply, cupProduct_apply,
    funext b1, funext b2, funext b3, funext b4, mul_assoc]

/-- **cup 积保持上闭链**：两个上闭链的上积仍是上闭链。 -/
theorem cupProduct_isCocycle {p q : ℕ} (α : Cochain R X p) (β : Cochain R X q)
    (hα : coboundary α = 0) (hβ : coboundary β = 0) :
    coboundary (cupProduct α β) = 0 := by
  rw [coboundary_cupProduct, hα, hβ, cup_zero_left, cup_zero_right,
    cochainLenCast_zero, cochainLenCast_zero, smul_zero, add_zero]

/-- **左因子良定义性**：把左因子换成上边缘（右因子为上闭链），上积恰为
    一个上边缘——witness 是 `cupProduct w β`（分次 Leibniz + ∂β = 0）。 -/
theorem cupProduct_coboundary_left {p q : ℕ} (w : Cochain R X (p+1))
    (β : Cochain R X q) (hβ : coboundary β = 0) :
    coboundary (cupProduct w β)
      = cochainLenCast (show p + 2 + q = p + 1 + q + 1 from by omega)
        (cupProduct (coboundary w) β) := by
  rw [coboundary_cupProduct, hβ, cup_zero_right, cochainLenCast_zero, smul_zero,
    add_zero]

/-- **右因子良定义性**：把右因子换成上边缘（左因子为上闭链），上积恰为
    一个上边缘——witness 是 `cupProduct α w`（分次 Leibniz + ∂α = 0）。 -/
theorem cupProduct_coboundary_right {p q : ℕ} (α : Cochain R X p)
    (w : Cochain R X (q+1)) (hα : coboundary α = 0) :
    coboundary (cupProduct α w)
      = (-1:R)^((p:ℕ)) • cochainLenCast
        (show p + (q + 2) = p + (q + 1) + 1 from by omega)
        (cupProduct α (coboundary w)) := by
  rw [coboundary_cupProduct, hα, cup_zero_left, cochainLenCast_zero, zero_add]

/-! ## cup 单位律 -/

/-- **cup 左单位律**：`1 ⌀ α = α`。直接内联 cochainOfFun 避免多层 delta。 -/
theorem cupProduct_unit_left {q : ℕ} (α : Cochain R X q) :
    cupProduct (cochainOfFun (fun _ => (1 : R))) α
      = cochainLenCast (show q = 0 + q from by omega) α := by
  funext σ
  rw [cochainLenCast_apply, cupProduct_apply]
  have h1 : cochainOfFun (fun _ => (1 : R))
      (fun k : Fin (0 + 1) => σ (cupLeft 0 q k)) = 1 := rfl
  rw [h1, one_mul]
  congr 1
  funext k
  apply congrArg σ
  apply Fin.ext
  rw [cupRight_val, Fin.val_cast]
  omega

/-- **cup 右单位律**：`α ⌀ 1 = α`。 -/
theorem cupProduct_unit_right {p : ℕ} (α : Cochain R X p) :
    cupProduct α (cochainOfFun (fun _ => (1 : R))) = α := by
  funext σ
  rw [cupProduct_apply]
  have h1 : cochainOfFun (fun _ => (1 : R))
      (fun k : Fin (0 + 1) => σ (cupRight p 0 k)) = 1 := rfl
  rw [h1, mul_one]
  rfl

/-- 单位律在上同调层面成立（右）。 -/
theorem coboundary_cupProduct_unit_right {p : ℕ} (α : Cochain R X p) :
    coboundary (cupProduct α (cochainOfFun (fun _ => (1 : R)))) = coboundary α := by
  rw [cupProduct_unit_right]

end CupCohomology

end SDG.DifferentialForms
