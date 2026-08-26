import SDG.NoChoice
import SDG.Infinitesimal
import SDG.Derivative
import SDG.Rational
import SDG.Taylor
import SDG.Order

open SDG.Order

/-!
# SDG.Integration

积分公理（Integration Axiom）、原函数与定积分。

Kock 综合微分几何（SDG）的**第二积分公理**定义在**单位区间** $I = [0,1]$ 上：
每个函数 $f : I \to R$ 都有唯一的原函数 $g : I \to R$，满足 $g(0) = 0$ 且
$g' = f$（「存在且唯一」用 `ExistsUnique'` 编码）：

$$\forall f : I \to R,\ \exists!\, g : I \to R,\ g(0) = 0 \ \land\ \forall x : I,\ g'(x) = f(x).$$

区间 $I = [0,1]$（`SDG.Order.UnitInterval`）由非严格序 `≤` 定义；关键事实是
无穷小量被 $0$ 夹住（$0 \le d \le 0$，见 `SDG.Order`），故对 $x \in I,\ d \in D$
有 $x + d \in I$（`UnitInterval.add_d`），这使得「沿无穷小方向」的区间导数
`sderiv_I` 良定。由此定义**原函数** `primitive f` 与**定积分**
$\int_a^b f = \mathrm{primitive}\,f\,b - \mathrm{primitive}\,f\,a$
（$a, b \in I$），并证明：

* 微积分基本定理：$\frac{d}{dx}\int_0^x f = f(x)$（$x \in I$）；
* 原函数与积分的线性性（和、差、取负、数乘、常值）；
* 定积分的区间可加性 $\int_a^b f + \int_b^c f = \int_a^c f$ 与上下限交换。

进一步，用 $[0,1]$ 上的积分经参数化 $x = a + t(b-a)$ 的换元定义**$R$ 上的定积分**
`integralR f a b := (b - a) \int_0^1 f(a + t(b-a))\,dt$（$a, b \in R$），并给出其
基本性质（退化、常值、零、和、差、负、数乘）。

导数运算律（和、差、负、数乘、积）见 `SDG.Derivative`；$R$ 为 $\mathbb{Q}$-代数
时的 $\frac{1}{n!}$ 除法见 `SDG.Taylor`（用于 $\int x\,dx = x^2/2$）。
-/

namespace SDG.Integration

/-! ## 积分公理 -/

/-- **积分公理**（定义在单位区间 $I = [0,1]$ 上）：每个函数 $f : I \to R$ 都有
唯一的原函数 $g : I \to R$，满足 $g(0) = 0$ 且 $\forall x : I,\ g'(x) = f(x)$。

这里 $g'(x)$ 是区间 $I$ 上的合成导数，由 $R$ 的 Kock-Lawvere 公理与
`UnitInterval.add_d`（$x + d \in I$，$\forall d \in D$）良定，即使
$g(x+d) = g(x) + g'(x)\,d$（$\forall d \in D$）成立的唯一元素。 -/
class IsIntegration (R : Type u) extends IsKockLawvere_one R, IsSDGOrder R where
  integration (f : UnitInterval R → R) :
    ExistsUnique' fun g : UnitInterval R → R ↦
      g 0 = 0 ∧ ∀ x : UnitInterval R,
        (IsKockLawvere_one.isKockLawvere_one
          (fun d : D R ↦ g (UnitInterval.add_d R x d))).1 = f x

/-! ## 区间上的导数 -/

/-- 区间 $I$ 上的**合成导数**：对 $g : I \to R$ 与 $x : I$，$g'(x)$ 是使
$g(x+d) = g(x) + g'(x) \cdot d$（$\forall d \in D$）成立的唯一元素。
（与积分公理中的导数一致。） -/
def sderiv_I {R : Type u} [IsIntegration R]
    (g : UnitInterval R → R) (x : UnitInterval R) : R :=
  (IsKockLawvere_one.isKockLawvere_one fun d : D R ↦ g (UnitInterval.add_d R x d)).1

/-- 区间导数的刻画：$g(x+d) = g(x) + g'(x)\, d$（$\forall d \in D$）。 -/
theorem sderiv_I_spec {R : Type u} [IsIntegration R]
    (g : UnitInterval R → R) (x : UnitInterval R) (d : D R) :
    g (UnitInterval.add_d R x d) = g x + sderiv_I g x * (d : R) := by
  unfold sderiv_I
  simpa [UnitInterval.add_d] using
    (IsKockLawvere_one.isKockLawvere_one fun d : D R ↦ g (UnitInterval.add_d R x d)).2.1 d

/-- 区间导数的和法则：$(g + h)' = g' + h'$。 -/
lemma sderiv_I_add {R : Type u} [IsIntegration R]
    (g h : UnitInterval R → R) (x : UnitInterval R) :
    sderiv_I (fun t ↦ g t + h t) x = sderiv_I g x + sderiv_I h x := by
  symm
  apply (IsKockLawvere_one.isKockLawvere_one
    (fun d : D R ↦ g (UnitInterval.add_d R x d) + h (UnitInterval.add_d R x d))).2.2
      (sderiv_I g x + sderiv_I h x)
  intro d
  have hg := sderiv_I_spec g x d
  have hh := sderiv_I_spec h x d
  have hP0 : g (UnitInterval.add_d R x 0) + h (UnitInterval.add_d R x 0) = g x + h x := by
    simp [UnitInterval.add_d]
  rw [hP0]
  calc
    g (UnitInterval.add_d R x d) + h (UnitInterval.add_d R x d)
        = (g x + sderiv_I g x * (d : R)) + (h x + sderiv_I h x * (d : R)) := by rw [hg, hh]
    _ = g x + h x + (sderiv_I g x + sderiv_I h x) * (d : R) := by ring

/-- 区间导数的取负：$(-g)' = -g'$。 -/
lemma sderiv_I_neg {R : Type u} [IsIntegration R]
    (g : UnitInterval R → R) (x : UnitInterval R) :
    sderiv_I (fun t ↦ -g t) x = -sderiv_I g x := by
  symm
  apply (IsKockLawvere_one.isKockLawvere_one
    (fun d : D R ↦ -(g (UnitInterval.add_d R x d)))).2.2 (-sderiv_I g x)
  intro d
  have hg := sderiv_I_spec g x d
  have hP0 : -(g (UnitInterval.add_d R x 0)) = -g x := by
    simp [UnitInterval.add_d]
  rw [hP0]
  calc
    -(g (UnitInterval.add_d R x d)) = -(g x + sderiv_I g x * (d : R)) := by rw [hg]
    _ = -g x + (-sderiv_I g x) * (d : R) := by ring

/-- 区间导数的数乘：$(c \cdot g)' = c \cdot g'$。 -/
lemma sderiv_I_smul {R : Type u} [IsIntegration R]
    (c : R) (g : UnitInterval R → R) (x : UnitInterval R) :
    sderiv_I (fun t ↦ c * g t) x = c * sderiv_I g x := by
  symm
  apply (IsKockLawvere_one.isKockLawvere_one
    (fun d : D R ↦ c * g (UnitInterval.add_d R x d))).2.2 (c * sderiv_I g x)
  intro d
  have hg := sderiv_I_spec g x d
  have hP0 : c * g (UnitInterval.add_d R x 0) = c * g x := by
    simp [UnitInterval.add_d]
  rw [hP0]
  calc
    c * g (UnitInterval.add_d R x d) = c * (g x + sderiv_I g x * (d : R)) := by rw [hg]
    _ = c * g x + (c * sderiv_I g x) * (d : R) := by ring

/-- 区间导数的差法则：$(g - h)' = g' - h'$。 -/
lemma sderiv_I_sub {R : Type u} [IsIntegration R]
    (g h : UnitInterval R → R) (x : UnitInterval R) :
    sderiv_I (fun t ↦ g t - h t) x = sderiv_I g x - sderiv_I h x := by
  calc
    sderiv_I (fun t ↦ g t - h t) x = sderiv_I (fun t ↦ g t + (-h t)) x := by
      congr 1
      funext t
      rw [sub_eq_add_neg]
    _ = sderiv_I g x + sderiv_I (fun t ↦ -h t) x := sderiv_I_add g (fun t ↦ -h t) x
    _ = sderiv_I g x + (-sderiv_I h x) := by rw [sderiv_I_neg h x]
    _ = sderiv_I g x - sderiv_I h x := by rw [sub_eq_add_neg]

/-- 常函数的区间导数：$(\lambda x.\, c)' = 0$。 -/
lemma sderiv_I_const {R : Type u} [IsIntegration R] (c : R) (x : UnitInterval R) :
    sderiv_I (fun _ : UnitInterval R ↦ c) x = 0 := by
  unfold sderiv_I
  symm
  apply (IsKockLawvere_one.isKockLawvere_one (fun _ : D R ↦ c)).2.2 0
  intro d
  simp

/-- 区间导数的积法则（莱布尼茨）：$(g \cdot h)' = g' \cdot h + g \cdot h'$。 -/
lemma sderiv_I_mul {R : Type u} [IsIntegration R]
    (g h : UnitInterval R → R) (x : UnitInterval R) :
    sderiv_I (fun t ↦ g t * h t) x = sderiv_I g x * h x + g x * sderiv_I h x := by
  symm
  apply (IsKockLawvere_one.isKockLawvere_one
    (fun d : D R ↦ g (UnitInterval.add_d R x d) * h (UnitInterval.add_d R x d))).2.2
      (sderiv_I g x * h x + g x * sderiv_I h x)
  intro d
  have hg := sderiv_I_spec g x d
  have hh := sderiv_I_spec h x d
  have hd : (d : R) * (d : R) = 0 := D.mul_eq_zero R d
  have hP0 : g (UnitInterval.add_d R x 0) * h (UnitInterval.add_d R x 0) = g x * h x := by
    simp [UnitInterval.add_d]
  rw [hP0]
  calc
    g (UnitInterval.add_d R x d) * h (UnitInterval.add_d R x d)
        = (g x + sderiv_I g x * (d : R)) * (h x + sderiv_I h x * (d : R)) := by rw [hg, hh]
    _ = g x * h x + (sderiv_I g x * h x + g x * sderiv_I h x) * (d : R)
          + sderiv_I g x * sderiv_I h x * ((d : R) * (d : R)) := by ring
    _ = g x * h x + (sderiv_I g x * h x + g x * sderiv_I h x) * (d : R) := by
            rw [hd]
            ring

/-- **仿射链式法则**：$(\lambda t.\, f(a + t(b-a)))' = (b-a) \cdot f'(a + t(b-a))$
（区间上对仿射复合求导；$f'$ 是 $R$ 上的导数 `sderiv f`）。 -/
lemma sderiv_I_affine {R : Type u} [IsIntegration R] (f : R → R) (a b : R)
    (x : UnitInterval R) :
    sderiv_I (fun t : UnitInterval R ↦ f (a + (t : R) * (b - a))) x
      = (b - a) * sderiv f (a + (x : R) * (b - a)) := by
  unfold sderiv_I
  symm
  apply (IsKockLawvere_one.isKockLawvere_one
    (fun d : D R ↦ f (a + ((UnitInterval.add_d R x d : UnitInterval R) : R) * (b - a)))).2.2
      ((b - a) * sderiv f (a + (x : R) * (b - a)))
  intro d
  let y : R := a + (x : R) * (b - a)
  have hinf_mem : ((d : R) * (b - a)) * ((d : R) * (b - a)) = 0 := by
    calc
      ((d : R) * (b - a)) * ((d : R) * (b - a)) = (d : R) * (d : R) * (b - a) * (b - a) := by ring
      _ = 0 := by rw [D.mul_eq_zero R d]; simp
  let inf : D R := D.ofMul R ((d : R) * (b - a)) hinf_mem
  have hspec := sderiv_spec f y inf
  have hadd : ((UnitInterval.add_d R x d : UnitInterval R) : R) = (x : R) + (d : R) := by
    simp [UnitInterval.add_d]
  have hadd0 : ((UnitInterval.add_d R x 0 : UnitInterval R) : R) = (x : R) := by
    simp [UnitInterval.add_d]
  rw [hadd, hadd0]
  have hmain : f (a + (((x : R) + (d : R)) * (b - a))) = f y + (b - a) * sderiv f y * (d : R) := by
    have heq1 : a + (((x : R) + (d : R)) * (b - a)) = y + (inf : R) := by
      dsimp [y, inf]
      ring
    rw [heq1]
    rw [hspec]
    dsimp [inf]
    ring
  exact hmain

/-- 恒等函数（限制在区间上）的导数：$(\lambda x.\, x)' = 1$。 -/
lemma sderiv_I_id {R : Type u} [IsIntegration R] (x : UnitInterval R) :
    sderiv_I (fun t : UnitInterval R ↦ (t : R)) x = 1 := by
  unfold sderiv_I
  change (IsKockLawvere_one.isKockLawvere_one
    (fun d : D R ↦ (x : R) + (d : R))).1 = 1
  exact sderiv_id (x : R)

/-- 平方函数的导数：$(\lambda x.\, x^2)' = 2x$。 -/
lemma sderiv_I_sq {R : Type u} [IsIntegration R] (x : UnitInterval R) :
    sderiv_I (fun t : UnitInterval R ↦ (t : R) * (t : R)) x = 2 * (x : R) := by
  unfold sderiv_I
  change (IsKockLawvere_one.isKockLawvere_one
    (fun d : D R ↦ ((x : R) + (d : R)) * ((x : R) + (d : R)))).1 = 2 * (x : R)
  exact sderiv_pow_two (x : R)

/-- 线性函数的区间导数：$(\lambda x.\, c \cdot x)' = c$。 -/
lemma sderiv_I_const_mul {R : Type u} [IsIntegration R]
    (c : R) (x : UnitInterval R) :
    sderiv_I (fun t : UnitInterval R ↦ c * (t : R)) x = c := by
  calc
    sderiv_I (fun t : UnitInterval R ↦ c * (t : R)) x
        = c * sderiv_I (fun t : UnitInterval R ↦ (t : R)) x :=
            sderiv_I_smul (c := c) (fun t : UnitInterval R ↦ (t : R)) (x := x)
    _ = c * 1 := by rw [sderiv_I_id]
    _ = c := by ring

/-! ## 原函数 -/

/-- **原函数**（初值为 0）：`primitive f` 是满足 $g(0) = 0$ 且 $g' = f$ 的唯一函数。 -/
def primitive {R : Type u} [IsIntegration R] (f : UnitInterval R → R) : UnitInterval R → R :=
  (IsIntegration.integration f).1

/-- 原函数在 0 处取值为 0：$\mathrm{primitive}\,f\,0 = 0$。 -/
theorem primitive_zero {R : Type u} [IsIntegration R] (f : UnitInterval R → R) :
    primitive f 0 = 0 :=
  (IsIntegration.integration f).2.1.1

/-- 原函数的导数等于被积函数：$(\mathrm{primitive}\,f)' = f$。 -/
theorem sderiv_primitive {R : Type u} [IsIntegration R] (f : UnitInterval R → R)
    (x : UnitInterval R) :
    sderiv_I (primitive f) x = f x := by
  unfold sderiv_I
  exact (IsIntegration.integration f).2.1.2 x

/-- **原函数的唯一性**：若 $g(0) = 0$ 且 $g' = f$，则 $g = \mathrm{primitive}\,f$。 -/
theorem primitive_unique {R : Type u} [IsIntegration R] (f g : UnitInterval R → R)
    (h0 : g 0 = 0) (hderiv : ∀ x : UnitInterval R, sderiv_I g x = f x) :
    g = primitive f := by
  change g = (IsIntegration.integration f).1
  exact (IsIntegration.integration f).2.2 g ⟨h0, by
    intro x
    unfold sderiv_I at hderiv
    exact hderiv x⟩

/-! ## 原函数的运算律 -/

/-- 和的导数（配合原函数）：$(\mathrm{primitive}\,f + \mathrm{primitive}\,g)' = f + g$。 -/
lemma sderiv_primitive_add {R : Type u} [IsIntegration R] (f g : UnitInterval R → R)
    (x : UnitInterval R) :
    sderiv_I (fun t ↦ primitive f t + primitive g t) x = f x + g x := by
  calc
    sderiv_I (fun t ↦ primitive f t + primitive g t) x
        = sderiv_I (primitive f) x + sderiv_I (primitive g) x :=
            sderiv_I_add (g := primitive f) (h := primitive g) (x := x)
    _ = f x + g x := by rw [sderiv_primitive f x, sderiv_primitive g x]

/-- 原函数对被积函数求和的线性性：
$\mathrm{primitive}\,(f + g) = \mathrm{primitive}\,f + \mathrm{primitive}\,g$。 -/
theorem primitive_add {R : Type u} [IsIntegration R] (f g : UnitInterval R → R) :
    primitive (fun x ↦ f x + g x) = fun x ↦ primitive f x + primitive g x := by
  symm
  exact primitive_unique (fun x ↦ f x + g x) (fun x ↦ primitive f x + primitive g x)
    (by simp [primitive_zero]) (by intro x; exact sderiv_primitive_add f g x)

/-- 取负的导数（配合原函数）：$(-\mathrm{primitive}\,f)' = -f$。 -/
lemma sderiv_primitive_neg {R : Type u} [IsIntegration R] (f : UnitInterval R → R)
    (x : UnitInterval R) :
    sderiv_I (fun t ↦ -primitive f t) x = -f x := by
  calc
    sderiv_I (fun t ↦ -primitive f t) x
        = -sderiv_I (primitive f) x := sderiv_I_neg (g := primitive f) (x := x)
    _ = -f x := by rw [sderiv_primitive f x]

/-- 原函数对被积函数取负：$\mathrm{primitive}\,(-f) = -\mathrm{primitive}\,f$。 -/
theorem primitive_neg {R : Type u} [IsIntegration R] (f : UnitInterval R → R) :
    primitive (fun x ↦ -f x) = fun x ↦ -primitive f x := by
  symm
  exact primitive_unique (fun x ↦ -f x) (fun x ↦ -primitive f x)
    (by simp [primitive_zero]) (by intro x; exact sderiv_primitive_neg f x)

/-- 差的导数（配合原函数）：$(\mathrm{primitive}\,f - \mathrm{primitive}\,g)' = f - g$。 -/
lemma sderiv_primitive_sub {R : Type u} [IsIntegration R] (f g : UnitInterval R → R)
    (x : UnitInterval R) :
    sderiv_I (fun t ↦ primitive f t - primitive g t) x = f x - g x := by
  calc
    sderiv_I (fun t ↦ primitive f t - primitive g t) x
        = sderiv_I (primitive f) x - sderiv_I (primitive g) x :=
            sderiv_I_sub (g := primitive f) (h := primitive g) (x := x)
    _ = f x - g x := by rw [sderiv_primitive f x, sderiv_primitive g x]

/-- 原函数对被积函数作差：$\mathrm{primitive}\,(f - g) = \mathrm{primitive}\,f - \mathrm{primitive}\,g$。 -/
theorem primitive_sub {R : Type u} [IsIntegration R] (f g : UnitInterval R → R) :
    primitive (fun x ↦ f x - g x) = fun x ↦ primitive f x - primitive g x := by
  symm
  exact primitive_unique (fun x ↦ f x - g x) (fun x ↦ primitive f x - primitive g x)
    (by simp [primitive_zero]) (by intro x; exact sderiv_primitive_sub f g x)

/-- 数乘的导数（配合原函数）：$(c \cdot \mathrm{primitive}\,f)' = c \cdot f$。 -/
lemma sderiv_primitive_smul {R : Type u} [IsIntegration R] (c : R) (f : UnitInterval R → R)
    (x : UnitInterval R) :
    sderiv_I (fun t ↦ c * primitive f t) x = c * f x := by
  calc
    sderiv_I (fun t ↦ c * primitive f t) x
        = c * sderiv_I (primitive f) x := sderiv_I_smul (c := c) (g := primitive f) (x := x)
    _ = c * f x := by rw [sderiv_primitive f x]

/-- 原函数的数乘：$\mathrm{primitive}\,(c \cdot f) = c \cdot \mathrm{primitive}\,f$。 -/
theorem primitive_smul {R : Type u} [IsIntegration R] (c : R) (f : UnitInterval R → R) :
    primitive (fun x ↦ c * f x) = fun x ↦ c * primitive f x := by
  symm
  exact primitive_unique (fun x ↦ c * f x) (fun x ↦ c * primitive f x)
    (by simp [primitive_zero]) (by intro x; exact sderiv_primitive_smul c f x)

/-- 常函数的原函数：$\mathrm{primitive}\,(\lambda x.\, c)\,x = c \cdot x$。 -/
theorem primitive_const {R : Type u} [IsIntegration R] (c : R) (x : UnitInterval R) :
    primitive (fun _ : UnitInterval R ↦ c) x = c * (x : R) := by
  have h : (fun t : UnitInterval R ↦ c * (t : R)) = primitive (fun _ : UnitInterval R ↦ c) := by
    exact primitive_unique (fun _ : UnitInterval R ↦ c) (fun t : UnitInterval R ↦ c * (t : R))
      (by simp) (by intro t; exact sderiv_I_const_mul c t)
  exact (congrFun h x).symm

/-! ## 定积分 -/

/-- **定积分**：$\int_a^b f = \mathrm{primitive}\,f\,b - \mathrm{primitive}\,f\,a$
（$a, b \in I = [0,1]$）。 -/
def integral {R : Type u} [IsIntegration R] (f : UnitInterval R → R)
    (a b : UnitInterval R) : R :=
  primitive f b - primitive f a

/-- 从 0 起的积分就是原函数：$\int_0^t f = \mathrm{primitive}\,f\,t$。 -/
theorem integral_zero_left {R : Type u} [IsIntegration R] (f : UnitInterval R → R)
    (t : UnitInterval R) :
    integral f 0 t = primitive f t := by
  unfold integral
  simp [primitive_zero]

/-- **微积分基本定理**：$\frac{d}{dx}\int_0^x f = f(x)$（$x \in I$）。 -/
theorem sderiv_integral {R : Type u} [IsIntegration R] (f : UnitInterval R → R)
    (x : UnitInterval R) :
    sderiv_I (fun t ↦ integral f 0 t) x = f x := by
  have h : (fun t : UnitInterval R ↦ integral f 0 t) = primitive f := by
    funext t
    unfold integral
    simp [primitive_zero]
  rw [h]
  exact sderiv_primitive f x

/-- 退化积分：$\int_a^a f = 0$。 -/
theorem integral_refl {R : Type u} [IsIntegration R] (f : UnitInterval R → R)
    (a : UnitInterval R) :
    integral f a a = 0 := by
  unfold integral
  ring

/-- 区间可加性：$\int_a^b f + \int_b^c f = \int_a^c f$。 -/
theorem integral_add_interval {R : Type u} [IsIntegration R] (f : UnitInterval R → R)
    (a b c : UnitInterval R) :
    integral f a b + integral f b c = integral f a c := by
  unfold integral
  ring

/-- 上下限交换：$\int_a^b f + \int_b^a f = 0$。 -/
theorem integral_swap {R : Type u} [IsIntegration R] (f : UnitInterval R → R)
    (a b : UnitInterval R) :
    integral f a b + integral f b a = 0 := by
  unfold integral
  ring

/-- 上下限取负：$\int_b^a f = -\int_a^b f$。 -/
theorem integral_flip {R : Type u} [IsIntegration R] (f : UnitInterval R → R)
    (a b : UnitInterval R) :
    integral f b a = -integral f a b := by
  unfold integral
  ring

/-- 积分的加法性：$\int_a^b (f + g) = \int_a^b f + \int_a^b g$。 -/
theorem integral_add {R : Type u} [IsIntegration R] (f g : UnitInterval R → R)
    (a b : UnitInterval R) :
    integral (fun x ↦ f x + g x) a b = integral f a b + integral g a b := by
  unfold integral
  rw [primitive_add]
  ring

/-- 积分的取负：$\int_a^b (-f) = -\int_a^b f$。 -/
theorem integral_neg {R : Type u} [IsIntegration R] (f : UnitInterval R → R)
    (a b : UnitInterval R) :
    integral (fun x ↦ -f x) a b = -integral f a b := by
  unfold integral
  rw [primitive_neg]
  ring

/-- 积分的作差：$\int_a^b (f - g) = \int_a^b f - \int_a^b g$。 -/
theorem integral_sub {R : Type u} [IsIntegration R] (f g : UnitInterval R → R)
    (a b : UnitInterval R) :
    integral (fun x ↦ f x - g x) a b = integral f a b - integral g a b := by
  unfold integral
  rw [primitive_sub]
  ring

/-- 积分的数乘：$\int_a^b (c \cdot f) = c \cdot \int_a^b f$。 -/
theorem integral_smul {R : Type u} [IsIntegration R] (c : R) (f : UnitInterval R → R)
    (a b : UnitInterval R) :
    integral (fun x ↦ c * f x) a b = c * integral f a b := by
  unfold integral
  rw [primitive_smul]
  ring

/-- 常数函数的积分：$\int_a^b c = c \cdot (b - a)$。 -/
theorem integral_const {R : Type u} [IsIntegration R] (c : R) (a b : UnitInterval R) :
    integral (fun _ : UnitInterval R ↦ c) a b = c * ((b : R) - (a : R)) := by
  unfold integral
  rw [primitive_const, primitive_const]
  ring

/-- 零函数的积分：$\int_a^b 0 = 0$。 -/
theorem integral_zero_fn {R : Type u} [IsIntegration R] (a b : UnitInterval R) :
    integral (fun _ : UnitInterval R ↦ 0) a b = 0 := by
  unfold integral
  simp [primitive_const]

/-! ## 微积分基本定理与常值性 -/

/-- 零函数的原函数为零：$\mathrm{primitive}\,0\,x = 0$。 -/
theorem primitive_zero_fn {R : Type u} [IsIntegration R] (x : UnitInterval R) :
    primitive (fun _ : UnitInterval R ↦ 0) x = 0 := by
  have h : (fun _ : UnitInterval R ↦ 0) = primitive (fun _ : UnitInterval R ↦ 0) := by
    exact primitive_unique (fun _ : UnitInterval R ↦ 0) (fun _ : UnitInterval R ↦ 0)
      (by simp) (by intro x; simp [sderiv_I_const])
  exact (congrFun h x).symm

/-- **区间上的微积分基本定理**：$\int_u^v g' = g(v) - g(u)$
（$g : I \to R$，由原函数唯一性推出）。 -/
theorem integral_fundamental {R : Type u} [IsIntegration R] (g : UnitInterval R → R)
    (u v : UnitInterval R) :
    integral (sderiv_I g) u v = g v - g u := by
  have hprim : primitive (sderiv_I g) = fun t : UnitInterval R ↦ g t - g 0 := by
    symm
    exact primitive_unique (sderiv_I g) (fun t : UnitInterval R ↦ g t - g 0)
      (by simp) (by intro x; rw [sderiv_I_sub, sderiv_I_const]; ring)
  unfold integral
  rw [hprim]
  simp

/-- **$R$ 上导数为零的函数是常值**：若 $h' = 0$ 处处成立，则 $h$ 在任意两点
$a, b$ 处取值相同。由区间上原函数唯一性（沿连接 $a, b$ 的线段 $t \mapsto a + t(b-a)$）
推出。 -/
theorem const_of_sderiv_zero {R : Type u} [IsIntegration R] (h : R → R)
    (hderiv : ∀ x, sderiv h x = 0) (a b : R) :
    h a = h b := by
  have hgderiv : ∀ x : UnitInterval R,
      sderiv_I (fun t : UnitInterval R ↦ h (a + (t : R) * (b - a)) - h a) x = 0 := by
    intro x
    rw [sderiv_I_sub, sderiv_I_affine h a b x, hderiv, sderiv_I_const]
    ring
  have hg : (fun t : UnitInterval R ↦ h (a + (t : R) * (b - a)) - h a) =
      fun _ : UnitInterval R ↦ 0 := by
    have hg1 : (fun t : UnitInterval R ↦ h (a + (t : R) * (b - a)) - h a) =
        primitive (fun _ : UnitInterval R ↦ 0) := by
      exact primitive_unique (fun _ : UnitInterval R ↦ 0)
        (fun t : UnitInterval R ↦ h (a + (t : R) * (b - a)) - h a)
        (by simp) (by intro x; exact hgderiv x)
    funext t
    calc
      (fun t : UnitInterval R ↦ h (a + (t : R) * (b - a)) - h a) t =
          primitive (fun _ : UnitInterval R ↦ 0) t := congrFun hg1 t
      _ = 0 := primitive_zero_fn t
  have hb : h (a + ((1 : UnitInterval R) : R) * (b - a)) - h a = 0 :=
    congrFun hg (1 : UnitInterval R)
  have hseg : a + ((1 : UnitInterval R) : R) * (b - a) = b := by
    simp
  rw [hseg] at hb
  exact (sub_eq_zero.mp hb).symm

/-! ## R 上的定积分（由 $[0,1]$ 上的积分定义） -/

/-- **R 上的定积分**：用单位区间 $I = [0,1]$ 上的积分 `integral` 经参数化
$x = a + t(b-a)$ 的换元定义：
$$\int_a^b f(x)\,dx = (b - a) \int_0^1 f(a + t(b-a))\,dt,$$
其中右端的积分是区间积分 `integral`（对 $t \in [0,1]$）。 -/
def integralR {R : Type u} [IsIntegration R] (f : R → R) (a b : R) : R :=
  (b - a) * integral (fun t : UnitInterval R ↦ f (a + (t : R) * (b - a))) 0 1

/-- 退化积分：$\int_a^a f = 0$。 -/
theorem integralR_refl {R : Type u} [IsIntegration R] (f : R → R) (a : R) :
    integralR f a a = 0 := by
  unfold integralR
  ring

/-- 常数函数的积分：$\int_a^b c = c \cdot (b - a)$。 -/
theorem integralR_const {R : Type u} [IsIntegration R] (c a b : R) :
    integralR (fun _ : R ↦ c) a b = c * (b - a) := by
  unfold integralR
  change (b - a) * integral (fun _ : UnitInterval R ↦ c) 0 1 = c * (b - a)
  rw [integral_const]
  simp
  ring

/-- 零函数的积分：$\int_a^b 0 = 0$。 -/
theorem integralR_zero_fn {R : Type u} [IsIntegration R] (a b : R) :
    integralR (fun _ : R ↦ 0) a b = 0 := by
  unfold integralR
  simp [integral_zero_fn]

/-- 积分的加法性：$\int_a^b (f + g) = \int_a^b f + \int_a^b g$。 -/
theorem integralR_add {R : Type u} [IsIntegration R] (f g : R → R) (a b : R) :
    integralR (fun x ↦ f x + g x) a b = integralR f a b + integralR g a b := by
  unfold integralR
  change (b - a) * integral
      (fun t : UnitInterval R ↦ f (a + (t : R) * (b - a)) + g (a + (t : R) * (b - a))) 0 1
    = (b - a) * integral (fun t : UnitInterval R ↦ f (a + (t : R) * (b - a))) 0 1
      + (b - a) * integral (fun t : UnitInterval R ↦ g (a + (t : R) * (b - a))) 0 1
  rw [integral_add]
  ring

/-- 积分的取负：$\int_a^b (-f) = -\int_a^b f$。 -/
theorem integralR_neg {R : Type u} [IsIntegration R] (f : R → R) (a b : R) :
    integralR (fun x ↦ -f x) a b = -integralR f a b := by
  unfold integralR
  change (b - a) * integral (fun t : UnitInterval R ↦ -(f (a + (t : R) * (b - a)))) 0 1
    = -((b - a) * integral (fun t : UnitInterval R ↦ f (a + (t : R) * (b - a))) 0 1)
  rw [integral_neg]
  ring

/-- 积分的作差：$\int_a^b (f - g) = \int_a^b f - \int_a^b g$。 -/
theorem integralR_sub {R : Type u} [IsIntegration R] (f g : R → R) (a b : R) :
    integralR (fun x ↦ f x - g x) a b = integralR f a b - integralR g a b := by
  unfold integralR
  change (b - a) * integral
      (fun t : UnitInterval R ↦ f (a + (t : R) * (b - a)) - g (a + (t : R) * (b - a))) 0 1
    = (b - a) * integral (fun t : UnitInterval R ↦ f (a + (t : R) * (b - a))) 0 1
      - (b - a) * integral (fun t : UnitInterval R ↦ g (a + (t : R) * (b - a))) 0 1
  rw [integral_sub]
  ring

/-- 积分的数乘：$\int_a^b (c \cdot f) = c \cdot \int_a^b f$。 -/
theorem integralR_smul {R : Type u} [IsIntegration R] (c : R) (f : R → R) (a b : R) :
    integralR (fun x ↦ c * f x) a b = c * integralR f a b := by
  unfold integralR
  change (b - a) * integral (fun t : UnitInterval R ↦ c * f (a + (t : R) * (b - a))) 0 1
    = c * ((b - a) * integral (fun t : UnitInterval R ↦ f (a + (t : R) * (b - a))) 0 1)
  rw [integral_smul]
  ring

/-! ## $R$ 上定积分的区间可加性 -/

/-- **换元恒等式**（$R$ 上定积分的微积分基本定理所需的代数恒等式）：
$$\int_0^1 f(a+t(x-a))\,dt + (x-a)\int_0^1 t\, f'(a+t(x-a))\,dt = f(x).$$
由区间微积分基本定理应用于 $G(t) = t \cdot f(a+t(x-a))$（$G' = f(\cdot) + t(x-a)f'(\cdot)$）得到。 -/
lemma integral_fundamental_identity {R : Type u} [IsIntegration R] (f : R → R) (a x : R) :
    integral (fun t : UnitInterval R ↦ f (a + (t : R) * (x - a))) 0 1
      + (x - a) * integral (fun t : UnitInterval R ↦ (t : R) * sderiv f (a + (t : R) * (x - a))) 0 1
    = f x := by
  let G : UnitInterval R → R := fun t ↦ (t : R) * f (a + (t : R) * (x - a))
  have hG : ∀ t : UnitInterval R,
      sderiv_I G t = f (a + (t : R) * (x - a)) + (x - a) * ((t : R) * sderiv f (a + (t : R) * (x - a))) := by
    intro t
    unfold G
    rw [sderiv_I_mul, sderiv_I_id, sderiv_I_affine f a x t]
    ring
  have hsderivG : sderiv_I G =
      fun t : UnitInterval R ↦ f (a + (t : R) * (x - a)) + (x - a) * ((t : R) * sderiv f (a + (t : R) * (x - a))) := by
    funext t
    exact hG t
  have hF := integral_fundamental G (0 : UnitInterval R) (1 : UnitInterval R)
  have hGend : G (1 : UnitInterval R) - G (0 : UnitInterval R) = f x := by
    unfold G
    simp
  have hinteg : integral (sderiv_I G) 0 1
      = integral (fun t : UnitInterval R ↦ f (a + (t : R) * (x - a))) 0 1
        + (x - a) * integral (fun t : UnitInterval R ↦ (t : R) * sderiv f (a + (t : R) * (x - a))) 0 1 := by
    rw [hsderivG]
    rw [integral_add, integral_smul]
  calc
    integral (fun t : UnitInterval R ↦ f (a + (t : R) * (x - a))) 0 1
        + (x - a) * integral (fun t : UnitInterval R ↦ (t : R) * sderiv f (a + (t : R) * (x - a))) 0 1
        = integral (sderiv_I G) 0 1 := hinteg.symm
    _ = G (1 : UnitInterval R) - G (0 : UnitInterval R) := hF
    _ = f x := hGend

/-- **KL 步进**：$\int_a^{x+d} f = \int_a^x f + d \cdot f(x)$（$d \in D$）。
对参数化 $a + t(x+d-a)$ 的被积函数按 KL 展开、利用换元恒等式得到。 -/
lemma integralR_step {R : Type u} [IsIntegration R] (f : R → R) (a x : R) (d : D R) :
    integralR f a (x + (d : R)) = integralR f a x + (d : R) * f x := by
  unfold integralR
  have hd : (d : R) * (d : R) = 0 := D.mul_eq_zero R d
  have hpoint : ∀ t : UnitInterval R,
      f (a + (t : R) * ((x + (d : R)) - a))
        = f (a + (t : R) * (x - a)) + (d : R) * ((t : R) * sderiv f (a + (t : R) * (x - a))) := by
    intro t
    let hinft : D R := D.ofMul R ((t : R) * (d : R)) (by
      calc
        ((t : R) * (d : R)) * ((t : R) * (d : R)) = (t : R) * (t : R) * ((d : R) * (d : R)) := by ring
        _ = 0 := by rw [hd]; ring)
    have hspec := sderiv_spec f (a + (t : R) * (x - a)) hinft
    have heq : a + (t : R) * ((x + (d : R)) - a) = a + (t : R) * (x - a) + (hinft : R) := by
      dsimp [hinft]
      ring
    rw [heq, hspec]
    dsimp [hinft]
    ring
  have hK : integral (fun t : UnitInterval R ↦ f (a + (t : R) * ((x + (d : R)) - a))) 0 1
      = integral (fun t : UnitInterval R ↦ f (a + (t : R) * (x - a))) 0 1
        + (d : R) * integral (fun t : UnitInterval R ↦ (t : R) * sderiv f (a + (t : R) * (x - a))) 0 1 := by
    have hfun : (fun t : UnitInterval R ↦ f (a + (t : R) * ((x + (d : R)) - a)))
        = fun t : UnitInterval R ↦ f (a + (t : R) * (x - a)) + (d : R) * ((t : R) * sderiv f (a + (t : R) * (x - a))) := by
      funext t
      exact hpoint t
    rw [hfun, integral_add, integral_smul]
  rw [hK]
  have hstep : (x + (d : R) - a) *
      (integral (fun t : UnitInterval R ↦ f (a + (t : R) * (x - a))) 0 1
        + (d : R) * integral (fun t : UnitInterval R ↦ (t : R) * sderiv f (a + (t : R) * (x - a))) 0 1)
      = (x - a) * integral (fun t : UnitInterval R ↦ f (a + (t : R) * (x - a))) 0 1
        + (d : R) * f x := by
    have hid := integral_fundamental_identity f a x
    calc
      (x + (d : R) - a) *
          (integral (fun t : UnitInterval R ↦ f (a + (t : R) * (x - a))) 0 1
            + (d : R) * integral (fun t : UnitInterval R ↦ (t : R) * sderiv f (a + (t : R) * (x - a))) 0 1)
          = (x - a) * integral (fun t : UnitInterval R ↦ f (a + (t : R) * (x - a))) 0 1
            + (x - a) * (d : R) * integral (fun t : UnitInterval R ↦ (t : R) * sderiv f (a + (t : R) * (x - a))) 0 1
            + (d : R) * integral (fun t : UnitInterval R ↦ f (a + (t : R) * (x - a))) 0 1
            + (d : R) * (d : R) * integral (fun t : UnitInterval R ↦ (t : R) * sderiv f (a + (t : R) * (x - a))) 0 1 := by ring
      _ = (x - a) * integral (fun t : UnitInterval R ↦ f (a + (t : R) * (x - a))) 0 1
          + (d : R) * (integral (fun t : UnitInterval R ↦ f (a + (t : R) * (x - a))) 0 1
              + (x - a) * integral (fun t : UnitInterval R ↦ (t : R) * sderiv f (a + (t : R) * (x - a))) 0 1)
          + (d : R) * (d : R) * integral (fun t : UnitInterval R ↦ (t : R) * sderiv f (a + (t : R) * (x - a))) 0 1 := by ring
      _ = (x - a) * integral (fun t : UnitInterval R ↦ f (a + (t : R) * (x - a))) 0 1
          + (d : R) * (integral (fun t : UnitInterval R ↦ f (a + (t : R) * (x - a))) 0 1
              + (x - a) * integral (fun t : UnitInterval R ↦ (t : R) * sderiv f (a + (t : R) * (x - a))) 0 1) := by
              rw [show (d : R) * (d : R) = 0 from hd]
              ring
      _ = (x - a) * integral (fun t : UnitInterval R ↦ f (a + (t : R) * (x - a))) 0 1
          + (d : R) * f x := by
              rw [← hid]
  exact hstep

/-- **$R$ 上定积分的微积分基本定理**：$\frac{d}{dx}\int_a^x f = f(x)$。 -/
theorem sderiv_integralR {R : Type u} [IsIntegration R] (f : R → R) (a x : R) :
    sderiv (fun x : R ↦ integralR f a x) x = f x := by
  symm
  apply (IsKockLawvere_one.isKockLawvere_one (fun d : D R ↦ integralR f a (x + (d : R)))).2.2 (f x)
  intro d
  calc
    integralR f a (x + (d : R)) = integralR f a x + (d : R) * f x := integralR_step f a x d
    _ = integralR f a x + f x * (d : R) := by ring
    _ = integralR f a (x + (0 : D R)) + f x * (d : R) := by simp

/-- **$R$ 上定积分的区间可加性**：$\int_a^b f + \int_b^c f = \int_a^c f$。 -/
theorem integralR_add_interval {R : Type u} [IsIntegration R] (f : R → R) (a b c : R) :
    integralR f a b + integralR f b c = integralR f a c := by
  have hright : ∀ x : R, sderiv (fun x : R ↦ integralR f a x - integralR f b x) x = 0 := by
    intro x
    rw [sderiv_sub, sderiv_integralR f a x, sderiv_integralR f b x]
    ring
  have hc := const_of_sderiv_zero (fun x : R ↦ integralR f a x - integralR f b x) hright b c
  have hc0 : integralR f a b = integralR f a c - integralR f b c := by
    simpa [integralR_refl] using hc
  calc
    integralR f a b + integralR f b c = (integralR f a c - integralR f b c) + integralR f b c := by rw [hc0]
    _ = integralR f a c := by ring

/-! ## 积分顺序交换（Fubini） -/

/-- **积分号下求导**：$\frac{d}{dt}\int_0^1 G(s,t)\,ds = \int_0^1 \frac{\partial G}{\partial t}(s,t)\,ds$
（$G : I \to I \to R$，$\frac{\partial G}{\partial t}(s,t)$ 是固定 $s$ 时 $t \mapsto G(s,t)$
的区间导数 `sderiv_I`）。逐点用 KL 展开 $G(s, t+d)$ 后由积分线性性得到。 -/
lemma sderiv_I_integral {R : Type u} [IsIntegration R]
    (G : UnitInterval R → UnitInterval R → R) (t : UnitInterval R) :
    sderiv_I (fun t ↦ integral (fun s : UnitInterval R ↦ G s t) 0 1) t
      = integral (fun s : UnitInterval R ↦ sderiv_I (fun t : UnitInterval R ↦ G s t) t) 0 1 := by
  symm
  apply (IsKockLawvere_one.isKockLawvere_one
    (fun d : D R ↦ integral (fun s : UnitInterval R ↦ G s (UnitInterval.add_d R t d)) 0 1)).2.2
      (integral (fun s : UnitInterval R ↦ sderiv_I (fun t : UnitInterval R ↦ G s t) t) 0 1)
  intro d
  have hpoint : ∀ s : UnitInterval R,
      G s (UnitInterval.add_d R t d)
        = G s t + (d : R) * sderiv_I (fun t : UnitInterval R ↦ G s t) t := by
    intro s
    have h := sderiv_I_spec (fun t : UnitInterval R ↦ G s t) t d
    rw [h]
    ring
  have hP0 : integral (fun s : UnitInterval R ↦ G s (UnitInterval.add_d R t 0)) 0 1
      = integral (fun s : UnitInterval R ↦ G s t) 0 1 := by
    congr 1
    funext s
    simp [UnitInterval.add_d]
  rw [hP0]
  have hfun : (fun s : UnitInterval R ↦ G s (UnitInterval.add_d R t d))
      = fun s : UnitInterval R ↦ G s t + (d : R) * sderiv_I (fun t : UnitInterval R ↦ G s t) t := by
    funext s
    exact hpoint s
  rw [hfun, integral_add, integral_smul]
  ring

/-- **积分顺序交换（Fubini）**：对 $F : I \to I \to R$，
$$\int_0^1 \left(\int_0^1 F(s,t)\,dt\right) ds = \int_0^1 \left(\int_0^1 F(s,t)\,ds\right) dt.$$

考虑差值函数 $D(t) = \int_0^1\left(\int_0^t F(s,u)\,du\right)ds - \int_0^t\left(\int_0^1 F(s,u)\,ds\right)du$；
其导数由积分号下求导（`sderiv_I_integral`）与区间 FTC（`sderiv_integral`）均为
$\int_0^1 F(s,t)\,ds$，故 $D' = 0$ 且 $D(0) = 0$，由原函数唯一性 $D \equiv 0$。 -/
theorem integral_swap_order {R : Type u} [IsIntegration R]
    (F : UnitInterval R → UnitInterval R → R) :
    integral (fun s : UnitInterval R ↦ integral (fun t : UnitInterval R ↦ F s t) 0 1) 0 1
      = integral (fun t : UnitInterval R ↦ integral (fun s : UnitInterval R ↦ F s t) 0 1) 0 1 := by
  let D : UnitInterval R → R :=
    fun t ↦ integral (fun s : UnitInterval R ↦ integral (fun u : UnitInterval R ↦ F s u) 0 t) 0 1
        - integral (fun u : UnitInterval R ↦ integral (fun s : UnitInterval R ↦ F s u) 0 1) 0 t
  have hD0 : D (0 : UnitInterval R) = 0 := by
    unfold D
    simp [integral_refl, integral_zero_fn]
  have hDderiv : ∀ t : UnitInterval R, sderiv_I D t = 0 := by
    intro t
    unfold D
    rw [sderiv_I_sub]
    have hterm1 : sderiv_I
        (fun t : UnitInterval R ↦ integral (fun s : UnitInterval R ↦ integral (fun u : UnitInterval R ↦ F s u) 0 t) 0 1) t
        = integral (fun s : UnitInterval R ↦ F s t) 0 1 := by
      calc
        sderiv_I (fun t : UnitInterval R ↦ integral (fun s : UnitInterval R ↦ integral (fun u : UnitInterval R ↦ F s u) 0 t) 0 1) t
            = integral (fun s : UnitInterval R ↦ sderiv_I (fun t : UnitInterval R ↦ integral (fun u : UnitInterval R ↦ F s u) 0 t) t) 0 1 :=
                sderiv_I_integral (fun s : UnitInterval R ↦ fun t : UnitInterval R ↦ integral (fun u : UnitInterval R ↦ F s u) 0 t) t
        _ = integral (fun s : UnitInterval R ↦ F s t) 0 1 := by
                apply congrArg (fun h : UnitInterval R → R ↦ integral h 0 1)
                funext s
                exact sderiv_integral (fun u : UnitInterval R ↦ F s u) t
    have hterm2 : sderiv_I
        (fun t : UnitInterval R ↦ integral (fun u : UnitInterval R ↦ integral (fun s : UnitInterval R ↦ F s u) 0 1) 0 t) t
        = integral (fun s : UnitInterval R ↦ F s t) 0 1 :=
      sderiv_integral (fun u : UnitInterval R ↦ integral (fun s : UnitInterval R ↦ F s u) 0 1) t
    rw [hterm1, hterm2]
    ring
  have hDconst : D = fun _ : UnitInterval R ↦ 0 := by
    have hDm : (fun t : UnitInterval R ↦ D t - D (0 : UnitInterval R)) = primitive (fun _ : UnitInterval R ↦ 0) := by
      exact primitive_unique (fun _ : UnitInterval R ↦ 0) (fun t : UnitInterval R ↦ D t - D (0 : UnitInterval R))
        (by simp) (by intro t; rw [sderiv_I_sub, hDderiv t, sderiv_I_const]; ring)
    funext t
    have ht := congrFun hDm t
    have ht' : D t - D (0 : UnitInterval R) = 0 := by
      rw [ht]
      exact primitive_zero_fn t
    rw [hD0] at ht'
    exact sub_eq_zero.mp ht'
  have h1 : D (1 : UnitInterval R) = 0 := congrFun hDconst (1 : UnitInterval R)
  unfold D at h1
  exact sub_eq_zero.mp h1

/-! ## 恒等函数的积分（需要 $\mathbb{Q}$-代数） -/

/-- $\frac{1}{2} t^2$ 的区间导数：$(\frac{1}{2} t^2)' = t$
（$\frac{1}{2} = \mathrm{invFactorial}\ R\ 2$，$R$ 是 $\mathbb{Q}$-代数）。 -/
lemma sderiv_primitive_id_aux {R : Type u} [IsIntegration R] [Algebra SDG.Rational.Q R]
    (x : UnitInterval R) :
    sderiv_I (fun t : UnitInterval R ↦ invFactorial R 2 * ((t : R) * (t : R))) x = (x : R) := by
  calc
    sderiv_I (fun t : UnitInterval R ↦ invFactorial R 2 * ((t : R) * (t : R))) x
        = invFactorial R 2 * sderiv_I (fun t : UnitInterval R ↦ (t : R) * (t : R)) x :=
            sderiv_I_smul (c := invFactorial R 2) (fun t : UnitInterval R ↦ (t : R) * (t : R)) (x := x)
    _ = invFactorial R 2 * (2 * (x : R)) := by rw [sderiv_I_sq]
    _ = (x : R) := by
            have hf : invFactorial R 2 * (2 : R) = 1 := by
              have hf' := invFactorial_mul R 2
              have h2 : (Nat.factorial 2 : R) = (2 : R) := by norm_num
              rw [h2] at hf'
              exact hf'
            calc
              invFactorial R 2 * (2 * (x : R)) = (invFactorial R 2 * (2 : R)) * (x : R) := by ring
              _ = 1 * (x : R) := by rw [hf]
              _ = (x : R) := by ring

/-- 恒等函数的原函数：$\mathrm{primitive}\,(\lambda x.\, x)\,x = \frac{1}{2} x^2$
（$\frac{1}{2} = \mathrm{invFactorial}\ R\ 2$）。 -/
theorem primitive_id {R : Type u} [IsIntegration R] [Algebra SDG.Rational.Q R]
    (x : UnitInterval R) :
    primitive (fun t : UnitInterval R ↦ (t : R)) x = invFactorial R 2 * (x : R) * (x : R) := by
  have h : (fun t : UnitInterval R ↦ invFactorial R 2 * ((t : R) * (t : R))) =
      primitive (fun t : UnitInterval R ↦ (t : R)) := by
    exact primitive_unique (fun t : UnitInterval R ↦ (t : R))
      (fun t : UnitInterval R ↦ invFactorial R 2 * ((t : R) * (t : R)))
      (by simp) (by intro t; exact sderiv_primitive_id_aux t)
  calc
    primitive (fun t : UnitInterval R ↦ (t : R)) x
        = invFactorial R 2 * ((x : R) * (x : R)) := (congrFun h x).symm
    _ = invFactorial R 2 * (x : R) * (x : R) := by ring

end SDG.Integration
