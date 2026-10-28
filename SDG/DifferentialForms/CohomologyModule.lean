import SDG.DifferentialForms.Currents

/-!
# 同调的 R-模结构

`Hⁿ`（de Rham 侧，`deRhamCohomology`）与 `Hₙ`（电流侧，`currentHomology`）
的 `Module R` 结构——补齐 `AddCommGroup` 之上的数乘层（此前双侧商对象
只有加法交换群，smul 双线性因缺 Module 而搁置）。

路线：Mathlib 的 `ModuleCon`（模同余）商——`ModuleCon.Quotient` 的
`Module` instance 由 `fast_instance% Quotient.mk''_surjective.module`
现成提供；商对象类型经 `have` + `exact` 的项级 defeq 提升挂回既有定义
（`deRhamCohomology n := AddCon.Quotient (deRhamCon n)`，两者同为
`Quotient (…Setoid…)`，unification 不做 defeq 搜索故须手工桥）。

商层 smul 的语义 wrapper（`deRhamSMul`/`currentSMul`）与 instance 的
数乘 defeq（`rfl` 实证），类投影的 smul 展开沿 `Quotient.map` 的
mk-β + proof irrelevance 透明。收官应用：配对 `deRhamPairing` 的
R-双线性（两条 smul 相容）。

全部无选择公理。
-/

namespace SDG.DifferentialForms

section CohomologyModule

variable {R : Type u} [CommRing R] {X : Type u}

/-! ### de Rham 侧：`Module R Hⁿ` -/

/-- 上循环子模上的模同余：`deRhamCon` 的加法同余 + 数乘封闭
（差为上边缘 ⟹ 数乘差为上边缘，witness `r • w`）。 -/
def deRhamModuleCon (n : ℕ) :
    ModuleCon R (cocycles (R := R) (X := X) (n := n + 1)) where
  toAddCon := deRhamCon (R := R) (X := X) n
  smul := by
    rintro r a b h
    have h' : ((a : Cochain R X (n + 1)) - (b : Cochain R X (n + 1)) :
        Cochain R X (n + 1)) ∈ coboundaries (R := R) (X := X) n := h
    rw [mem_coboundaries] at h'
    obtain ⟨w, hw⟩ := h'
    show ((r • a - r • b : Cochain R X (n + 1)) : Cochain R X (n + 1))
      ∈ coboundaries (R := R) (X := X) n
    rw [mem_coboundaries]
    refine ⟨r • w, ?_⟩
    rw [← coboundaryLinear_apply, LinearMap.map_smul, coboundaryLinear_apply,
      ← smul_sub, hw]

/-- **`Hⁿ` 的 `Module R` 结构**：`ModuleCon` 商的现成 instance 经项级
defeq 提升挂回 `deRhamCohomology`（unification 不做 defeq 搜索，
`have` 内层可 elabor、`exact` 项级解包装——`AddCon.addCommGroup`
同款配方）。 -/
instance instModuleDeRhamCohomology (n : ℕ) :
    Module R (deRhamCohomology (R := R) (X := X) n) := by
  have h : Module R (ModuleCon.Quotient (S := R)
      (M := ↥(cocycles (R := R) (X := X) (n := n + 1)))
      (deRhamModuleCon (R := R) (X := X) n)) :=
    inferInstance
  exact h

/-- 商层数乘的语义 wrapper（与 instance 的数乘 defeq，见
`deRhamSMul_eq`）。 -/
def deRhamSMul (n : ℕ) (r : R) (x : deRhamCohomology (R := R) (X := X) n) :
    deRhamCohomology (R := R) (X := X) n :=
  Quotient.map
    (fun a : ↥(cocycles (R := R) (X := X) (n := n + 1)) =>
      (r • a : ↥(cocycles (R := R) (X := X) (n := n + 1))))
    (fun a b h => (deRhamModuleCon (R := R) (X := X) n).smul r h)
    x

/-- wrapper 与商层数乘逐点相等（rfl——instance 的 SMul 字段就是
`Quotient.map (r • ·)` 的同一形式）。 -/
theorem deRhamSMul_eq (n : ℕ) (r : R) (x : deRhamCohomology (R := R) (X := X) n) :
    deRhamSMul n r x = r • x := rfl

/-- 上循环对数乘封闭。 -/
theorem isCocycle_smul {n : ℕ} (r : R) {α : Cochain R X n} (hα : IsCocycle α) :
    IsCocycle (r • α) := by
  show coboundary (r • α) = 0
  rw [← coboundaryLinear_apply, LinearMap.map_smul, coboundaryLinear_apply,
    hα, smul_zero]

/-- **类投影的数乘展开**：`r • [α] = [r • α]`（`Quotient.map` 的
mk-β + proof irrelevance，rfl 透明）。 -/
theorem deRhamClass_smul {n : ℕ} (r : R) {α : Cochain R X (n + 1)}
    (hα : IsCocycle α) :
    r • deRhamClass (R := R) (X := X) hα
      = deRhamClass (R := R) (X := X) (isCocycle_smul r hα) := rfl

/-! ### 电流侧：`Module R Hₙ` -/

/-- 循环电流子模上的模同余：`currentCon` 的加法同余 + 数乘封闭
（差为边缘 ⟹ 数乘差为边缘，witness `r • S`）。 -/
def currentModuleCon (n : ℕ) :
    ModuleCon R (chainCycles (R := R) (X := X) (n := n)) where
  toAddCon := currentCon (R := R) (X := X) n
  smul := by
    rintro r a b h
    have h' : ((a : Current R X (n + 1)) - (b : Current R X (n + 1)) :
        Current R X (n + 1)) ∈ currentBoundariesAdd (R := R) (X := X) n := h
    obtain ⟨S, hS⟩ := h'
    refine ⟨r • S, ?_⟩
    show currentBoundary (r • S)
      = (r • (a : Current R X (n + 1)) : Current R X (n + 1))
        - (r • (b : Current R X (n + 1)) : Current R X (n + 1))
    rw [currentBoundary_smul, hS, smul_sub]

/-- **`Hₙ` 的 `Module R` 结构**（与 de Rham 侧对偶，同款 defeq 提升）。 -/
instance instModuleCurrentHomology (n : ℕ) :
    Module R (currentHomology (R := R) (X := X) n) := by
  have h : Module R (ModuleCon.Quotient (S := R)
      (M := ↥(chainCycles (R := R) (X := X) (n := n)))
      (currentModuleCon (R := R) (X := X) n)) :=
    inferInstance
  exact h

/-- 电流侧商层数乘的语义 wrapper。 -/
def currentSMul (n : ℕ) (r : R) (x : currentHomology (R := R) (X := X) n) :
    currentHomology (R := R) (X := X) n :=
  Quotient.map
    (fun a : ↥(chainCycles (R := R) (X := X) (n := n)) =>
      (r • a : ↥(chainCycles (R := R) (X := X) (n := n))))
    (fun a b h => (currentModuleCon (R := R) (X := X) n).smul r h)
    x

/-- wrapper 与电流侧商层数乘逐点相等（rfl）。 -/
theorem currentSMul_eq (n : ℕ) (r : R) (x : currentHomology (R := R) (X := X) n) :
    currentSMul n r x = r • x := rfl

/-- 循环电流对数乘封闭。 -/
theorem isChainCycle_smul {n : ℕ} (r : R) {T : Current R X (n + 1)}
    (hT : IsChainCycle T) : IsChainCycle (r • T) := by
  show currentBoundary (r • T) = 0
  rw [currentBoundary_smul, hT, smul_zero]

/-- **电流类投影的数乘展开**：`r • [T] = [r • T]`。 -/
theorem currentClass_smul {n : ℕ} (r : R) {T : Current R X (n + 1)}
    (hT : IsChainCycle T) :
    r • currentHomologyClass (R := R) (X := X) hT
      = currentHomologyClass (R := R) (X := X) (isChainCycle_smul r hT) := rfl

/-! ### 配对的 R-双线性收官 -/

/-- 类层配对对上同调类的数乘相容：`⟨[T], r•[c]⟩ = r•⟨[T],[c]⟩`
（`T` 线性）。 -/
theorem deRhamPairing_smul_right {n : ℕ} {T : Current R X (n + 1)}
    (hT : IsChainCycle T) {c : Cochain R X (n + 1)} (hc : IsCocycle c)
    (r : R) :
    deRhamPairing (R := R) (X := X) n (currentHomologyClass hT)
        (r • deRhamClass hc)
      = r • deRhamPairing (R := R) (X := X) n (currentHomologyClass hT)
          (deRhamClass hc) := by
  rw [deRhamClass_smul]
  calc deRhamPairing (R := R) (X := X) n (currentHomologyClass hT)
        (deRhamClass (isCocycle_smul r hc))
      = T (r • c) := rfl
    _ = r • T c := LinearMap.map_smul T r c
    _ = r • deRhamPairing (R := R) (X := X) n (currentHomologyClass hT)
          (deRhamClass hc) := rfl

/-- 类层配对对电流类的数乘相容：`⟨r•[T], [c]⟩ = r•⟨[T],[c]⟩`
（`Current = Cochain →ₗ R` 的数乘语义）。 -/
theorem deRhamPairing_smul_left {n : ℕ} {T : Current R X (n + 1)}
    (hT : IsChainCycle T) {c : Cochain R X (n + 1)} (hc : IsCocycle c)
    (r : R) :
    deRhamPairing (R := R) (X := X) n (r • currentHomologyClass hT)
        (deRhamClass hc)
      = r • deRhamPairing (R := R) (X := X) n (currentHomologyClass hT)
          (deRhamClass hc) := by
  rw [currentClass_smul]
  calc deRhamPairing (R := R) (X := X) n
        (currentHomologyClass (isChainCycle_smul r hT)) (deRhamClass hc)
      = (r • T) c := rfl
    _ = r • (T c) := LinearMap.smul_apply r T c
    _ = r • deRhamPairing (R := R) (X := X) n (currentHomologyClass hT)
          (deRhamClass hc) := rfl

end CohomologyModule

end SDG.DifferentialForms

#print axioms SDG.DifferentialForms.instModuleDeRhamCohomology
#print axioms SDG.DifferentialForms.instModuleCurrentHomology
#print axioms SDG.DifferentialForms.deRhamClass_smul
#print axioms SDG.DifferentialForms.currentClass_smul
#print axioms SDG.DifferentialForms.deRhamPairing_smul_left
#print axioms SDG.DifferentialForms.deRhamPairing_smul_right
