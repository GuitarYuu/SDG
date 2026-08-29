import SDG.DifferentialForms.Core

/-!
# SDG.DifferentialForms.Simplicial

单纯形面映射基础设施。

余面映射 `faceMap i : Fin n → Fin (n+1)` 用 `Fin.succAbove` 实现
（已审计无公理依赖），作为后续单纯形形式、外微分的面算子交错和
公式、Čech 上同调和 Stokes 定理的组合基础。
-/

universe u

namespace SDG.DifferentialForms

/-! ## 面映射 -/

/-- 余面映射 `δⁱ : Fin n → Fin (n+1)`：跳过位置 `i` 嵌入。 -/
def faceMap {n : ℕ} (i : Fin (n + 1)) : Fin n → Fin (n + 1) :=
  i.succAbove

lemma faceMap_apply {n : ℕ} (i : Fin (n + 1)) (k : Fin n) :
    faceMap i k = i.succAbove k := rfl

/-! ## 奇异单形上的面操作 -/

variable {X : Type u}

/-- 奇异单形的第 `i` 个面：`σ : Fin (n+1) → X` 删除第 `i` 个顶点。 -/
def face {n : ℕ} (σ : Fin (n + 1) → X) (i : Fin (n + 1)) : Fin n → X :=
  fun k ↦ σ (faceMap i k)

lemma face_apply {n : ℕ} (σ : Fin (n + 1) → X) (i : Fin (n + 1)) (k : Fin n) :
    face σ i k = σ (i.succAbove k) := rfl

/-! ## 面映射的基本性质 -/

/-- 面映射是单射（跳过一个位置的单调嵌入）。 -/
lemma faceMap_injective {n : ℕ} (i : Fin (n + 1)) :
    Function.Injective (faceMap i) := Fin.succAbove_right_injective

end SDG.DifferentialForms
