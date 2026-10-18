import AngularPrimitiveContinuation
import AngularPrimitiveReduction

/-! Continued angular L-functions for the full unit-compatible family,
including imprimitive finite characters. All functions are constructed from
the actual primitive theta and the exact finite Euler deletion product. -/

noncomputable section
open scoped Classical Topology

namespace OAI.SevenEighths.Angular.FamilyContinuation

open PrimitiveReduction

/-- Primitive continuation selected by OAI-003's actual conductor presentation. -/
def primitiveL (χ : AngularCharacter) : ℂ → ℂ := by
  letI : NeZero (generator χ) := ⟨generator_ne_zero χ⟩
  exact ThetaContinuation.LFunction (generator χ) (primitive χ) rfl
    (primitive_isPrimitive χ)

/-- The physical angular L-function, with its original source-modulus mask. -/
def LFunction (χ : AngularCharacter) (s : ℂ) : ℂ := primitiveL χ s * factors χ s

theorem primitiveL_eq_series (χ : AngularCharacter) (s : ℂ) (hs : 1 < s.re) :
    primitiveL χ s = (primitive χ).series s := by
  letI : NeZero (generator χ) := ⟨generator_ne_zero χ⟩
  exact ThetaContinuation.LFunction_eq_series (generator χ) (primitive χ) rfl
    (primitive_isPrimitive χ) s hs

theorem LFunction_eq_series (χ : AngularCharacter) (s : ℂ) (hs : 1 < s.re) :
    LFunction χ s = χ.series s := by
  rw [LFunction, primitiveL_eq_series χ s hs, series_eq_primitive_mul_factors χ s hs]

theorem primitiveL_differentiable (χ : AngularCharacter) (hk : χ.k ≠ 0) :
    Differentiable ℂ (primitiveL χ) := by
  letI : NeZero (generator χ) := ⟨generator_ne_zero χ⟩
  exact ThetaContinuation.LFunction_differentiable (generator χ) (primitive χ) rfl
    (primitive_isPrimitive χ) hk

theorem LFunction_differentiable (χ : AngularCharacter) (hk : χ.k ≠ 0) :
    Differentiable ℂ (LFunction χ) :=
  (primitiveL_differentiable χ hk).mul (factors_differentiable χ)

theorem primitiveL_differentiableAt (χ : AngularCharacter) (s : ℂ)
    (hs : 0 < s.re) (h1 : s ≠ 1) : DifferentiableAt ℂ (primitiveL χ) s := by
  letI : NeZero (generator χ) := ⟨generator_ne_zero χ⟩
  exact ThetaContinuation.LFunction_differentiableAt (generator χ) (primitive χ) rfl
    (primitive_isPrimitive χ) s hs h1

theorem LFunction_differentiableAt (χ : AngularCharacter) (s : ℂ)
    (hs : 0 < s.re) (h1 : s ≠ 1) : DifferentiableAt ℂ (LFunction χ) s :=
  (primitiveL_differentiableAt χ s hs h1).mul (factors_differentiable χ s)

theorem LFunction_ne_zero (χ : AngularCharacter) (s : ℂ) (hs : 1 < s.re) :
    LFunction χ s ≠ 0 := by
  rw [LFunction_eq_series χ s hs]
  exact χ.series_ne_zero s hs

/-- Exact algebraic zero transfer throughout Re(s)>0. At a type-zero pole this
is only an equality of totalized values. Analytic zero transfer uses the
regularity theorems above, excluding s=1 unless the type is nonzero.
This reduces the zero-free problem and does not prove a new strip. -/
theorem LFunction_eq_zero_iff (χ : AngularCharacter) (s : ℂ) (hs : 0 < s.re) :
    LFunction χ s = 0 ↔ primitiveL χ s = 0 := by
  rw [LFunction, mul_eq_zero]
  simp only [factors_ne_zero χ hs, or_false]

theorem LFunction_ne_zero_iff (χ : AngularCharacter) (s : ℂ) (hs : 0 < s.re) :
    LFunction χ s ≠ 0 ↔ primitiveL χ s ≠ 0 :=
  not_congr (LFunction_eq_zero_iff χ s hs)

end OAI.SevenEighths.Angular.FamilyContinuation
