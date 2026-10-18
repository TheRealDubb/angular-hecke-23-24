import AngularAllTypeTransport
import OAI.NumberTheory.DirichletL.Hecke.FiniteDeletion

/-! Actual angular regularization on Re(s)>0. Type zero uses the already
identified finite Hecke function; nonzero types use the entire angular L-function. -/
noncomputable section
open scoped Classical Topology
namespace OAI.CubicEisenstein.AngularSeedRegularization
open SevenEighths SevenEighths.Angular

def regularizedL (χ : AngularCharacter) (s : ℂ) : ℂ :=
  if hk : χ.k = 0 then
    HeckeReciprocal.regularizedL (FiniteIdentification.toFinite χ hk) s
  else (s - 1) * FamilyContinuation.LFunction χ s

theorem regularizedL_analytic (χ : AngularCharacter) :
    AnalyticOnNhd ℂ (regularizedL χ) {s : ℂ | 0 < s.re} := by
  by_cases hk : χ.k = 0
  · have he : regularizedL χ =
        HeckeReciprocal.regularizedL (FiniteIdentification.toFinite χ hk) := by
      funext s
      simp only [regularizedL, dite_eq_left hk]
    rw [he]
    exact HeckeFiniteDeletion.regularizedL_analytic (FiniteIdentification.toFinite χ hk)
  · have he : regularizedL χ = fun s => (s - 1) * FamilyContinuation.LFunction χ s := by
      funext s
      simp only [regularizedL, dite_eq_right hk]
    rw [he]
    apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt 0)).mpr
    exact ((differentiable_id.sub_const (1 : ℂ)).mul
      (FamilyContinuation.LFunction_differentiable χ hk)).differentiableOn

theorem regularizedL_eq (χ : AngularCharacter) (s : ℂ) (h0 : s ≠ 0) (h1 : s ≠ 1) :
    regularizedL χ s = (s - 1) * FamilyContinuation.LFunction χ s := by
  by_cases hk : χ.k = 0
  · rw [regularizedL, dite_eq_left hk, HeckeReciprocal.regularizedL_eq _ h0 h1,
      FiniteIdentification.typeZero_LFunction χ hk s h0 h1]
  · simp only [regularizedL, dite_eq_right hk]

end OAI.CubicEisenstein.AngularSeedRegularization
