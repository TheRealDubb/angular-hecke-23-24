import AngularNormTwist
import AngularFamilyContinuation
import AngularSeedNonvanishing

/-! Continuation of the actual norm-twisted ideal series. Type-zero exclusions
translate with the vertical shift; nonzero angular types remain entire. -/
noncomputable section
open scoped Classical Topology
open Complex
namespace OAI.SevenEighths.Angular.NormTwist

def LFunction (χ : AngularCharacter) (τ : ℝ) (s : ℂ) : ℂ :=
  FamilyContinuation.LFunction χ (s-(τ:ℂ)*I)

theorem shift_re (τ : ℝ) (s : ℂ) : (s-(τ:ℂ)*I).re = s.re := by simp

theorem shift_ne_one_iff (τ : ℝ) (s : ℂ) :
    s-(τ:ℂ)*I ≠ 1 ↔ s ≠ 1+(τ:ℂ)*I := by
  constructor
  · intro h he
    apply h
    rw [he,add_sub_cancel_right]
  · intro h he
    apply h
    linear_combination he

theorem LFunction_eq_series (χ : AngularCharacter) (τ : ℝ) (s : ℂ)
    (hs : 1 < s.re) : LFunction χ τ s = IdealEuler.series (twistedIdealHom χ τ) s := by
  rw [LFunction,FamilyContinuation.LFunction_eq_series χ _ (by simpa using hs),series_shift]

theorem LFunction_differentiable (χ : AngularCharacter) (τ : ℝ) (hk : χ.k ≠ 0) :
    Differentiable ℂ (LFunction χ τ) :=
  (FamilyContinuation.LFunction_differentiable χ hk).comp (differentiable_id.sub_const _)

theorem LFunction_differentiableAt (χ : AngularCharacter) (τ : ℝ) (s : ℂ)
    (hs : 0 < s.re) (hpole : χ.k = 0 → s ≠ 1+(τ:ℂ)*I) :
    DifferentiableAt ℂ (LFunction χ τ) s := by
  by_cases hk : χ.k = 0
  · exact (FamilyContinuation.LFunction_differentiableAt χ _ (by simpa using hs)
      ((shift_ne_one_iff τ s).mpr (hpole hk))).comp s (differentiableAt_id.sub_const _)
  · exact LFunction_differentiable χ τ hk s

theorem halfPlane_transport_iff (χ : AngularCharacter) (τ β : ℝ) :
    (∀ s : ℂ, β < s.re → (χ.k = 0 → s ≠ 1) → FamilyContinuation.LFunction χ s ≠ 0) ↔
    (∀ s : ℂ, β < s.re → (χ.k = 0 → s ≠ 1+(τ:ℂ)*I) → LFunction χ τ s ≠ 0) := by
  constructor
  · intro h s hs hpole
    exact h _ (by simpa using hs) (fun hk => (shift_ne_one_iff τ s).mpr (hpole hk))
  · intro h s hs hpole
    have hh := h (s+(τ:ℂ)*I) (by simpa using hs) (fun hk he =>
      hpole hk (add_right_cancel he))
    simpa only [LFunction,add_sub_cancel_right] using hh

theorem physical_seed_all_norm_twists (χ : AngularCharacter) (τ : ℝ) (s : ℂ)
    (hs : (23:ℝ)/24 < s.re) (hpole : χ.k = 0 → s ≠ 1+(τ:ℂ)*I) :
    LFunction χ τ s ≠ 0 := by
  apply (halfPlane_transport_iff χ τ ((23:ℝ)/24)).mp
    (OAI.CubicEisenstein.AngularSeedNonvanishing.physical_seed_all_types χ) s hs hpole

end OAI.SevenEighths.Angular.NormTwist
