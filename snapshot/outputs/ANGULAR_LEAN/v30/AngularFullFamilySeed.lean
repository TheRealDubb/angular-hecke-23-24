import AngularTypeZeroEntire
import AngularNormTwistContinuation

noncomputable section
open scoped Classical Topology
open Complex
namespace OAI.SevenEighths.Angular.FullFamilySeed

theorem physical_seed (χ : AngularCharacter) (s : ℂ)
    (hs : (23:ℝ)/24 < s.re) (hpole : χ.k = 0 → χ.residue = 1 → s ≠ 1) :
    FamilyContinuation.LFunction χ s ≠ 0 := by
  by_cases hk : χ.k = 0
  · by_cases hχ : χ.residue = 1
    · exact OAI.CubicEisenstein.AngularSeedNonvanishing.physical_seed_all_types χ s hs
        (fun _ => hpole hk hχ)
    · by_cases h1 : s = 1
      · subst s
        exact TypeZeroEntire.LFunction_one_ne_zero χ hk hχ
      · exact OAI.CubicEisenstein.AngularSeedNonvanishing.physical_seed_all_types χ s hs (fun _ => h1)
  · exact OAI.CubicEisenstein.AngularSeedNonvanishing.physical_seed_all_types χ s hs
      (fun he => (hk he).elim)

theorem physical_seed_norm_twist (χ : AngularCharacter) (τ : ℝ) (s : ℂ)
    (hs : (23:ℝ)/24 < s.re)
    (hpole : χ.k = 0 → χ.residue = 1 → s ≠ 1+(τ:ℂ)*I) :
    NormTwist.LFunction χ τ s ≠ 0 := by
  exact physical_seed χ _ (by simpa using hs)
    (fun hk hχ => (NormTwist.shift_ne_one_iff τ s).mpr (hpole hk hχ))

theorem nonprincipal_entire (χ : AngularCharacter)
    (hnonprincipal : χ.k ≠ 0 ∨ χ.residue ≠ 1) :
    Differentiable ℂ (FamilyContinuation.LFunction χ) := by
  by_cases hk : χ.k = 0
  · exact TypeZeroEntire.LFunction_entire χ hk (hnonprincipal.resolve_left (not_not.mpr hk))
  · exact FamilyContinuation.LFunction_differentiable χ hk

theorem norm_twist_nonprincipal_entire (χ : AngularCharacter) (τ : ℝ)
    (hnonprincipal : χ.k ≠ 0 ∨ χ.residue ≠ 1) :
    Differentiable ℂ (NormTwist.LFunction χ τ) :=
  (nonprincipal_entire χ hnonprincipal).comp (differentiable_id.sub_const _)

theorem norm_twist_differentiableAt (χ : AngularCharacter) (τ : ℝ) (s : ℂ)
    (hs : 0 < s.re)
    (hpole : χ.k = 0 → χ.residue = 1 → s ≠ 1+(τ:ℂ)*I) :
    DifferentiableAt ℂ (NormTwist.LFunction χ τ) s := by
  by_cases hχ : χ.residue = 1
  · exact NormTwist.LFunction_differentiableAt χ τ s hs (fun hk => hpole hk hχ)
  · exact norm_twist_nonprincipal_entire χ τ (Or.inr hχ) s

theorem halfPlane_transport_iff (χ : AngularCharacter) (τ β : ℝ) :
    (∀ s : ℂ, β < s.re → (χ.k = 0 → χ.residue = 1 → s ≠ 1) →
      FamilyContinuation.LFunction χ s ≠ 0) ↔
    (∀ s : ℂ, β < s.re → (χ.k = 0 → χ.residue = 1 → s ≠ 1+(τ:ℂ)*I) →
      NormTwist.LFunction χ τ s ≠ 0) := by
  constructor
  · intro h s hs hpole
    exact h _ (by simpa using hs)
      (fun hk hχ => (NormTwist.shift_ne_one_iff τ s).mpr (hpole hk hχ))
  · intro h s hs hpole
    have hh := h (s+(τ:ℂ)*I) (by simpa using hs)
      (fun hk hχ he => hpole hk hχ (add_right_cancel he))
    simpa only [NormTwist.LFunction,add_sub_cancel_right] using hh

end OAI.SevenEighths.Angular.FullFamilySeed
