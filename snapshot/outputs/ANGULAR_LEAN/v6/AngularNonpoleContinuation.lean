import AngularFamilyInflation
import Mathlib.Analysis.Normed.Module.Connected

/-! Analytic regularity away from the possible theta poles, for every angular
type. No value at a pole is interpreted as an analytic zero. -/

noncomputable section
open Filter Set Complex
open scoped Classical Topology

namespace OAI.SevenEighths.Angular.NonpoleContinuation

theorem primitive_differentiableAt (c : O) [NeZero c] (χ : AngularCharacter)
    (hmod : χ.modulus = Ideal.span {c})
    (hχ : FiniteFourier.IsPrimitiveOnIdeals (hmod ▸ χ.residue))
    (s : ℂ) (h0 : s ≠ 0) (h1 : s ≠ 1) :
    DifferentiableAt ℂ (ThetaContinuation.LFunction c χ hmod hχ) s := by
  by_cases hk : χ.k = 0
  · apply (ThetaContinuation.decompleteFactor_differentiable c χ s).mul
    apply ThetaContinuation.completed_differentiableAt c χ hmod hχ s
    · left
      simpa only [hk, Int.natAbs_zero, Nat.cast_zero, zero_div, add_zero] using h0
    · left
      simpa only [hk, Int.natAbs_zero, Nat.cast_zero, zero_div, add_zero, zero_add] using h1
  · exact ThetaContinuation.LFunction_differentiable c χ hmod hχ hk s

theorem primitiveL_differentiableAt (χ : AngularCharacter) (s : ℂ)
    (h0 : s ≠ 0) (h1 : s ≠ 1) :
    DifferentiableAt ℂ (FamilyContinuation.primitiveL χ) s := by
  letI : NeZero (PrimitiveReduction.generator χ) :=
    ⟨PrimitiveReduction.generator_ne_zero χ⟩
  exact primitive_differentiableAt (PrimitiveReduction.generator χ)
    (PrimitiveReduction.primitive χ) rfl (PrimitiveReduction.primitive_isPrimitive χ) s h0 h1

theorem LFunction_differentiableAt (χ : AngularCharacter) (s : ℂ)
    (h0 : s ≠ 0) (h1 : s ≠ 1) :
    DifferentiableAt ℂ (FamilyContinuation.LFunction χ) s :=
  (primitiveL_differentiableAt χ s h0 h1).mul (PrimitiveReduction.factors_differentiable χ s)

/-- Identity principle on the actual common nonpole domain. -/
theorem eq_of_right_halfPlane {f g : ℂ → ℂ}
    (hf : ∀ z, z ≠ 0 → z ≠ 1 → DifferentiableAt ℂ f z)
    (hg : ∀ z, z ≠ 0 → z ≠ 1 → DifferentiableAt ℂ g z)
    (he : ∀ z, 1 < z.re → f z = g z)
    (s : ℂ) (h0 : s ≠ 0) (h1 : s ≠ 1) : f s = g s := by
  let U : Set ℂ := {0,1}ᶜ
  have hU : IsOpen U := (Set.toFinite ({0,1} : Set ℂ)).isClosed.isOpen_compl
  have hpc : IsPreconnected U :=
    ((Set.toFinite ({0,1} : Set ℂ)).countable.isConnected_compl_of_one_lt_rank
      (Complex.rank_real_complex ▸ Nat.one_lt_ofNat)).isPreconnected
  have hmem : s ∈ U := by simp [U, h0, h1]
  have htwo : (2 : ℂ) ∈ U := by norm_num [U]
  apply AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := ℂ)
    (f := f) (g := g) _ _ hpc htwo _ hmem
  · apply DifferentiableOn.analyticOnNhd _ hU
    intro z hz
    have hz' : z ≠ 0 ∧ z ≠ 1 := by simpa [U] using hz
    exact (hf z hz'.1 hz'.2).differentiableWithinAt
  · apply DifferentiableOn.analyticOnNhd _ hU
    intro z hz
    have hz' : z ≠ 0 ∧ z ≠ 1 := by simpa [U] using hz
    exact (hg z hz'.1 hz'.2).differentiableWithinAt
  · filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds
      (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    exact he z hz

end OAI.SevenEighths.Angular.NonpoleContinuation
