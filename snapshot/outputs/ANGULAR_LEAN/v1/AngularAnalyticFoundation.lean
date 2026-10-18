import OAI.NumberTheory.DirichletL.Eisenstein.InverseCuspCoordinates

/-!
# Mellin reflection with arbitrary angular derivative order

These are identities of actual Mellin transforms and complex powers. They do
not assert that an angular theta function satisfies a reflection identity, nor
that an angular L-function has been continued. The first theorem is valid for
the totalized Mellin integral; the pointwise corollary explicitly requires the
reflection identity as a hypothesis. No convergence follows merely from this
identity.
-/

namespace OAI.SevenEighths.Angular.AnalyticFoundation

noncomputable section
open MeasureTheory

/-- Reflection for a profile with the factor produced by a j-th pure cusp
derivative. The Mellin arguments are paired by s ↦ 1-s. -/
theorem cusp_mellin_reflection_order (j : ℕ) (g : ℝ → ℂ) (A s : ℂ)
    (Q : ℝ) (hQ : 0 < Q) :
    mellin (fun v : ℝ => A * ((v : ℂ) ^ (-2 * (j : ℂ)) * g ((Q * v)⁻¹)))
      (2 * s + (j : ℂ) - 1) =
      A * (Q : ℂ) ^ ((j : ℂ) + 1 - 2 * s) *
        mellin g ((j : ℂ) + 1 - 2 * s) := by
  have he : (fun v : ℝ => A * ((v : ℂ) ^ (-2 * (j : ℂ)) * g ((Q * v)⁻¹))) =
      (fun v : ℝ => A • ((v : ℂ) ^ (-2 * (j : ℂ)) • g ((Q * v)⁻¹))) := by
    funext v
    simp only [smul_eq_mul]
  rw [he, mellin_const_smul, mellin_cpow_smul]
  have hm := mellin_comp_mul_left (fun v : ℝ => g v⁻¹)
    (2 * s + (j : ℂ) - 1 + (-2 * (j : ℂ))) hQ
  rw [mellin_comp_inv] at hm
  rw [hm]
  simp only [smul_eq_mul]
  rw [show -(2 * s + (j : ℂ) - 1 + (-2 * (j : ℂ))) =
      (j : ℂ) + 1 - 2 * s by ring]
  ring

/-- Apply the transform identity to an actual positive-height reflection law. -/
theorem cusp_mellin_reflection_order_of_identity (j : ℕ) (f g : ℝ → ℂ)
    (A s : ℂ) (Q : ℝ) (hQ : 0 < Q)
    (hfg : ∀ v : ℝ, 0 < v →
      f v = A * ((v : ℂ) ^ (-2 * (j : ℂ)) * g ((Q * v)⁻¹))) :
    mellin f (2 * s + (j : ℂ) - 1) =
      A * (Q : ℂ) ^ ((j : ℂ) + 1 - 2 * s) *
        mellin g ((j : ℂ) + 1 - 2 * s) := by
  rw [← cusp_mellin_reflection_order j g A s Q hQ]
  unfold mellin
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  rw [hfg v hv]

/-- The norm part of the derivative prefactor cancels the j-dependent
conductor exponent. No statement about the angular phase is made here. -/
theorem derivative_conductor_cancellation (j : ℕ) (Q : ℝ) (hQ : 0 < Q)
    (s : ℂ) :
    (Q : ℂ) ^ (-(j : ℂ)) * (Q : ℂ) ^ ((j : ℂ) + 1 - 2 * s) =
      (Q : ℂ) ^ (1 - 2 * s) := by
  rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hQ.ne')]
  congr 1
  ring

/-- Normalized scalar reflection has conductor exponent 1-2s for every j. -/
theorem normalized_cusp_mellin_reflection_order (j : ℕ) (g : ℝ → ℂ)
    (phase s : ℂ) (Q : ℝ) (hQ : 0 < Q) :
    mellin (fun v : ℝ => (phase * (Q : ℂ) ^ (-(j : ℂ))) *
      ((v : ℂ) ^ (-2 * (j : ℂ)) * g ((Q * v)⁻¹)))
      (2 * s + (j : ℂ) - 1) =
      phase * (Q : ℂ) ^ (1 - 2 * s) *
        mellin g ((j : ℂ) + 1 - 2 * s) := by
  rw [cusp_mellin_reflection_order j g _ s Q hQ]
  rw [mul_assoc phase, derivative_conductor_cancellation j Q hQ s]

end
end OAI.SevenEighths.Angular.AnalyticFoundation
