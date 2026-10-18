import OAI.NumberTheory.DirichletL.QuadraticSieve.MainTermDifference
import OAI.NumberTheory.DirichletL.Mellin.ReflectedKernel

/-! Shifted gamma multipliers for derivative order n+1 and angular type -n.
All bounds fix n first. Their constants may depend on n and the strip width;
no estimate uniform in a growing angular type is asserted. -/

noncomputable section
open scoped Classical

namespace OAI.CubicEisenstein.AngularReflectionKernel

def upperShift (n : ℕ) : ℝ := (n : ℝ) / 2 + 7 / 6
def lowerShift (n : ℕ) : ℝ := (n : ℝ) / 2 + 5 / 6

theorem upperShift_pos (n : ℕ) : 0 < upperShift n := by
  unfold upperShift
  positivity

theorem lowerShift_pos (n : ℕ) : 0 < lowerShift n := by
  unfold lowerShift
  positivity

theorem upperShift_gt_quarter (n : ℕ) : 1 / 4 < upperShift n := by
  unfold upperShift
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem lowerShift_gt_quarter (n : ℕ) : 1 / 4 < lowerShift n := by
  unfold lowerShift
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

def gammaMultiplier (n : ℕ) (s : ℂ) : ℂ :=
  Complex.Gamma ((upperShift n : ℂ) + s) * Complex.Gamma ((lowerShift n : ℂ) + s) /
    (Complex.Gamma ((upperShift n : ℂ) - s) * Complex.Gamma ((lowerShift n : ℂ) - s))

theorem gammaMultiplier_zero (s : ℂ) :
    gammaMultiplier 0 s = CubicReflectionKernel.gammaMultiplier s := by
  simp [gammaMultiplier, upperShift, lowerShift, CubicReflectionKernel.gammaMultiplier]

theorem gammaMultiplier_neg (n : ℕ) (s : ℂ) :
    gammaMultiplier n (-s) = (gammaMultiplier n s)⁻¹ := by
  simp only [gammaMultiplier, sub_neg_eq_add, ← sub_eq_add_neg, inv_div]

theorem gammaMultiplier_eq_pair (n : ℕ) (s : ℂ) :
    gammaMultiplier n s =
      (Complex.Gamma ((upperShift n : ℂ) + s) / Complex.Gamma ((upperShift n : ℂ) - s)) *
      (Complex.Gamma ((lowerShift n : ℂ) + s) / Complex.Gamma ((lowerShift n : ℂ) - s)) := by
  exact (div_mul_div_comm _ _ _ _).symm

theorem gammaMultiplier_norm_imaginary (n : ℕ) (u : ℝ) :
    ‖gammaMultiplier n ((u : ℂ) * Complex.I)‖ = 1 := by
  have ha := CubicReflectionKernel.Gamma_vertical_ne_zero (upperShift n) u (upperShift_pos n)
  have hb := CubicReflectionKernel.Gamma_vertical_ne_zero (lowerShift n) u (lowerShift_pos n)
  rw [gammaMultiplier, CubicReflectionKernel.Gamma_vertical_conj,
    CubicReflectionKernel.Gamma_vertical_conj, norm_div, norm_mul, norm_mul, norm_star, norm_star]
  exact div_self (mul_ne_zero (norm_ne_zero_iff.mpr ha) (norm_ne_zero_iff.mpr hb))

/-- Holomorphy uses the entire reciprocal gamma factors. A denominator
gamma pole therefore introduces a zero rather than a singularity. -/
theorem gammaMultiplier_differentiableAt (n : ℕ) (s : ℂ)
    (hs : -((n : ℝ) / 2 + 5 / 6) < s.re) :
    DifferentiableAt ℂ (gammaMultiplier n) s := by
  have h1 := (CubicReflectionKernel.Gamma_differentiableAt_of_re_pos
    ((upperShift n : ℂ) + s) (by
      simp only [Complex.add_re, Complex.ofReal_re]
      dsimp [upperShift]
      linarith)).comp s (differentiableAt_const _ |>.add differentiableAt_id)
  have h2 := (CubicReflectionKernel.Gamma_differentiableAt_of_re_pos
    ((lowerShift n : ℂ) + s) (by
      simp only [Complex.add_re, Complex.ofReal_re]
      dsimp [lowerShift]
      linarith)).comp s (differentiableAt_const _ |>.add differentiableAt_id)
  have h3 := (Complex.differentiable_one_div_Gamma ((upperShift n : ℂ) - s)).comp s
    (differentiableAt_const _ |>.sub differentiableAt_id)
  have h4 := (Complex.differentiable_one_div_Gamma ((lowerShift n : ℂ) - s)).comp s
    (differentiableAt_const _ |>.sub differentiableAt_id)
  convert ((h1.mul h2).mul (h3.mul h4)) using 1
  ext z
  simp only [gammaMultiplier, Function.comp_def, div_eq_mul_inv, mul_inv_rev, Pi.mul_apply]
  ring

/-- An explicit bound on the left contour. The real gamma arguments all
remain positive, for every natural extra derivative count n. -/
theorem gammaMultiplier_left_bound (n : ℕ) (t : ℝ) :
    ‖gammaMultiplier n (((-(1/4) : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (Real.Gamma ((n : ℝ)/2 + 11/12) / Real.Gamma ((n : ℝ)/2 + 17/12)) *
      (Real.Gamma ((n : ℝ)/2 + 7/12) / Real.Gamma ((n : ℝ)/2 + 13/12)) := by
  have ha : 0 < upperShift n + -(1/4) := by linarith [upperShift_gt_quarter n]
  have hb : 0 < lowerShift n + -(1/4) := by linarith [lowerShift_gt_quarter n]
  have h1 := CubicReflectionKernel.Gamma_shifted_pair_bound (upperShift n) (-(1/4)) t 0
    ha (by norm_num)
  have h2 := CubicReflectionKernel.Gamma_shifted_pair_bound (lowerShift n) (-(1/4)) t 0
    hb (by norm_num)
  norm_num only [Nat.cast_zero, add_zero] at h1 h2
  have hu1 : upperShift n + -(1/4) = (n : ℝ)/2 + 11/12 := by unfold upperShift; ring
  have hu2 : upperShift n - -(1/4) = (n : ℝ)/2 + 17/12 := by unfold upperShift; ring
  have hl1 : lowerShift n + -(1/4) = (n : ℝ)/2 + 7/12 := by unfold lowerShift; ring
  have hl2 : lowerShift n - -(1/4) = (n : ℝ)/2 + 13/12 := by unfold lowerShift; ring
  rw [hu1, hu2] at h1
  rw [hl1, hl2] at h2
  rw [gammaMultiplier_eq_pair, norm_mul]
  exact mul_le_mul h1 h2 (norm_nonneg _) (div_nonneg
    (Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < (n : ℝ)/2 + 11/12)).le
    (Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < (n : ℝ)/2 + 17/12)).le)

/-- Polynomial growth on each fixed horizontal strip, with a positive
constant allowed to depend on n and A. -/
theorem gammaMultiplier_strip_bound (n A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-(1/4 : ℝ)) (A : ℝ), ∀ t : ℝ,
      ‖gammaMultiplier n ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C * (1 + |t|) ^ (4 * A + 4) := by
  obtain ⟨C₁, hC₁, h1⟩ := CubicReflectionKernel.Gamma_pair_strip_bound
    (upperShift n) (upperShift_gt_quarter n) A
  obtain ⟨C₂, hC₂, h2⟩ := CubicReflectionKernel.Gamma_pair_strip_bound
    (lowerShift n) (lowerShift_gt_quarter n) A
  refine ⟨C₁ * C₂, mul_pos hC₁ hC₂, ?_⟩
  intro σ hσ t
  rw [gammaMultiplier_eq_pair, norm_mul]
  calc
    _ ≤ (C₁ * (1 + |t|) ^ (2*A+2)) * (C₂ * (1 + |t|) ^ (2*A+2)) :=
      mul_le_mul (h1 σ hσ t) (h2 σ hσ t) (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [mul_mul_mul_comm, ← pow_add]
      congr 2
      omega

def axisMultiplier (n : ℕ) (u : ℝ) : ℂ :=
  gammaMultiplier n (((2 * Real.pi * u : ℝ) : ℂ) * Complex.I)

theorem axisMultiplier_norm (n : ℕ) (u : ℝ) : ‖axisMultiplier n u‖ = 1 :=
  gammaMultiplier_norm_imaginary n _

theorem axisMultiplier_continuous (n : ℕ) : Continuous (axisMultiplier n) := by
  have h1 := (CubicReflectionKernel.Gamma_vertical_continuous (upperShift n) (upperShift_pos n)).comp
    (show Continuous (fun u : ℝ => 2 * Real.pi * u) by fun_prop)
  have h2 := (CubicReflectionKernel.Gamma_vertical_continuous (lowerShift n) (lowerShift_pos n)).comp
    (show Continuous (fun u : ℝ => 2 * Real.pi * u) by fun_prop)
  have h3 := (CubicReflectionKernel.Gamma_vertical_continuous (upperShift n) (upperShift_pos n)).comp
    (show Continuous (fun u : ℝ => -(2 * Real.pi * u)) by fun_prop)
  have h4 := (CubicReflectionKernel.Gamma_vertical_continuous (lowerShift n) (lowerShift_pos n)).comp
    (show Continuous (fun u : ℝ => -(2 * Real.pi * u)) by fun_prop)
  have hne (u : ℝ) :
      Complex.Gamma ((upperShift n : ℂ) + ((-(2 * Real.pi * u) : ℝ) : ℂ) * Complex.I) *
      Complex.Gamma ((lowerShift n : ℂ) + ((-(2 * Real.pi * u) : ℝ) : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (CubicReflectionKernel.Gamma_vertical_ne_zero _ _ (upperShift_pos n))
      (CubicReflectionKernel.Gamma_vertical_ne_zero _ _ (lowerShift_pos n))
  convert (h1.mul h2).div (h3.mul h4) hne using 1
  ext u
  simp only [axisMultiplier, gammaMultiplier, Function.comp_def, Complex.ofReal_neg,
    neg_mul, ← sub_eq_add_neg, Pi.div_apply, Pi.mul_apply]

end OAI.CubicEisenstein.AngularReflectionKernel
