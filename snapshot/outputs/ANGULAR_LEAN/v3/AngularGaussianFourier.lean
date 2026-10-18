import AngularGaussianDeriv

/-! Fourier transforms of the actual harmonic-polynomial Gaussian Schwartz
functions. Both pure complex and conjugate powers are treated at every degree. -/

noncomputable section
open scoped SchwartzMap FourierTransform
open LineDeriv FourierTransform

namespace OAI.SevenEighths.Angular.GaussianFourier

open GaussianSchwartz

def mulZ (f : SchwartzMap ℂ ℂ) : SchwartzMap ℂ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun z : ℂ => z) f

def mulConj (f : SchwartzMap ℂ ℂ) : SchwartzMap ℂ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun z : ℂ => star z) f

@[simp] theorem mulZ_apply (f : SchwartzMap ℂ ℂ) (z : ℂ) : mulZ f z = z * f z :=
  SchwartzMap.smulLeftCLM_apply_apply (by fun_prop) _ _

@[simp] theorem mulConj_apply (f : SchwartzMap ℂ ℂ) (z : ℂ) :
    mulConj f z = star z * f z :=
  SchwartzMap.smulLeftCLM_apply_apply
    (Complex.conjCLE.toContinuousLinearMap.hasTemperateGrowth) _ _

theorem plusD_smul (c : ℂ) (f : SchwartzMap ℂ ℂ) : plusD (c • f) = c • plusD f := by
  simp only [plusD, lineDerivOp_smul, smul_add, smul_smul]
  rw [mul_comm Complex.I c]

theorem minusD_smul (c : ℂ) (f : SchwartzMap ℂ ℂ) : minusD (c • f) = c • minusD f := by
  simp only [minusD, lineDerivOp_smul, smul_sub, smul_smul]
  rw [mul_comm Complex.I c]

theorem plusD_fourier (f : SchwartzMap ℂ ℂ) :
    plusD (𝓕 f) = (-(2 * Real.pi * Complex.I) : ℂ) • 𝓕 (mulZ f) := by
  calc
    _ = 𝓕 ((-(2 * Real.pi * Complex.I) : ℂ) •
        SchwartzMap.smulLeftCLM ℂ (inner ℝ · (1 : ℂ)) f +
      Complex.I • ((-(2 * Real.pi * Complex.I) : ℂ) •
        SchwartzMap.smulLeftCLM ℂ (inner ℝ · Complex.I) f)) := by
      simp only [plusD, SchwartzMap.lineDerivOp_fourier_eq, FourierTransform.fourier_add, FourierTransform.fourier_smul]
    _ = 𝓕 ((-(2 * Real.pi * Complex.I) : ℂ) • mulZ f) := by
      congr 1
      ext z
      simp only [add_apply, smul_apply]
      rw [SchwartzMap.smulLeftCLM_apply_apply (Function.hasTemperateGrowth_inner_left (1 : ℂ)),
        SchwartzMap.smulLeftCLM_apply_apply (Function.hasTemperateGrowth_inner_left Complex.I)]
      simp only [inner_one, inner_I, mulZ_apply, Complex.real_smul, smul_eq_mul]
      have hz : (z.re : ℂ) + Complex.I * z.im = z := by
        simpa only [mul_comm] using Complex.re_add_im z
      linear_combination -(2 * Real.pi * Complex.I : ℂ) * f z * hz
    _ = _ := FourierTransform.fourier_smul _ _

theorem minusD_fourier (f : SchwartzMap ℂ ℂ) :
    minusD (𝓕 f) = (-(2 * Real.pi * Complex.I) : ℂ) • 𝓕 (mulConj f) := by
  calc
    _ = 𝓕 ((-(2 * Real.pi * Complex.I) : ℂ) •
        SchwartzMap.smulLeftCLM ℂ (inner ℝ · (1 : ℂ)) f -
      Complex.I • ((-(2 * Real.pi * Complex.I) : ℂ) •
        SchwartzMap.smulLeftCLM ℂ (inner ℝ · Complex.I) f)) := by
      simp only [minusD, SchwartzMap.lineDerivOp_fourier_eq, sub_eq_add_neg, FourierTransform.fourier_add, FourierTransform.fourier_neg, FourierTransform.fourier_smul]
    _ = 𝓕 ((-(2 * Real.pi * Complex.I) : ℂ) • mulConj f) := by
      congr 1
      ext z
      simp only [sub_apply, smul_apply]
      rw [SchwartzMap.smulLeftCLM_apply_apply (Function.hasTemperateGrowth_inner_left (1 : ℂ)),
        SchwartzMap.smulLeftCLM_apply_apply (Function.hasTemperateGrowth_inner_left Complex.I)]
      simp only [inner_one, inner_I, mulConj_apply, Complex.real_smul, smul_eq_mul]
      have hz : (z.re : ℂ) - Complex.I * z.im = star z := by
        apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
      linear_combination -(2 * Real.pi * Complex.I : ℂ) * f z * hz
    _ = _ := FourierTransform.fourier_smul _ _

@[simp] theorem mulZ_holo (a : ℝ) (ha : 0 < a) (m : ℕ) :
    mulZ (holo a ha m) = holo a ha (m + 1) := by
  ext z
  simp only [mulZ_apply, holo_apply, pow_succ]
  ring

@[simp] theorem mulConj_anti (a : ℝ) (ha : 0 < a) (m : ℕ) :
    mulConj (anti a ha m) = anti a ha (m + 1) := by
  ext z
  simp only [mulConj_apply, anti_apply, pow_succ]
  ring

theorem fourier_gaussian (a : ℝ) (ha : 0 < a) :
    𝓕 (gaussian a ha) = (1 / (a : ℂ)) • gaussian (1 / a) (one_div_pos.mpr ha) := by
  ext w
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hb : 0 < ((Real.pi * a : ℝ) : ℂ).re := by
    change 0 < Real.pi * a
    exact mul_pos Real.pi_pos ha
  have hf : (gaussian a ha : ℂ → ℂ) =
      fun z => Complex.exp (-((Real.pi * a : ℝ) : ℂ) * ‖z‖ ^ 2) := by
    funext z
    rw [gaussian_apply]
    push_cast
    ring_nf
  change 𝓕 (gaussian a ha : ℂ → ℂ) w = (1 / (a : ℂ)) * gaussian (1 / a) _ w
  rw [hf, fourier_gaussian_innerProductSpace hb, gaussian_apply]
  simp only [Complex.finrank_real_complex, Nat.cast_ofNat, div_self (two_ne_zero : (2 : ℂ) ≠ 0),
    Complex.cpow_one]
  push_cast
  have hpref : (Real.pi : ℂ) / (Real.pi * a) = 1 / a := by field_simp
  rw [hpref]
  congr 2
  field_simp

def fourierScalar (a : ℝ) (m : ℕ) : ℂ := (-Complex.I) ^ m / (a : ℂ) ^ (m + 1)

theorem fourierScalar_step (a : ℝ) (ha : 0 < a) (m : ℕ) :
    fourierScalar a m * (-(2 * Real.pi * (1 / a) : ℝ) : ℂ) =
      (-(2 * Real.pi * Complex.I) : ℂ) * fourierScalar a (m + 1) := by
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  unfold fourierScalar
  push_cast
  simp only [pow_succ]
  field_simp
  ring_nf
  simp [Complex.I_sq]

theorem fourier_holo (a : ℝ) (ha : 0 < a) (m : ℕ) :
    𝓕 (holo a ha m) = fourierScalar a m • holo (1 / a) (one_div_pos.mpr ha) m := by
  induction m with
  | zero =>
    have hz (b : ℝ) (hb : 0 < b) : holo b hb 0 = gaussian b hb := by
      ext z
      simp only [holo_apply, pow_zero, one_mul]
    rw [hz, hz, fourier_gaussian]
    simp [fourierScalar]
  | succ m ih =>
    have hc : (-(2 * Real.pi * Complex.I) : ℂ) ≠ 0 := by
      exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero two_ne_zero
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
    have h := plusD_fourier (holo a ha m)
    rw [mulZ_holo, ih, plusD_smul, plusD_holo, smul_smul, fourierScalar_step a ha] at h
    ext z
    apply mul_left_cancel₀ hc
    simpa only [smul_apply, smul_eq_mul, mul_assoc] using
      (congrArg (fun f : SchwartzMap ℂ ℂ => f z) h).symm

theorem fourier_anti (a : ℝ) (ha : 0 < a) (m : ℕ) :
    𝓕 (anti a ha m) = fourierScalar a m • anti (1 / a) (one_div_pos.mpr ha) m := by
  induction m with
  | zero =>
    have hz (b : ℝ) (hb : 0 < b) : anti b hb 0 = gaussian b hb := by
      ext z
      simp only [anti_apply, pow_zero, one_mul]
    rw [hz, hz, fourier_gaussian]
    simp [fourierScalar]
  | succ m ih =>
    have hc : (-(2 * Real.pi * Complex.I) : ℂ) ≠ 0 := by
      exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero two_ne_zero
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
    have h := minusD_fourier (anti a ha m)
    rw [mulConj_anti, ih, minusD_smul, minusD_anti, smul_smul, fourierScalar_step a ha] at h
    ext z
    apply mul_left_cancel₀ hc
    simpa only [smul_apply, smul_eq_mul, mul_assoc] using
      (congrArg (fun f : SchwartzMap ℂ ℂ => f z) h).symm

end OAI.SevenEighths.Angular.GaussianFourier
