import AngularGaussianFourier

/-! The two harmonic Gaussian Fourier identities in OAI-003's exact paper
convention. The negative angular branch retains the factor (-1)^m. -/

noncomputable section
open scoped SchwartzMap FourierTransform

namespace OAI.SevenEighths.Angular.GaussianFourier

open GaussianSchwartz EisensteinSchwartzPoisson

theorem gaussian_paperFrequency (a : ℝ) (ha : 0 < a) (u : ℂ) :
    gaussian (1 / a) (one_div_pos.mpr ha) (paperFrequency u) =
      gaussian (4 / (3 * a)) (by positivity) u := by
  rw [gaussian_apply, gaussian_apply]
  have hn : (‖paperFrequency u‖ : ℂ) ^ 2 = (4 / 3 : ℂ) * (‖u‖ : ℂ) ^ 2 := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) (paperFrequency_norm_sq u)
    simpa only [Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_div,
      Complex.ofReal_ofNat] using h
  rw [hn]
  push_cast
  congr 1
  field_simp

theorem neg_I_paperFrequency (u : ℂ) :
    -Complex.I * paperFrequency u = (2 / Real.sqrt 3 : ℝ) * star u := by
  unfold paperFrequency
  push_cast
  simp only [starRingEnd_apply]
  ring_nf
  simp [Complex.I_sq]

theorem neg_I_conj_paperFrequency (u : ℂ) :
    -Complex.I * star (paperFrequency u) = -(2 / Real.sqrt 3 : ℝ) * u := by
  simp [paperFrequency]
  ring_nf
  simp [Complex.I_sq]

theorem paper_scalar (a : ℝ) (ha : 0 < a) (m : ℕ) :
    ((2 / Real.sqrt 3 : ℝ) : ℂ) / (a : ℂ) ^ (m + 1) *
      ((2 / Real.sqrt 3 : ℝ) : ℂ) ^ m =
      (2 / ((Real.sqrt 3 : ℂ) * a)) ^ (m + 1) := by
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hr0 : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))
  push_cast
  simp only [div_pow, mul_pow, pow_succ]
  field_simp

theorem paperFourier_holo (a : ℝ) (ha : 0 < a) (m : ℕ) (u : ℂ) :
    paperFourier (holo a ha m) u =
      (2 / ((Real.sqrt 3 : ℂ) * a)) ^ (m + 1) * (star u) ^ m *
        gaussian (4 / (3 * a)) (by positivity) u := by
  rw [paperFourier_eq_standard]
  change (2 / Real.sqrt 3 : ℝ) • (𝓕 (holo a ha m)) (paperFrequency u) = _
  rw [fourier_holo a ha m]
  simp only [smul_apply, holo_apply, smul_eq_mul, Complex.real_smul]
  rw [gaussian_paperFrequency a ha u]
  unfold fourierScalar
  calc
    _ = (((2 / Real.sqrt 3 : ℝ) : ℂ) / (a : ℂ) ^ (m + 1)) *
        (-Complex.I * paperFrequency u) ^ m * gaussian (4 / (3 * a)) (by positivity) u := by
      rw [mul_pow]
      ring
    _ = _ := by
      rw [neg_I_paperFrequency, mul_pow]
      rw [← mul_assoc, paper_scalar a ha]

theorem paperFourier_anti (a : ℝ) (ha : 0 < a) (m : ℕ) (u : ℂ) :
    paperFourier (anti a ha m) u =
      (-1 : ℂ) ^ m * (2 / ((Real.sqrt 3 : ℂ) * a)) ^ (m + 1) * u ^ m *
        gaussian (4 / (3 * a)) (by positivity) u := by
  rw [paperFourier_eq_standard]
  change (2 / Real.sqrt 3 : ℝ) • (𝓕 (anti a ha m)) (paperFrequency u) = _
  rw [fourier_anti a ha m]
  simp only [smul_apply, anti_apply, smul_eq_mul, Complex.real_smul]
  rw [gaussian_paperFrequency a ha u]
  unfold fourierScalar
  calc
    _ = (((2 / Real.sqrt 3 : ℝ) : ℂ) / (a : ℂ) ^ (m + 1)) *
        (-Complex.I * star (paperFrequency u)) ^ m * gaussian (4 / (3 * a)) (by positivity) u := by
      rw [mul_pow]
      ring
    _ = (-1 : ℂ) ^ m *
        ((((2 / Real.sqrt 3 : ℝ) : ℂ) / (a : ℂ) ^ (m + 1)) *
        ((2 / Real.sqrt 3 : ℝ) : ℂ) ^ m) * u ^ m *
        gaussian (4 / (3 * a)) (by positivity) u := by
      rw [neg_I_conj_paperFrequency]
      push_cast
      rw [mul_pow, neg_pow]
      ring
    _ = _ := by rw [paper_scalar a ha]

end OAI.SevenEighths.Angular.GaussianFourier
