import AngularGaussianWeighted

noncomputable section
open scoped SchwartzMap FourierTransform ContDiff
open LineDeriv
namespace OAI.SevenEighths.Angular.GaussianFourier
open GaussianSchwartz

theorem weighted_lineDeriv (L : ℂ →L[ℝ] ℂ) (a : ℝ) (ha : 0 < a)
    (m : ℕ) (w v : ℂ) :
    (∂_{v} (weighted L a ha m)) w =
      ((m : ℂ) * (L w) ^ (m - 1) * L v -
        (2 * Real.pi * a : ℝ) * (inner ℝ w v : ℝ) * (L w) ^ m) * gaussian a ha w := by
  have hline : HasDerivAt (fun t : ℝ => w + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add w
  have hL : HasDerivAt (fun t : ℝ => L (w + t • v)) (L v) 0 := by
    convert! L.hasFDerivAt.comp_hasDerivAt 0 hline using 1
  have hg : HasDerivAt (fun t : ℝ => gaussian a ha (w + t • v))
      ((-(2 * Real.pi * a : ℝ) * inner ℝ w v : ℝ) * gaussian a ha w) 0 := by
    convert ((hline.norm_sq.const_mul (-(Real.pi * a))).exp).ofReal_comp using 1
    · funext t
      rfl
    · simp only [zero_smul, add_zero]
      rw [gaussian_apply_real]
      push_cast
      ring
  have hw := (hL.pow m).mul hg
  have hder : HasLineDerivAt ℝ (weighted L a ha m)
      (((m : ℂ) * (L w) ^ (m - 1) * L v -
        (2 * Real.pi * a : ℝ) * (inner ℝ w v : ℝ) * (L w) ^ m) * gaussian a ha w) w v := by
    change HasDerivAt (fun t : ℝ => weighted L a ha m (w + t • v)) _ 0
    convert hw using 1
    · funext t
      simp only [weighted_apply, Pi.pow_apply, Pi.mul_apply]
    · simp only [zero_smul, add_zero, Pi.pow_apply]
      push_cast
      ring
  rw [SchwartzMap.lineDerivOp_apply]
  exact hder.lineDeriv

def plusD (f : SchwartzMap ℂ ℂ) : SchwartzMap ℂ ℂ :=
  ∂_{(1 : ℂ)} f + Complex.I • ∂_{Complex.I} f

def minusD (f : SchwartzMap ℂ ℂ) : SchwartzMap ℂ ℂ :=
  ∂_{(1 : ℂ)} f - Complex.I • ∂_{Complex.I} f

theorem inner_one (z : ℂ) : inner ℝ z (1 : ℂ) = z.re := by
  simp

theorem inner_I (z : ℂ) : inner ℝ z Complex.I = z.im := by
  simp [Complex.mul_re]

theorem plusD_holo (a : ℝ) (ha : 0 < a) (m : ℕ) :
    plusD (holo a ha m) = (-(2 * Real.pi * a : ℝ) : ℂ) • holo a ha (m + 1) := by
  ext z
  simp only [plusD, add_apply, smul_apply, smul_eq_mul,
    holo, weighted_lineDeriv, ContinuousLinearMap.id_apply, inner_one, inner_I, weighted_apply,
    pow_succ]
  have hz : (z.re : ℂ) + Complex.I * z.im = z := by
    simpa only [mul_comm] using Complex.re_add_im z
  push_cast
  linear_combination (norm := ring_nf) -(2 * Real.pi * a : ℂ) * z ^ m * gaussian a ha z * hz
  simp [Complex.I_sq]

theorem minusD_anti (a : ℝ) (ha : 0 < a) (m : ℕ) :
    minusD (anti a ha m) = (-(2 * Real.pi * a : ℝ) : ℂ) • anti a ha (m + 1) := by
  ext z
  simp only [minusD, sub_apply, smul_apply, smul_eq_mul,
    anti, weighted_lineDeriv, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
    map_one, Complex.conj_I, inner_one, inner_I, weighted_apply, pow_succ]
  have hz : (z.re : ℂ) - Complex.I * z.im = star z := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  push_cast
  simp only [starRingEnd_apply] at *
  linear_combination (norm := ring_nf) -(2 * Real.pi * a : ℂ) * (star z) ^ m * gaussian a ha z * hz
  simp [Complex.I_sq]

end OAI.SevenEighths.Angular.GaussianFourier
