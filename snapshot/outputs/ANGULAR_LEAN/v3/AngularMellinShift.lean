import AngularPolynomial
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet

/-! Exact radius and Gaussian-scale cancellation for the shifted angular Mellin
argument. These equalities connect physical coefficients to the ideal exponent;
they do not alone justify interchanging a sum and an integral. -/

noncomputable section

namespace OAI.SevenEighths.Angular.MellinShift

theorem radial_halfDegree (r : ℝ) (hr : 0 < r) (m : ℕ) :
    ((r : ℂ) ^ 2) ^ ((m : ℂ) / 2) = (r : ℂ) ^ m := by
  rw [← Complex.cpow_nat_mul' (n := 2)]
  · norm_num only [Nat.cast_ofNat]
    rw [show (2 : ℂ) * ((m : ℂ) / 2) = m by ring, Complex.cpow_natCast]
  · simp only [Complex.arg_ofReal_of_nonneg hr.le, mul_zero]
    linarith [Real.pi_pos]
  · simp only [Complex.arg_ofReal_of_nonneg hr.le, mul_zero]
    exact Real.pi_pos.le

theorem radial_cpow_shift (r : ℝ) (hr : 0 < r) (m : ℕ) (s : ℂ) :
    (r : ℂ) ^ m / ((r ^ 2 : ℝ) : ℂ) ^ (s + (m : ℂ) / 2) =
      1 / ((r ^ 2 : ℝ) : ℂ) ^ s := by
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  rw [Complex.ofReal_pow, Complex.cpow_add _ _ (pow_ne_zero 2 hrC),
    radial_halfDegree r hr m, mul_comm _ ((r : ℂ) ^ m), ← div_div,
    div_self (pow_ne_zero m hrC)]

theorem radial_rpow_halfDegree (r : ℝ) (hr : 0 < r) (m : ℕ) :
    (r ^ 2) ^ ((m : ℝ) / 2) = r ^ m := by
  rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le]
  norm_num only [Nat.cast_ofNat]
  rw [show (2 : ℝ) * ((m : ℝ) / 2) = m by ring, Real.rpow_natCast]

theorem radial_rpow_shift (r : ℝ) (hr : 0 < r) (m : ℕ) (s : ℝ) :
    r ^ m / (r ^ 2) ^ (s + (m : ℝ) / 2) = 1 / (r ^ 2) ^ s := by
  rw [Real.rpow_add (sq_pos_of_pos hr), radial_rpow_halfDegree r hr m,
    mul_comm _ (r ^ m), ← div_div, div_self (pow_ne_zero m hr.ne')]

theorem scaled_cpow_shift (A r : ℝ) (hA : 0 < A) (hr : 0 < r)
    (m : ℕ) (s : ℂ) :
    (r : ℂ) ^ m / ((A * r ^ 2 : ℝ) : ℂ) ^ (s + (m : ℂ) / 2) =
      (A : ℂ) ^ (-(s + (m : ℂ) / 2)) / ((r ^ 2 : ℝ) : ℂ) ^ s := by
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hA.le (sq_nonneg r)]
  calc
    _ = (A : ℂ) ^ (-(s + (m : ℂ) / 2)) *
        ((r : ℂ) ^ m / ((r ^ 2 : ℝ) : ℂ) ^ (s + (m : ℂ) / 2)) := by
      rw [Complex.cpow_neg]
      ring
    _ = _ := by rw [radial_cpow_shift r hr m s]; ring

theorem scaled_rpow_shift (A r : ℝ) (hA : 0 < A) (hr : 0 < r)
    (m : ℕ) (s : ℝ) :
    r ^ m / (A * r ^ 2) ^ (s + (m : ℝ) / 2) =
      A ^ (-(s + (m : ℝ) / 2)) / (r ^ 2) ^ s := by
  rw [Real.mul_rpow hA.le (sq_nonneg r)]
  calc
    _ = A ^ (-(s + (m : ℝ) / 2)) *
        (r ^ m / (r ^ 2) ^ (s + (m : ℝ) / 2)) := by
      rw [Real.rpow_neg hA.le]
      ring
    _ = _ := by rw [radial_rpow_shift r hr m s]; ring

end OAI.SevenEighths.Angular.MellinShift
