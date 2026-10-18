import AngularFiniteCuspDualMellin

/-! Exact natural-order reflection factors. These algebraic identities are
used only after the physical reflection and Mellin convergence are proved. -/

noncomputable section
open scoped Classical Topology

namespace OAI.CubicEisenstein.AngularMellinOrderAlgebra

open AngularHigherMellin

theorem cpow_neg_nat (z : ℂ) (m : ℕ) : z ^ (-(m : ℂ)) = (z ^ m)⁻¹ := by
  rw [Complex.cpow_neg, Complex.cpow_natCast]

theorem order_prefactor (κ c : ℂ) (v : ℝ) (j : ℕ) :
    κ * (-1 / (c ^ 2 * (v : ℂ) ^ 2)) ^ j =
      (κ * (-1 : ℂ) ^ j / c ^ (2 * j)) * (v : ℂ) ^ (-2 * (j : ℂ)) := by
  have he : -2 * (j : ℂ) = -((2 * j : ℕ) : ℂ) := by push_cast; ring
  rw [he, cpow_neg_nat]
  simp only [div_pow, mul_pow, pow_mul, div_eq_mul_inv, mul_inv_rev, inv_pow]
  ring

theorem reflected_nat_reverse (m : ℕ) (A : ℂ) (hA : A ≠ 0) (Q : ℝ) (hQ : 0 < Q)
    (f g : ℝ → ℂ) (hfg : ∀ v : ℝ, 0 < v → f v = reflected (m : ℂ) A Q g v)
    (v : ℝ) (hv : 0 < v) :
    g v = reflected (m : ℂ) (A⁻¹ / (Q : ℂ) ^ m) Q f v := by
  have hQc : (Q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ.ne'
  have hvc : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hinv : (Q * (Q * v)⁻¹)⁻¹ = v := by field_simp
  have he := hfg (Q * v)⁻¹ (inv_pos.mpr (mul_pos hQ hv))
  rw [reflected, hinv] at he
  rw [reflected, he]
  simp only [cpow_neg_nat, Complex.ofReal_inv, Complex.ofReal_mul, mul_pow, inv_pow]
  field_simp

theorem order_prefactor_ne_zero (κ c : ℂ) (hκ : κ ≠ 0) (hc : c ≠ 0) (j : ℕ) :
    κ * (-1 : ℂ) ^ j / c ^ (2 * j) ≠ 0 :=
  div_ne_zero (mul_ne_zero hκ (pow_ne_zero j (by norm_num))) (pow_ne_zero _ hc)

end OAI.CubicEisenstein.AngularMellinOrderAlgebra
