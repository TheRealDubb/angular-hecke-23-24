import AngularBesselHigherIntegral

/-!
# Actual cubic Bessel derivatives and uniform exponential bounds

The real prefactor in the proved Schläfli identity is differentiated by an
explicit recurrence. This identifies every actual real-parameter derivative
of the complex-valued K kernel and proves uniform exponential decay for
x ≥ δ > 0. Constants depend on derivative order and δ. No assertion about
the infinite spatial series or the final zero-free theorem is made here.
-/

noncomputable section
open Filter MeasureTheory Set
open scoped Classical Topology ContDiff

namespace OAI.CubicEisenstein.AngularBesselHigherKernel

open AngularBesselHigherDensity AngularBesselHigherIntegral

def exponent (p : ℕ) : ℝ := -(1 : ℝ) / 3 - (p : ℝ)

def prefactorCoefficient (p : ℕ) : ℝ := exponent p / 2

def weightedIntegral (p q : ℕ) (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (x / 2) ^ exponent p * integral q 0 0 x

def kernelDerivative : ℕ → ℕ → ℕ → ℝ → ℝ
  | 0, p, q, x => weightedIntegral p q x
  | n + 1, p, q, x =>
      prefactorCoefficient p * kernelDerivative n (p + 1) q x +
        kernelDerivative n p (q + 1) x

def gammaMass : ℝ := (2 : ℝ) ^ (1 / 3 : ℝ) * Real.Gamma (1 / 3)

def kernelBound : ℕ → ℕ → ℕ → ℝ → ℝ
  | 0, p, q, δ =>
      (1 / 2 : ℝ) * (δ / 2) ^ exponent p * boundConstant q 0 0 δ * gammaMass
  | n + 1, p, q, δ =>
      ‖prefactorCoefficient p‖ * kernelBound n (p + 1) q δ +
        kernelBound n p (q + 1) δ

theorem weightedIntegral_hasDerivAt (p q : ℕ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (weightedIntegral p q)
      (prefactorCoefficient p * weightedIntegral (p + 1) q x +
        weightedIntegral p (q + 1) x) x := by
  have hp := (((hasDerivAt_id x).div_const 2).rpow_const
    (p := exponent p) (Or.inl (by positivity))).const_mul (1 / 2 : ℝ)
  have h := hp.mul (integral_hasDerivAt q 0 0 x hx)
  convert h using 1
  · funext y
    rfl
  · have he : exponent p - 1 = exponent (p + 1) := by
      simp only [exponent, Nat.cast_add, Nat.cast_one]
      ring
    simp only [weightedIntegral, prefactorCoefficient, he, id_eq]
    ring

theorem kernelDerivative_hasDerivAt (n p q : ℕ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (kernelDerivative n p q) (kernelDerivative (n + 1) p q x) x := by
  induction n generalizing p q with
  | zero => exact weightedIntegral_hasDerivAt p q x hx
  | succ n ih =>
      exact ((ih (p + 1) q).const_mul (prefactorCoefficient p)).add (ih p (q + 1))

theorem gammaMass_pos : 0 < gammaMass := by
  unfold gammaMass
  exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (Real.Gamma_pos_of_pos (by norm_num))

theorem kernelBound_nonneg (n p q : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    0 ≤ kernelBound n p q δ := by
  induction n generalizing p q with
  | zero =>
      have hB := boundConstant_nonneg q 0 0 δ
      have hG := gammaMass_pos.le
      unfold kernelBound
      positivity
  | succ n ih =>
      exact add_nonneg (mul_nonneg (norm_nonneg _) (ih _ _)) (ih _ _)

theorem weightedIntegral_bound (p q : ℕ) (δ x : ℝ) (hδ : 0 < δ) (hx : δ ≤ x) :
    ‖weightedIntegral p q x‖ ≤ kernelBound 0 p q δ * Real.exp (-x / 4) := by
  have hxp : 0 < x := hδ.trans_le hx
  have he : exponent p ≤ 0 := by
    unfold exponent
    have hp : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
    linarith
  have hpow := Real.rpow_le_rpow_of_nonpos (half_pos hδ)
    (show δ / 2 ≤ x / 2 by linarith) he
  have hI := integral_norm_bound q 0 0 δ x hδ hx
  have hB := boundConstant_nonneg q 0 0 δ
  have hG := gammaMass_pos.le
  have hnorm : ‖weightedIntegral p q x‖ =
      (1 / 2 : ℝ) * (x / 2) ^ exponent p * ‖integral q 0 0 x‖ := by
    unfold weightedIntegral
    rw [norm_mul, norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
      Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  rw [hnorm]
  calc
    _ ≤ (1 / 2 : ℝ) * (δ / 2) ^ exponent p *
        (boundConstant q 0 0 δ * Real.exp (-x / 4) * gammaMass) := by
      change ‖integral q 0 0 x‖ ≤ boundConstant q 0 0 δ * Real.exp (-x / 4) * gammaMass at hI
      gcongr
    _ = _ := by unfold kernelBound; ring

theorem kernelDerivative_bound (n p q : ℕ) (δ x : ℝ) (hδ : 0 < δ) (hx : δ ≤ x) :
    ‖kernelDerivative n p q x‖ ≤ kernelBound n p q δ * Real.exp (-x / 4) := by
  induction n generalizing p q with
  | zero => exact weightedIntegral_bound p q δ x hδ hx
  | succ n ih =>
      calc
        _ ≤ ‖prefactorCoefficient p * kernelDerivative n (p + 1) q x‖ +
            ‖kernelDerivative n p (q + 1) x‖ := norm_add_le _ _
        _ = ‖prefactorCoefficient p‖ * ‖kernelDerivative n (p + 1) q x‖ +
            ‖kernelDerivative n p (q + 1) x‖ := by rw [norm_mul]
        _ ≤ ‖prefactorCoefficient p‖ * (kernelBound n (p + 1) q δ * Real.exp (-x / 4)) +
            kernelBound n p (q + 1) δ * Real.exp (-x / 4) := by gcongr <;> apply ih
        _ = _ := by simp only [kernelBound]; ring

theorem schlafliBesselK_cubic_eq_kernel (x : ℝ) (hx : 0 < x) :
    schlafliBesselK (1 / 3 : ℂ) x = (kernelDerivative 0 0 0 x : ℂ) := by
  simpa only [kernelDerivative, weightedIntegral, exponent, Nat.cast_zero, sub_zero,
    AngularBesselHigherIntegral.integral_zero] using schlafliBesselK_cubic_real x hx

theorem schlafliBesselK_cubic_iteratedDeriv (n : ℕ) (x : ℝ) (hx : 0 < x) :
    iteratedDeriv n (schlafliBesselK (1 / 3 : ℂ)) x = (kernelDerivative n 0 0 x : ℂ) := by
  induction n generalizing x with
  | zero => simpa using schlafliBesselK_cubic_eq_kernel x hx
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have he : iteratedDeriv n (schlafliBesselK (1 / 3 : ℂ)) =ᶠ[𝓝 x]
          (fun y => (kernelDerivative n 0 0 y : ℂ)) := by
        filter_upwards [Ioi_mem_nhds hx] with y hy
        exact ih y hy
      rw [he.deriv_eq]
      exact (kernelDerivative_hasDerivAt n 0 0 x hx).ofReal_comp.deriv

theorem schlafliBesselK_cubic_iteratedDeriv_hasDerivAt (n : ℕ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (iteratedDeriv n (schlafliBesselK (1 / 3 : ℂ)))
      (iteratedDeriv (n + 1) (schlafliBesselK (1 / 3 : ℂ)) x) x := by
  rw [schlafliBesselK_cubic_iteratedDeriv (n + 1) x hx]
  apply (kernelDerivative_hasDerivAt n 0 0 x hx).ofReal_comp.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact schlafliBesselK_cubic_iteratedDeriv n y hy

theorem schlafliBesselK_cubic_iteratedDeriv_bound (n : ℕ) (δ x : ℝ)
    (hδ : 0 < δ) (hx : δ ≤ x) :
    ‖iteratedDeriv n (schlafliBesselK (1 / 3 : ℂ)) x‖ ≤
      kernelBound n 0 0 δ * Real.exp (-x / 4) := by
  rw [schlafliBesselK_cubic_iteratedDeriv n x (hδ.trans_le hx), Complex.norm_real]
  exact kernelDerivative_bound n 0 0 δ x hδ hx

theorem schlafliBesselK_cubic_uniform_derivative_bounds (n : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, δ ≤ x →
      ‖iteratedDeriv n (schlafliBesselK (1 / 3 : ℂ)) x‖ ≤ C * Real.exp (-x / 4) :=
  ⟨kernelBound n 0 0 δ, kernelBound_nonneg n 0 0 δ hδ,
    fun x hx => schlafliBesselK_cubic_iteratedDeriv_bound n δ x hδ hx⟩

end OAI.CubicEisenstein.AngularBesselHigherKernel
