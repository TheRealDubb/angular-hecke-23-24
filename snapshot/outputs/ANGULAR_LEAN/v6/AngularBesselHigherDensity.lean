import OAI.NumberTheory.DirichletL.Eisenstein.ConjugateCuspProfiles

/-!
# Actual higher Schläfli density derivatives

A finite recursive family differentiates polynomial multiples of the actual
OAI cubic Schläfli density. Every fixed member has an explicit uniform,
integrable majorant for x bounded away from zero. The exponential rate x/4
leaves slack for arbitrary polynomial factors; no uniformity in derivative
order and no spatial smoothness of the infinite Bessel series is asserted.
-/

noncomputable section
open Filter MeasureTheory Set
open scoped Classical Topology

namespace OAI.CubicEisenstein.AngularBesselHigherDensity

def monomial (a b : ℕ) (x t : ℝ) : ℝ :=
  (x ^ a / t ^ b) * cubicBesselDensity x t

def density : ℕ → ℕ → ℕ → ℝ → ℝ → ℝ
  | 0, a, b, x, t => monomial a b x t
  | n + 1, a, b, x, t =>
      (a : ℝ) * density n (a - 1) b x t -
        (1 / 2 : ℝ) * density n (a + 1) (b + 1) x t

def majorant (t : ℝ) : ℝ := t ^ (-(2 : ℝ) / 3) * Real.exp (-t / 2)

def boundConstant : ℕ → ℕ → ℕ → ℝ → ℝ
  | 0, a, b, δ => (4 ^ a * (a.factorial : ℝ)) *
      ((8 / δ ^ 2) ^ b * (b.factorial : ℝ))
  | n + 1, a, b, δ =>
      (a : ℝ) * boundConstant n (a - 1) b δ +
        (1 / 2 : ℝ) * boundConstant n (a + 1) (b + 1) δ

@[simp] theorem density_zero (x t : ℝ) : density 0 0 0 x t = cubicBesselDensity x t := by
  simp [density, monomial]

theorem monomial_hasDerivAt (a b : ℕ) (x t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun y => monomial a b y t)
      ((a : ℝ) * monomial (a - 1) b x t -
        (1 / 2 : ℝ) * monomial (a + 1) (b + 1) x t) x := by
  have h := (((hasDerivAt_id x).pow a).div_const (t ^ b)).mul
    (cubicBesselDensity_hasDerivAt x t)
  convert h using 1
  · funext y
    rfl
  · simp only [monomial, cubicBesselDensityDeriv, mul_one, pow_succ, id_eq, Pi.pow_apply]
    field_simp [ht.ne']
    ring

theorem density_hasDerivAt (n a b : ℕ) (x t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun y => density n a b y t) (density (n + 1) a b x t) x := by
  induction n generalizing a b with
  | zero => exact monomial_hasDerivAt a b x t ht
  | succ n ih =>
      exact ((ih (a - 1) b).const_mul (a : ℝ)).sub
        ((ih (a + 1) (b + 1)).const_mul (1 / 2 : ℝ))

theorem pow_exp_damping (n : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    u ^ n * Real.exp (-u) ≤ (n.factorial : ℝ) := by
  have h := Real.pow_div_factorial_le_exp u hu n
  have hf : (0 : ℝ) < n.factorial := by positivity
  have hpow : u ^ n ≤ Real.exp u * (n.factorial : ℝ) :=
    (div_le_iff₀ hf).mp h
  calc
    _ ≤ (Real.exp u * (n.factorial : ℝ)) * Real.exp (-u) :=
      mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = _ := by rw [mul_right_comm, ← Real.exp_add]; simp

theorem x_pow_damping (a : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    x ^ a * Real.exp (-x / 4) ≤ 4 ^ a * (a.factorial : ℝ) := by
  have h := mul_le_mul_of_nonneg_left (pow_exp_damping a (x / 4) (by positivity))
    (by positivity : (0 : ℝ) ≤ 4 ^ a)
  have heq : (4 : ℝ) ^ a * (x / 4) ^ a = x ^ a := by
    rw [← mul_pow]
    congr 1
    ring
  calc
    _ = 4 ^ a * ((x / 4) ^ a * Real.exp (-(x / 4))) := by
      rw [← mul_assoc, heq]
      congr 1
      congr 1
      ring
    _ ≤ _ := h

theorem inverse_t_pow_damping (b : ℕ) (δ x t : ℝ)
    (hδ : 0 < δ) (hx : δ ≤ x) (ht : 0 < t) :
    (1 / t ^ b) * Real.exp (-(x ^ 2 / (8 * t))) ≤
      (8 / δ ^ 2) ^ b * (b.factorial : ℝ) := by
  have hxp : 0 < x := hδ.trans_le hx
  have he := pow_exp_damping b (x ^ 2 / (8 * t)) (by positivity)
  have hscaled := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ (8 / x ^ 2) ^ b)
  have heq : (8 / x ^ 2) ^ b * (x ^ 2 / (8 * t)) ^ b = 1 / t ^ b := by
    rw [← mul_pow]
    have hbase : (8 / x ^ 2) * (x ^ 2 / (8 * t)) = 1 / t := by
      field_simp
    rw [hbase, div_pow, one_pow]
  calc
    _ = (8 / x ^ 2) ^ b * ((x ^ 2 / (8 * t)) ^ b *
        Real.exp (-(x ^ 2 / (8 * t)))) := by rw [← mul_assoc, heq]
    _ ≤ (8 / x ^ 2) ^ b * (b.factorial : ℝ) := hscaled
    _ ≤ _ := by gcongr

theorem density_exponential_split (x t : ℝ) (ht : 0 < t) :
    Real.exp (-t - x ^ 2 / (4 * t)) ≤
      Real.exp (-x / 4) * Real.exp (-x / 4) * Real.exp (-t / 2) *
        Real.exp (-(x ^ 2 / (8 * t))) := by
  have hyoung : x / 2 - t / 2 ≤ x ^ 2 / (8 * t) :=
    (le_div_iff₀ (show 0 < 8 * t by positivity)).mpr
      (by nlinarith [sq_nonneg (x - 2 * t)])
  simp only [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hsplit : x ^ 2 / (4 * t) = 2 * (x ^ 2 / (8 * t)) := by ring
  rw [hsplit]
  linarith

theorem monomial_bound (a b : ℕ) (δ x t : ℝ)
    (hδ : 0 < δ) (hx : δ ≤ x) (ht : 0 < t) :
    ‖monomial a b x t‖ ≤ boundConstant 0 a b δ * Real.exp (-x / 4) * majorant t := by
  have hxp : 0 < x := hδ.trans_le hx
  have hnonneg : 0 ≤ monomial a b x t := by unfold monomial cubicBesselDensity; positivity
  rw [Real.norm_of_nonneg hnonneg]
  calc
    _ ≤ (x ^ a / t ^ b) * t ^ (-(2 : ℝ) / 3) *
        (Real.exp (-x / 4) * Real.exp (-x / 4) * Real.exp (-t / 2) *
          Real.exp (-(x ^ 2 / (8 * t)))) := by
      unfold monomial cubicBesselDensity
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left (density_exponential_split x t ht) (by positivity)
    _ = (x ^ a * Real.exp (-x / 4)) *
        ((1 / t ^ b) * Real.exp (-(x ^ 2 / (8 * t)))) *
        Real.exp (-x / 4) * majorant t := by unfold majorant; ring
    _ ≤ (4 ^ a * (a.factorial : ℝ)) *
        ((8 / δ ^ 2) ^ b * (b.factorial : ℝ)) * Real.exp (-x / 4) * majorant t := by
      have h1 := x_pow_damping a x hxp.le
      have h2 := inverse_t_pow_damping b δ x t hδ hx ht
      unfold majorant
      gcongr
    _ = _ := rfl

theorem boundConstant_nonneg (n a b : ℕ) (δ : ℝ) : 0 ≤ boundConstant n a b δ := by
  induction n generalizing a b with
  | zero => unfold boundConstant; positivity
  | succ n ih =>
      exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) (ih _ _))
        (mul_nonneg (by norm_num) (ih _ _))

theorem density_bound (n a b : ℕ) (δ x t : ℝ)
    (hδ : 0 < δ) (hx : δ ≤ x) (ht : 0 < t) :
    ‖density n a b x t‖ ≤ boundConstant n a b δ * Real.exp (-x / 4) * majorant t := by
  induction n generalizing a b with
  | zero => exact monomial_bound a b δ x t hδ hx ht
  | succ n ih =>
      calc
        _ ≤ ‖(a : ℝ) * density n (a - 1) b x t‖ +
            ‖(1 / 2 : ℝ) * density n (a + 1) (b + 1) x t‖ := norm_sub_le _ _
        _ = (a : ℝ) * ‖density n (a - 1) b x t‖ +
            (1 / 2 : ℝ) * ‖density n (a + 1) (b + 1) x t‖ := by
          rw [norm_mul, norm_mul, Real.norm_of_nonneg (Nat.cast_nonneg _),
            Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        _ ≤ (a : ℝ) * (boundConstant n (a - 1) b δ * Real.exp (-x / 4) * majorant t) +
            (1 / 2 : ℝ) * (boundConstant n (a + 1) (b + 1) δ *
              Real.exp (-x / 4) * majorant t) := by gcongr <;> apply ih
        _ = _ := by simp only [boundConstant]; ring

theorem majorant_integrable : IntegrableOn majorant (Ioi 0) :=
  cubicBesselDerivativeMajorant_integrable

theorem density_measurable (n a b : ℕ) (x : ℝ) : Measurable (density n a b x) := by
  induction n generalizing a b with
  | zero =>
      change Measurable (fun t => monomial a b x t)
      unfold monomial cubicBesselDensity
      fun_prop
  | succ n ih => exact (measurable_const.mul (ih _ _)).sub (measurable_const.mul (ih _ _))

theorem density_integrable (n a b : ℕ) (x : ℝ) (hx : 0 < x) :
    IntegrableOn (density n a b x) (Ioi 0) := by
  apply (majorant_integrable.const_mul
    (boundConstant n a b x * Real.exp (-x / 4))).mono'
  · exact (density_measurable n a b x).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact density_bound n a b x x t hx le_rfl ht

end OAI.CubicEisenstein.AngularBesselHigherDensity
