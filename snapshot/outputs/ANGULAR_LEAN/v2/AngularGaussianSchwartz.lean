import OAI.NumberTheory.DirichletL.GaussSum.SexticRadialPoisson

/-!
Concrete full planar Gaussian Schwartz functions. This file proves decay of
all real Frechet derivatives; no assumed Schwartz/growth/equality contract is
used. It does not assert an angular theta functional equation or zero-free bound.
-/

noncomputable section

open scoped SchwartzMap ContDiff

namespace OAI.SevenEighths.Angular.GaussianSchwartz

/-- An explicit bound for every polynomial weight times a decaying Gaussian. -/
theorem polynomial_gaussian_bound (b : ℝ) (hb : 0 < b) (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r : ℝ, 0 ≤ r →
      (1 + r) ^ N * Real.exp (-b * r ^ 2) ≤ B := by
  refine ⟨(2 / b) ^ N * (N.factorial : ℝ) * Real.exp b, by positivity, ?_⟩
  intro r hr
  let x := b * (1 + r ^ 2)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hbase : 1 + r ≤ (2 / b) * x := by
    dsimp [x]
    have heq : (2 / b) * (b * (1 + r ^ 2)) = 2 * (1 + r ^ 2) := by
      field_simp
    rw [heq]
    nlinarith [sq_nonneg (r - 1 / 2)]
  have hpow : (1 + r) ^ N ≤ (2 / b) ^ N * x ^ N := by
    simpa only [mul_pow] using pow_le_pow_left₀ (by positivity : 0 ≤ 1 + r) hbase N
  have hfac : x ^ N ≤ (N.factorial : ℝ) * Real.exp x := by
    have hf : (0 : ℝ) < N.factorial := by positivity
    have h := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp x hx N)
    simpa only [mul_comm] using h
  calc
    (1 + r) ^ N * Real.exp (-b * r ^ 2)
        ≤ ((2 / b) ^ N * x ^ N) * Real.exp (-b * r ^ 2) := by gcongr
    _ ≤ ((2 / b) ^ N * ((N.factorial : ℝ) * Real.exp x)) *
        Real.exp (-b * r ^ 2) := by gcongr
    _ = (2 / b) ^ N * (N.factorial : ℝ) * Real.exp b := by
      have hsum : x + -b * r ^ 2 = b := by dsimp [x]; ring
      rw [mul_assoc, mul_assoc, ← Real.exp_add, hsum]
      ring

/-- The Gaussian exponent has proved temperate growth, uniformly through each
fixed finite derivative order. -/
theorem gaussianExponent_temperate (b : ℝ) :
    Function.HasTemperateGrowth (fun z : ℂ => -b * ‖z‖ ^ 2) := by
  fun_prop

/-- All derivative orders of the real exponential have norm equal to its value. -/
theorem norm_iteratedFDeriv_exp (n : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ n Real.exp x‖ = Real.exp x := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate,
    Real.iter_deriv_exp]
  exact Real.norm_of_nonneg (Real.exp_pos x).le

/-- Every derivative of the full planar Gaussian decays faster than every
polynomial. The proof uses the general composition derivative bound, with the
Gaussian exponential retained instead of replaced by a constant. -/
theorem realGaussian_decay (b : ℝ) (hb : 0 < b) (p n : ℕ) :
    ∃ B : ℝ, ∀ z : ℂ,
      ‖z‖ ^ p * ‖iteratedFDeriv ℝ n (fun z : ℂ => Real.exp (-b * ‖z‖ ^ 2)) z‖ ≤ B := by
  let φ : ℂ → ℝ := fun z => -b * ‖z‖ ^ 2
  have hφ : Function.HasTemperateGrowth φ := gaussianExponent_temperate b
  obtain ⟨K, C, hC, hφbound⟩ := hφ.norm_iteratedFDeriv_le_uniform n
  obtain ⟨B, hB, hBbound⟩ := polynomial_gaussian_bound b hb (p + K * n)
  refine ⟨(n.factorial : ℝ) * (1 + C) ^ n * B, ?_⟩
  intro z
  have hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i φ z‖ ≤
      ((1 + C) * (1 + ‖z‖) ^ K) ^ i := by
    intro i hi hin
    calc
      _ ≤ C * (1 + ‖z‖) ^ K := hφbound i hin z
      _ ≤ (1 + C) * (1 + ‖z‖) ^ K := by gcongr; linarith
      _ ≤ _ := by
        apply le_self_pow₀
        · exact one_le_mul_of_one_le_of_one_le (by linarith)
            (one_le_pow₀ (by simp))
        · omega
  have hderiv : ‖iteratedFDeriv ℝ n (Real.exp ∘ φ) z‖ ≤
      (n.factorial : ℝ) * Real.exp (φ z) * ((1 + C) * (1 + ‖z‖) ^ K) ^ n :=
    norm_iteratedFDeriv_comp_le Real.contDiff_exp hφ.1 (by exact_mod_cast le_top) z
      (fun i _ => (norm_iteratedFDeriv_exp i (φ z)).le) hD
  have hweight : ‖z‖ ^ p ≤ (1 + ‖z‖) ^ p := by
    gcongr
    linarith
  change ‖z‖ ^ p * ‖iteratedFDeriv ℝ n (Real.exp ∘ φ) z‖ ≤ _
  calc
    _ ≤ (1 + ‖z‖) ^ p * ((n.factorial : ℝ) * Real.exp (φ z) *
        ((1 + C) * (1 + ‖z‖) ^ K) ^ n) :=
      mul_le_mul hweight hderiv (norm_nonneg _) (by positivity)
    _ = (n.factorial : ℝ) * (1 + C) ^ n *
        ((1 + ‖z‖) ^ (p + K * n) * Real.exp (-b * ‖z‖ ^ 2)) := by
      dsimp [φ]
      rw [mul_pow, ← pow_mul, pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hBbound ‖z‖ (norm_nonneg _)) (by positivity)

/-- The full real-valued planar Gaussian, bundled with its proved Schwartz bounds. -/
def realGaussian (b : ℝ) (hb : 0 < b) : SchwartzMap ℂ ℝ where
  toFun z := Real.exp (-b * ‖z‖ ^ 2)
  smooth' := (gaussianExponent_temperate b).1.exp
  decay' := realGaussian_decay b hb

@[simp] theorem realGaussian_apply (b : ℝ) (hb : 0 < b) (z : ℂ) :
    realGaussian b hb z = Real.exp (-b * ‖z‖ ^ 2) := rfl

/-- The full planar Gaussian with the source's pi-normalized parameter. -/
def gaussian (a : ℝ) (ha : 0 < a) : SchwartzMap ℂ ℂ :=
  (realGaussian (Real.pi * a) (mul_pos Real.pi_pos ha)).postcompCLM
    Complex.ofRealCLM

@[simp] theorem gaussian_apply (a : ℝ) (ha : 0 < a) (z : ℂ) :
    gaussian a ha z = Complex.exp (-Real.pi * (a : ℂ) * (‖z‖ : ℂ) ^ 2) := by
  change (Real.exp (-(Real.pi * a) * ‖z‖ ^ 2) : ℂ) = _
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

end OAI.SevenEighths.Angular.GaussianSchwartz
