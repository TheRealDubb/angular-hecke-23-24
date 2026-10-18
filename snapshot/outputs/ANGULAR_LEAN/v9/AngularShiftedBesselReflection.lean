import AngularGammaMultiplier
import AngularProjectedMellin
import AngularAnalyticFoundation
import OAI.NumberTheory.DirichletL.Eisenstein.SourceCuspKernels

/-! Shifted normalization of the actual Bessel Mellin transform. Reflection
retains the extra conductor/scaling powers and the raw dual radial weight.
The generic reflection hypothesis is explicit; the physical initial identity
is instantiated from the already proved finite Fourier projector. -/

noncomputable section
open MeasureTheory
open scoped Classical BigOperators

namespace OAI.CubicEisenstein.AngularShiftedBesselReflection

open CompletedGauss AngularProjectedMellin AngularFiniteProjector
open SevenEighths.Angular

def continuedDirichlet (n : ℕ) (F : ℝ → ℂ) (q : ℝ) (s : ℂ) : ℂ :=
  inverseBesselMellinFactor q (s + (n : ℂ) / 2) * mellin F (2 * s + (n : ℂ))

def smoothingIntegrand (n : ℕ) (F : ℝ → ℂ) (q : ℝ)
    (V : ℝ → ℂ) (X : ℝ) (s : ℂ) : ℂ :=
  mellin V (s - 1 / 2) * (X : ℂ) ^ (s - 1 / 2) * continuedDirichlet n F q s

def reflectionFactor (n : ℕ) (q d : ℝ) (s : ℂ) : ℂ :=
  ((4 * Real.pi * q : ℝ) : ℂ) ^ (2 * s + (n : ℂ) + 1) *
    (2 : ℂ) ^ (2 - 4 * s) /
      ((4 * Real.pi * d : ℝ) : ℂ) ^ (3 - 2 * s + (n : ℂ))

theorem shifted_factor_identity (n : ℕ) (q d : ℝ) (s : ℂ) :
    inverseBesselMellinFactor q (s + (n : ℂ) / 2) *
      besselMellinFactor d (1 - s + (n : ℂ) / 2) =
        reflectionFactor n q d s * AngularReflectionKernel.gammaMultiplier n (1 / 2 - s) := by
  have hu : (AngularReflectionKernel.upperShift n : ℂ) = (n : ℂ) / 2 + 7 / 6 := by
    simp [AngularReflectionKernel.upperShift]
  have hl : (AngularReflectionKernel.lowerShift n : ℂ) = (n : ℂ) / 2 + 5 / 6 := by
    simp [AngularReflectionKernel.lowerShift]
  have hp : (2 : ℂ) ^ (1 - 2 * s - (n : ℂ)) *
      (2 : ℂ) ^ (1 - 2 * s + (n : ℂ)) = (2 : ℂ) ^ (2 - 4 * s) := by
    rw [← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
    congr 1
    ring
  unfold inverseBesselMellinFactor besselMellinFactor reflectionFactor
    AngularReflectionKernel.gammaMultiplier
  rw [hu, hl,
    show (2 : ℂ) * (s + (n : ℂ) / 2) + 1 = 2 * s + (n : ℂ) + 1 by ring,
    show (1 : ℂ) - 2 * (s + (n : ℂ) / 2) = 1 - 2 * s - (n : ℂ) by ring,
    show (2 : ℂ) * (1 - s + (n : ℂ) / 2) - 1 = 1 - 2 * s + (n : ℂ) by ring,
    show (2 : ℂ) * (1 - s + (n : ℂ) / 2) + 1 = 3 - 2 * s + (n : ℂ) by ring,
    show (1 : ℂ) - s + (n : ℂ) / 2 + 1 / 3 = 4 / 3 - s + (n : ℂ) / 2 by ring,
    show (1 : ℂ) - s + (n : ℂ) / 2 + 2 / 3 = 5 / 3 - s + (n : ℂ) / 2 by ring,
    show (n : ℂ) / 2 + 7 / 6 + (1 / 2 - s) = 5 / 3 - s + (n : ℂ) / 2 by ring,
    show (n : ℂ) / 2 + 5 / 6 + (1 / 2 - s) = 4 / 3 - s + (n : ℂ) / 2 by ring,
    show (n : ℂ) / 2 + 7 / 6 - (1 / 2 - s) = s + (n : ℂ) / 2 + 2 / 3 by ring,
    show (n : ℂ) / 2 + 5 / 6 - (1 / 2 - s) = s + (n : ℂ) / 2 + 1 / 3 by ring]
  have he := congrArg (fun z : ℂ =>
    (((4 * Real.pi * q : ℝ) : ℂ) ^ (2 * s + (n : ℂ) + 1) *
      (Complex.Gamma (s + (n : ℂ) / 2 + 1 / 3))⁻¹ *
      (Complex.Gamma (s + (n : ℂ) / 2 + 2 / 3))⁻¹ *
      Complex.Gamma (4 / 3 - s + (n : ℂ) / 2) *
      Complex.Gamma (5 / 3 - s + (n : ℂ) / 2) *
      (((4 * Real.pi * d : ℝ) : ℂ) ^ (3 - 2 * s + (n : ℂ)))⁻¹) * z) hp
  simp only [div_eq_mul_inv, mul_inv_rev] at he ⊢
  linear_combination he

theorem reflectionFactor_eq_base (n : ℕ) (q d : ℝ) (hq : 0 < q) (hd : 0 < d)
    (s : ℂ) :
    reflectionFactor n q d s = ((q / d : ℝ) : ℂ) ^ n * besselReflectionFactor q d s := by
  have hq0 : ((4 * Real.pi * q : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hd0 : ((4 * Real.pi * d : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hratio : ((4 * Real.pi * q : ℝ) : ℂ) / ((4 * Real.pi * d : ℝ) : ℂ) =
      ((q / d : ℝ) : ℂ) := by
    rw [← Complex.ofReal_div]
    congr 1
    field_simp [Real.pi_ne_zero, hd.ne'] <;> ring
  have hp : ((4 * Real.pi * q : ℝ) : ℂ) ^ n / ((4 * Real.pi * d : ℝ) : ℂ) ^ n =
      ((q / d : ℝ) : ℂ) ^ n := by rw [← div_pow, hratio]
  unfold reflectionFactor besselReflectionFactor
  rw [show (2 : ℂ) * s + (n : ℂ) + 1 = (2 * s + 1) + (n : ℂ) by ring,
    Complex.cpow_add _ _ hq0, Complex.cpow_add _ _ hd0,
    Complex.cpow_natCast, Complex.cpow_natCast, ← hp]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The physical initial normalization retains its known nontrivial scalar. -/
theorem continuedDirichlet_finiteProjector (χ : AngularCharacter) (n : ℕ)
    (hk : χ.k = -(n : ℤ)) (c : ActualEisensteinCubic.O) (hc : c ≠ 0)
    [Fintype (ActualEisensteinCubic.O ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : ActualEisensteinCubic.O)} * χ.modulus)
    (s : ℂ) (hs : 3 / 2 < s.re) :
    continuedDirichlet n (finiteProjector χ n c hc) thetaBesselScale s =
      (thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale) ^ n) *
        completedDirichletSeries χ.elementHom.toMonoidHom s := by
  have ht : -(1 / 3 : ℝ) < (s + (n : ℂ) / 2).re := by
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re]
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith
  rw [continuedDirichlet, finiteProjector_mellin χ n hk c hc hcQ s hs]
  have hi := inverseBesselMellinFactor_mul thetaBesselScale thetaBesselScale_pos
    (s + (n : ℂ) / 2) ht
  calc
    _ = (thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale) ^ n) *
        (inverseBesselMellinFactor thetaBesselScale (s + (n : ℂ) / 2) *
          besselMellinFactor thetaBesselScale (s + (n : ℂ) / 2)) *
        completedDirichletSeries χ.elementHom.toMonoidHom s := by ring
    _ = _ := by rw [hi, mul_one]

/-- The raw dual coefficient has an extra negative half-order radial weight. -/
theorem continuedDirichlet_reflection {ι : Type*} [Countable ι]
    (n : ℕ) (F : ℝ → ℂ) (r : ι → ℝ) (hr : ∀ i, 0 < r i) (b : ι → ℂ)
    (q d Q : ℝ) (hd : 0 < d) (hQ : 0 < Q) (A : ℂ)
    (hreflect : ∀ v : ℝ, 0 < v → F v = A *
      ((v : ℂ) ^ (-2 * ((n : ℂ) + 1)) * radialBesselProfile r b d ((Q * v)⁻¹)))
    (s : ℂ) (hs : s.re < 4 / 3 + (n : ℝ) / 2)
    (hb : Summable (fun i => ‖b i‖ * r i ^ (s.re - 1 / 2 - (n : ℝ) / 2))) :
    continuedDirichlet n F q s =
      (A * (Q : ℂ) ^ ((n : ℂ) + 2 - 2 * s) * reflectionFactor n q d s) *
        AngularReflectionKernel.gammaMultiplier n (1 / 2 - s) *
          (∑' i, b i * (r i : ℂ) ^ (s - 1 / 2 - (n : ℂ) / 2)) := by
  have ht : -(1 / 3 : ℝ) < (1 - s + (n : ℂ) / 2).re := by
    simp only [Complex.add_re, Complex.sub_re, Complex.one_re,
      Complex.div_ofNat_re, Complex.natCast_re]
    linarith
  have hb' : Summable (fun i => ‖b i‖ * r i ^ (1 / 2 - (1 - s + (n : ℂ) / 2).re)) := by
    convert hb using 1
    funext i
    congr 2
    simp only [Complex.add_re, Complex.sub_re, Complex.one_re,
      Complex.div_ofNat_re, Complex.natCast_re]
    ring
  have hm := radialBesselProfile_mellin r hr b d hd (1 - s + (n : ℂ) / 2) ht hb'
  have hc := AnalyticFoundation.cusp_mellin_reflection_order_of_identity (n + 1)
    F (radialBesselProfile r b d) A s Q hQ (by simpa only [Nat.cast_add, Nat.cast_one] using hreflect)
  have hm' : mellin (radialBesselProfile r b d) ((n : ℂ) + 2 - 2 * s) =
      besselMellinFactor d (1 - s + (n : ℂ) / 2) *
        (∑' i, b i * (r i : ℂ) ^ (s - 1 / 2 - (n : ℂ) / 2)) := by
    simpa only [besselMellinFactor,
      show (2 : ℂ) * (1 - s + (n : ℂ) / 2) = (n : ℂ) + 2 - 2 * s by ring,
      show (1 / 2 : ℂ) - (1 - s + (n : ℂ) / 2) = s - 1 / 2 - (n : ℂ) / 2 by ring] using hm
  simp only [Nat.cast_add, Nat.cast_one] at hc
  rw [show (2 : ℂ) * s + ((n : ℂ) + 1) - 1 = 2 * s + (n : ℂ) by ring,
    show ((n : ℂ) + 1) + 1 - 2 * s = (n : ℂ) + 2 - 2 * s by ring, hm'] at hc
  rw [continuedDirichlet, hc]
  calc
    _ = (A * (Q : ℂ) ^ ((n : ℂ) + 2 - 2 * s)) *
        (inverseBesselMellinFactor q (s + (n : ℂ) / 2) *
          besselMellinFactor d (1 - s + (n : ℂ) / 2)) *
        (∑' i, b i * (r i : ℂ) ^ (s - 1 / 2 - (n : ℂ) / 2)) := by ring
    _ = _ := by rw [shifted_factor_identity]; ring

theorem raw_radial_power_cancel (r : ℝ) (hr : 0 < r) (n : ℕ) (s : ℂ) :
    (Real.sqrt r : ℂ) ^ n * (r : ℂ) ^ (s - 1 / 2 - (n : ℂ) / 2) =
      (r : ℂ) ^ (s - 1 / 2) := by
  have h := sqrt_power_complex_cancel r hr n (1 - s)
  simpa only [
    show (1 / 2 : ℂ) - (1 - s + (n : ℂ) / 2) = s - 1 / 2 - (n : ℂ) / 2 by ring,
    show (1 / 2 : ℂ) - (1 - s) = s - 1 / 2 by ring] using h

theorem normalized_radial_sum {ι : Type*} (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (a : ι → ℂ) (n : ℕ) (s : ℂ) :
    (∑' i, (a i * (Real.sqrt (r i) : ℂ) ^ n) *
      (r i : ℂ) ^ (s - 1 / 2 - (n : ℂ) / 2)) =
        ∑' i, a i * (r i : ℂ) ^ (s - 1 / 2) := by
  apply tsum_congr
  intro i
  rw [mul_assoc, raw_radial_power_cancel _ (hr i)]

theorem shifted_reflection_scale (n : ℕ) (q d Q X : ℝ)
    (hq : 0 < q) (hd : 0 < d) (hQ : 0 < Q) (hX : 0 < X) (w : ℂ) :
    (Q : ℂ) ^ ((n : ℂ) + 2 - 2 * (1 / 2 - w)) *
      reflectionFactor n q d (1 / 2 - w) * (X : ℂ) ^ (-w) =
        ((Q : ℂ) ^ (n + 1) * ((q / d : ℝ) : ℂ) ^ (n + 2)) *
          ((CubicReflectionKernel.paperScale * (27 * q ^ 2 * d ^ 2 * X / Q ^ 2) : ℝ) : ℂ) ^ (-w) := by
  have hp := bessel_reflection_scale q d Q X 1 hq hd hQ hX (by norm_num) w
  simp only [Complex.ofReal_one, Complex.one_cpow, mul_one] at hp
  rw [reflectionFactor_eq_base n q d hq hd,
    show (n : ℂ) + 2 - 2 * (1 / 2 - w) = (n : ℂ) + (2 - 2 * (1 / 2 - w)) by ring,
    Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hQ.ne'), Complex.cpow_natCast]
  calc
    _ = ((Q : ℂ) ^ n * ((q / d : ℝ) : ℂ) ^ n) *
        ((Q : ℂ) ^ (2 - 2 * (1 / 2 - w)) *
          besselReflectionFactor q d (1 / 2 - w) * (X : ℂ) ^ (-w)) := by ring
    _ = ((Q : ℂ) ^ n * ((q / d : ℝ) : ℂ) ^ n) *
        (((Q * (q / d) ^ 2 : ℝ) : ℂ) *
          ((CubicReflectionKernel.paperScale * (27 * q ^ 2 * d ^ 2 * X / Q ^ 2) : ℝ) : ℂ) ^ (-w)) := by
      rw [hp]
    _ = _ := by
      simp only [Complex.ofReal_mul, Complex.ofReal_pow, pow_add, pow_one]
      ring

/-- The original smoothing window remains unchanged, while the dual raw
coefficient and conductor/scale prefactor retain all order-dependent powers. -/
theorem reflected_smoothing_line {ι : Type*} [Countable ι]
    (n : ℕ) (F : ℝ → ℂ) (r : ι → ℝ) (hr : ∀ i, 0 < r i) (b : ι → ℂ)
    (q d Q : ℝ) (hq : 0 < q) (hd : 0 < d) (hQ : 0 < Q) (A : ℂ)
    (hreflect : ∀ v : ℝ, 0 < v → F v = A *
      ((v : ℂ) ^ (-2 * ((n : ℂ) + 1)) * radialBesselProfile r b d ((Q * v)⁻¹)))
    (hb : Summable (fun i => ‖b i‖ * r i ^ (-(3 / 2 : ℝ) - (n : ℝ) / 2)))
    (V : ℝ → ℂ) (X : ℝ) (hX : 0 < X) (t : ℝ) :
    smoothingIntegrand n F q V X ((-1 : ℂ) + (-t) * Complex.I) =
      (A * (Q : ℂ) ^ (n + 1) * ((q / d : ℝ) : ℂ) ^ (n + 2)) *
        ((∑' i, (b i * (r i : ℂ) ^ (-(n : ℂ) / 2)) *
            (r i : ℂ) ^ (-((3 / 2 : ℂ) + t * Complex.I))) *
          (((CubicReflectionKernel.paperScale * (27 * q ^ 2 * d ^ 2 * X / Q ^ 2) : ℝ) : ℂ) ^
            (-((3 / 2 : ℂ) + t * Complex.I)) *
              (mellin V (-((3 / 2 : ℂ) + t * Complex.I)) *
                AngularReflectionKernel.gammaMultiplier n ((3 / 2 : ℂ) + t * Complex.I)))) := by
  let s : ℂ := (-1 : ℂ) + (-t) * Complex.I
  let w : ℂ := (3 / 2 : ℂ) + t * Complex.I
  have hsre : s.re = -1 := by dsimp [s]; norm_num
  have hs : s.re - 1 / 2 - (n : ℝ) / 2 = -(3 / 2 : ℝ) - (n : ℝ) / 2 := by
    dsimp [s]
    norm_num
  have hsl : s.re < 4 / 3 + (n : ℝ) / 2 := by
    rw [hsre]
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hsw : 1 / 2 - w = s := by dsimp [s, w]; ring
  have hw : 1 / 2 - s = w := by rw [← hsw]; ring
  have hsw' : s - 1 / 2 = -w := by rw [← hsw]; ring
  have hsum : Summable (fun i => ‖b i‖ * r i ^ (s.re - 1 / 2 - (n : ℝ) / 2)) := by
    simpa only [hs] using hb
  have he := continuedDirichlet_reflection n F r hr b q d Q hd hQ A hreflect s hsl hsum
  have hp := shifted_reflection_scale n q d Q X hq hd hQ hX w
  rw [hsw] at hp
  have hsplit (i : ι) : (r i : ℂ) ^ (-w - (n : ℂ) / 2) =
      (r i : ℂ) ^ (-(n : ℂ) / 2) * (r i : ℂ) ^ (-w) := by
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (hr i).ne')]
    congr 1
    ring
  change smoothingIntegrand n F q V X s = _
  rw [smoothingIntegrand, he, hw, hsw']
  simp_rw [hsplit]
  change _ = (A * (Q : ℂ) ^ (n + 1) * ((q / d : ℝ) : ℂ) ^ (n + 2)) *
    ((∑' i, (b i * (r i : ℂ) ^ (-(n : ℂ) / 2)) * (r i : ℂ) ^ (-w)) *
      (((CubicReflectionKernel.paperScale * (27 * q ^ 2 * d ^ 2 * X / Q ^ 2) : ℝ) : ℂ) ^ (-w) *
        (mellin V (-w) * AngularReflectionKernel.gammaMultiplier n w)))
  have hsum_eq : (∑' i, b i * ((r i : ℂ) ^ (-(n : ℂ) / 2) * (r i : ℂ) ^ (-w))) =
      ∑' i, (b i * (r i : ℂ) ^ (-(n : ℂ) / 2)) * (r i : ℂ) ^ (-w) := by
    apply tsum_congr
    intro i
    ring
  rw [hsum_eq]
  calc
    _ = (A * (∑' i, (b i * (r i : ℂ) ^ (-(n : ℂ) / 2)) * (r i : ℂ) ^ (-w)) *
        mellin V (-w) * AngularReflectionKernel.gammaMultiplier n w) *
        ((Q : ℂ) ^ ((n : ℂ) + 2 - 2 * s) * reflectionFactor n q d s * (X : ℂ) ^ (-w)) := by ring
    _ = _ := by rw [hp]; ring

end OAI.CubicEisenstein.AngularShiftedBesselReflection
