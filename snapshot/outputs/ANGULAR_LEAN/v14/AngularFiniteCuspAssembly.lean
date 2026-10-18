import AngularPhysicalReindex

/-! Finite physical cusp assembly for the actual angular completed sum.
Only the finite residue multiplier is expanded over quotient classes.
All profile summability and smoothing-integral hypotheses are discharged
from the physical cusp data; the initial scalar is divided exactly once. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators Topology ContDiff MatrixGroups

namespace OAI.CubicEisenstein.AngularFiniteCuspAssembly

open SevenEighths.Angular CompletedGauss ConcreteTraceCRT
open AngularFiniteProjector AngularCompletedCoefficient AngularHigherProfiles
open AngularProfileDirichlet
open AngularBesselDerivatives AngularProjectedReflection AngularPhysicalSmoothedReflection
open AngularShiftedBesselReflection AngularSmoothingContour

local notation "Eis" => ActualEisensteinCubic.O
local instance : Countable Eis := ActualEisensteinCubic.latticeCoordEquiv.injective.countable

/-- A literal finite Fourier multiplier identity identifies the physical
higher-order profiles. The infinite series is interchanged only after its
summability is proved. -/
theorem finiteProjector_eq_cusp_profiles (χ : AngularCharacter) (n : ℕ)
    (c : Eis) (hc : c ≠ 0) [Fintype (Eis ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * χ.modulus)
    {ι : Type*} [Fintype ι] (d : ι → SourceCuspDatum) (w : ι → ℂ)
    (hmult : ∀ h : Eis, (∑ i, w i * ShortDraftTrace.breveE
      (-cuspFrequency h * (d i).point)) = fixedThetaTwist (finiteResidueHom χ) h)
    (v : ℝ) (hv : 0 < v) :
    finiteProjector χ n c hc v =
      ∑ i, w i * barProfile cubicSourceConjugateFunction (n + 1) (d i).point v := by
  rw [finiteProjector_fourier χ n c hc hcQ v hv]
  symm
  let term : ι → NonzeroFrequency → ℂ := fun i h =>
    conjugateBarCoefficient sourceBesselCoefficients (n + 1) (d i).point h * (v : ℂ) *
      schlafliBesselK (1/3) (4 * Real.pi * ‖cuspFrequency h.val‖ * v)
  have hsum (i : ι) : Summable (fun h => w i * term i h) :=
    (conjugate_fourier_summable sourceBesselCoefficients (n + 1) (d i).point v hv).mul_left (w i)
  calc
    _ = ∑ i, ∑' h : NonzeroFrequency, w i * term i h := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [source_conjugate_barProfile_fourier n _ v hv, ← tsum_mul_left]
    _ = ∑' h : NonzeroFrequency, ∑ i, w i * term i h :=
      (Summable.tsum_finsetSum (fun i (_ : i ∈ Finset.univ) => hsum i)).symm
    _ = ∑' h : NonzeroFrequency,
        (-2 * Real.pi * Complex.I * star (cuspFrequency h.val)) ^ (n + 1) *
          fixedThetaTwist (finiteResidueHom χ) h.val *
            star (sourceResidualFourierCoefficient h.val) * (v : ℂ) *
              schlafliBesselK (1/3) (4 * Real.pi * ‖cuspFrequency h.val‖ * v) := by
      apply tsum_congr
      intro h
      have he (i : ι) : w i * term i h =
          (w i * ShortDraftTrace.breveE (-cuspFrequency h.val * (d i).point)) *
            (-2 * Real.pi * Complex.I * star (cuspFrequency h.val)) ^ (n + 1) *
              star (sourceResidualFourierCoefficient h.val) * (v : ℂ) *
                schlafliBesselK (1/3) (4 * Real.pi * ‖cuspFrequency h.val‖ * v) := by
        simp only [term, conjugateBarCoefficient, derivativeScalar, sourceBesselCoefficients]
        ring
      simp_rw [he]
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, hmult]
      ring
    _ = _ := by
      symm
      rw [← tsum_subtype_eq_of_support_subset (s := {h : Eis | h ≠ 0}) (by
        intro h hh hz
        subst h
        exact hh (by simp [cuspFrequency]))]
      rfl

theorem smoothingIntegrand_finite_profiles (n : ℕ) (F : ℝ → ℂ)
    {ι : Type*} [Fintype ι] (d : ι → SourceCuspDatum) (w : ι → ℂ)
    (hF : ∀ v : ℝ, 0 < v → F v =
      ∑ i, w i * barProfile cubicSourceConjugateFunction (n + 1) (d i).point v)
    (V : ℝ → ℂ) (X : ℝ) (s : ℂ) :
    smoothingIntegrand n F thetaBesselScale V X s =
      ∑ i, w i * smoothingIntegrand n
        (barProfile cubicSourceConjugateFunction (n + 1) (d i).point)
          thetaBesselScale V X s := by
  have hm : mellin F (2 * s + (n : ℂ)) =
      ∑ i, w i * mellin (barProfile cubicSourceConjugateFunction (n + 1) (d i).point)
        (2 * s + (n : ℂ)) := by
    rw [mellin_eq_of_positive_eq F _ hF]
    have hi (i : ι) : IntegrableOn
        (fun v : ℝ => (v : ℂ) ^ (2 * s + (n : ℂ) - 1) *
          (w i * barProfile cubicSourceConjugateFunction (n + 1) (d i).point v)) (Ioi 0) := by
      simpa only [MellinConvergent, smul_eq_mul] using
        ((datum_mellin_entire n (d i)).1 (2 * s + (n : ℂ))).const_smul (w i)
    unfold mellin
    simp only [smul_eq_mul, Finset.mul_sum]
    rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
    apply Finset.sum_congr rfl
    intro i hi
    simpa only [mellin, smul_eq_mul] using mellin_const_smul
      (barProfile cubicSourceConjugateFunction (n + 1) (d i).point)
        (2 * s + (n : ℂ)) (w i)
  unfold smoothingIntegrand continuedDirichlet
  rw [hm]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The actual angular completed sum equals an arbitrary finite physical
cusp decomposition satisfying the literal finite residue multiplier identity.
All analytic regularity, convergence and contour-shift inputs are proved. -/
theorem completedT_of_finite_cusp_multiplier (χ : AngularCharacter) (n : ℕ)
    (hk : χ.k = -(n : ℤ)) (c : Eis) (hc : c ≠ 0)
    [Fintype (Eis ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * χ.modulus)
    {ι : Type*} [Fintype ι] (d : ι → SourceCuspDatum) (w : ι → ℂ)
    (hmult : ∀ h : Eis, (∑ i, w i * ShortDraftTrace.breveE
      (-cuspFrequency h * (d i).point)) = fixedThetaTwist (finiteResidueHom χ) h)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hWs : Function.support W ⊆ Icc a b) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0 < X) :
    completedT χ.elementHom.toMonoidHom W X =
      ∑ i, w i * (datumSmoothedDual n (d i) (Vstar W) X /
        (thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale)^n)) := by
  have hFG := finiteProjector_eq_cusp_profiles χ n c hc hcQ d w hmult
  have hVs := Vstar_support W a b hWs
  have hV := Vstar_contDiff W a b ha hWs hW
  have hi (i : ι) := datum_smoothing_integrable n (d i) (Vstar W) a b ha hVs hV X hX
  have he : (thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale)^n) *
      completedT χ.elementHom.toMonoidHom W X =
        ∑ i, w i * datumSmoothedDual n (d i) (Vstar W) X := by
    have hleft : Integrable (fun t : ℝ => smoothingIntegrand n (finiteProjector χ n c hc)
        thetaBesselScale (Vstar W) X (((-1 : ℝ) : ℂ) + t * Complex.I)) := by
      simpa only [Complex.ofReal_neg, Complex.ofReal_one] using
        finiteProjector_left_integrable χ n c hc (Vstar W) a b ha hVs hV X hX
    rw [finiteProjector_mellin_shift χ n hk c hc hcQ W a b ha hWs hW X hX
      (-1) (by norm_num) hleft]
    simp_rw [smoothingIntegrand_finite_profiles n (finiteProjector χ n c hc) d w hFG]
    rw [integral_finsetSum Finset.univ (fun i _ => by
      simpa only [Complex.ofReal_neg, Complex.ofReal_one] using (hi i).const_mul (w i)),
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi'
    rw [integral_const_mul]
    calc
      _ = w i * ((1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
        smoothingIntegrand n (barProfile cubicSourceConjugateFunction (n + 1) (d i).point)
          thetaBesselScale (Vstar W) X ((-1 : ℂ) + t * Complex.I)) := by
        simp only [Complex.ofReal_neg, Complex.ofReal_one]
        ring
      _ = _ := by rw [datum_smoothing_integral n (d i) (Vstar W) a b ha hVs hV X hX]
  have hT : thetaDerivativeScalar *
      (-2 * Real.pi * Complex.I * star thetaFrequencyScale)^n ≠ 0 :=
    mul_ne_zero thetaDerivativeScalar_ne_zero (pow_ne_zero n
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
        (star_ne_zero.mpr (norm_pos_iff.mp thetaBesselScale_pos))))
  have he' := congrArg (fun z : ℂ => z /
    (thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale)^n)) he
  rw [mul_div_cancel_left₀ _ hT, Finset.sum_div] at he'
  simpa only [mul_div_assoc] using he'

end OAI.CubicEisenstein.AngularFiniteCuspAssembly
