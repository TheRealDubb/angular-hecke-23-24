import AngularCompletedCoefficient
import AngularProfileDirichlet

/-! Actual finite Fourier projection of every positive-order conjugate
source profile. The interchange of the finite Fourier sum with the physical
Bessel series is justified by frequency-weighted Bessel summability. Only
the finite residue character enters the quotient projector. -/

noncomputable section
open scoped Classical BigOperators

namespace OAI.CubicEisenstein.AngularFiniteProjector

open CompletedGauss ConcreteTraceCRT EisensteinEmbedding CubicJacobiGlobal
open SevenEighths.Angular AngularCompletedCoefficient AngularProfileDirichlet
open AngularBesselClosure AngularBesselDerivatives AngularHigherProfiles

local notation "Eis" => ActualEisensteinCubic.O

/-- The finite projector uses only the residue part, acting on the actual
order-(n+1) conjugate-source derivative profile. -/
def finiteProjector (χ : AngularCharacter) (n : ℕ) (c : Eis) (hc : c ≠ 0)
    [Fintype (Eis ⧸ Ideal.span {c})] (v : ℝ) : ℂ :=
  ∑ h : Eis ⧸ Ideal.span {c},
    finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient (finiteResidueHom χ) c) h *
      barProfile cubicSourceConjugateFunction (n+1) (thetaFourierTranslation c h) v

/-- A genuine summability statement for the Fourier expansion at every
fixed derivative order and positive height. -/
theorem conjugate_fourier_summable (coeff : SubexponentialBesselCoefficients)
    (j : ℕ) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    Summable (fun h : NonzeroFrequency => conjugateBarCoefficient coeff j z h * (v : ℂ) *
      schlafliBesselK (1/3) (4 * Real.pi * ‖cuspFrequency h.val‖ * v)) := by
  have hs := ((frequencyPow coeff j).summable (v,z) hv).subtype (fun h => h ≠ 0)
  apply (hs.star.mul_left ((-derivativeScalar) ^ j)).congr
  intro h
  have hx : 0 < 4 * Real.pi * ‖cuspFrequency h.val‖ * v := by
    have hf := norm_pos_iff.mpr (cuspFrequency_ne_zero h.val h.property)
    positivity
  simp only [Function.comp_apply]
  rw [(frequencyPow coeff j).term_bessel h.val h.property v hv z,
    schlafliBesselK_cubic_real _ hx]
  simp only [frequencyPow_value, conjugateBarCoefficient, star_mul, star_pow,
    breveE_star, Complex.star_def, Complex.conj_ofReal, neg_mul]
  ring

theorem source_conjugate_barProfile_fourier (n : ℕ) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    barProfile cubicSourceConjugateFunction (n+1) z v =
      ∑' h : NonzeroFrequency,
        conjugateBarCoefficient sourceBesselCoefficients (n+1) z h * (v : ℂ) *
          schlafliBesselK (1/3) (4 * Real.pi * ‖cuspFrequency h.val‖ * v) := by
  unfold cubicSourceConjugateFunction
  rw [cubicSourceResidualFunction_eq_bessel]
  exact conjugate_barProfile_full_fourier sourceBesselCoefficients _ n z v hv

/-- Finite Fourier inversion of the differentiated physical source. The
infinite sum is interchanged only after its actual summability is proved. -/
theorem finiteProjector_fourier (χ : AngularCharacter) (n : ℕ) (c : Eis) (hc : c ≠ 0)
    [Fintype (Eis ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * χ.modulus) (v : ℝ) (hv : 0 < v) :
    finiteProjector χ n c hc v = ∑' h : Eis,
      (-2 * Real.pi * Complex.I * star (cuspFrequency h)) ^ (n+1) *
        fixedThetaTwist (finiteResidueHom χ) h * star (sourceResidualFourierCoefficient h) *
          (v : ℂ) * schlafliBesselK (1/3) (4 * Real.pi * ‖cuspFrequency h‖ * v) := by
  let weight : (Eis ⧸ Ideal.span {c}) → ℂ :=
    finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient (finiteResidueHom χ) c)
  let term : (Eis ⧸ Ideal.span {c}) → NonzeroFrequency → ℂ := fun a h =>
    conjugateBarCoefficient sourceBesselCoefficients (n+1) (thetaFourierTranslation c a) h *
      (v : ℂ) * schlafliBesselK (1/3) (4 * Real.pi * ‖cuspFrequency h.val‖ * v)
  have hsum (a : Eis ⧸ Ideal.span {c}) : Summable (fun h => weight a * term a h) :=
    (conjugate_fourier_summable sourceBesselCoefficients (n+1)
      (thetaFourierTranslation c a) v hv).mul_left (weight a)
  calc
    _ = ∑ a : Eis ⧸ Ideal.span {c}, ∑' h : NonzeroFrequency, weight a * term a h := by
      unfold finiteProjector
      apply Finset.sum_congr rfl
      intro a ha
      rw [source_conjugate_barProfile_fourier n _ v hv, ← tsum_mul_left]
    _ = ∑' h : NonzeroFrequency, ∑ a : Eis ⧸ Ideal.span {c}, weight a * term a h :=
      (Summable.tsum_finsetSum (fun a (_ : a ∈ Finset.univ) => hsum a)).symm
    _ = ∑' h : NonzeroFrequency,
        (-2 * Real.pi * Complex.I * star (cuspFrequency h.val)) ^ (n+1) *
          fixedThetaTwist (finiteResidueHom χ) h.val *
            star (sourceResidualFourierCoefficient h.val) * (v : ℂ) *
              schlafliBesselK (1/3) (4 * Real.pi * ‖cuspFrequency h.val‖ * v) := by
      apply tsum_congr
      intro h
      have he (a : Eis ⧸ Ideal.span {c}) : weight a * term a h =
          (weight a * ShortDraftTrace.breveE (-cuspFrequency h.val * thetaFourierTranslation c a)) *
            (-2 * Real.pi * Complex.I * star (cuspFrequency h.val)) ^ (n+1) *
              star (sourceResidualFourierCoefficient h.val) * (v : ℂ) *
                schlafliBesselK (1/3) (4 * Real.pi * ‖cuspFrequency h.val‖ * v) := by
        simp only [term, conjugateBarCoefficient, derivativeScalar, sourceBesselCoefficients]
        ring
      simp_rw [he]
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
      have hi := thetaFourierTranslation_inversion c hc
        (fixedThetaQuotient (finiteResidueHom χ) c) h.val
      change (∑ a, weight a * ShortDraftTrace.breveE
        (-cuspFrequency h.val * thetaFourierTranslation c a)) = _ at hi
      rw [hi, fixedThetaQuotient_mk (finiteResidueHom χ) χ.modulus
        (finiteResidueHom_factorsModulo χ) c hcQ]
      ring
    _ = _ := by
      symm
      rw [← tsum_subtype_eq_of_support_subset (s := {h : Eis | h ≠ 0}) (by
        intro h hh hz
        subst h
        exact hh (by simp [cuspFrequency]))]
      rfl

/-- Actual projected profile, reindexed onto the pinned squarefree/cube
primary pairs and identified with the actual angular completed coefficient. -/
theorem finiteProjector_primary_pairs (χ : AngularCharacter) (n : ℕ)
    (hk : χ.k = -(n : ℤ)) (c : Eis) (hc : c ≠ 0)
    [Fintype (Eis ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * χ.modulus) (v : ℝ) (hv : 0 < v) :
    finiteProjector χ n c hc v =
      (thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale) ^ n) *
      ∑' p : ({I : Ideal Eis // Squarefree I ∧ primaryGenerator I ≠ 0} ×
        {J : Ideal Eis // primaryGenerator J ≠ 0}),
        completedMellinCoefficient χ.elementHom.toMonoidHom (primaryCubePairToMellinIndex p) *
          ((completedMellinLength (primaryCubePairToMellinIndex p) : ℂ) *
            (Real.sqrt (completedMellinLength (primaryCubePairToMellinIndex p)) : ℂ) ^ n) *
          (v : ℂ) * schlafliBesselK (1/3)
            (4 * Real.pi * thetaBesselScale *
              Real.sqrt (completedMellinLength (primaryCubePairToMellinIndex p)) * v) := by
  rw [finiteProjector_fourier χ n c hc hcQ v hv]
  let w : Eis → ℂ := fun h => (-2 * Real.pi * Complex.I * star (cuspFrequency h)) ^ (n+1) *
    fixedThetaTwist (finiteResidueHom χ) h * (v : ℂ) *
      schlafliBesselK (1/3) (4 * Real.pi * ‖cuspFrequency h‖ * v)
  have hw : ∀ h : Eis, w h ≠ 0 → ActualEisensteinCubic.lambda ^ 2 ∣ h - 1 := by
    intro h hwh
    by_contra hh
    exact hwh (by simp only [w, fixedThetaTwist_not_primary _ h hh, mul_zero, zero_mul])
  calc
    _ = ∑' h : Eis, w h * star (sourceResidualFourierCoefficient h) := by
      apply tsum_congr
      intro h
      dsimp only [w]
      ring
    _ = ∑' p : ({I : Ideal Eis // Squarefree I ∧ primaryGenerator I ≠ 0} ×
        {J : Ideal Eis // primaryGenerator J ≠ 0}),
        w (primaryGenerator p.1.val * (primaryGenerator p.2.val) ^ 3) *
          star (sourceResidualFourierCoefficient
            (primaryGenerator p.1.val * (primaryGenerator p.2.val) ^ 3)) :=
      sourceFourier_tsum_primary_pairs w hw
    _ = _ := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro p
      let ip := primaryCubePairToMellinIndex p
      have he := thetaPair_angular_derivative_coefficient χ n hk ip.1 ip.2
        p.1.property.2 p.2.property p.1.property.1
      have hn := thetaPair_frequency_norm ip.1 ip.2 p.1.property.2 p.2.property
      change (-2 * Real.pi * Complex.I *
          star (cuspFrequency (primaryGenerator ip.1.val * (primaryGenerator ip.2.val) ^ 3))) ^ (n+1) *
        fixedThetaTwist (finiteResidueHom χ)
          (primaryGenerator ip.1.val * (primaryGenerator ip.2.val) ^ 3) * (v : ℂ) *
          schlafliBesselK (1/3)
            (4 * Real.pi * ‖cuspFrequency (primaryGenerator ip.1.val * (primaryGenerator ip.2.val) ^ 3)‖ * v) *
        star (sourceResidualFourierCoefficient
          (primaryGenerator ip.1.val * (primaryGenerator ip.2.val) ^ 3)) =
        (thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale) ^ n) *
          (completedMellinCoefficient χ.elementHom.toMonoidHom ip *
            ((completedMellinLength ip : ℂ) * (Real.sqrt (completedMellinLength ip) : ℂ) ^ n) *
            (v : ℂ) * schlafliBesselK (1/3)
              (4 * Real.pi * thetaBesselScale * Real.sqrt (completedMellinLength ip) * v))
      rw [hn, show 4 * Real.pi * (thetaBesselScale * Real.sqrt (completedMellinLength ip)) * v =
        4 * Real.pi * thetaBesselScale * Real.sqrt (completedMellinLength ip) * v by ring]
      calc
        _ = ((-2 * Real.pi * Complex.I *
            star (cuspFrequency (primaryGenerator ip.1.val * (primaryGenerator ip.2.val) ^ 3))) ^ (n+1) *
          fixedThetaTwist (finiteResidueHom χ)
            (primaryGenerator ip.1.val * (primaryGenerator ip.2.val) ^ 3) *
          star (sourceResidualFourierCoefficient
            (primaryGenerator ip.1.val * (primaryGenerator ip.2.val) ^ 3))) *
          (v : ℂ) * schlafliBesselK (1/3)
            (4 * Real.pi * thetaBesselScale * Real.sqrt (completedMellinLength ip) * v) := by ring
        _ = _ := by rw [he]; ring

/-- The same actual profile equality over all completed Mellin indices;
the original support theorem supplies the zero coefficients off support. -/
theorem finiteProjector_completed_indices (χ : AngularCharacter) (n : ℕ)
    (hk : χ.k = -(n : ℤ)) (c : Eis) (hc : c ≠ 0)
    [Fintype (Eis ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * χ.modulus) (v : ℝ) (hv : 0 < v) :
    finiteProjector χ n c hc v =
      (thetaDerivativeScalar * (-2 * Real.pi * Complex.I * star thetaFrequencyScale) ^ n) *
      ∑' p : CompletedMellinIndex,
        completedMellinCoefficient χ.elementHom.toMonoidHom p *
          ((completedMellinLength p : ℂ) * (Real.sqrt (completedMellinLength p) : ℂ) ^ n) *
          (v : ℂ) * schlafliBesselK (1/3)
            (4 * Real.pi * thetaBesselScale * Real.sqrt (completedMellinLength p) * v) := by
  rw [finiteProjector_primary_pairs χ n hk c hc hcQ v hv]
  congr 1
  simpa only [mul_assoc] using
    (completedMellinCoefficient_tsum_primary_pairs χ.elementHom.toMonoidHom
      (fun p => ((completedMellinLength p : ℂ) * (Real.sqrt (completedMellinLength p) : ℂ) ^ n) *
        (v : ℂ) * schlafliBesselK (1/3)
          (4 * Real.pi * thetaBesselScale * Real.sqrt (completedMellinLength p) * v))).symm

end OAI.CubicEisenstein.AngularFiniteProjector
