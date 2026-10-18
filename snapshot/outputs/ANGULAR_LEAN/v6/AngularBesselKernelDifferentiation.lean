import AngularBesselKernelSeries

/-!
# Joint differentiation of the actual shifted Bessel series

The real Fréchet derivative is a sum of three fixed linear maps weighted by
actual shifted/weighted series. Uniform summable bounds justify passage of
the derivative through the lattice sum on every positive-height slab.
-/

noncomputable section
open Filter Set
open scoped Classical Topology ContDiff

namespace OAI.CubicEisenstein.AngularBesselKernelDifferentiation

open AngularBesselClosure AngularBesselKernelSeries

def termFDeriv (coeff : SubexponentialBesselCoefficients) (n : ℕ)
    (h : Eis) (p : ℝ × ℂ) : (ℝ × ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.fst ℝ ℝ ℂ).smulRight
      ((4 * Real.pi : ℂ) * term (radial coeff) (n + 1) h p) +
    ((2 * Real.pi * Complex.I : ℂ) * term (frequency coeff) n h p) •
      ContinuousLinearMap.snd ℝ ℝ ℂ +
    ((2 * Real.pi * Complex.I : ℂ) * term (conjugateFrequency coeff) n h p) •
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (ContinuousLinearMap.snd ℝ ℝ ℂ))

def seriesFDeriv (coeff : SubexponentialBesselCoefficients) (n : ℕ)
    (p : ℝ × ℂ) : (ℝ × ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.fst ℝ ℝ ℂ).smulRight
      ((4 * Real.pi : ℂ) * series (radial coeff) (n + 1) p) +
    ((2 * Real.pi * Complex.I : ℂ) * series (frequency coeff) n p) •
      ContinuousLinearMap.snd ℝ ℝ ℂ +
    ((2 * Real.pi * Complex.I : ℂ) * series (conjugateFrequency coeff) n p) •
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (ContinuousLinearMap.snd ℝ ℝ ℂ))

theorem term_hasFDerivAt (coeff : SubexponentialBesselCoefficients) (n : ℕ)
    (h : Eis) (p : ℝ × ℂ) (hp : 0 < p.1) :
    HasFDerivAt (term coeff n h) (termFDeriv coeff n h p) p := by
  change HasFDerivAt (fun q : ℝ × ℂ => if h = 0 then 0 else
    coeff.value h * kernel n (4 * Real.pi * ‖cuspFrequency h‖ * q.1) *
      ShortDraftTrace.breveE (cuspFrequency h * q.2)) (termFDeriv coeff n h p) p
  by_cases hh : h = 0
  · have hz : termFDeriv coeff n h p = 0 := by
      apply ContinuousLinearMap.ext
      intro direction
      simp only [termFDeriv, term, hh, ite_true]
      change (direction.1 : ℂ) * ((4 * Real.pi : ℂ) * 0) +
        ((2 * Real.pi * Complex.I : ℂ) * 0) * direction.2 +
        ((2 * Real.pi * Complex.I : ℂ) * 0) * star direction.2 = 0
      ring
    rw [hz]
    simpa only [hh, ite_true] using (hasFDerivAt_const (𝕜 := ℝ) (0 : ℂ) p)
  have hr : 0 < ‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
  have hslope : HasDerivAt (fun y : ℝ => 4 * Real.pi * ‖cuspFrequency h‖ * y)
      (4 * Real.pi * ‖cuspFrequency h‖) p.1 := by
    simpa only [id_eq, mul_one] using
      (hasDerivAt_id p.1).const_mul (4 * Real.pi * ‖cuspFrequency h‖)
  have hk := (kernel_hasDerivAt n (4 * Real.pi * ‖cuspFrequency h‖ * p.1)
    (by positivity)).scomp p.1 hslope
  have ha : HasDerivAt
      (fun y : ℝ => coeff.value h * kernel n (4 * Real.pi * ‖cuspFrequency h‖ * y))
      (coeff.value h * (4 * Real.pi * ‖cuspFrequency h‖ : ℝ) *
        kernel (n + 1) (4 * Real.pi * ‖cuspFrequency h‖ * p.1)) p.1 := by
    convert! hk.const_mul (coeff.value h) using 1
    simp [Complex.real_smul, mul_assoc]
  have hv := ha.hasFDerivAt.comp p (hasFDerivAt_fst (𝕜 := ℝ) (p := p))
  have hz := (brevePhase_hasFDerivAt (cuspFrequency h) p.2).comp p
    (hasFDerivAt_snd (𝕜 := ℝ) (p := p))
  have hd : HasFDerivAt
      (fun q : ℝ × ℂ => (coeff.value h * kernel n (4 * Real.pi * ‖cuspFrequency h‖ * q.1)) *
        ShortDraftTrace.breveE (cuspFrequency h * q.2))
      (termFDeriv coeff n h p) p := by
    convert! hv.mul hz using 1
    apply ContinuousLinearMap.ext
    intro direction
    simp only [termFDeriv, term_radial, term_frequency, term_conjugateFrequency]
    change (direction.1 : ℂ) * ((4 * Real.pi : ℂ) *
        ((‖cuspFrequency h‖ : ℂ) * term coeff (n + 1) h p)) +
      ((2 * Real.pi * Complex.I : ℂ) * (cuspFrequency h * term coeff n h p)) * direction.2 +
      ((2 * Real.pi * Complex.I : ℂ) * (star (cuspFrequency h) * term coeff n h p)) *
        star direction.2 =
      (coeff.value h * kernel n (4 * Real.pi * ‖cuspFrequency h‖ * p.1)) *
        (ShortDraftTrace.breveE (cuspFrequency h * p.2) * horizontalPhaseCLM (cuspFrequency h) direction.2) +
      ShortDraftTrace.breveE (cuspFrequency h * p.2) *
        ((direction.1 : ℂ) * (coeff.value h * (4 * Real.pi * ‖cuspFrequency h‖ : ℝ) *
          kernel (n + 1) (4 * Real.pi * ‖cuspFrequency h‖ * p.1)))
    simp only [term, hh, ite_false, horizontalPhaseCLM_apply, horizontalPhaseMultiplier,
      map_mul, Complex.star_def]
    push_cast
    ring
  simpa only [hh, ite_false] using hd

theorem termFDeriv_norm_le (coeff : SubexponentialBesselCoefficients) (n : ℕ)
    (h : Eis) (p : ℝ × ℂ) :
    ‖termFDeriv coeff n h p‖ ≤
      (‖ContinuousLinearMap.fst ℝ ℝ ℂ‖ * ‖(4 * Real.pi : ℂ)‖) *
        ‖term (radial coeff) (n + 1) h p‖ +
      (‖(2 * Real.pi * Complex.I : ℂ)‖ * ‖ContinuousLinearMap.snd ℝ ℝ ℂ‖) *
        ‖term (frequency coeff) n h p‖ +
      (‖(2 * Real.pi * Complex.I : ℂ)‖ *
        ‖(Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (ContinuousLinearMap.snd ℝ ℝ ℂ)‖) *
        ‖term (conjugateFrequency coeff) n h p‖ := by
  unfold termFDeriv
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_add_le _ _) le_rfl).trans
  simp only [ContinuousLinearMap.norm_smulRight_apply, norm_mul, norm_smul]
  exact le_of_eq (by ring)

theorem termFDeriv_norm_bound (coeff : SubexponentialBesselCoefficients) (n : ℕ)
    (a : ℝ) (ha : 0 < a) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : Eis) (p : ℝ × ℂ), a ≤ p.1 →
      ‖termFDeriv coeff n h p‖ ≤ C * Real.exp (-(Real.pi * a / 2) * ‖cuspFrequency h‖) := by
  obtain ⟨A, hA, hAb⟩ := term_norm_bound (radial coeff) (n + 1) a ha
  obtain ⟨B, hB, hBb⟩ := term_norm_bound (frequency coeff) n a ha
  obtain ⟨C, hC, hCb⟩ := term_norm_bound (conjugateFrequency coeff) n a ha
  refine ⟨(‖ContinuousLinearMap.fst ℝ ℝ ℂ‖ * ‖(4 * Real.pi : ℂ)‖) * A +
      (‖(2 * Real.pi * Complex.I : ℂ)‖ * ‖ContinuousLinearMap.snd ℝ ℝ ℂ‖) * B +
      (‖(2 * Real.pi * Complex.I : ℂ)‖ *
        ‖(Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (ContinuousLinearMap.snd ℝ ℝ ℂ)‖) * C,
    by positivity, ?_⟩
  intro h p hp
  apply (termFDeriv_norm_le coeff n h p).trans
  calc
    _ ≤ (‖ContinuousLinearMap.fst ℝ ℝ ℂ‖ * ‖(4 * Real.pi : ℂ)‖) *
        (A * Real.exp (-(Real.pi * a / 2) * ‖cuspFrequency h‖)) +
      (‖(2 * Real.pi * Complex.I : ℂ)‖ * ‖ContinuousLinearMap.snd ℝ ℝ ℂ‖) *
        (B * Real.exp (-(Real.pi * a / 2) * ‖cuspFrequency h‖)) +
      (‖(2 * Real.pi * Complex.I : ℂ)‖ *
        ‖(Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (ContinuousLinearMap.snd ℝ ℝ ℂ)‖) *
        (C * Real.exp (-(Real.pi * a / 2) * ‖cuspFrequency h‖)) := by
      gcongr
      · exact hAb h p hp
      · exact hBb h p hp
      · exact hCb h p hp
    _ = _ := by ring

theorem termFDeriv_hasSum (coeff : SubexponentialBesselCoefficients) (n : ℕ)
    (p : ℝ × ℂ) (hp : 0 < p.1) :
    HasSum (fun h : Eis => termFDeriv coeff n h p) (seriesFDeriv coeff n p) := by
  have hr := (term_summable (radial coeff) (n + 1) p hp).hasSum.mul_left (4 * Real.pi : ℂ)
  have hz := (term_summable (frequency coeff) n p hp).hasSum.mul_left (2 * Real.pi * Complex.I : ℂ)
  have hb := (term_summable (conjugateFrequency coeff) n p hp).hasSum.mul_left
    (2 * Real.pi * Complex.I : ℂ)
  have hv := (ContinuousLinearMap.smulRightL ℝ (ℝ × ℂ) ℂ
    (ContinuousLinearMap.fst ℝ ℝ ℂ)).hasSum hr
  have hs := (hv.add (hz.smul_const (ContinuousLinearMap.snd ℝ ℝ ℂ))).add
    (hb.smul_const ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (ContinuousLinearMap.snd ℝ ℝ ℂ)))
  exact hs

theorem termFDeriv_summable (coeff : SubexponentialBesselCoefficients) (n : ℕ)
    (p : ℝ × ℂ) (hp : 0 < p.1) : Summable (fun h : Eis => termFDeriv coeff n h p) :=
  (termFDeriv_hasSum coeff n p hp).summable

theorem series_hasFDerivAt (coeff : SubexponentialBesselCoefficients) (n : ℕ)
    (p : ℝ × ℂ) (hp : 0 < p.1) :
    HasFDerivAt (series coeff n) (seriesFDeriv coeff n p) p := by
  let a := p.1 / 2
  let b := 2 * p.1
  have ha : 0 < a := by dsimp [a]; linarith
  have hap : a < p.1 := by dsimp [a]; linarith
  have hpb : p.1 < b := by dsimp [b]; linarith
  obtain ⟨C, _, hbound⟩ := termFDeriv_norm_bound coeff n a ha
  have hsum := (summable_exp_neg_cuspFrequency_norm (Real.pi * a / 2) (by positivity)).mul_left C
  let slab : Set (ℝ × ℂ) := Ioo a b ×ˢ univ
  have hslab : IsOpen slab := isOpen_Ioo.prod isOpen_univ
  have hconn : IsPreconnected slab := isPreconnected_Ioo.prod isPreconnected_univ
  have hpSlab : p ∈ slab := ⟨⟨hap, hpb⟩, mem_univ _⟩
  have h := hasFDerivAt_tsum_of_isPreconnected hsum hslab hconn
    (fun h q hq => term_hasFDerivAt coeff n h q (ha.trans hq.1.1))
    (fun h q hq => hbound h q hq.1.1.le)
    hpSlab (term_summable coeff n p hp) hpSlab
  rw [(termFDeriv_hasSum coeff n p hp).tsum_eq] at h
  exact h

theorem series_fderiv (coeff : SubexponentialBesselCoefficients) (n : ℕ)
    (p : ℝ × ℂ) (hp : 0 < p.1) :
    fderiv ℝ (series coeff n) p = seriesFDeriv coeff n p :=
  (series_hasFDerivAt coeff n p hp).fderiv

end OAI.CubicEisenstein.AngularBesselKernelDifferentiation
