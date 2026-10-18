import AngularRetainedSource
import OAI.NumberTheory.DirichletL.MeanSquare.ThetaDensity

/-! Retained and high-radial source terms assembled for the actual
truncated second source, with the angular base left explicit. -/
noncomputable section
open MeasureTheory
open scoped Classical BigOperators SchwartzMap ContDiff
namespace OAI.CubicEisenstein.AngularInitialDensity
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open SecondPassArithmetic SecondPassIntegration JointLogSeparation
open InitialMeanSquare hiding outsideCanonicalDensity HasInitialCanonicalDensityAtRadius
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)

theorem HasInitialCanonicalDensityAtRadius.nonzero_source_bound (base : ActualEisensteinCubic.O →* ℂ) (hbase : ∀ x, ‖base x‖ ≤ 1)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S) (hSp : ∀P∈S,Prime P)
    (hcan : HasInitialCanonicalDensityAtRadius base S hbad)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ,ℂ)) (a b σ ε : ℝ)
    (hU : ∀ t,g t ≠ 0 → U t=1)
    (hgs : ∀ t,g t ≠ 0 → |t| ≤ initialErrorWindow a b)
    (hσ : (1 : ℝ)/20 < σ) (hε : 0 < ε) :
    ∃ (C Cpool : ℝ) (E : ℕ),0 < C ∧ 1 ≤ Cpool ∧ 20 ≤ E ∧
      ∀ (D : ℕ) (Z : ℝ),1 ≤ Z → Cpool*Z^E ≤ D →
      let p := outsidePrime S D
      let hp := outsidePrime_ne_zero S hbad D
      let hg := outsidePrime_good S hbad D
      let hinj := outsidePrime_injective S hbad D
      letI := outsidePrime_maximal S hbad D
      let Ψ := base
      let H := Z^(1+σ)
      ‖truncatedSecondSource p hp hg hinj Finset.univ Ψ 1 1 1
        (fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V)
        W H (fun _ _ => (initialErrorCutoff a b Z H).erase 0)‖ ≤ C*H*Z^ε := by
  let η := min 1 (ε/100)
  let ν := (σ-(1 : ℝ)/20)/3
  have hη : 0 < η := lt_min zero_lt_one (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηε : 35*η ≤ ε := by
    have hh : η ≤ ε/100 := min_le_right _ _
    linarith
  have hν : 0 < ν := by dsimp [ν]; linarith
  have hσ0 : 0 ≤ σ := by linarith
  have hmargin : ν+ν ≤ σ-(1 : ℝ)/20 := by dsimp [ν]; linarith
  obtain ⟨Cl,Cpool,E,hCl,hCpool,hPE,hlow⟩ := HasInitialCanonicalDensityAtRadius.retained_source base hbase S hbad hSp hcan U hUc hUs g W
    a b σ ν ν η hU hgs hσ0 hν hη hmargin
  obtain ⟨Ch,hCh,hhigh⟩ := initial_high_radial_source U hUc hUs g W a b ν 1 η hU hgs hν hη hη1
  refine ⟨Cl+Ch,Cpool,E,by positivity,hCpool,hPE,?_⟩
  intro D Z hZ hpool
  dsimp only
  let p := outsidePrime S D
  let hp := outsidePrime_ne_zero S hbad D
  let hcop := outsidePrime_coprime S hbad D
  let hg := outsidePrime_good S hbad D
  let hinj := outsidePrime_injective S hbad D
  let := outsidePrime_maximal S hbad D
  let Ψ := base
  let H := Z^(1+σ)
  let M := initialErrorWindow a b
  let K := fun (_ _ : Finset (OutsidePrimeIndex S D)) => initialErrorCutoff a b Z H
  let Kmax := initialErrorRowBound a b Z H
  let G := fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V
  let s := fun (R : Finset (OutsidePrimeIndex S D)) (j : SecondLogIndex) =>
    initialSquarefreeSector p (secondLogSector p ∅ Finset.univ K R Z M j)
  let f := fun (ray : SecondRayIndex) (R : Finset (OutsidePrimeIndex S D)) (j : SecondLogIndex) =>
    ‖secondExpansionSource p hp hcop hg Finset.univ Ψ 1 1 1 ray (s R j) G G W H‖
  let Lsum := ∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p Finset.univ (Z*Real.exp M),
    ∑ j ∈ secondLogBinBox (Z*Real.exp M) Kmax,
      if initialRadial Z H (primeProductNorm p R) j ≤ Z^ν then f ray R j else 0
  let Hsum := ∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p Finset.univ (Z*Real.exp M),
    ∑ j ∈ secondLogBinBox (Z*Real.exp M) Kmax,
      if Z^ν < initialRadial Z H (primeProductNorm p R) j then f ray R j else 0
  have hZp := zero_lt_one.trans_le hZ
  have hH : 1 ≤ H := Real.one_le_rpow hZ (by linarith)
  have hHp := zero_lt_one.trans_le hH
  have hΨ : ∀ z,‖Ψ z‖ ≤ 1 := hbase
  have hL : Lsum ≤ Cl*H*Z^(35*η) := hlow D Z hZ hpool
  have hHi : Hsum ≤ Ch*Z^(-(1 : ℝ)) :=
    hhigh p hp hcop hg hinj (outsidePrime_odd S hbad D) (outsidePrime_primary S hbad D)
      Finset.univ Ψ 1 Z H hZ hH hΨ (fun _ R j => s R j) (fun _ _ _ => Finset.filter_subset _ _)
  have hrow : ∀ R ∈ (Finset.univ : Finset (OutsidePrimeIndex S D)).powerset,
      ∀ x ∈ secondSupportedSector p Finset.univ K R Z M,elementNorm (sourceObservation p x).1 ≤ Kmax := by
    intro R hR x hx
    exact initialErrorRowBound_valid p hp Finset.univ R a b Z H hZp hHp x hx
  have htotal := initial_nonzero_source_norm_le_squarefree_bins p hp hcop hg hinj
    (outsidePrime_odd S hbad D) (outsidePrime_primary S hbad D) Finset.univ Ψ 1 g W
    Z H M Kmax hZp hgs K hrow
  have hpart : (∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p Finset.univ (Z*Real.exp M),
      ∑ j ∈ secondLogBinBox (Z*Real.exp M) Kmax,f ray R j)=Lsum+Hsum := by
    dsimp only [Lsum,Hsum]
    simp only [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ray hray
    apply Finset.sum_congr rfl
    intro R hR
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hh : initialRadial Z H (primeProductNorm p R) j ≤ Z^ν
    · rw [ite_eq_left hh,ite_eq_right (not_lt.mpr hh),add_zero]
    · rw [ite_eq_right hh,ite_eq_left (lt_of_not_ge hh),zero_add]
  have hpower : Z^(35*η) ≤ Z^ε := Real.rpow_le_rpow_of_exponent_le hZ hηε
  have hsmall : Z^(-(1 : ℝ)) ≤ H*Z^ε := by
    have h1 : Z^(-(1 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hZ (by norm_num)
    exact h1.trans (one_le_mul_of_one_le_of_one_le hH (Real.one_le_rpow hZ hε.le))
  calc
    _ ≤ ∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p Finset.univ (Z*Real.exp M),
      ∑ j ∈ secondLogBinBox (Z*Real.exp M) Kmax,f ray R j := htotal
    _ = Lsum+Hsum := hpart
    _ ≤ Cl*H*Z^(35*η)+Ch*Z^(-(1 : ℝ)) := add_le_add hL hHi
    _ ≤ Cl*H*Z^ε+Ch*(H*Z^ε) := add_le_add
      (mul_le_mul_of_nonneg_left hpower (mul_nonneg hCl.le hHp.le))
      (mul_le_mul_of_nonneg_left hsmall hCh.le)
    _ = (Cl+Ch)*H*Z^ε := by ring

end OAI.CubicEisenstein.AngularInitialDensity
