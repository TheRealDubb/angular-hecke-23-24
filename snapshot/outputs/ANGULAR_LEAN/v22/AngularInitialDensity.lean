import AngularPhysicalSieveEnergy
import OAI.NumberTheory.DirichletL.RowCompletion.InitialDensity

/-! The actual initial paired density on the original outside-prime source
arrays, generalized from norm-pullback characters to the angular base.
The original radius, pool, side orientations and support hypotheses remain. -/
noncomputable section
open MeasureTheory
open scoped Classical BigOperators SchwartzMap ContDiff
namespace OAI.CubicEisenstein.AngularInitialDensity
open ActualEisensteinCubic CanonicalRowCompletion
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open SecondPassIntegration hiding O
open InitialMeanSquare hiding O outsideCanonicalDensity HasInitialCanonicalDensityAtRadius
open CanonicalCubeSeparation
open CanonicalCoefficientClass (IsBaseRayTwist)
open FirstPassCubeLabels (primeProductNorm firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)

def outsideCanonicalDensity (base : ActualEisensteinCubic.O →* ℂ)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S) (D : ℕ)
    (ray : SecondRayIndex) (R : Finset (OutsidePrimeIndex S D))
    (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)) (V₁ V₂ : ℝ → ℂ) (X : ℝ) (J : ℕ) : ℝ :=
  letI := outsidePrime_maximal S hbad D
  densityChildEnergy (outsidePrime S D) (outsidePrime_ne_zero S hbad D)
    (outsidePrime_coprime S hbad D) (outsidePrime_good S hbad D) Finset.univ
    (secondRayMinus base ray)
    (secondRayPlus base ray)
    (primeSubsetGenerator (fun i => Ideal.span {outsidePrime S D i}) R) T V₁ V₂ X X (2*J)

def HasInitialCanonicalDensityAtRadius (base : ActualEisensteinCubic.O →* ℂ)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S) : Prop :=
  ∀ deltaLoss : ℝ,0 < deltaLoss → ∀ P : ℕ,∀ A : ℝ,0≤A → ∃ J : ℕ,
    ∀ V₁ V₂ : ℝ → ℂ,HasCompactSupport V₁ → HasCompactSupport V₂ →
    ContDiff ℝ ∞ V₁ → ContDiff ℝ ∞ V₂ →
    (∀s,V₁ s≠0→|s|≤A) → (∀s,V₂ s≠0→|s|≤A) →
    ∃ (C Cpool : ℝ) (E : ℕ),0 < C ∧ 1 ≤ Cpool ∧ P ≤ E ∧ ∀ (D : ℕ) (Z X lengthScale K : ℝ)
      (R : Finset (OutsidePrimeIndex S D)) (ray : SecondRayIndex) (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)),
      1 ≤ Z → Cpool*Z^E ≤ D → 1 ≤ X → 1 ≤ lengthScale → 1 ≤ K →
      X ≤ Z^P → lengthScale ≤ Z^P → K ≤ Z^P →
      initialExcludedNorm S*primeProductNorm (outsidePrime S D) R ≤ Z^P →
      X*lengthScale ≤ Z^2 →
      K*(initialExcludedNorm S*primeProductNorm (outsidePrime S D) R) ≤ X*lengthScale*Z^(-(1 : ℝ)/20) →
      (∀ z ∈ T,Admissible z.1 ∧ (Ideal.absNorm z.1 : ℝ) ≤ lengthScale ∧
        z.2 ≠ 0 ∧ ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ K) →
      (∀z∈T,IsCoprime z.1 (∏P∈S,P)) →
      outsideCanonicalDensity base S hbad D ray R T V₁ V₂ X J ≤ C*Z^deltaLoss*(X*lengthScale)^2

theorem hasInitialCanonicalDensityAtRadius_of_theta (angularOrder : ℕ)
    (base : ActualEisensteinCubic.O →* ℂ) (hbase : ∀ u, ‖base u‖ ≤ 1)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hSp : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (ρ q levelBound : ℝ) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound)
    (hmodels : AngularSieveModels.HasCanonicalThetaModels angularOrder S base ρ q levelBound) :
    HasInitialCanonicalDensityAtRadius base S hbad := by
  intro deltaLoss hδ P A hA
  obtain ⟨d,henergy⟩:=AngularSieveDensity.outsideLogEnergy_small_power angularOrder S hSp hbad base hbase
    ρ q levelBound hρ hq hlevel hmodels deltaLoss hδ A hA
  refine ⟨d,?_⟩
  intro V₁ V₂ hVc₁ hVc₂ hVs₁ hVs₂ hV₁ hV₂
  have hs₁ : ContDiff ℝ ∞ (orientedLogProfile true V₁):=Complex.conjCLE.contDiff.comp hVs₁
  have hb₁ : ∀s,orientedLogProfile true V₁ s≠0→|s|≤A := by
    intro s hs
    apply hV₁ s
    intro hz
    exact hs (by simp [orientedLogProfile,hz])
  obtain ⟨C₁,hC₁,he₁⟩:=henergy (orientedLogProfile true V₁) hs₁ hb₁
  obtain ⟨C₂,hC₂,he₂⟩:=henergy (orientedLogProfile false V₂) hVs₂ hV₂
  obtain ⟨A',Vmax,hA',hVmax,hbV₁,hbV₂,hsV₁,hsV₂⟩:=
    initial_two_windows_bounded V₁ V₂ hVc₁ hVc₂ hVs₁.continuous hVs₂.continuous
  obtain ⟨Z₀,hZ₀,hthreshold⟩:=canonicalInitialThreshold S
  let I₀:=∫t : ℝ,firstLogDensity 0 t
  have hI₀ : 0≤I₀:=integral_nonneg (fun t=>FirstPassCubeLabels.firstLogDensity_nonneg 0 t)
  let Ccan:=6*(C₁+C₂)*I₀^3
  let Cele:=initialElementaryConstant A' Vmax*I₀^3
  let C:=Ccan+Cele*Z₀^3+1
  have hCcan : 0≤Ccan:=by dsimp only [Ccan];positivity
  have hCele : 0≤Cele:=mul_nonneg (initialElementaryConstant_nonneg A' Vmax) (pow_nonneg hI₀ _)
  have hC : 0<C:=by dsimp only [C];positivity
  have hcanC : Ccan≤C:=by
    have hp : 0≤Cele*Z₀^3:=by positivity
    dsimp only [C]
    linarith
  have heleC : Cele*Z₀^3≤C:=by
    dsimp only [C]
    linarith
  let Cpool:=Real.exp (radiusIter A 3000)
  refine ⟨C,Cpool,max P 3,hC,Real.one_le_exp (radiusIter_nonneg A hA 3000),le_max_left _ _,?_⟩
  intro D Z X lengthScale K R ray T hZ hpool hX hL hK hXP hLP hKP hRP hmass hinv hT hout
  let p:=outsidePrime S D
  let hp:=outsidePrime_ne_zero S hbad D
  let hcop:=outsidePrime_coprime S hbad D
  let hg:=outsidePrime_good S hbad D
  let:=outsidePrime_maximal S hbad D
  let Ψ₁:=secondRayMinus base ray
  let Ψ₂:=secondRayPlus base ray
  let m:=primeSubsetGenerator (fun i=>Ideal.span {p i}) R
  let labels:=T.image Prod.fst
  have hmember : IsBaseRayTwist base base:=Or.inl rfl
  have hη : 0≤canonicalDescentPadding deltaLoss:=(canonicalDescentPadding_budget deltaLoss hδ).1.le
  have hstate₁ := initialCanonicalState S D hbad base Ψ₁ (hmember.secondMinus ray)
    Z (canonicalDescentPadding deltaLoss) X lengthScale K hZ hη hX hL hK R T hmass hinv
    (fun z hz=>⟨(hT z hz).1,(hT z hz).2.1⟩) hout
  have hstate₂ := initialCanonicalState S D hbad base Ψ₂ (hmember.secondPlus ray)
    Z (canonicalDescentPadding deltaLoss) X lengthScale K hZ hη hX hL hK R T hmass hinv
    (fun z hz=>⟨(hT z hz).1,(hT z hz).2.1⟩) hout
  have hZδ : 1≤Z^deltaLoss:=Real.one_le_rpow hZ hδ.le
  have hD : Real.exp (radiusIter A 3000)*Z^3≤D :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hZ (le_max_right P 3)) (Real.exp_pos _).le).trans hpool
  have hlabels : ∀z∈T,z.1∈labels:=fun z hz=>Finset.mem_image.mpr ⟨z,hz,rfl⟩
  have hrows : ∀z∈T,‖eisEmbedding z.2‖^2≤K:=fun z hz=>(hT z hz).2.2.2
  have hzero : ∀z∈T,z.2≠0:=fun z hz=>(hT z hz).2.2.1
  by_cases hlarge : Z₀≤Z
  · obtain ⟨hZgt,hZbig,hfixed⟩:=hthreshold Z hlarge
    have hleft (t : ℝ) : canonicalLogEnergy p hp hcop hg Finset.univ
        (normHeightTwist Ψ₁ t) m labels (orientedLogProfile true V₁) X K≤
        ((C₁+C₂)*Z^deltaLoss)*(X*lengthScale)^2*(1+‖t‖)^(2*d) := by
      have hh:=he₁ D Z Ψ₁ m labels X lengthScale K t hstate₁ hZgt hZbig hfixed hD
      change canonicalLogEnergy p hp hcop hg Finset.univ (normHeightTwist Ψ₁ t) m labels
        (orientedLogProfile true V₁) X K≤_ at hh
      apply hh.trans
      rw [Real.norm_eq_abs]
      gcongr
      · linarith
      · linarith [abs_nonneg t]
      · omega
    have hright (t : ℝ) : canonicalLogEnergy p hp hcop hg Finset.univ
        (normHeightTwist Ψ₂ t) m labels (orientedLogProfile false V₂) X K≤
        ((C₁+C₂)*Z^deltaLoss)*(X*lengthScale)^2*(1+‖t‖)^(2*d) := by
      have hh:=he₂ D Z Ψ₂ m labels X lengthScale K t hstate₂ hZgt hZbig hfixed hD
      change canonicalLogEnergy p hp hcop hg Finset.univ (normHeightTwist Ψ₂ t) m labels
        (orientedLogProfile false V₂) X K≤_ at hh
      apply hh.trans
      rw [Real.norm_eq_abs]
      gcongr
      · linarith
      · linarith [abs_nonneg t]
      · omega
    have hd:=densityChildEnergy_from_canonical_heights p hp hcop hg Finset.univ Ψ₁ Ψ₂ m T labels
      V₁ V₂ X lengthScale K ((C₁+C₂)*Z^deltaLoss) d (by linarith) (by linarith) (by positivity)
      hlabels hrows hzero hleft hright
    change outsideCanonicalDensity base S hbad D ray R T V₁ V₂ X d≤_ at hd
    have hcan : outsideCanonicalDensity base S hbad D ray R T V₁ V₂ X d≤Ccan*Z^deltaLoss*(X*lengthScale)^2 := by
      convert hd using 1 ; dsimp only [Ccan,I₀] ; ring
    exact hcan.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcanC (Real.rpow_nonneg (by linarith) _)) (sq_nonneg _))
  · have hKcap : K≤Z₀^3:=hstate₁.row_le_global.trans
      (pow_le_pow_left₀ (by linarith) (le_of_not_ge hlarge) 3)
    have hΨ₁ : ∀u,‖Ψ₁ u‖≤1:=fun u=>(secondRayMinus_norm_le base ray u).trans (hbase u)
    have hΨ₂ : ∀u,‖Ψ₂ u‖≤1:=fun u=>(secondRayPlus_norm_le base ray u).trans (hbase u)
    have hd:=initial_density_elementary_squared_mass p hp hcop hg (outsidePrime_odd S hbad D)
      (outsidePrime_injective S hbad D) Finset.univ Ψ₁ Ψ₂ hΨ₁ hΨ₂ m T V₁ V₂
      X lengthScale K A' Vmax d (by linarith) hL hK hA' hVmax hbV₁ hbV₂ hsV₁ hsV₂
      (fun z hz=>⟨(hT z hz).1.1,(hT z hz).2.1,(hT z hz).2.2.2⟩)
    change outsideCanonicalDensity base S hbad D ray R T V₁ V₂ X d≤Cele*K*(X*lengthScale)^2 at hd
    apply hd.trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact (mul_le_mul_of_nonneg_left hKcap hCele).trans
      (heleC.trans (le_mul_of_one_le_right hC.le hZδ))


theorem physical_initial_density (χ : SevenEighths.Angular.AngularCharacter) (angularOrder : ℕ)
    (hk : χ.k = -(angularOrder : ℤ)) :
    HasInitialCanonicalDensityAtRadius χ.elementHom.toMonoidHom
      (reflectionExcludedPrimes (AngularRayOrbit.orbitConductor χ))
      (reflectionExcludedPrimes_bad (AngularRayOrbit.orbitConductor χ)) := by
  exact hasInitialCanonicalDensityAtRadius_of_theta angularOrder
    χ.elementHom.toMonoidHom (fun a => χ.norm_elementCoeff_le_one a)
    (reflectionExcludedPrimes (AngularRayOrbit.orbitConductor χ))
    (reflectionExcludedPrimes_prime (AngularRayOrbit.orbitConductor χ))
    (reflectionExcludedPrimes_bad (AngularRayOrbit.orbitConductor χ))
    1 CompletedGauss.completedRamifiedStep
    (fixedCuspLevelBound (reflectionConductor (AngularRayOrbit.orbitConductor χ)))
    (by norm_num) CompletedGauss.completedRamifiedStep_gt_one
    (reflectionLevelBound_ge_one _ (AngularRayOrbit.orbitConductor_ne_zero χ))
    (AngularSieveModels.actual_canonicalThetaModels χ angularOrder hk)

end OAI.CubicEisenstein.AngularInitialDensity
