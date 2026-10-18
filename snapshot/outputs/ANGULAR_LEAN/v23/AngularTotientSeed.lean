import AngularSixthPower

/-! A physical angular Mobius-totient seed bound, with exponent 23/24 + epsilon.
This is not the target zero-free bound. -/
noncomputable section
namespace OAI.CubicEisenstein.AngularTotientSeed
open scoped BigOperators Classical SchwartzMap ContDiff Topology
open Filter Asymptotics MeasureTheory
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O idealRowSum
open EisensteinSchwartzPoisson hiding O
open IdealMobiusDivisorSum hiding O
open ConcreteTraceCRT ShortDraftHeckeBridge
open QuadraticInitialBound hiding O
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalRowCompletion InitialMeanSquare
open SevenEighths.Angular
open AngularIdealRow (mobiusWeight)
open SixthPowerAverage hiding outside_totient_moebius_bound
  average_remainder_small_power totient_sum_normalized_bound
open AngularSixthPower

theorem outside_totient_moebius_bound 
    (χ : AngularCharacter)
    (S : Finset (Ideal ActualEisensteinCubic.O))
    (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
    (hcan : AngularInitialDensity.HasInitialCanonicalDensityAtRadius
      (conjugateMonoid χ.elementHom.toMonoidHom) S hbad)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(D : ℕ) (Z : ℝ),1≤Z → b*Z≤D →
      ‖∑I∈outsideIdealsUpTo S D,mobiusWeight χ I*W ((Ideal.absNorm I:ℝ)/Z)*totientDensity I‖≤
        C*Z^((23:ℝ)/24+ε) := by
  obtain ⟨V,hV,hVs,hV0,hVhat⟩:=exists_averaging_test
  obtain ⟨Cm,hCm,hm⟩:=AngularPoissonMoment.outside_mean_square_of_canonical_density_at_radius χ S hbad hSp hcan
    W a b ha hs hW ((1:ℝ)/10) (2*ε) (by norm_num) (by positivity)
  simp only [show (1:ℝ)+1/10=11/10 by norm_num] at hm
  obtain ⟨Ce,hCe,he⟩:=average_remainder_small_power ε hε
  have hWc : HasCompactSupport W := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hs
  let Ws : 𝓢(ℝ,ℂ):=hWc.toSchwartzMap hW
  let G : ℝ:=SchwartzMap.seminorm ℝ 0 0 Ws
  let B : ℝ:=max 1 b
  let Err : ℝ:=Ce*G*pvControl V*B^(1+ε)
  let Avg : ℝ:=Real.sqrt (768*Cm)
  let C : ℝ:=(Avg+Err)/‖paperRadialFourier V 0‖
  have hG : 0≤G:=apply_nonneg _ _
  have hB : 1≤B:=le_max_left _ _
  have hErr : 0≤Err:=mul_nonneg (mul_nonneg (mul_nonneg hCe.le hG) (pvControl_nonneg V)) (by positivity)
  have hAvg : 0<Avg:=Real.sqrt_pos.mpr (by positivity)
  have hhat : 0<‖paperRadialFourier V 0‖:=norm_pos_iff.mpr hVhat
  refine ⟨C,div_pos (by linarith) hhat,?_⟩
  intro D Z hZ hD
  have hZp : 0<Z:=by linarith
  let Y : ℝ:=Z^((11:ℝ)/60)
  have hY : 1≤Y:=Real.one_le_rpow hZ (by norm_num)
  have hYp : 0<Y:=by linarith
  let F:=outsideIdealsUpTo S D
  let A : ActualEisensteinCubic.O→ℂ:=AngularIdealRow.idealRowSum F (outsideIdealsUpTo_ne_bot S D)
    (outside_good S D hbad) χ (fun n=>W (n/Z))
  have hYpow : Y^6=Z^((11:ℝ)/10) := by
    dsimp only [Y]
    rw [←Real.rpow_mul_natCast hZp.le]
    norm_num
  have hms : (∑z∈(averagingRows Y).image (fun b=>b^6),‖A z‖^2)≤
      Cm*Z*Z^((11:ℝ)/10)*Z^(2*ε) := by
    apply hm D Z hZ hD
    · intro z hz
      have hn:=(averagingRows_power_norm Y hY hz).2
      simpa only [hYpow,show (1:ℝ)+1/10=11/10 by norm_num] using hn
    · intro z hz
      exact (averagingRows_power_norm Y hY hz).1
  have havg2:= (average_tsum_cauchy V hV hVs hV0 Y hY A).trans
    (mul_le_mul_of_nonneg_left hms (by positivity : 0≤768*Y))
  have heq : 768*Y*(Cm*Z*Z^((11:ℝ)/10)*Z^(2*ε))=
      (Avg*Z^((137:ℝ)/120+ε))^2 := by
    dsimp only [Y,Avg]
    rw [mul_pow,Real.sq_sqrt (by positivity : (0:ℝ)≤768*Cm),←Real.rpow_mul_natCast hZp.le]
    calc
      _ = (768*Cm)*(Z^((11:ℝ)/60)*Z^(1:ℝ)*Z^((11:ℝ)/10)*Z^(2*ε)) := by rw [Real.rpow_one];ring
      _ = (768*Cm)*Z^((11:ℝ)/60+1+11/10+2*ε) := by
        rw [←Real.rpow_add hZp,←Real.rpow_add hZp,←Real.rpow_add hZp]
      _ = _ := by congr 2 ; ring
  rw [heq] at havg2
  have havg : ‖∑'z : ActualEisensteinCubic.O,V (‖eisEmbedding z‖^2/Y)*A (z^6)‖≤
      Avg*Z^((137:ℝ)/120+ε) := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp havg2
  have herr : ‖∑I∈F,mobiusWeight χ I*W ((Ideal.absNorm I:ℝ)/Z)*
      maskedPrincipalRemainder (fun i : primePool F=>i.val) (idealSupport F I) V Y‖≤Err*Z^(1+ε) := by
    have hbZ : 1≤B*Z:=by nlinarith [mul_nonneg (sub_nonneg.mpr hB) (sub_nonneg.mpr hZ)]
    have hh:=he F (outsideIdealsUpTo_ne_bot S D) χ (fun n=>W (n/Z)) V Y (B*Z) G hYp hbZ hG
      (fun n=>Ws.norm_le_seminorm ℝ (n/Z)) (by
        intro I hI hn
        have hh:=(hs hn).2
        exact ((div_le_iff₀ hZp).mp hh).trans (mul_le_mul_of_nonneg_right (le_max_right 1 b) hZp.le))
    calc
      _≤Ce*G*pvControl V*(B*Z)^(1+ε):=hh
      _=Err*Z^(1+ε):=by rw [Real.mul_rpow (by linarith : 0≤B) hZp.le];dsimp only [Err];ring
  have hexponent : Z^(1+ε)≤Z^((137:ℝ)/120+ε) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hmain:=totient_sum_normalized_bound F (outsideIdealsUpTo_ne_bot S D)
    (outside_good S D hbad) χ (fun n=>W (n/Z)) V Y hYp
  have hbound : Y*‖paperRadialFourier V 0‖*
      ‖∑I∈F,mobiusWeight χ I*W ((Ideal.absNorm I:ℝ)/Z)*totientDensity I‖≤
      (Avg+Err)*Z^((137:ℝ)/120+ε) := by
    apply hmain.trans
    have := add_le_add havg (herr.trans (mul_le_mul_of_nonneg_left hexponent hErr))
    simpa only [add_mul] using this
  have hzexp : Z^((137:ℝ)/120+ε)=Y*Z^((23:ℝ)/24+ε) := by
    dsimp only [Y]
    rw [←Real.rpow_add hZp]
    congr 1
    ring
  apply (mul_le_mul_iff_right₀ (mul_pos hYp hhat)).mp
  apply hbound.trans_eq
  rw [hzexp]
  dsimp only [C]
  field_simp [hhat.ne']

theorem physical_totient_moebius_bound (χ : AngularCharacter) (angularOrder : ℕ)
    (hk : χ.k = (angularOrder : ℤ))
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (ε : ℝ) (hε : 0 < ε) :
    let S := reflectionExcludedPrimes (AngularRayOrbit.orbitConductor χ.conjugate)
    ∃ C : ℝ, 0 < C ∧ ∀ (D : ℕ) (Z : ℝ), 1 ≤ Z → b*Z ≤ D →
      ‖∑ I ∈ outsideIdealsUpTo S D,
        mobiusWeight χ I * W ((Ideal.absNorm I : ℝ)/Z) * SixthPowerAverage.totientDensity I‖
          ≤ C * Z^((23 : ℝ)/24+ε) := by
  have hkconj : χ.conjugate.k = -(angularOrder : ℤ) := by
    change -χ.k = -(angularOrder : ℤ)
    rw [hk]
  have he : χ.conjugate.elementHom.toMonoidHom = conjugateMonoid χ.elementHom.toMonoidHom := by
    ext a
    exact χ.conjugate_elementCoeff a
  have hcan := AngularInitialDensity.physical_initial_density χ.conjugate angularOrder hkconj
  rw [he] at hcan
  exact outside_totient_moebius_bound χ
    (reflectionExcludedPrimes (AngularRayOrbit.orbitConductor χ.conjugate))
    (reflectionExcludedPrimes_bad (AngularRayOrbit.orbitConductor χ.conjugate))
    (reflectionExcludedPrimes_prime (AngularRayOrbit.orbitConductor χ.conjugate))
    hcan W a b ha hs hW ε hε

end OAI.CubicEisenstein.AngularTotientSeed
