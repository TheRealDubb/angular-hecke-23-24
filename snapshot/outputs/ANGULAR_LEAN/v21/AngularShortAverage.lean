import AngularUniformFiberEnergy

/-! Short cubic-divisor averages for the shifted angular kernel. The geometric
short-divisor summation is reused unchanged; the model predicate and kernel
energy hypothesis are explicitly the angular ones. -/
noncomputable section
open scoped Classical BigOperators ContDiff
namespace OAI.CubicEisenstein.AngularHeight
open CompletedHeight CompletedGauss ActualEisensteinCubic CompletedDyadic
open CanonicalQuadraticSieve

theorem uniform_polynomial_short_completed_average (angularOrder : ℕ) {κ : Type*}
    (Wfamily : κ→ℝ→ℝ→ℂ) (hWfamily : HasUniformPolynomialKernel angularOrder Wfamily)
    (ε ρ q levelBound : ℝ) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃heightDegree : ℕ,∀w : κ,∃C : ℝ,0<C ∧ ∀(θ : ℝ) (rays : ℕ) (Z K X F : ℝ),1≤Z → 1≤K → 1≤F →
      F≤Z^(1/1000:ℝ) → ∀G : Ideal ActualEisensteinCubic.O,G≠0 → (∀P∈fixedBadPrimes,P∣G) →
      K*(Ideal.absNorm G:ℝ)≤X*F*Z^(-(1/40:ℝ)) →
    ∀rows : Finset (Ideal ActualEisensteinCubic.O),(∀I∈rows,I≠0 ∧ (Ideal.absNorm I:ℝ)≤K) →
    ∀Ψ : idealRange F→Ideal ActualEisensteinCubic.O→ActualEisensteinCubic.O→*ℂ,(∀f I z,‖Ψ f I z‖≤1) → ∀lengthScale : ℂ,
      (∀f : idealRange F,∀H∈shortCubeRange (Z^(1/1000:ℝ)),
        AngularDyadicModels.HasExactCompletedDyadicModels angularOrder rays rows K (X/(Ideal.absNorm H:ℝ)^3) ρ q levelBound
          f.val (G*f.val) (Wfamily w θ) (Ψ f) lengthScale) →
      (∑f : idealRange F,∑I∈rows,‖shortCompletedSum (Ψ f I) (Wfamily w θ) X (Z^(1/1000:ℝ))‖^2)/F≤
        (C*(1+‖θ‖)^heightDegree)*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm G:ℝ)*F)^ε*K*Z^ε := by
  obtain ⟨heightDegree,hheight⟩ := uniform_polynomial_mean_square_of_exact_reflection angularOrder
    Wfamily hWfamily ε ρ q levelBound hε hρ hq hlevel
  obtain ⟨Cs,hCs,hs⟩ := short_completed_normalized_small_power ε hε
  refine ⟨heightDegree,?_⟩
  intro w
  obtain ⟨Cbase,hCbase,hbase⟩ := hheight w
  refine ⟨Cs*Cbase,by positivity,?_⟩
  intro θ rays Z K X F hZ hK hF hFZ G hG hbad hmargin rows hrows Ψ hΨ lengthScale hmodels
  let Cr := Cbase*(1+‖θ‖)^heightDegree
  have hCr : 0<Cr := by dsimp [Cr]; positivity
  have hr := hbase θ
  have hG1 : 1≤(Ideal.absNorm G:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hG (Ideal.absNorm_eq_zero_iff.mp hz))
  let A : ℝ := Cr*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm G:ℝ)*F)^ε
  have hA : 0≤A := by dsimp [A]; positivity
  have hcompleted (f : idealRange F) (H : Ideal ActualEisensteinCubic.O) (hH : H∈shortCubeRange (Z^(1/1000:ℝ))) :
      (∑I : rows,‖completedT (Ψ f I.val) (Wfamily w θ) (X/(Ideal.absNorm H:ℝ)^3)‖^2)≤
        A*(K+K^2*(Ideal.absNorm G:ℝ)*(Ideal.absNorm f.val:ℝ)*(Ideal.absNorm H:ℝ)^3/X) := by
    have hf0 := (mem_idealRange.mp f.property).1.1
    have hfN := (mem_idealRange.mp f.property).2
    have hHN := (mem_shortCubeRange _ H).mp hH
    have hH1 : 1≤(Ideal.absNorm H:ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hHN.1 (Ideal.absNorm_eq_zero_iff.mp hz))
    have hH0 : (Ideal.absNorm H:ℝ)≠0 := by linarith
    have hscale := short_cube_scales Z K (Ideal.absNorm G:ℝ) X F (Ideal.absNorm H:ℝ)
      hZ hK hG1 hF hFZ hH1 hHN.2.le hmargin
    have hb := hr rays K (X/(Ideal.absNorm H:ℝ)^3) hK hscale.1 rows f.val (G*f.val)
      (mul_ne_zero hG hf0) (fun P hP => dvd_trans (hbad P hP) (dvd_mul_right G f.val))
      hrows (Ψ f) lengthScale (hmodels f H hH)
    rw [Finset.sum_coe_sort (s := rows) (f := fun I : Ideal ActualEisensteinCubic.O => ‖completedT (Ψ f I) (Wfamily w θ) (X/(Ideal.absNorm H:ℝ)^3)‖^2)]
    apply hb.trans
    simp only [map_mul,Nat.cast_mul]
    have hpow : (K*((Ideal.absNorm G:ℝ)*(Ideal.absNorm f.val:ℝ)))^ε≤
        (K*(Ideal.absNorm G:ℝ)*F)^ε := by
      apply Real.rpow_le_rpow (by positivity) _ hε.le
      have hh := mul_le_mul_of_nonneg_left hfN (show 0≤K*(Ideal.absNorm G:ℝ) by positivity)
      nlinarith
    have hshape : K+K^2*((Ideal.absNorm G:ℝ)*(Ideal.absNorm f.val:ℝ))/(X/(Ideal.absNorm H:ℝ)^3)=
        K+K^2*(Ideal.absNorm G:ℝ)*(Ideal.absNorm f.val:ℝ)*(Ideal.absNorm H:ℝ)^3/X := by
      field_simp

    rw [hshape]
    change Cr*(rays:ℝ)^2*‖lengthScale‖^2*(K*((Ideal.absNorm G:ℝ)*(Ideal.absNorm f.val:ℝ)))^ε*_≤A*_
    have hX0 : 0<X := by
      have hh := (le_div_iff₀ (show 0<(Ideal.absNorm H:ℝ)^3 by positivity)).mp hscale.1
      exact (show 0<(Ideal.absNorm H:ℝ)^3 by positivity).trans_le (by simpa only [one_mul] using hh)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity)
  have hb := hs Z K (Ideal.absNorm G:ℝ) X F A hZ hK hG1 hF hFZ hA hmargin
    (fun f (I : rows) => Ψ f I.val) (fun f I z => hΨ f I.val z) (Wfamily w θ) hcompleted
  have hsum (f : idealRange F) :
      (∑I : rows,‖shortCompletedSum (Ψ f I.val) (Wfamily w θ) X (Z^(1/1000:ℝ))‖^2)=
      ∑I∈rows,‖shortCompletedSum (Ψ f I) (Wfamily w θ) X (Z^(1/1000:ℝ))‖^2 :=
    Finset.sum_coe_sort (s := rows) (f := fun I : Ideal ActualEisensteinCubic.O => ‖shortCompletedSum (Ψ f I) (Wfamily w θ) X (Z^(1/1000:ℝ))‖^2)
  simp_rw [hsum] at hb
  apply hb.trans_eq
  dsimp [A,Cr]
  ring

theorem short_completed_average_uniform_height (angularOrder : ℕ)
    (a b : ℝ) (ha : 0<a)
    (ε ρ q levelBound : ℝ) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃heightDegree : ℕ,∀W : ℝ→ℂ, Function.support W⊆Set.Icc a b → ContDiff ℝ ∞ W → ∃C : ℝ,0<C ∧ ∀(θ : ℝ) (rays : ℕ) (Z K X F : ℝ),1≤Z → 1≤K → 1≤F →
      F≤Z^(1/1000:ℝ) → ∀G : Ideal ActualEisensteinCubic.O,G≠0 → (∀P∈fixedBadPrimes,P∣G) →
      K*(Ideal.absNorm G:ℝ)≤X*F*Z^(-(1/40:ℝ)) →
    ∀rows : Finset (Ideal ActualEisensteinCubic.O),(∀I∈rows,I≠0 ∧ (Ideal.absNorm I:ℝ)≤K) →
    ∀Ψ : idealRange F→Ideal ActualEisensteinCubic.O→ActualEisensteinCubic.O→*ℂ,(∀f I z,‖Ψ f I z‖≤1) → ∀lengthScale : ℂ,
      (∀f : idealRange F,∀H∈shortCubeRange (Z^(1/1000:ℝ)),
        AngularDyadicModels.HasExactCompletedDyadicModels angularOrder rays rows K (X/(Ideal.absNorm H:ℝ)^3) ρ q levelBound
          f.val (G*f.val) (normTwistedSource W θ) (Ψ f) lengthScale) →
      (∑f : idealRange F,∑I∈rows,‖shortCompletedSum (Ψ f I) (normTwistedSource W θ) X (Z^(1/1000:ℝ))‖^2)/F≤
        (C*(1+‖θ‖)^heightDegree)*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm G:ℝ)*F)^ε*K*Z^ε := by
  obtain ⟨n,hn⟩ := uniform_polynomial_short_completed_average angularOrder
    (fun W : SupportedSmoothSource a b => normTwistedSource W.val)
    (normTwistedSource_uniform_polynomial_kernel angularOrder a b ha)
    ε ρ q levelBound hε hρ hq hlevel
  refine ⟨n,?_⟩
  intro W hsupp hW
  exact hn ⟨W,hsupp,hW⟩


theorem short_completed_average_uniform_twist (angularOrder : ℕ)
    (a b : ℝ) (ha : 0<a)
    (ε ρ q levelBound : ℝ) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃heightDegree : ℕ,∀W : ℝ→ℂ, Function.support W⊆Set.Icc a b → ContDiff ℝ ∞ W → ∃C : ℝ,0<C ∧ ∀(θ : ℝ) (rays : ℕ) (Z K X F : ℝ),1≤Z → 1≤K → 1≤F →
      F≤Z^(1/1000:ℝ) → ∀G : Ideal ActualEisensteinCubic.O,G≠0 → (∀P∈fixedBadPrimes,P∣G) →
      K*(Ideal.absNorm G:ℝ)≤X*F*Z^(-(1/40:ℝ)) →
    ∀rows : Finset (Ideal ActualEisensteinCubic.O),(∀I∈rows,I≠0 ∧ (Ideal.absNorm I:ℝ)≤K) →
    ∀Ψ : idealRange F→Ideal ActualEisensteinCubic.O→ActualEisensteinCubic.O→*ℂ,(∀f I z,‖Ψ f I z‖≤1) → ∀lengthScale : ℂ,
      (∀f : idealRange F,∀H∈shortCubeRange (Z^(1/1000:ℝ)),
        AngularDyadicModels.HasExactCompletedDyadicModels angularOrder rays rows K (X/(Ideal.absNorm H:ℝ)^3) ρ q levelBound
          f.val (G*f.val) (normTwistedSource W θ) (Ψ f) lengthScale) →
      (∑f : idealRange F,∑I∈rows,‖shortCompletedSum (SecondPassArithmetic.normHeightTwist (Ψ f I) θ) W X (Z^(1/1000:ℝ))‖^2)/F≤
        (C*(1+‖θ‖)^heightDegree)*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm G:ℝ)*F)^ε*K*Z^ε := by
  obtain ⟨n,hn⟩ := short_completed_average_uniform_height angularOrder a b ha ε ρ q levelBound hε hρ hq hlevel
  refine ⟨n,?_⟩
  intro W hsupp hW
  obtain ⟨C,hC,h⟩ := hn W hsupp hW
  refine ⟨C,hC,?_⟩
  intro θ rays Z K X F hZ hK hF hFZ G hG hbad hmargin rows hrows Ψ hΨ lengthScale hmodel
  have hGpos : 0<(Ideal.absNorm G:ℝ) := lt_of_lt_of_le zero_lt_one (norm_at_least_one G hG)
  have hright : 0 < F*Z^(-(1/40:ℝ)) := mul_pos (lt_of_lt_of_le zero_lt_one hF)
    (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hZ) _)
  have hprod : 0 < X*(F*Z^(-(1/40:ℝ))) := by
    have hh := lt_of_lt_of_le (mul_pos (lt_of_lt_of_le zero_lt_one hK) hGpos) hmargin
    simpa only [mul_assoc] using hh
  have hX : 0<X := (mul_pos_iff_of_pos_right hright).mp hprod
  simp_rw [shortCompletedSum_normHeight_norm _ _ _ _ _ hX]
  exact h θ rays Z K X F hZ hK hF hFZ G hG hbad hmargin rows hrows Ψ hΨ lengthScale hmodel


end OAI.CubicEisenstein.AngularHeight
