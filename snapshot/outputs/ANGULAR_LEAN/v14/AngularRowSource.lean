import AngularActiveStrata
import AngularRowClosure

/-! Actual fixed/free row source for the negative-type angular family.
The finite coefficient is periodic; the complete angular coefficient is not.
All active and inactive strata and Fourier weights are retained. -/

noncomputable section
open scoped Classical BigOperators ContDiff MatrixGroups

namespace OAI.CubicEisenstein.AngularRowSource

open SevenEighths SevenEighths.Angular ActualEisensteinCubic CompletedGauss
open CanonicalQuadraticSieve CubicJacobiGlobal CanonicalRowCompletion
open AngularCompletedCoefficient AngularControlledStratum

local notation "Eis" => ActualEisensteinCubic.O

def actualControlledSource (n : ℕ) (I Q:Ideal Eis) (hI:Supported I)
    (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ:(Ideal.span {c}:Ideal Eis)=Ideal.span {(9:Eis)}*Q)
    (G:∀h:Eis⧸Ideal.span {c},FixedFourierGeometry c h)
    (φ:Eis→*ℂ) (W:ℝ→ℂ) (X:ℝ) : ℂ := by
  letI : ∀P:FreePrimeIndex I Q,(Ideal.span {freePrimaryPrime I Q P}:Ideal Eis).IsMaximal:=
    freePrimaryPrime_maximal I Q hI
  exact
    ∑h:Eis⧸Ideal.span {c},fixedThetaRowCoeff c hc φ h*
      ∑A:Finset (FreePrimeIndex I Q),
        primeInactiveFourierWeight (freePrimaryPrime I Q) (freePrimaryPrime_ne_zero I Q hI)
          (freePrimaryPrime_good I Q hI)
          (fun P=>(UniqueFactorizationMonoid.normalizedFactors I).count P.val.val%6) A*
        angularSmoothedValue n (freePrimaryControlledStratum I Q hI c hcQ h (G h) A)
          (mul_dvd_mul_left 9 (G h).denominator_dvd)
          (primary_finset_product Finset.univ (fun P:A=>freePrimaryPrime I Q P.val)
            (fun P _=>freePrimaryPrime_primary I Q hI P.val))
          (G h).primary (G h).shape (fun P=>freePrimaryPrime_ne_zero I Q hI P.val)
          (G h).denominator_ne_zero (fun P=>freePrimaryPrime_good I Q hI P.val)
          (fun P=>(UniqueFactorizationMonoid.normalizedFactors I).count P.val.val.val%6) W X

theorem fixedFree_completedT_eq_actualControlledSource (I Q:Ideal Eis) (hI:Supported I)
    (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ:(Ideal.span {c}:Ideal Eis)=Ideal.span {(9:Eis)}*Q)
    (G:∀h:Eis⧸Ideal.span {c},FixedFourierGeometry c h)
    (φ:Eis→*ℂ) (hφ:CanonicalCoefficientClass.FactorsModulo Q φ)
    (ψ : AngularCharacter) (n : ℕ) (hk : ψ.k = -(n : ℤ))
    (hψfinite : ∀ a : Eis, lambda^2 ∣ a-1 → finiteResidueHom ψ a =
      (φ*freePrimeRow I hI Q) a)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    completedT ψ.elementHom.toMonoidHom W X=actualControlledSource n I Q hI c hc hcQ G φ W X := by
  let : ∀P:FreePrimeIndex I Q,(Ideal.span {freePrimaryPrime I Q P}:Ideal Eis).IsMaximal:=
    freePrimaryPrime_maximal I Q hI
  let call:=ConcretePrimeRowBridge.idealGenerator (Ideal.span {(9:Eis)}*ψ.modulus)
  have hcall:call≠0:=by
    apply ConcretePrimeRowBridge.idealGenerator_ne_zero
    apply mul_ne_zero _ ψ.modulus_ne_bot
    simp only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot]
    norm_num
  let : Finite (Eis⧸Ideal.span {call}):=ConcreteTraceCRT.finite_quotient_span hcall
  let : Fintype (Eis⧸Ideal.span {call}):=Fintype.ofFinite _
  have hcallQ:Ideal.span {call}≤Ideal.span {(9:Eis)}*ψ.modulus:=by
    rw [ConcretePrimeRowBridge.span_idealGenerator]
  exact AngularActiveStrata.completedT_fixed_active_strata
    (freePrimaryPrime I Q) (freePrimaryPrime_ne_zero I Q hI)
    (freePrimaryPrime_primary I Q hI) (freePrimaryPrime_good I Q hI)
    (fun P=>(UniqueFactorizationMonoid.normalizedFactors I).count P.val.val%6)
    c hc G (9*c) (fun h=>mul_dvd_mul_left 9 (G h).denominator_dvd)
    (fun h A=>freePrimaryControlledStratum I Q hI c hcQ h (G h) A)
    Q hcQ.le φ (freePrimeRow I hI Q) hφ (freePrimeRow_eq_primary_family I Q hI)
    ψ n hk hψfinite call hcall hcallQ W lo hi hlo hsupp hW X hX

/-- Exact source assembly for the actual angular row twist. Its finite
fixed/free factorization and all higher-profile analytic inputs are supplied
by proved results, not additional row-model hypotheses. -/
theorem rowTwist_completedT_eq_actualControlledSource
    (χ : AngularCharacter) (n : ℕ) (hk : χ.k = -(n : ℤ))
    (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ:(Ideal.span {c}:Ideal Eis)=Ideal.span {(9:Eis)}*(χ.modulus*Ideal.span {(72:Eis)}))
    (G:∀h:Eis⧸Ideal.span {c},FixedFourierGeometry c h)
    (m f z:Eis) (hm:m≠0) (hf:f≠0) (hz:z≠0) (hmLam:lambda∣m) (hm2:(2:Eis)∣m) :
    ∃(I:Ideal Eis)(hI:Supported I)(φ:Eis→*ℂ),
      CanonicalCoefficientClass.FactorsModulo (χ.modulus*Ideal.span {(72:Eis)}) φ ∧
      (∀a,‖φ a‖≤1) ∧
      (∀h:Eis⧸Ideal.span {c},‖fixedThetaRowCoeff c hc φ h‖≤1) ∧
      ∀(W:ℝ→ℂ)(lo hi:ℝ),0<lo→Function.support W⊆Set.Icc lo hi→ContDiff ℝ ∞ W→
        ∀X:ℝ,0<X→completedT (rowTwist χ.elementHom.toMonoidHom m f z) W X=
          actualControlledSource n I (χ.modulus*Ideal.span {(72:Eis)}) hI c hc hcQ G φ W X := by
  obtain ⟨ψ,hψk,hψbound,hψ,hψres⟩ := AngularRowClosure.exists_angular_row_character
    χ m f z hm hf hz hmLam hm2
  obtain ⟨I,hI,φ,hφ,hφn,hcop,hrow⟩ := exists_actual_coprime_row
    (finiteResidueHom χ) χ.modulus (finiteResidueHom_factorsModulo χ)
      (finiteResidueHom_norm_le_one χ) m f z hm hf hz hmLam hm2
  refine ⟨I,hI,φ,hφ,hφn,fixedThetaRowCoeff_norm c hc φ hφn,?_⟩
  intro W lo hi hlo hsupp hW X hX
  have he : ψ.elementHom.toMonoidHom = rowTwist χ.elementHom.toMonoidHom m f z := by
    ext a
    exact hψ a
  rw [←he]
  apply fixedFree_completedT_eq_actualControlledSource I _ hI c hc hcQ G φ hφ
    ψ n (hψk.trans hk) _ W lo hi hlo hsupp hW X hX
  intro a ha
  rw [hψres, hrow a ha]
  rfl

/-- The same source identity for prescribed physical row data. This retains
the moving ideal and fixed factor chosen for the representative-fiber proof,
instead of replacing them by unrelated existential row data. -/
theorem goodMask_completedT_eq_actualControlledSource
    {m f z : Eis} (D : GoodMaskRowData m f z)
    (χ : AngularCharacter) (n : ℕ) (hk : χ.k = -(n : ℤ))
    (Q : Ideal Eis) (hχ : CanonicalCoefficientClass.FactorsModulo Q (finiteResidueHom χ))
    (c : Eis) (hc : c ≠ 0) [Fintype (Eis ⧸ Ideal.span {c})]
    (hcQ : (Ideal.span {c} : Ideal Eis) = Ideal.span {(9 : Eis)} * (Q * Ideal.span {(72 : Eis)}))
    (G : ∀ h : Eis ⧸ Ideal.span {c}, FixedFourierGeometry c h)
    (hm : m ≠ 0) (hf : f ≠ 0) (hz : z ≠ 0)
    (hmLam : lambda ∣ m) (hm2 : (2 : Eis) ∣ m)
    (W : ℝ → ℂ) (lo hi : ℝ) (hlo : 0 < lo)
    (hsupp : Function.support W ⊆ Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0 < X) :
    completedT (rowTwist χ.elementHom.toMonoidHom m f z) W X =
      actualControlledSource n D.movingIdeal (Q * Ideal.span {(72 : Eis)})
        D.movingSupported c hc hcQ G (D.fixedFactor (finiteResidueHom χ) Q) W X := by
  obtain ⟨ψ,hψk,hψbound,hψ,hψres⟩ := AngularRowClosure.exists_angular_row_character
    χ m f z hm hf hz hmLam hm2
  have he : ψ.elementHom.toMonoidHom = rowTwist χ.elementHom.toMonoidHom m f z := by
    ext a
    exact hψ a
  rw [←he]
  apply fixedFree_completedT_eq_actualControlledSource D.movingIdeal _ D.movingSupported
    c hc hcQ G (D.fixedFactor (finiteResidueHom χ) Q)
    (D.fixedFactor_periodic (finiteResidueHom χ) Q hχ)
    ψ n (hψk.trans hk) _ W lo hi hlo hsupp hW X hX
  intro a ha
  rw [hψres, D.row_primary (finiteResidueHom χ) Q hmLam hm2 a ha]
  rfl

end OAI.CubicEisenstein.AngularRowSource
