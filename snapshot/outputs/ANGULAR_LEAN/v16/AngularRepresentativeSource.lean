import AngularRowSource
import OAI.NumberTheory.DirichletL.RowCompletion.ReflectedFibers

/-! Actual representative rows for angular characters, preserving the prescribed
moving ideal, finite fixed factor, all inactive Fourier weights and source strata.
The angular stratum already includes the full derivative normalization; no extra
thetaDerivativeScalar inverse is inserted outside the source sum. -/
noncomputable section
open scoped BigOperators Classical ContDiff
namespace OAI.CubicEisenstein.AngularRepresentativeSource
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion
open CanonicalRowCompletion.ActualFiber SevenEighths.Angular AngularCompletedCoefficient
local notation "Eis" => ActualEisensteinCubic.O
variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]

def sourceStratumValue (angularOrder : ℕ)
    (h:Eis⧸Ideal.span {reflectionConductor q})
    (B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)))
    (J:RowIndex q m rows R F) (W:ℝ→ℂ) (X:ℝ) : ℂ := by
  let lengthScale:Ideal Eis:=(data q m hm rows R F hF hrows v J).movingIdeal
  have hL:Supported lengthScale:=(data q m hm rows R F hF hrows v J).movingSupported
  let A:=sourcePrimeSet q hq m hm rows R F hR hF hrows v B J
  let G:=fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h
  letI : ∀P:sourcePrimeSet q hq m hm rows R F hR hF hrows v B J,
      (Ideal.span {freePrimaryPrime (data q m hm rows R F hF hrows v J).movingIdeal
        (CanonicalCoefficientClass.fixedBaseConductor q*Ideal.span {(72:Eis)}) P.val}:Ideal Eis).IsMaximal:=
    fun P=>freePrimaryPrime_maximal _ _ (data q m hm rows R F hF hrows v J).movingSupported P.val
  exact @AngularControlledStratum.angularSmoothedValue A (Finset.Subtype.fintype A)
    _ _ _ _ _ angularOrder (sourceStratum q hq m hm rows R F hR hF hrows v h B J) _
    (mul_dvd_mul_left 9 G.denominator_dvd)
    (primary_finset_product Finset.univ (fun P:A=>freePrimaryPrime lengthScale (freeConductor q) P.val)
      (fun P _=>freePrimaryPrime_primary lengthScale (freeConductor q) hL P.val))
    G.primary G.shape (fun P=>freePrimaryPrime_ne_zero lengthScale (freeConductor q) hL P.val)
    G.denominator_ne_zero (fun P=>freePrimaryPrime_good lengthScale (freeConductor q) hL P.val)
    (fun P=>(UniqueFactorizationMonoid.normalizedFactors lengthScale).count P.val.val.val%6) W X

private lemma finset_union_image_decidableEq_eq {α β : Type*} (d₁ d₂ : DecidableEq β)
    (t : Finset β) (f : α → β) (s : Finset α) :
    @Union.union (Finset β) (@Finset.instUnion β d₁) t (@Finset.image α β d₁ f s) =
      @Union.union (Finset β) (@Finset.instUnion β d₂) t (@Finset.image α β d₂ f s) := by
  cases Subsingleton.elim d₁ d₂
  rfl

theorem completedT_eq_nonresidual_source
    (χ : AngularCharacter) (angularOrder : ℕ) (hk : χ.k = -(angularOrder : ℤ))
    (hχ : CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q)
      (finiteResidueHom χ))
    (J:RowIndex q m rows R F) (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo)
    (hsupp:Function.support W⊆Set.Icc lo hi) (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    completedT (rowTwist χ.elementHom.toMonoidHom (maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
      (v.val*ConcretePrimeRowBridge.idealGenerator J.val)) W X=
      ∑h:Eis⧸Ideal.span {reflectionConductor q},
          fixedThetaRowCoeff (reflectionConductor q) (reflectionConductor_ne_zero q hq)
            ((data q m hm rows R F hF hrows v J).fixedFactor (finiteResidueHom χ) (CanonicalCoefficientClass.fixedBaseConductor q)) h*
          ∑B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)),
            FreeReflection.reflectionInactiveStratumWeight R F (maskIdeal q m F) (freeConductor q) B*
              sourceStratumValue q hq m hm rows R F hR hF hrows v angularOrder h B J W X := by
  let D:=data q m hm rows R F hF hrows v J
  let : ∀P:FreePrimeIndex D.movingIdeal (CanonicalCoefficientClass.fixedBaseConductor q*Ideal.span {(72:Eis)}),
      (Ideal.span {freePrimaryPrime D.movingIdeal
        (CanonicalCoefficientClass.fixedBaseConductor q*Ideal.span {(72:Eis)}) P}:Ideal Eis).IsMaximal:=
    freePrimaryPrime_maximal D.movingIdeal _ D.movingSupported
  let (A:Finset (FreePrimeIndex D.movingIdeal (freeConductor q))) :
      ∀P:A,(Ideal.span {freePrimaryPrime D.movingIdeal
        (CanonicalCoefficientClass.fixedBaseConductor q*Ideal.span {(72:Eis)}) P.val}:Ideal Eis).IsMaximal:=
    fun P=>freePrimaryPrime_maximal D.movingIdeal _ D.movingSupported P.val
  have hJ:J.val≠0:=hrows J.val (Finset.mem_filter.mp J.property).1
  have hz:Ideal.span {v.val*ConcretePrimeRowBridge.idealGenerator J.val}=J.val:=by
    rw [Ideal.span_singleton_mul_left_unit v.isUnit,ConcretePrimeRowBridge.span_idealGenerator]
  have parts:=representativeFiber_parts rows R (maskIdeal q m F) J
  have hsplit:splitIndex q hq m hm rows R F hR hF hrows v J=
      D.primeFiberEquiv R J.val F (freeConductor q) hR hJ hF (maskElement_ne_zero q m hm)
        (ConcretePrimeRowBridge.span_idealGenerator F) hz (mask_bad q m F)
        (residual_coprime_free_base q hq m F J.val) parts.1.symm parts.2.symm := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    apply Subtype.ext
    cases x <;> rfl
  have hml:lambda∣maskElement q m:=by
    exact ((reflectionExcludedGenerator_bad q).1).trans (dvd_mul_left _ m)
  have hm2:(2:Eis)∣maskElement q m:=by
    exact ((reflectionExcludedGenerator_bad q).2).trans (dvd_mul_left _ m)
  rw [AngularRowSource.goodMask_completedT_eq_actualControlledSource D χ angularOrder hk
    (CanonicalCoefficientClass.fixedBaseConductor q) hχ (reflectionConductor q)
    (reflectionConductor_ne_zero q hq) (reflectionConductor_ideal q)
    (fun h=>fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h)
    (maskElement_ne_zero q m hm) (ConcretePrimeRowBridge.idealGenerator_ne_zero F hF.ne_zero)
    (mul_ne_zero v.ne_zero (ConcretePrimeRowBridge.idealGenerator_ne_zero J.val hJ))
    hml hm2 W lo hi hlo hsupp hW X hX]
  unfold AngularRowSource.actualControlledSource
  apply Finset.sum_congr rfl
  intro h hh
  apply congrArg (fun z:ℂ=>fixedThetaRowCoeff (reflectionConductor q)
    (reflectionConductor_ne_zero q hq) (D.fixedFactor (finiteResidueHom χ) (CanonicalCoefficientClass.fixedBaseConductor q)) h*z)
  let weight : Finset (FreePrimeIndex D.movingIdeal (freeConductor q)) → ℂ := fun A =>
    @AngularControlledStratum.angularSmoothedValue A (Finset.Subtype.fintype A)
      _ _ _ _ _ angularOrder (D.activeStratum (CanonicalCoefficientClass.fixedBaseConductor q)
        (reflectionConductor q) (reflectionConductor_ideal q) h
        (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h) A) _
      (mul_dvd_mul_left 9 (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).denominator_dvd)
      (primary_finset_product Finset.univ (fun P:A=>freePrimaryPrime D.movingIdeal (freeConductor q) P.val)
        (fun P _=>freePrimaryPrime_primary D.movingIdeal (freeConductor q) D.movingSupported P.val))
      (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).primary
      (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).shape
      (fun P=>freePrimaryPrime_ne_zero D.movingIdeal (freeConductor q) D.movingSupported P.val)
      (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).denominator_ne_zero
      (fun P=>freePrimaryPrime_good D.movingIdeal (freeConductor q) D.movingSupported P.val)
      (fun P=>(UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val.val%6) W X
  convert D.inactive_source_reindex R J.val F (freeConductor q) hR hJ hF
    (maskElement_ne_zero q m hm) (ConcretePrimeRowBridge.span_idealGenerator F) hz
    (mask_bad q m F) (residual_coprime_free_base q hq m F J.val) parts.1.symm parts.2.symm
    weight using 1
  · apply Finset.sum_congr (by ext A; exact iff_of_true (Finset.mem_univ A) (Finset.mem_univ A))
    intro A hA
    rfl
  · apply Finset.sum_congr (by ext B; exact iff_of_true (Finset.mem_univ B) (Finset.mem_univ B))
    intro B hB
    congr 1
    calc
      sourceStratumValue q hq m hm rows R F hR hF hrows v angularOrder h B J W X=
          weight (sourcePrimeSet q hq m hm rows R F hR hF hrows v B J):=by
        rfl
      _=_:=by
        apply congrArg weight
        rw [sourcePrimeSet, completeActiveSet, hsplit]
        exact finset_union_image_decidableEq_eq _ _ _ _ _

end OAI.CubicEisenstein.AngularRepresentativeSource
