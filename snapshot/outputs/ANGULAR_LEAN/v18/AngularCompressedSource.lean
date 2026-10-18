import AngularRepresentativeSource
import AngularResidualBranches
import OAI.NumberTheory.DirichletL.RowCompletion.BranchDecoding

/-! Literal compressed angular source. The normalized strata retain exactly
one thetaDerivativeScalar inverse. The completed sum uses the full angular
character; its fixed finite coefficients use only finiteResidueHom. -/
noncomputable section
open scoped BigOperators Classical ContDiff
namespace OAI.CubicEisenstein.AngularCompressedSource
open ActualEisensteinCubic CompletedGauss CompletedDyadic CanonicalQuadraticSieve
open CubicJacobiGlobal CanonicalRowCompletion CanonicalRowCompletion.ActualFiber
open SevenEighths.Angular AngularCompletedCoefficient
local notation "Eis" => ActualEisensteinCubic.O
local instance sourceUnitsFintype : Fintype Eisˣ := by
  letI : Finite Eisˣ := PrimaryIdealUnitReindex.finite_units
  exact Fintype.ofFinite _
variable (angularOrder : ℕ) (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]

def sourceCompressedTerm
    (h:Eis⧸Ideal.span {reflectionConductor q})
    (B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)))
    (J:RowIndex q m rows R F) (u:Eisˣ) (l:B→Fin 3) (W:ℝ→ℂ) (X:ℝ) : ℂ := by
  let lengthScale:Ideal Eis:=(data q m hm rows R F hF hrows v J).movingIdeal
  have hL:Supported lengthScale:=(data q m hm rows R F hF hrows v J).movingSupported
  let A:=sourcePrimeSet q hq m hm rows R F hR hF hrows v B J
  let G:=fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h
  let E:=selectedActiveEquiv (splitIndex q hq m hm rows R F hR hF hrows v J) B
  letI : ∀P:sourcePrimeSet q hq m hm rows R F hR hF hrows v B J,
      (Ideal.span {freePrimaryPrime (data q m hm rows R F hF hrows v J).movingIdeal
        (CanonicalCoefficientClass.fixedBaseConductor q*Ideal.span {(72:Eis)}) P.val}:Ideal Eis).IsMaximal:=
    fun P=>freePrimaryPrime_maximal _ _ (data q m hm rows R F hF hrows v J).movingSupported P.val
  exact ∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
    @AngularStratumBranches.stratumBranchTerm _ _ G A (Finset.Subtype.fintype A) _ _ angularOrder
      (sourceStratum q hq m hm rows R F hR hF hrows v h B J) _
      (fun P:A=>freePrimaryPrime_ne_zero lengthScale (freeConductor q) hL P.val)
      (fun P:A=>freePrimaryPrime_good lengthScale (freeConductor q) hL P.val)
      (fun P:A=>(UniqueFactorizationMonoid.normalizedFactors lengthScale).count P.val.val.val%6)
      u (residualLabelVia E l) W X
      (nonzeroDualDilation (sourceDivisor q m R F B l 1) (sourceDivisor q m R F B l 2)
        (sourceDivisor_ne_zero q m R F B l 1) (sourceDivisor_ne_zero q m R F B l 2) x)

omit [Fintype (Eis ⧸ Ideal.span {reflectionConductor q})] in
theorem sourceStratumValue_eq_compressed
    (h:Eis⧸Ideal.span {reflectionConductor q})
    (B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)))
    (J:RowIndex q m rows R F) (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo)
    (hsupp:Function.support W⊆Set.Icc lo hi) (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    AngularRepresentativeSource.sourceStratumValue q hq m hm rows R F hR hF hrows v angularOrder h B J W X=
      thetaDerivativeScalar⁻¹*fixedRadialCoefficientScalar*
        (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).shape.stratumShapeFactor
          ((fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).c0*
            ∏P:sourcePrimeSet q hq m hm rows R F hR hF hrows v B J,
              freePrimaryPrime (data q m hm rows R F hF hrows v J).movingIdeal (freeConductor q) P.val)*
        ∑'u:Eisˣ,∑l:B→Fin 3,sourceCompressedTerm angularOrder q hq m hm rows R F hR hF hrows v h B J u l W X := by
  let lengthScale:Ideal Eis:=(data q m hm rows R F hF hrows v J).movingIdeal
  have hL:Supported lengthScale:=(data q m hm rows R F hF hrows v J).movingSupported
  let A:=sourcePrimeSet q hq m hm rows R F hR hF hrows v B J
  let p:A→Eis:=fun P=>freePrimaryPrime lengthScale (freeConductor q) P.val
  let G:=fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h
  let E:=selectedActiveEquiv (splitIndex q hq m hm rows R F hR hF hrows v J) B
  let j:A→ℕ:=fun P=>(UniqueFactorizationMonoid.normalizedFactors lengthScale).count P.val.val.val%6
  let : ∀P:sourcePrimeSet q hq m hm rows R F hR hF hrows v B J,
      (Ideal.span {freePrimaryPrime (data q m hm rows R F hF hrows v J).movingIdeal
        (CanonicalCoefficientClass.fixedBaseConductor q*Ideal.span {(72:Eis)}) P.val}:Ideal Eis).IsMaximal:=
    fun P=>freePrimaryPrime_maximal _ _ (data q m hm rows R F hF hrows v J).movingSupported P.val
  have hjres (P:PrimeIndex (rowResidualPart J.val (maskIdeal q m F))) : j (E (Sum.inl P))=1:=by
    change (UniqueFactorizationMonoid.normalizedFactors lengthScale).count
      (E (Sum.inl P)).val.val.val%6=1
    rw [selectedActiveEquiv_inl]
    exact splitIndex_local_exponent q hq m hm rows R F hR hF hrows v J (Sum.inl P)
  have hPB:(fun b:B=>Ideal.span {p (E (Sum.inr b))}:B→Ideal Eis)=(fun b=>b.val.val):=by
    funext b
    rw [show p (E (Sum.inr b))=freePrimaryPrime lengthScale (freeConductor q) (E (Sum.inr b)).val from rfl,
      freePrimaryPrime_span lengthScale (freeConductor q) hL,selectedActiveEquiv_inr]
    exact splitIndex_prime_val q hq m hm rows R F hR hF hrows v J (Sum.inr b.val)
  have hjB:(fun b:B=>j (E (Sum.inr b)))=(fun b=>completedLocalExponent R F b.val.val):=by
    funext b
    change (UniqueFactorizationMonoid.normalizedFactors lengthScale).count
      (E (Sum.inr b)).val.val.val%6=completedLocalExponent R F b.val.val
    rw [selectedActiveEquiv_inr]
    exact splitIndex_local_exponent q hq m hm rows R F hR hF hrows v J (Sum.inr b.val)
  have hdiv (l:B→Fin 3) (side:Fin 3) :
      reflectionExtractedDivisor (fun b:B=>Ideal.span {p (E (Sum.inr b))})
        (fun b:B=>j (E (Sum.inr b))) l side=sourceDivisor q m R F B l side := by
    rw [hPB,hjB]
    rfl
  have hcop:Pairwise (fun a b:A=>IsCoprime (Ideal.span {p a}) (Ideal.span {p b})):=by
    intro a b hab
    exact freePrimaryPrime_coprime lengthScale (freeConductor q) hL (fun he=>hab (Subtype.ext he))
  have he := @AngularResidualBranches.smoothedValue_eq_nonresidual_equiv _ _ G
    _ B A _ (Finset.Subtype.fintype B) (Finset.Subtype.fintype A) p _ angularOrder E
    (sourceStratum q hq m hm rows R F hR hF hrows v h B J)
    (fun P => freePrimaryPrime_maximal lengthScale (freeConductor q) hL P.val)
    (mul_dvd_mul_left 9 G.denominator_dvd)
    (primary_finset_product Finset.univ p (fun P _=>freePrimaryPrime_primary lengthScale (freeConductor q) hL P.val))
    (fun P=>freePrimaryPrime_ne_zero lengthScale (freeConductor q) hL P.val) hcop
    (fun P=>freePrimaryPrime_good lengthScale (freeConductor q) hL P.val)
    (fun P=>freePrimaryPrime_odd lengthScale (freeConductor q) hL P.val) j
    (fun _=>Nat.mod_lt _ (by decide)) hjres W lo hi hlo hsupp hW X hX
  refine he.trans ?_
  apply congrArg (fun z:ℂ=>thetaDerivativeScalar⁻¹*fixedRadialCoefficientScalar*G.shape.stratumShapeFactor (G.c0*∏P:A,p P)*z)
  apply tsum_congr
  intro u
  apply Finset.sum_congr (by ext l; simp only [Finset.mem_univ])
  intro l hl
  unfold sourceCompressedTerm
  dsimp only
  apply tsum_congr
  intro x
  congr 1
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun I:Ideal Eis=>I*x.2.1.val) (hdiv l 1)
    · apply Subtype.ext
      exact congrArg (fun I:Ideal Eis=>I*x.2.2.val) (hdiv l 2)

def compressedSourceTotal (Ψ:Eis→*ℂ)
    (J:RowIndex q m rows R F) (W:ℝ→ℂ) (X:ℝ) : ℂ :=
  ∑h:Eis⧸Ideal.span {reflectionConductor q},
    sourceFixedCoefficient q hq m hm rows R F hF hrows v Ψ h J*
    ∑B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)),
      FreeReflection.reflectionInactiveStratumWeight R F (maskIdeal q m F) (freeConductor q) B*
      sourceShapeFactor q hq m hm rows R F hR hF hrows v h B J*
      ∑u:Eisˣ,∑l:B→Fin 3,sourceCompressedTerm angularOrder q hq m hm rows R F hR hF hrows v h B J u l W X

theorem completedT_eq_compressedSourceTotal
    (χ : AngularCharacter) (hk : χ.k = -(angularOrder : ℤ))
    (hχ : CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q)
      (finiteResidueHom χ))
    (J:RowIndex q m rows R F) (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo)
    (hsupp:Function.support W⊆Set.Icc lo hi) (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    completedT (rowTwist χ.elementHom.toMonoidHom (maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
      (v.val*ConcretePrimeRowBridge.idealGenerator J.val)) W X=
      (thetaDerivativeScalar⁻¹*fixedRadialCoefficientScalar)*
        compressedSourceTotal angularOrder q hq m hm rows R F hR hF hrows v (finiteResidueHom χ) J W X := by
  rw [AngularRepresentativeSource.completedT_eq_nonresidual_source q hq m hm rows R F hR hF hrows v χ angularOrder hk hχ
    J W lo hi hlo hsupp hW X hX]
  unfold compressedSourceTotal
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  rw [mul_left_comm (thetaDerivativeScalar⁻¹*fixedRadialCoefficientScalar)]
  apply congrArg (fun z:ℂ=>sourceFixedCoefficient q hq m hm rows R F hF hrows v (finiteResidueHom χ) h J*z)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  rw [sourceStratumValue_eq_compressed angularOrder q hq m hm rows R F hR hF hrows v h B J
    W lo hi hlo hsupp hW X hX,tsum_fintype]
  change _=((thetaDerivativeScalar⁻¹*fixedRadialCoefficientScalar)*
    (FreeReflection.reflectionInactiveStratumWeight R F (maskIdeal q m F) (freeConductor q) B*
      sourceShapeFactor q hq m hm rows R F hR hF hrows v h B J*
        ∑u:Eisˣ,∑l:B→Fin 3,sourceCompressedTerm angularOrder q hq m hm rows R F hR hF hrows v h B J u l W X))
  dsimp only [sourceShapeFactor]
  ring

end OAI.CubicEisenstein.AngularCompressedSource
