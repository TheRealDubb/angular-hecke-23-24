import AngularFiniteCuspAssembly
import AngularControlledStratum
import OAI.NumberTheory.DirichletL.GaussSum.ResidualEquivalence

/-! Actual finite active/inactive conductor-stratum assembly at every
fixed angular order. The pinned finite multiplier identity is reused;
the shifted physical profile and kernel are supplied by the new proof. -/

noncomputable section
open scoped Classical BigOperators ContDiff MatrixGroups

namespace OAI.CubicEisenstein.AngularActiveStrata

open SevenEighths.Angular ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
open CanonicalRowCompletion AngularCompletedCoefficient AngularControlledStratum

local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance fixedActiveQuotientFintype (P:Ideal Eis) [P.IsMaximal] :
    Fintype (Eis⧸P) := Fintype.ofFinite _

variable {ι:Type*} [Fintype ι] (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
variable (hp:∀i,p i≠0) (hprimary:∀i,lambda^2∣p i-1)
variable (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ)
variable (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
variable (G:∀h:Eis⧸Ideal.span {c},FixedFourierGeometry c h) (N:Eis)
variable (hN:∀h,(9:Eis)*(G h).c0∣N)
variable (D:∀h:Eis⧸Ideal.span {c},∀A:Finset ι,
  ControlledStratumArithmetic (fun i:A=>p i.val) N (G h).a0 (G h).c0 (G h).mode)

theorem completedT_fixed_active_strata (Q:Ideal Eis)
    (hcQ:Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    (φ χ:Eis→*ℂ) (hφ:CanonicalCoefficientClass.FactorsModulo Q φ)
    (hχ:∀n,χ n=finiteSexticRow (fun i=>Ideal.span {p i}) hg j n)
    (ψ : AngularCharacter) (n : ℕ) (hk : ψ.k = -(n : ℤ))
    (hψfinite : ∀ a : Eis, lambda^2 ∣ a-1 → finiteResidueHom ψ a = (φ*χ) a)
    (call:Eis) (hcall:call≠0) [Fintype (Eis⧸Ideal.span {call})]
    (hcallQ:Ideal.span {call}≤Ideal.span {(9:Eis)}*ψ.modulus)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    completedT ψ.elementHom.toMonoidHom W X=
      ∑h:Eis⧸Ideal.span {c},fixedThetaRowCoeff c hc φ h*
        ∑A:Finset ι,primeInactiveFourierWeight p hp hg j A*
          angularSmoothedValue n (D h A) (hN h)
            (primary_finset_product Finset.univ (fun i:A=>p i.val) (fun i _=>hprimary i.val))
            (G h).primary (G h).shape (fun i=>hp i.val) (G h).denominator_ne_zero
            (fun i=>hg i.val) (fun i=>j i.val) W X := by
  have hmult (a : Eis) :
      (∑ t : FixedActiveCuspIndex c p, fixedActiveCuspWeight p hp hg j c hc φ t *
        ShortDraftTrace.breveE (-cuspFrequency a *
          (fixedActiveCuspDatum p hp hprimary c G N hN D t).point)) =
        fixedThetaTwist (finiteResidueHom ψ) a := by
    rw [fixedActiveCusp_fourier_multiplier p hp hprimary hg j c hc G N hN D Q hcQ φ χ hφ hχ]
    by_cases ha : lambda^2 ∣ a-1
    · rw [fixedThetaTwist_primary _ a ha, fixedThetaTwist_primary _ a ha, hψfinite a ha]
    · rw [fixedThetaTwist_not_primary _ a ha, fixedThetaTwist_not_primary _ a ha]
  rw [AngularFiniteCuspAssembly.completedT_of_finite_cusp_multiplier ψ n hk call hcall hcallQ
    (fixedActiveCuspDatum p hp hprimary c G N hN D)
    (fixedActiveCuspWeight p hp hg j c hc φ) hmult
    W lo hi hlo hsupp hW X hX]
  simp only [FixedActiveCuspIndex,Fintype.sum_sigma,fixedActiveCuspWeight,fixedActiveCuspDatum,
    angularSmoothedValue,activeStratumDatum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro A hA
  apply Finset.sum_congr (by ext v; simp only [Finset.mem_univ])
  intro v hv
  ring

end OAI.CubicEisenstein.AngularActiveStrata
