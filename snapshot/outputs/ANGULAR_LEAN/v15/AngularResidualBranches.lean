import AngularStratumBranches
import OAI.NumberTheory.DirichletL.GaussSum.ResidualEquivalence

/-! The actual angular stratum series after residual-label elimination.
Zero branches follow from the pinned local arithmetic, not a residue
vanishing assumption about an ordinary or metaplectic L-function. -/

noncomputable section
open scoped Classical BigOperators ContDiff MatrixGroups

namespace OAI.CubicEisenstein.AngularResidualBranches

open ActualEisensteinCubic CompletedGauss CompletedDyadic ConcreteTraceCRT
open CubicJacobiGlobal LocalReflectionBrackets AngularControlledStratum AngularStratumBranches

local notation "Eis" => ActualEisensteinCubic.O
variable {c : Eis} {h : Eis ⧸ Ideal.span {c}} (G : FixedFourierGeometry c h)
variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]
variable {p : ι → Eis} {N : Eis}

omit [Fintype α] [Fintype β] in
lemma stratumBranchTerm_residual_zero_equiv (n : ℕ) (E:α⊕β≃ι)
    (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i})
    (j:ι→ℕ) (hres:∀i:α,j (E (Sum.inl i))=1)
    (u:Eisˣ) (e:ι→Fin 3) (hbad:∃i:α,e (E (Sum.inl i))≠0)
    (W:ℝ→ℂ) (X:ℝ) (x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal) :
    stratumBranchTerm G n D hp hg j u e W X x=0 := by
  dsimp only [stratumBranchTerm,AngularRawKernel.rawDualKernelTerm,unextractedCuspCoefficient]
  rw [reflectedBranch_residual_zero_equiv E _ hg j hres e hbad,mul_zero,zero_div,zero_mul]

theorem smoothedValue_eq_nonresidual_equiv (n : ℕ) (E:α⊕β≃ι)
    (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*G.c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hp:∀i,p i≠0)
    (hcop:Pairwise (fun i k=>IsCoprime (Ideal.span {p i}) (Ideal.span {p k})))
    (hg:∀i,lambda∉Ideal.span {p i})
    (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (j:ι→ℕ) (hj:∀i,j i<6) (hres:∀i:α,j (E (Sum.inl i))=1)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hsupp:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    angularSmoothedValue n D hN hr G.primary G.shape hp G.denominator_ne_zero hg j W X=
      thetaDerivativeScalar⁻¹*fixedRadialCoefficientScalar*G.shape.stratumShapeFactor (G.c0*∏i,p i)*
        ∑'u:Eisˣ,∑e:β→Fin 3,
          let P:β→Ideal Eis:=fun i=>Ideal.span {p (E (Sum.inr i))}
          let jβ:β→ℕ:=fun i=>j (E (Sum.inr i))
          let A:=reflectionExtractedDivisor P jβ e 1
          let B:=reflectionExtractedDivisor P jβ e 2
          let hA:=reflectionExtractedDivisor_ne_zero P (fun _i=>NeZero.ne _) jβ e 1
          let hB:=reflectionExtractedDivisor_ne_zero P (fun _i=>NeZero.ne _) jβ e 2
          ∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
            stratumBranchTerm G n D hp hg j u (residualLabelVia E e) W X (nonzeroDualDilation A B hA hB x) := by
  rw [smoothedValue_eq_extracted_branch_sums G n D hN hr hp hcop hg hchar j hj W a b ha hsupp hW X hX]
  apply congrArg (fun z:ℂ=>thetaDerivativeScalar⁻¹*fixedRadialCoefficientScalar*G.shape.stratumShapeFactor (G.c0*∏i,p i)*z)
  apply tsum_congr
  intro u
  let f:(ι→Fin 3)→ℂ:=fun e=>
    ∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
      stratumBranchTerm G n D hp hg j u e W X
        (nonzeroDualDilation
          (reflectionExtractedDivisor (fun i=>Ideal.span {p i}) j e 1)
          (reflectionExtractedDivisor (fun i=>Ideal.span {p i}) j e 2)
          (reflectionExtractedDivisor_ne_zero _ (fun i=>NeZero.ne _) j e 1)
          (reflectionExtractedDivisor_ne_zero _ (fun i=>NeZero.ne _) j e 2) x)
  change (∑e,f e)=_
  have hz:∀e,(∃i:α,e (E (Sum.inl i))≠0)→f e=0 := by
    intro e he
    calc
      f e=∑'(_x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal),(0:ℂ) := by
        apply tsum_congr
        intro x
        exact stratumBranchTerm_residual_zero_equiv G n E D hp hg j hres u e he W X _
      _=0:=tsum_zero
  rw [sum_labels_drop_residual_equiv E f hz]
  apply Finset.sum_congr rfl
  intro e he
  dsimp only [f]
  apply tsum_congr
  intro x
  rw [nonzeroDualDilation_residual_equiv E _ j hres]

end OAI.CubicEisenstein.AngularResidualBranches
