import AngularIdealIndex
import AngularRawKernel
import OAI.NumberTheory.DirichletL.RowCompletion.ControlledPrimeStrata

/-! Actual angular stratum branch convergence, justified Fubini and divisor
extraction. Every shifted kernel and angular coefficient is literal. -/

noncomputable section
open scoped Classical BigOperators ContDiff MatrixGroups

namespace OAI.CubicEisenstein.AngularStratumBranches

open SevenEighths.Angular ActualEisensteinCubic CompletedGauss CompletedDyadic
open ConcreteTraceCRT CubicJacobiGlobal LocalReflectionBrackets
open AngularStratumModel AngularControlledStratum AngularIdealIndex

local notation "Eis" => ActualEisensteinCubic.O

theorem unextractedCuspCoefficient_summable (n : ℕ) {ι:Type*} [Fintype ι]
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:ι→ℕ) (e:ι→Fin 3) (ρ q:ℝ) (hρ:0<ρ) (hq:1<q)
    (η:ℕ→Ideal Eis→Ideal Eis→ℂ) (σ:ℕ→ℂ)
    (hη:∀m I J,‖η m I J‖≤1) (hσ:∀m,‖σ m‖≤1)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hsupp:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (scale:ℝ) (hscale:0<scale) :
    Summable (fun x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal=>
      ‖AngularRawKernel.rawDualKernelTerm n (Vstar W) scale ρ q (unextractedCuspCoefficient P hg j e ρ q η σ) x‖) := by
  apply AngularRawKernel.rawDualKernelTerm_summable_norm n (Vstar W) a b ha (Vstar_support W a b hsupp)
    (Vstar_contDiff W a b ha hsupp hW) scale ρ q
    ((Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 1):ℝ)*
      Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ)/
      Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ))/ρ)
    hscale hρ hq (by positivity)
  exact unextractedCuspCoefficient_norm P hg j e ρ q hρ hq.le η σ hη hσ


variable {c : Eis} {h : Eis ⧸ Ideal.span {c}} (G : FixedFourierGeometry c h)
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N : Eis}

def stratumBranchTerm (n : ℕ) (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ)
    (u:Eisˣ) (e:ι→Fin 3) (W:ℝ→ℂ) (X:ℝ)
    (x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal) : ℂ :=
  AngularRawKernel.rawDualKernelTerm n (Vstar W) (X/(G.levelScale*(Ideal.absNorm (Ideal.span {∏i,p i}):ℝ)^2))
    1 completedRamifiedStep
    (unextractedCuspCoefficient (fun i=>Ideal.span {p i}) hg j e 1 completedRamifiedStep
      (angularArray G n (Ideal.Quotient.mk _ (-(D.matrix (fun _=>1) 1 1)*D.U)) u)
      (angularModelRowPhase G n D hp hg j u)) x

theorem stratumBranchTerm_summable (n : ℕ) (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*G.c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i})
    (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2) (j:ι→ℕ) (hj:∀i,j i<6)
    (u:Eisˣ) (e:ι→Fin 3) (W:ℝ→ℂ) (a b:ℝ) (ha:0<a)
    (hsupp:Function.support W⊆Set.Icc a b) (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    Summable (fun x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal=>‖stratumBranchTerm G n D hp hg j u e W X x‖) := by
  have hn:0<(Ideal.absNorm (Ideal.span {∏i,p i}):ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz=>
      (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))
        (Ideal.span_singleton_eq_bot.mp (Ideal.absNorm_eq_zero_iff.mp hz)))
  have hlevel:=G.levelScale_pos
  apply unextractedCuspCoefficient_summable n (fun i=>Ideal.span {p i}) hg j e 1 completedRamifiedStep
    (by norm_num) completedRamifiedStep_gt_one _ _ (angularArray_norm_le_one G n _ u)
    (fun m=>(angularModelRowPhase_norm G n D hN hr G.primary hp hg hchar j hj u m).le)
    W a b ha hsupp hW _ (by positivity)

theorem stratumBranchTerm_fubini (n : ℕ) (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*G.c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i})
    (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2) (j:ι→ℕ) (hj:∀i,j i<6)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hsupp:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    (∑'t:CuspIdealIndex,∑e:ι→Fin 3,stratumBranchTerm G n D hp hg j t.1 e W X t.2)=
      ∑'u:Eisˣ,∑e:ι→Fin 3,∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
        stratumBranchTerm G n D hp hg j u e W X x := by
  let:Finite Eisˣ:=PrimaryIdealUnitReindex.finite_units
  have hs:=stratumBranchTerm_summable G n D hN hr hp hg hchar j hj
    (W:=W) (a:=a) (b:=b) (ha:=ha) (hsupp:=hsupp) (hW:=hW) (X:=X) (hX:=hX)
  have hu (u:Eisˣ):Summable (fun x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal=>
      ‖∑e:ι→Fin 3,stratumBranchTerm G n D hp hg j u e W X x‖) := by
    have hb:Summable (fun x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal=>
      ∑e:ι→Fin 3,‖stratumBranchTerm G n D hp hg j u e W X x‖) :=
      (hasSum_sum (fun e _=>(hs u e).hasSum)).summable
    exact hb.of_nonneg_of_le (fun _=>norm_nonneg _) (fun _=>norm_sum_le _ _)
  have hall:Summable (fun t:CuspIdealIndex=>
      ‖∑e:ι→Fin 3,stratumBranchTerm G n D hp hg j t.1 e W X t.2‖) :=
    (summable_prod_of_nonneg (fun _=>norm_nonneg _)).mpr ⟨hu,Summable.of_finite⟩
  rw [hall.of_norm.tsum_prod]
  apply tsum_congr
  intro u
  exact Summable.tsum_finsetSum (fun e _=>(hs u e).of_norm)

theorem reflectedValue_eq_branch_sums (n : ℕ)
    (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*G.c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i})
    (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2) (j:ι→ℕ) (hj:∀i,j i<6)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hsupp:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    angularReflectedValue n D G.shape hp G.denominator_ne_zero hg j W X=
      thetaDerivativeScalar⁻¹*fixedRadialCoefficientScalar*G.shape.stratumShapeFactor (G.c0*∏i,p i)*
        ∑'u:Eisˣ,∑e:ι→Fin 3,∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
          stratumBranchTerm G n D hp hg j u e W X x := by
  rw [angularReflectedValue_eq_ideal_series]
  apply congrArg (fun z:ℂ=>thetaDerivativeScalar⁻¹*fixedRadialCoefficientScalar*
    G.shape.stratumShapeFactor (G.c0*∏i,p i)*z)
  rw [←stratumBranchTerm_fubini G n D hN hr hp hg hchar j hj W a b ha hsupp hW X hX]
  apply tsum_congr
  intro t
  dsimp only [stratumBranchTerm,AngularRawKernel.rawDualKernelTerm,unextractedCuspCoefficient]
  simp only [Finset.mul_sum,Finset.sum_mul,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e he
  dsimp only [ramifiedScale]
  ring

theorem stratumBranchTerm_tsum_extract (n : ℕ) (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i})
    (hcop:Pairwise (fun i k=>IsCoprime (Ideal.span {p i}) (Ideal.span {p k})))
    (j:ι→ℕ) (e:ι→Fin 3) (u:Eisˣ) (W:ℝ→ℂ) (X:ℝ) :
    let A:=reflectionExtractedDivisor (fun i=>Ideal.span {p i}) j e 1
    let B:=reflectionExtractedDivisor (fun i=>Ideal.span {p i}) j e 2
    let hA:=reflectionExtractedDivisor_ne_zero (fun i=>Ideal.span {p i}) (fun _i=>NeZero.ne _) j e 1
    let hB:=reflectionExtractedDivisor_ne_zero (fun i=>Ideal.span {p i}) (fun _i=>NeZero.ne _) j e 2
    (∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,stratumBranchTerm G n D hp hg j u e W X x)=
      ∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
        stratumBranchTerm G n D hp hg j u e W X (nonzeroDualDilation A B hA hB x) := by
  dsimp only
  apply tsum_nonzeroDualDilation
  intro x hx
  dsimp only [stratumBranchTerm,AngularRawKernel.rawDualKernelTerm,unextractedCuspCoefficient] at hx
  have hnum:= (div_ne_zero_iff.mp (mul_ne_zero_iff.mp hx).1).1
  have ha : angularArray G n (Ideal.Quotient.mk _ (-(D.matrix (fun _=>1) 1 1)*D.U))
      u x.1 x.2.1.val x.2.2.val ≠ 0 :=
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hnum).1).2
  rw [angularArray] at ha
  have hpair:G.array (Ideal.Quotient.mk _ (-(D.matrix (fun _=>1) 1 1)*D.U)) u x.1 x.2.1.val x.2.2.val*
      reflectedBranch (fun i=>Ideal.span {p i}) hg j e
        (primaryGenerator x.2.1.val) (primaryGenerator x.2.2.val)≠0 :=
    mul_ne_zero (mul_ne_zero_iff.mp ha).2 (mul_ne_zero_iff.mp hnum).2
  have hs:=fixedCuspBranchNumerator_support (fun i=>Ideal.span {p i}) hg hcop j e
    G.shape.index u (G.staticPhase (Ideal.Quotient.mk _ (-(D.matrix (fun _=>1) 1 1)*D.U)) u)
    x.1 x.2.1.val x.2.2.val hpair
  exact ⟨hs.1,hs.2.1⟩

theorem smoothedValue_eq_extracted_branch_sums (n : ℕ)
    (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*G.c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hp:∀i,p i≠0)
    (hcop:Pairwise (fun i k=>IsCoprime (Ideal.span {p i}) (Ideal.span {p k})))
    (hg:∀i,lambda∉Ideal.span {p i})
    (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2) (j:ι→ℕ) (hj:∀i,j i<6)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hsupp:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    angularSmoothedValue n D hN hr G.primary G.shape hp G.denominator_ne_zero hg j W X=
      thetaDerivativeScalar⁻¹*fixedRadialCoefficientScalar*G.shape.stratumShapeFactor (G.c0*∏i,p i)*
        ∑'u:Eisˣ,∑e:ι→Fin 3,
          let A:=reflectionExtractedDivisor (fun i=>Ideal.span {p i}) j e 1
          let B:=reflectionExtractedDivisor (fun i=>Ideal.span {p i}) j e 2
          let hA:=reflectionExtractedDivisor_ne_zero (fun i=>Ideal.span {p i}) (fun _i=>NeZero.ne _) j e 1
          let hB:=reflectionExtractedDivisor_ne_zero (fun i=>Ideal.span {p i}) (fun _i=>NeZero.ne _) j e 2
          ∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
            stratumBranchTerm G n D hp hg j u e W X (nonzeroDualDilation A B hA hB x) := by
  rw [angular_smoothed_eq_reflected n D hN hr G.primary G.shape hp G.denominator_ne_zero hcop hg hchar
    j hj W a b ha hsupp hW X hX,
    reflectedValue_eq_branch_sums G n D hN hr hp hg hchar j hj W a b ha hsupp hW X hX]
  apply congrArg (fun z:ℂ=>thetaDerivativeScalar⁻¹*fixedRadialCoefficientScalar*G.shape.stratumShapeFactor (G.c0*∏i,p i)*z)
  apply tsum_congr
  intro u
  apply Finset.sum_congr rfl
  intro e he
  exact stratumBranchTerm_tsum_extract G n D hp hg hcop j e u W X

end OAI.CubicEisenstein.AngularStratumBranches
