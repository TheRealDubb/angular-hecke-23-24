import AngularBranchData
import AngularStratumBranches
import OAI.NumberTheory.DirichletL.GaussSum.ActiveReindexing

/-! Literal actual angular branch-to-model identities. Column dilation is
retained. The angular static array depends only on fixed geometry, finite
residue, unit, valuation and column ideals, with no moving-row parameter. -/
noncomputable section
open scoped BigOperators Classical ContDiff
namespace OAI.CubicEisenstein.AngularBranchRealization
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CompletedDyadic
open AngularStratumModel SevenEighths.Angular
local notation "Eis" => ActualEisensteinCubic.O
section
variable {c:Eis} {h:Eis⧸Ideal.span {c}} (G:FixedFourierGeometry c h)
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N:Eis}
theorem stratumBranchTerm_tsum_eq_rawValue_at_row (angularOrder : ℕ)
    (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ)
    {I F Q:Ideal Eis} {levelBound K:ℝ} (d:ReflectedBranchData levelBound K I F Q)
    (hK:0<completedResidualScale K I Q)
    (k:idealRange (completedResidualScale K I Q))
    (E:PrimeIndex k.val⊕d.primes≃ι)
    (hres:∀r,Ideal.span {p (E (Sum.inl r))}=r.val)
    (hnonres:∀r,Ideal.span {p (E (Sum.inr r))}=r.val)
    (hjres:∀r,j (E (Sum.inl r))=1)
    (hjnonres:∀r,j (E (Sum.inr r))=completedLocalExponent I F r.val)
    (hlevel:d.levelScale=G.levelScale) (u:Eisˣ) (W:ℝ→ℂ) (X:ℝ) :
    letI : ∀r:d.primes,r.val.IsMaximal:=d.maximal
    let A:=reflectionExtractedDivisor (fun r:d.primes=>r.val)
      (fun r=>completedLocalExponent I F r.val) d.label 1
    let B:=reflectionExtractedDivisor (fun r:d.primes=>r.val)
      (fun r=>completedLocalExponent I F r.val) d.label 2
    let hA:=reflectionExtractedDivisor_ne_zero (fun r:d.primes=>r.val) (fun _r=>NeZero.ne _)
      (fun r=>completedLocalExponent I F r.val) d.label 1
    let hB:=reflectionExtractedDivisor_ne_zero (fun r:d.primes=>r.val) (fun _r=>NeZero.ne _)
      (fun r=>completedLocalExponent I F r.val) d.label 2
    (∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
      AngularStratumBranches.stratumBranchTerm G angularOrder D hp hg j u (residualLabelVia E d.label) W X (nonzeroDualDilation A B hA hB x))=
      4*AngularBranchData.rawValue angularOrder d
        (fun m n b=>angularArray G angularOrder (Ideal.Quotient.mk _ (-(D.matrix (fun _=>1) 1 1)*D.U)) u m (A*n) (B*b))
        (fun m k'=>angularModelRowPhase G angularOrder D hp hg j u m*residualArgumentPhase k'.val 1 A B)
        W X 1 completedRamifiedStep k := by
  let : ∀r:d.primes,r.val.IsMaximal:=d.maximal
  dsimp only
  let A:=reflectionExtractedDivisor (fun r:d.primes=>r.val)
    (fun r=>completedLocalExponent I F r.val) d.label 1
  let B:=reflectionExtractedDivisor (fun r:d.primes=>r.val)
    (fun r=>completedLocalExponent I F r.val) d.label 2
  let η:=angularArray G angularOrder (Ideal.Quotient.mk _ (-(D.matrix (fun _=>1) 1 1)*D.U)) u
  let σ:=angularModelRowPhase G angularOrder D hp hg j u
  have hfull:Ideal.span {∏i,p i}=k.val*∏r:d.primes,r.val := by
    rw [FiniteGaussPhase.span_finset_prod]
    exact active_product_admissible_equiv k.val (mem_idealRange.mp k.property).1.2.1 (fun i=>Ideal.span {p i})
      (fun r:d.primes=>r.val) E hres hnonres
  have hk0:k.val≠0:=(mem_idealRange.mp k.property).1.1
  unfold AngularBranchData.rawValue
  rw [←tsum_mul_left]
  apply tsum_congr
  intro x
  have hcoef:=residual_equiv_coefficient_admissible k.val (mem_idealRange.mp k.property).1 (fun i=>Ideal.span {p i}) hg
    (fun r:d.primes=>r.val) d.good E hres hnonres j
    (fun r=>completedLocalExponent I F r.val) hjres hjnonres d.label
    1 completedRamifiedStep η σ x.1 x.2.1.val x.2.2.val
  have harg:
      (X/(G.levelScale*(Ideal.absNorm (Ideal.span {∏i,p i}):ℝ)^2))*
        (1*completedRamifiedStep^x.1)^3*(Ideal.absNorm (A*x.2.1.val):ℝ)*
        (Ideal.absNorm (B*x.2.2.val):ℝ)^3=
      ((completedBranchScale K (X/d.levelScale) I F Q (fun r:d.primes=>r.val) d.label)⁻¹*
        (completedResidualScale K I Q/(Ideal.absNorm k.val:ℝ))^2)*
        (1*completedRamifiedStep^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*
        (Ideal.absNorm x.2.2.val:ℝ)^3 := by
    rw [hlevel,completedBranchScale_raw_argument K X G.levelScale (1*completedRamifiedStep^x.1)
      I F Q (fun r:d.primes=>r.val) d.label k.val x.2.1.val x.2.2.val hK G.levelScale_pos hk0]
    rw [hfull]
    simp only [map_mul,Nat.cast_mul,mul_pow,div_eq_mul_inv,mul_inv_rev]
    ring
  dsimp only [AngularStratumBranches.stratumBranchTerm,nonzeroDualDilation,AngularRawKernel.rawDualKernelTerm]
  change unextractedCuspCoefficient (fun i=>Ideal.span {p i}) hg j (residualLabelVia E d.label)
      1 completedRamifiedStep η σ x.1 (A*x.2.1.val) (B*x.2.2.val)*_=_
  rw [hcoef,harg]
  exact mul_assoc _ _ _

end
open CompletedGauss.FreeReflection

def angularStaticPhase {c : Eis} {h : Eis ⧸ Ideal.span {c}}
    (G : FixedFourierGeometry c h) (angularOrder : ℕ) (v : G.PhaseResidue)
    (u : Eisˣ) (m : ℕ) (I J : Ideal Eis) : ℂ :=
  alpha (fixedCuspArrayIndex u m I J)^angularOrder * G.staticPhase v u m I J

theorem angularStaticPhase_norm_le_one {c : Eis} {h : Eis ⧸ Ideal.span {c}}
    (G : FixedFourierGeometry c h) (angularOrder : ℕ) (v : G.PhaseResidue)
    (u : Eisˣ) (m : ℕ) (I J : Ideal Eis) :
    ‖angularStaticPhase G angularOrder v u m I J‖ ≤ 1 := by
  rw [angularStaticPhase, norm_mul, norm_pow]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (pow_le_one₀ (norm_nonneg _) (alpha_norm_le_one _))).trans
      (G.staticPhase_norm_le_one v u m I J)

theorem angularStaticPhase_array {c : Eis} {h : Eis ⧸ Ideal.span {c}}
    (G : FixedFourierGeometry c h) (angularOrder : ℕ) (v : G.PhaseResidue)
    (u : Eisˣ) (m : ℕ) (I J : Ideal Eis) :
    fixedCuspArrayWithPhase G.shape.index u (angularStaticPhase G angularOrder v u) m I J =
      angularArray G angularOrder v u m I J := by
  simp only [fixedCuspArrayWithPhase, angularStaticPhase, angularArray, FixedFourierGeometry.array]
  ring

theorem sixPhaseFixedCuspBranch_value_eq_rawValue (angularOrder : ℕ)
    (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:pool I Q Q0→Fin 6) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hsupp:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (X ρ q:ℝ) (hX:0<X) (hρ:0<ρ) (hq:1<q)
    (hK:0<completedResidualScale K I Q)
    (k:idealRange (completedResidualScale K I Q))
    (hk:completedResidualScale K I Q/2≤(Ideal.absNorm k.val:ℝ)) :
    let d:=sixPhaseFixedCuspBranch I F Q Q0 hI hQ K levelBound levelScale hlevel hbound
      e cusp u phaseArray hphase rowPhase hrow
    AngularBranchData.value angularOrder d W X ρ q k=
      AngularBranchData.rawValue angularOrder d (d.extractedFixedCuspArrayWithPhase cusp u phaseArray) rowPhase W X ρ q k := by
  let d := sixReflectedBranch I F Q Q0 hI hQ K levelBound levelScale hlevel hbound e
    (fixedCuspArrayWithPhase cusp u phaseArray)
    (fixedCuspArrayWithPhase_norm_le_one cusp u phaseArray hphase) rowPhase hrow
  exact AngularBranchData.withCanonicalCuspArray_value angularOrder d
    (d.extractedFixedCuspArrayWithPhase cusp u phaseArray)
    (fun m n b => d.extractedFixedCuspArrayWithPhase_norm_le_one cusp u phaseArray hphase m n.val b.val)
    rowPhase hrow W a b ha hsupp hW X ρ q hX hρ hq hK k hk

theorem sixPhaseFixedCuspBranch_value_eq_geometric_rawValue (angularOrder : ℕ)
    {c:Eis} {h:Eis⧸Ideal.span {c}} (G:FixedFourierGeometry c h)
    (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound:ℝ) (hbound:G.levelScale≤levelBound)
    (e:pool I Q Q0→Fin 6) (v:G.PhaseResidue) (u:Eisˣ)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hsupp:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (X ρ q:ℝ) (hX:0<X) (hρ:0<ρ) (hq:1<q)
    (hK:0<completedResidualScale K I Q)
    (k:idealRange (completedResidualScale K I Q))
    (hk:completedResidualScale K I Q/2≤(Ideal.absNorm k.val:ℝ)) :
    let d:=sixPhaseFixedCuspBranch I F Q Q0 hI hQ K levelBound G.levelScale G.levelScale_pos hbound
      e G.shape.index u (angularStaticPhase G angularOrder v u) (angularStaticPhase_norm_le_one G angularOrder v u) rowPhase hrow
    let A:=reflectionExtractedDivisor (fun r:d.primes=>r.val)
      (fun r=>completedLocalExponent I F r.val) d.label 1
    let B:=reflectionExtractedDivisor (fun r:d.primes=>r.val)
      (fun r=>completedLocalExponent I F r.val) d.label 2
    AngularBranchData.value angularOrder d W X ρ q k=
      AngularBranchData.rawValue angularOrder d (fun m n b=>angularArray G angularOrder v u m (A*n) (B*b)) rowPhase W X ρ q k := by
  have he := sixPhaseFixedCuspBranch_value_eq_rawValue angularOrder I F Q Q0 hI hQ K levelBound
    G.levelScale G.levelScale_pos hbound e G.shape.index u (angularStaticPhase G angularOrder v u)
    (angularStaticPhase_norm_le_one G angularOrder v u) rowPhase hrow
    W a b ha hsupp hW X ρ q hX hρ hq hK k hk
  dsimp only
  apply he.trans
  apply congrArg (fun η => AngularBranchData.rawValue angularOrder
    (sixPhaseFixedCuspBranch I F Q Q0 hI hQ K levelBound G.levelScale G.levelScale_pos hbound
      e G.shape.index u (angularStaticPhase G angularOrder v u)
      (angularStaticPhase_norm_le_one G angularOrder v u) rowPhase hrow)
    η rowPhase W X ρ q k)
  funext m I J
  exact angularStaticPhase_array G angularOrder v u m _ _

end OAI.CubicEisenstein.AngularBranchRealization
