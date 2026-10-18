import AngularDyadicEnergy
import OAI.NumberTheory.DirichletL.GaussSum.DualKernelSummability

/-! Absolute convergence and exact dyadic reindexing of the shifted raw
dual kernel. The arithmetic coefficients remain the original literal
canonical branch array. Physical angular model membership is separate. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical ContDiff

namespace OAI.CubicEisenstein.AngularRawKernel

open CompletedGauss ActualEisensteinCubic CanonicalQuadraticSieve CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O

def rawDualKernelTerm (angularOrder : ℕ) (V : ℝ→ℂ) (scale ρ q : ℝ)
    (β : ℕ→Ideal Eis→Ideal Eis→ℂ) (x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal) : ℂ :=
  β x.1 x.2.1.val x.2.2.val * AngularReflectionKernel.paperKernel angularOrder V
    (scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*(Ideal.absNorm x.2.2.val:ℝ)^3)

theorem rawDualKernelTerm_summable_norm (angularOrder : ℕ)
    (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (scale ρ q B : ℝ) (hscale : 0<scale) (hρ : 0<ρ) (hq : 1<q)
    (hB : 0≤B) (β : ℕ→Ideal Eis→Ideal Eis→ℂ)
    (hβ : ∀m,∀I J : NonzeroDualIdeal,‖β m I.val J.val‖≤B) :
    Summable (fun x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal =>
      ‖rawDualKernelTerm angularOrder V scale ρ q β x‖) := by
  obtain ⟨C,hC,hdec⟩:=AngularReflectionKernel.paperKernel_euler_power_decay angularOrder
    V a b ha hsupp hV 2 0
  have hq6 : 1<q^6 := one_lt_pow₀ hq (by norm_num)
  have hg : Summable (fun m : ℕ => ((q^6)⁻¹)^m) :=
    summable_geometric_of_lt_one (by positivity) ((inv_lt_one₀ (by positivity)).mpr hq6)
  have hi := nonzeroDualIdeal_inv_pow_summable 2 (by norm_num)
  have hj := nonzeroDualIdeal_inv_pow_summable 6 (by norm_num)
  have hij := hi.mul_of_nonneg hj (fun I=>by positivity) (fun J=>by positivity)
  have hs := hg.mul_of_nonneg hij (fun m=>by positivity) (fun IJ=>by positivity)
  have hmajor := hs.mul_left (B*C*(scale^2*ρ^6)⁻¹)
  apply hmajor.of_nonneg_of_le (fun _=>norm_nonneg _)
  intro x
  have hn:=nonzeroDualIdeal_norm_pos x.2.1
  have hb:=nonzeroDualIdeal_norm_pos x.2.2
  have hx : 0<scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*
      (Ideal.absNorm x.2.2.val:ℝ)^3 := by positivity
  have hk := (hdec _ hx).2
  simp only [LocalLogFourier.eulerDeriv,iteratedDeriv_zero,Real.exp_zero,mul_one] at hk
  norm_num only [Nat.cast_ofNat] at hk
  have hr : (scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*
      (Ideal.absNorm x.2.2.val:ℝ)^3)^(-(2:ℝ))=
      ((scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*
      (Ideal.absNorm x.2.2.val:ℝ)^3)^2)⁻¹ := by
    rw [Real.rpow_neg hx.le,Real.rpow_two]
  rw [hr,rawDualKernel_inverse_square] at hk
  calc
    _ = ‖β x.1 x.2.1.val x.2.2.val‖*
        ‖AngularReflectionKernel.paperKernel angularOrder V
          (scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*(Ideal.absNorm x.2.2.val:ℝ)^3)‖ := by
        rw [rawDualKernelTerm,norm_mul]
    _ ≤ B*(C*((scale^2*ρ^6)⁻¹*((q^6)⁻¹)^x.1 *
        (((Ideal.absNorm x.2.1.val:ℝ)^2)⁻¹*((Ideal.absNorm x.2.2.val:ℝ)^6)⁻¹))) :=
      mul_le_mul (hβ x.1 x.2.1 x.2.2) hk (norm_nonneg _) hB
    _ = _ := by ring

theorem reflectedBranchBlock_canonical (angularOrder : ℕ) {ι : Type*} [Fintype ι]
    (P : ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (W : ℝ→ℂ) (K Y ρ q : ℝ)
    (η : ℕ→Ideal Eis→Ideal Eis→ℂ) (σ : ℕ→idealRange K→ℂ)
    (i : ℕ×ℕ×ℕ) (k : idealRange K) (hK : 0<K)
    (hk : K/2≤(Ideal.absNorm k.val:ℝ)) :
    AngularDyadicEnergy.reflectedBranchBlock angularOrder P hg j e W K Y ρ q
      (fun l=>dualIdealDyad l.2.2) (fun l=>dualIdealDyad l.2.1)
      (fun l=>η l.1) (fun l=>σ l.1) i k =
    ∑n : dualIdealDyad i.2.2, ∑b : dualIdealDyad i.2.1,
      rawDualKernelTerm angularOrder (Vstar W) (Y⁻¹*(K/(Ideal.absNorm k.val:ℝ))^2) ρ q
        (canonicalRawBranchCoefficient P hg j e ρ q η (fun m=>σ m k) k.val)
        (i.1,⟨n.val,((mem_dualIdealDyad _ _).mp n.property).1⟩,
          ⟨b.val,((mem_dualIdealDyad _ _).mp b.property).1⟩) := by
  have hkm:=mem_idealRange.mp k.property
  have hwk:=completedShellWindow_log (Ideal.absNorm k.val:ℝ) K
    (nonzeroDualIdeal_norm_pos ⟨k.val,hkm.1.1⟩) hK hk hkm.2
  simp only [AngularDyadicEnergy.reflectedBranchBlock,AngularDyadicEnergy.completedSmoothDyadicBlock,Finset.mul_sum]
  rw [←Finset.sum_coe_sort (dualIdealDyad i.2.2)]
  apply Finset.sum_congr rfl
  intro n _
  rw [←Finset.sum_coe_sort (dualIdealDyad i.2.1)]
  apply Finset.sum_congr rfl
  intro b _
  have hn:=dualIdealDyad_bounds _ n.val n.property
  have hb:=dualIdealDyad_bounds _ b.val b.property
  have hwn:=completedShellWindow_log (Ideal.absNorm n.val:ℝ) ((2:ℝ)^i.2.2)
    (nonzeroDualIdeal_norm_pos ⟨n.val,hn.1⟩) (by positivity) hn.2.1 hn.2.2
  have hwb:=completedShellWindow_log (Ideal.absNorm b.val:ℝ) ((2:ℝ)^i.2.1)
    (nonzeroDualIdeal_norm_pos ⟨b.val,hb.1⟩) (by positivity) hb.2.1 hb.2.2
  rw [hwk,hwn,hwb,canonical_dual_kernel_argument K Y ρ q i k.val n.val b.val hK hkm.1.1 hn.1 hb.1]
  simp only [rawDualKernelTerm,canonicalRawBranchCoefficient]
  ring

theorem canonicalRawBranch_summable_norm (angularOrder : ℕ) {ι : Type*} [Fintype ι]
    (P : ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (K Y ρ q : ℝ) (hK : 0<K) (hY : 0<Y) (hρ : 0<ρ) (hq : 1<q)
    (η : ℕ→Ideal Eis→Ideal Eis→ℂ) (σ : ℕ→ℂ)
    (hη : ∀m,∀n b : NonzeroDualIdeal,‖η m n.val b.val‖≤1)
    (hσ : ∀m,‖σ m‖≤1) (k : Ideal Eis) (hk : k≠0) :
    Summable (fun x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal =>
      ‖rawDualKernelTerm angularOrder (Vstar W) (Y⁻¹*(K/(Ideal.absNorm k:ℝ))^2) ρ q
        (canonicalRawBranchCoefficient P hg j e ρ q η σ k) x‖) := by
  have hkn:=nonzeroDualIdeal_norm_pos ⟨k,hk⟩
  exact rawDualKernelTerm_summable_norm angularOrder (Vstar W) a b ha (Vstar_support W a b hsupp)
    (Vstar_contDiff W a b ha hsupp hW) _ ρ q (1/ρ) (by positivity) hρ hq (by positivity)
    _ (fun m n b=>canonicalRawBranchCoefficient_norm P hg j e ρ q hρ hq.le η σ hη hσ k m n b)

theorem canonical_reflected_series (angularOrder : ℕ) {ι : Type*} [Fintype ι]
    (P : ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (K Y ρ q : ℝ) (hK : 0<K) (hY : 0<Y) (hρ : 0<ρ) (hq : 1<q)
    (η : ℕ→Ideal Eis→Ideal Eis→ℂ) (σ : ℕ→idealRange K→ℂ)
    (hη : ∀m,∀n b : NonzeroDualIdeal,‖η m n.val b.val‖≤1)
    (hσ : ∀m k,‖σ m k‖≤1) (k : idealRange K)
    (hk : K/2≤(Ideal.absNorm k.val:ℝ)) :
    (∑'i : ℕ×ℕ×ℕ, AngularDyadicEnergy.reflectedBranchBlock angularOrder P hg j e W K Y ρ q
      (fun l=>dualIdealDyad l.2.2) (fun l=>dualIdealDyad l.2.1)
      (fun l=>η l.1) (fun l=>σ l.1) i k) =
    ∑'x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
      rawDualKernelTerm angularOrder (Vstar W) (Y⁻¹*(K/(Ideal.absNorm k.val:ℝ))^2) ρ q
        (canonicalRawBranchCoefficient P hg j e ρ q η (fun m=>σ m k) k.val) x := by
  have hs:=canonicalRawBranch_summable_norm angularOrder P hg j e W a b ha hsupp hW K Y ρ q
    hK hY hρ hq η (fun m=>σ m k) hη (fun m=>hσ m k) k.val
    (mem_idealRange.mp k.property).1.1
  rw [tsum_dualIdealDyads _ hs.of_norm]
  apply tsum_congr
  intro i
  exact reflectedBranchBlock_canonical angularOrder P hg j e W K Y ρ q η σ i k hK hk

end OAI.CubicEisenstein.AngularRawKernel
