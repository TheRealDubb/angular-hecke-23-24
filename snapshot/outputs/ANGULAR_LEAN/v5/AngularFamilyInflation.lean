import AngularFamilyConjugation

/-! Exact finite-prime deletion for the actual continued angular L-function.
The nonzero-type identity is continued from the physical series by uniqueness.
Nonvanishing of the deletion factors is proved on Re(s)>0. Thus adding a
finite conductor mask does not change zeros there; it does not itself establish
any zero-free region. -/

noncomputable section
open Filter Set Complex
open scoped Classical Topology BigOperators

namespace OAI.SevenEighths.Angular.FamilyInflation

open FamilyContinuation

def deleted (χ : AngularCharacter) (M : Ideal ActualEisensteinCubic.O) : ℂ → ℂ :=
  EulerFactors.deletedProduct (SmoothMobiusCorrection.primeSet M)
    (fun P => Ideal.absNorm P.val) (fun P => χ.idealHom P.val)

theorem deleted_eq (χ : AngularCharacter) (M : Ideal ActualEisensteinCubic.O) (s : ℂ) :
    deleted χ M s = ∏ P ∈ SmoothMobiusCorrection.primeSet M, (1 - χ.idealTerm s P.val) := by
  apply Finset.prod_congr rfl
  intro P _
  simp only [EulerFactors.factor, AngularCharacter.idealTerm, Complex.ofReal_natCast,
    Complex.cpow_neg, div_eq_mul_inv]

theorem deleted_differentiable (χ : AngularCharacter) (M : Ideal ActualEisensteinCubic.O) :
    Differentiable ℂ (deleted χ M) := by
  apply EulerFactors.differentiable_deletedProduct
  intro P _
  have h := SmoothMobiusCorrection.prime_norm_two_le P
  exact_mod_cast (by omega : 0 < Ideal.absNorm P.val)

theorem deleted_ne_zero (χ : AngularCharacter) (M : Ideal ActualEisensteinCubic.O)
    (s : ℂ) (hs : 0 < s.re) : deleted χ M s ≠ 0 := by
  apply EulerFactors.deletedProduct_ne_zero _ _ _ _ _ hs
  · intro P _
    have h := SmoothMobiusCorrection.prime_norm_two_le P
    exact_mod_cast (by omega : 1 < Ideal.absNorm P.val)
  · intro P _
    exact χ.norm_idealHom_le_one P.val

theorem LFunction_inflate (χ : AngularCharacter) (hk : χ.k ≠ 0)
    (M : Ideal ActualEisensteinCubic.O) (hM : M ≠ ⊥) (h : M ≤ χ.modulus) (s : ℂ) :
    LFunction (χ.inflate M hM h) s = LFunction χ s * deleted χ M s := by
  have hf := LFunction_differentiable (χ.inflate M hM h) hk
  have hg := (LFunction_differentiable χ hk).mul (deleted_differentiable χ M)
  have he : LFunction (χ.inflate M hM h) =ᶠ[𝓝 (2 : ℂ)]
      (fun z => LFunction χ z * deleted χ M z) := by
    have hn : ∀ᶠ z : ℂ in 𝓝 (2 : ℂ), 1 < z.re :=
      Complex.continuous_re.continuousAt.tendsto.eventually
        (Ioi_mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re))
    filter_upwards [hn] with z hz
    rw [LFunction_eq_series _ z hz, LFunction_eq_series χ z hz, deleted_eq]
    exact χ.inflate_series M hM h z hz
  exact congrFun ((hf.differentiableOn.analyticOnNhd isOpen_univ).eq_of_eventuallyEq
    (hg.differentiableOn.analyticOnNhd isOpen_univ) he) s

theorem inflate_zero_iff (χ : AngularCharacter) (hk : χ.k ≠ 0)
    (M : Ideal ActualEisensteinCubic.O) (hM : M ≠ ⊥) (h : M ≤ χ.modulus)
    (s : ℂ) (hs : 0 < s.re) :
    LFunction (χ.inflate M hM h) s = 0 ↔ LFunction χ s = 0 := by
  rw [LFunction_inflate χ hk M hM h s, mul_eq_zero]
  simp only [deleted_ne_zero χ M s hs, or_false]

theorem inflate_nonzero_iff (χ : AngularCharacter) (hk : χ.k ≠ 0)
    (M : Ideal ActualEisensteinCubic.O) (hM : M ≠ ⊥) (h : M ≤ χ.modulus)
    (s : ℂ) (hs : 0 < s.re) :
    LFunction (χ.inflate M hM h) s ≠ 0 ↔ LFunction χ s ≠ 0 :=
  not_congr (inflate_zero_iff χ hk M hM h s hs)

end OAI.SevenEighths.Angular.FamilyInflation
