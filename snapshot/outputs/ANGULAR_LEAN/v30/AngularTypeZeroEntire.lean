import AngularFiniteIdentification
import OAI.NumberTheory.DirichletL.Hecke.FiniteDeletion
import OAI.NumberTheory.DirichletL.Hecke.BoundaryIntegration

/-! Actual type-zero nonprincipal continuation, including its value at one.
The primitive theta origin terms vanish by nonprincipality, so entireness is
proved before analytic uniqueness is used for the finite-family identification. -/
noncomputable section
open scoped Classical Topology
open Set Filter Complex
namespace OAI.SevenEighths.Angular.TypeZeroEntire
open ActualEisensteinCubic FiniteIdentification PrimitiveReduction ThetaContinuation
open Polynomial

theorem finite_idealCoeff (χ : AngularCharacter) (hk : χ.k = 0) :
    HeckeFamily.idealCoeff (toFinite χ hk) = χ.idealHom := by
  have h := AngularCharacter.ofFinite_idealHom (toFinite χ hk)
  rw [ofFinite_toFinite χ hk] at h
  exact h.symm

theorem primitive_residue_nonprincipal (χ : AngularCharacter) (hk : χ.k = 0)
    (hχ : χ.residue ≠ 1) : (primitive χ).residue ≠ 1 := by
  have hmask (J : Ideal O) : HeckeFamily.idealCoeff (toFinite χ hk) J =
      if IsCoprime J (toFinite χ hk).modulus then
        HeckeFamily.idealCoeff (toFinite (primitive χ) hk) J else 0 := by
    rw [finite_idealCoeff χ hk,finite_idealCoeff (primitive χ) hk]
    exact idealHom_source_mask χ J
  exact fun h => hχ ((HeckeFiniteDeletion.principal_iff_of_mask
    (toFinite χ hk) (toFinite (primitive χ) hk) hmask).mpr h)

theorem weightedCoeff_zero (χ : AngularCharacter) (hk : χ.k = 0)
    (hχ : χ.residue ≠ 1) : weightedCoeff χ 0 = 0 := by
  rw [weightedCoeff_origin,if_pos hk,map_zero]
  exact HeckeCharacterAnalytic.residue_zero_of_nonprincipal (toFinite χ hk) hχ

theorem pair_strong_nonprincipal (c : O) [NeZero c] (χ : AngularCharacter)
    (hmod : χ.modulus = Ideal.span {c})
    (hp : FiniteFourier.IsPrimitiveOnIdeals (hmod ▸ χ.residue))
    (hk : χ.k = 0) (hχ : χ.residue ≠ 1) : IsStrongFEPair (pair c χ hmod hp) := by
  have hkc : χ.conjugate.k = 0 := by simp [hk]
  have hχc : χ.conjugate.residue ≠ 1 := by
    change star χ.residue ≠ 1
    intro h
    apply hχ
    simpa only [star_star, star_one] using congrArg star h
  constructor
  · exact weightedCoeff_zero χ hk hχ
  · exact weightedCoeff_zero χ.conjugate hkc hχc

theorem primitive_LFunction_entire (c : O) [NeZero c] (χ : AngularCharacter)
    (hmod : χ.modulus = Ideal.span {c})
    (hp : FiniteFourier.IsPrimitiveOnIdeals (hmod ▸ χ.residue))
    (hk : χ.k = 0) (hχ : χ.residue ≠ 1) :
    Differentiable ℂ (ThetaContinuation.LFunction c χ hmod hp) := by
  have h := (pair_strong_nonprincipal c χ hmod hp hk hχ).differentiable_Λ
  exact (decompleteFactor_differentiable c χ).mul
    ((h.comp (differentiable_id.add_const _)).div_const 6)

theorem LFunction_entire (χ : AngularCharacter) (hk : χ.k = 0)
    (hχ : χ.residue ≠ 1) : Differentiable ℂ (FamilyContinuation.LFunction χ) := by
  letI : NeZero (generator χ) := ⟨generator_ne_zero χ⟩
  have hprim : Differentiable ℂ (FamilyContinuation.primitiveL χ) :=
    primitive_LFunction_entire (generator χ) (primitive χ) rfl (primitive_isPrimitive χ)
      hk (primitive_residue_nonprincipal χ hk hχ)
  exact hprim.mul (factors_differentiable χ)

theorem LFunction_eq_finite (χ : AngularCharacter) (hk : χ.k = 0)
    (hχ : χ.residue ≠ 1) (s : ℂ) :
    FamilyContinuation.LFunction χ s = HeckeFamily.LFunction (toFinite χ hk) s := by
  have he : FamilyContinuation.LFunction χ =ᶠ[𝓝 (2:ℂ)]
      HeckeFamily.LFunction (toFinite χ hk) := by
    have hn : ∀ᶠ z : ℂ in 𝓝 (2:ℂ), 1 < z.re :=
      Complex.continuous_re.continuousAt.tendsto.eventually
        (Ioi_mem_nhds (by norm_num : (1:ℝ)<(2:ℂ).re))
    filter_upwards [hn] with z hz
    exact typeZero_LFunction χ hk z (by intro h; norm_num [h] at hz)
      (by intro h; norm_num [h] at hz)
  exact congrFun (((LFunction_entire χ hk hχ).differentiableOn.analyticOnNhd
    isOpen_univ).eq_of_eventuallyEq
    ((HeckeFamily.LFunction_entire_nonprincipal (toFinite χ hk) hχ).differentiableOn.analyticOnNhd
      isOpen_univ) he) s

theorem LFunction_one_ne_zero (χ : AngularCharacter) (hk : χ.k = 0)
    (hχ : χ.residue ≠ 1) : FamilyContinuation.LFunction χ 1 ≠ 0 := by
  rw [LFunction_eq_finite χ hk hχ]
  exact HeckeFamily.LFunction_one_ne_zero_nonprincipal (toFinite χ hk) hχ

end OAI.SevenEighths.Angular.TypeZeroEntire
