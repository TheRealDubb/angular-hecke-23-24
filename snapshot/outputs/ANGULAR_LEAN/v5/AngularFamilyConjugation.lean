import AngularFamilyContinuation
import AngularOrientedCharacter
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Star

/-! Conjugation of the actual continued L-functions, proved by analytic
uniqueness from the physical series. The global statements require nonzero
angular type, where the entire continuation has already been constructed.
No zero-free half-plane is assumed to have been proved here. -/

noncomputable section
open Filter Set Complex
open scoped Classical Topology ComplexConjugate

namespace OAI.SevenEighths.Angular.FamilyConjugation

open FamilyContinuation

theorem LFunction_conjugate (χ : AngularCharacter) (hk : χ.k ≠ 0) (s : ℂ) :
    LFunction χ.conjugate s = conj (LFunction χ (conj s)) := by
  have hk' : χ.conjugate.k ≠ 0 := by simpa only [AngularCharacter.conjugate_k, neg_ne_zero] using hk
  have hf := LFunction_differentiable χ.conjugate hk'
  have hg : Differentiable ℂ (fun z => conj (LFunction χ (conj z))) := by
    intro z
    convert! (LFunction_differentiable χ hk (conj z)).conj_conj using 1
    simp only [conj_conj]
  have he : LFunction χ.conjugate =ᶠ[𝓝 (2 : ℂ)]
      (fun z => conj (LFunction χ (conj z))) := by
    have hn : ∀ᶠ z : ℂ in 𝓝 (2 : ℂ), 1 < z.re :=
      Complex.continuous_re.continuousAt.tendsto.eventually
        (Ioi_mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re))
    filter_upwards [hn] with z hz
    rw [LFunction_eq_series χ.conjugate z hz,
      LFunction_eq_series χ (conj z) (by simpa only [conj_re] using hz)]
    exact χ.series_conjugate z hz
  exact congrFun ((hf.differentiableOn.analyticOnNhd isOpen_univ).eq_of_eventuallyEq
    (hg.differentiableOn.analyticOnNhd isOpen_univ) he) s

theorem conjugate_zero_iff (χ : AngularCharacter) (hk : χ.k ≠ 0) (s : ℂ) :
    LFunction χ.conjugate s = 0 ↔ LFunction χ (conj s) = 0 := by
  rw [LFunction_conjugate χ hk s]
  exact map_eq_zero conj

theorem conjugate_nonzero_iff (χ : AngularCharacter) (hk : χ.k ≠ 0) (s : ℂ) :
    LFunction χ.conjugate s ≠ 0 ↔ LFunction χ (conj s) ≠ 0 :=
  not_congr (conjugate_zero_iff χ hk s)

theorem conjugate_zero_free_halfPlane_iff (χ : AngularCharacter) (hk : χ.k ≠ 0) (σ : ℝ) :
    (∀ s : ℂ, σ < s.re → LFunction χ.conjugate s ≠ 0) ↔
      (∀ s : ℂ, σ < s.re → LFunction χ s ≠ 0) := by
  constructor
  · intro h s hs
    have hh := (conjugate_nonzero_iff χ hk (conj s)).mp (h (conj s) (by simpa using hs))
    simpa only [conj_conj] using hh
  · intro h s hs
    exact (conjugate_nonzero_iff χ hk s).mpr (h (conj s) (by simpa using hs))

theorem canonicalChild_LFunction {n : ℕ} (P : OrientedCharacter n)
    (hk : P.character.k ≠ 0) (s : ℂ) :
    LFunction P.canonicalChild s =
      match P.row with
      | .negative => LFunction P.character s
      | .positive => conj (LFunction P.character (conj s)) := by
  cases he : P.row with
  | negative => simp only [OrientedCharacter.canonicalChild, he]
  | positive =>
      simp only [OrientedCharacter.canonicalChild, he]
      exact LFunction_conjugate P.character hk s

theorem canonicalChild_zero_free_halfPlane_iff {n : ℕ} (P : OrientedCharacter n)
    (hk : P.character.k ≠ 0) (σ : ℝ) :
    (∀ s : ℂ, σ < s.re → LFunction P.canonicalChild s ≠ 0) ↔
      (∀ s : ℂ, σ < s.re → LFunction P.character s ≠ 0) := by
  cases he : P.row with
  | negative => simp only [OrientedCharacter.canonicalChild, he]
  | positive =>
      simp only [OrientedCharacter.canonicalChild, he]
      exact conjugate_zero_free_halfPlane_iff P.character hk σ

end OAI.SevenEighths.Angular.FamilyConjugation
