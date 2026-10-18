import AngularFiniteIdentification

/-! Conjugation and exact conductor-mask transport for all angular types on
the common nonpole domain. The type-zero pole is explicitly excluded. -/

noncomputable section
open Filter Set Complex
open scoped Classical Topology ComplexConjugate

namespace OAI.SevenEighths.Angular.AllTypeTransport

open FamilyContinuation FamilyInflation

theorem LFunction_conjugate (χ : AngularCharacter) (s : ℂ)
    (h0 : s ≠ 0) (h1 : s ≠ 1) :
    LFunction χ.conjugate s = conj (LFunction χ (conj s)) := by
  apply NonpoleContinuation.eq_of_right_halfPlane
    (fun z hz0 hz1 => NonpoleContinuation.LFunction_differentiableAt _ z hz0 hz1)
    _ _ s h0 h1
  · intro z hz0 hz1
    have hc0 : conj z ≠ 0 := by
      intro he
      apply hz0
      simpa only [conj_conj, map_zero] using congrArg conj he
    have hc1 : conj z ≠ 1 := by
      intro he
      apply hz1
      simpa only [conj_conj, map_one] using congrArg conj he
    convert! (NonpoleContinuation.LFunction_differentiableAt χ (conj z) hc0 hc1).conj_conj using 1
    simp only [conj_conj]
  · intro z hz
    rw [LFunction_eq_series χ.conjugate z hz,
      LFunction_eq_series χ (conj z) (by simpa only [conj_re] using hz)]
    exact χ.series_conjugate z hz

theorem conjugate_zero_iff (χ : AngularCharacter) (s : ℂ)
    (h0 : s ≠ 0) (h1 : s ≠ 1) :
    LFunction χ.conjugate s = 0 ↔ LFunction χ (conj s) = 0 := by
  rw [LFunction_conjugate χ s h0 h1]
  exact map_eq_zero conj

theorem conjugate_nonzero_iff (χ : AngularCharacter) (s : ℂ)
    (h0 : s ≠ 0) (h1 : s ≠ 1) :
    LFunction χ.conjugate s ≠ 0 ↔ LFunction χ (conj s) ≠ 0 :=
  not_congr (conjugate_zero_iff χ s h0 h1)

theorem LFunction_inflate (χ : AngularCharacter)
    (M : Ideal ActualEisensteinCubic.O) (hM : M ≠ ⊥) (h : M ≤ χ.modulus)
    (s : ℂ) (h0 : s ≠ 0) (h1 : s ≠ 1) :
    LFunction (χ.inflate M hM h) s = LFunction χ s * deleted χ M s := by
  apply NonpoleContinuation.eq_of_right_halfPlane
    (fun z hz0 hz1 => NonpoleContinuation.LFunction_differentiableAt _ z hz0 hz1)
    (fun z hz0 hz1 => (NonpoleContinuation.LFunction_differentiableAt χ z hz0 hz1).mul
      (deleted_differentiable χ M z)) _ s h0 h1
  intro z hz
  change LFunction (χ.inflate M hM h) z = LFunction χ z * deleted χ M z
  rw [LFunction_eq_series _ z hz, LFunction_eq_series χ z hz, deleted_eq]
  exact χ.inflate_series M hM h z hz

theorem inflate_zero_iff (χ : AngularCharacter)
    (M : Ideal ActualEisensteinCubic.O) (hM : M ≠ ⊥) (h : M ≤ χ.modulus)
    (s : ℂ) (hs : 0 < s.re) (h1 : s ≠ 1) :
    LFunction (χ.inflate M hM h) s = 0 ↔ LFunction χ s = 0 := by
  have h0 : s ≠ 0 := by intro he; simp [he] at hs
  rw [LFunction_inflate χ M hM h s h0 h1, mul_eq_zero]
  simp only [deleted_ne_zero χ M s hs, or_false]

theorem inflate_nonzero_iff (χ : AngularCharacter)
    (M : Ideal ActualEisensteinCubic.O) (hM : M ≠ ⊥) (h : M ≤ χ.modulus)
    (s : ℂ) (hs : 0 < s.re) (h1 : s ≠ 1) :
    LFunction (χ.inflate M hM h) s ≠ 0 ↔ LFunction χ s ≠ 0 :=
  not_congr (inflate_zero_iff χ M hM h s hs h1)

end OAI.SevenEighths.Angular.AllTypeTransport
