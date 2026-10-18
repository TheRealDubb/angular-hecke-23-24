import AngularNonpoleContinuation

/-! Exact identification of the type-zero angular continuation with OAI-003's
original finite Hecke L-function away from 0 and 1. This uses equality of the
actual series and analytic continuation, not a new abstract L-function. -/

noncomputable section
open scoped Classical Topology

namespace OAI.SevenEighths.Angular.FiniteIdentification

open FamilyContinuation

theorem ofFinite_LFunction (χ : HeckeFamily.Character) (s : ℂ)
    (h0 : s ≠ 0) (h1 : s ≠ 1) :
    LFunction (AngularCharacter.ofFinite χ) s = HeckeFamily.LFunction χ s := by
  apply NonpoleContinuation.eq_of_right_halfPlane
    (fun z hz0 hz1 => NonpoleContinuation.LFunction_differentiableAt _ z hz0 hz1)
    (fun _ hz0 hz1 => HeckeFamily.LFunction_differentiableAt χ hz0 (Or.inl hz1))
    _ s h0 h1
  intro z hz
  rw [LFunction_eq_series _ z hz]
  exact AngularCharacter.ofFinite_series χ z hz

/-- The finite residue character associated to an actual angular type zero. -/
def toFinite (χ : AngularCharacter) (hk : χ.k = 0) : HeckeFamily.Character :=
  HeckeFamily.Character.ofResidue χ.modulus χ.modulus_ne_bot χ.residue
    (fun u => by simpa only [hk, zpow_zero, one_mul] using χ.unit_compatible u)

theorem ofFinite_toFinite (χ : AngularCharacter) (hk : χ.k = 0) :
    AngularCharacter.ofFinite (toFinite χ hk) = χ := by
  cases χ with
  | mk k M hM r hu =>
      cases hk
      rfl

theorem typeZero_LFunction (χ : AngularCharacter) (hk : χ.k = 0) (s : ℂ)
    (h0 : s ≠ 0) (h1 : s ≠ 1) :
    LFunction χ s = HeckeFamily.LFunction (toFinite χ hk) s := by
  exact (congrArg (fun η => LFunction η s) (ofFinite_toFinite χ hk).symm).trans
    (ofFinite_LFunction _ s h0 h1)

theorem typeZero_zero_iff (χ : AngularCharacter) (hk : χ.k = 0) (s : ℂ)
    (h0 : s ≠ 0) (h1 : s ≠ 1) :
    LFunction χ s = 0 ↔ HeckeFamily.LFunction (toFinite χ hk) s = 0 := by
  rw [typeZero_LFunction χ hk s h0 h1]

end OAI.SevenEighths.Angular.FiniteIdentification
