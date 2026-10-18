import AngularBesselSpatialSmoothness
import AngularAllOrderCusp
import AngularBesselHorizontalRegularity

/-! All-order inverse-cusp composition for the actual full Bessel source.
The real spatial smoothness hypothesis is discharged, including the arbitrary
cusp constant. Constants in later estimates may depend on the fixed order. -/

noncomputable section
open scoped Classical Topology ContDiff

namespace OAI.CubicEisenstein.AngularPhysicalAllOrderCusp

open AngularBesselDerivatives AngularBesselHorizontalRegularity
open AngularBesselSpatialSmoothness AngularAllOrderCusp

theorem splitFull_contDiffAt (m : ℕ) (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) (p : ℂ × ℝ) (hp : 0 < p.2) :
    ContDiffAt ℝ m (splitFull coeff constant) p := by
  have hf := fullFunction_cusp_contDiffAt m coeff constant (p.2, p.1) hp
  have hs : ContDiffAt ℝ m (fun q : ℂ × ℝ => (q.2, q.1)) p :=
    contDiffAt_snd.prodMk contDiffAt_fst
  convert! hf.comp (f := fun q : ℂ × ℝ => (q.2, q.1)) p hs using 1

theorem fullFunction_inverse_cusp_all_pure (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) (j : ℕ) (c d : ℂ) (hc : c ≠ 0) (v : ℝ) (hv : 0 < v) :
    iteratedBar j (fun z => splitFull coeff constant (inverseCuspCoordinates c d v z)) 0 =
      (-1 / (c ^ 2 * (v : ℂ) ^ 2)) ^ j *
        iteratedZ j (fun z => splitFull coeff constant (z, 1 / (‖c‖ ^ 2 * v))) (-d / c) := by
  apply inverse_cusp_all_pure_of_pointwise_finite_orders j c d hc v hv (splitFull coeff constant)
  intro m p hp
  exact splitFull_contDiffAt m coeff constant p hp

end OAI.CubicEisenstein.AngularPhysicalAllOrderCusp
