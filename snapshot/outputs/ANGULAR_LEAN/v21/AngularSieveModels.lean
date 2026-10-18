import AngularRayOrbit
import AngularDyadicModels
import OAI.NumberTheory.DirichletL.RowCompletion.BranchDecoding

/-! Shifted angular models for every raw finite ray twist used by the actual
sieve. Model existence is supplied by physical reflection, not assumed. -/
noncomputable section
open scoped Classical BigOperators ContDiff
namespace OAI.CubicEisenstein.AngularSieveModels
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalCoefficientClass
open CanonicalRowCompletion CanonicalRowCompletion.ActualFiber ConcretePrimeRowBridge
open SecondPassArithmetic SevenEighths.Angular AngularRayOrbit
local notation "Eis" => ActualEisensteinCubic.O

def HasFixedShellModels (angularOrder : ℕ) (S:Finset (Ideal Eis)) (base:Eis→*ℂ)
    (rays:ℕ) (scale:ℂ) (ρ q level:ℝ) : Prop :=
  ∀ Ψ:Eis→*ℂ,IsBaseRayTwist base Ψ→∀m:Eis,m≠0→
    ∀ F:ℝ,∀f:idealRange F,∀u:Eisˣ,∀ W:ℝ→ℂ,∀a b:ℝ,
      0<a→Function.support W⊆Set.Icc a b→ContDiff ℝ ∞ W→
      ∀K X:ℝ,0<K→0<X→∀rows:Finset (Ideal Eis),
        (∀I∈rows,I≠0 ∧ K/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤K)→
        AngularCompletedModels.HasExactCompletedModels angularOrder rays rows K X ρ q level f.val
          (Ideal.span {m*excludedGenerator S}*f.val) W
          (CompletedUnitRows.unitRowFamily Ψ (m*excludedGenerator S) u f) scale

def HasCanonicalThetaModels (angularOrder : ℕ) (S : Finset (Ideal ActualEisensteinCubic.O)) (base : ActualEisensteinCubic.O→*ℂ)
    (ρ q levelBound : ℝ) : Prop :=
  ∀(A : ℝ),0≤A → ∀(W : ℝ→ℂ),
    Function.support W⊆Set.Icc (Real.exp (-A)) (Real.exp A) → ContDiff ℝ ∞ W →
    ∀κ : ℝ,0<κ → ∃C : ℝ,0≤C ∧
    ∀(Z K X F θ : ℝ),1≤Z → 1≤K → 0<X → 1≤F → F≤Z^((1:ℝ)/1000) →
    ∀(Ψ : ActualEisensteinCubic.O→*ℂ),IsBaseRayTwist base Ψ → ∀m : ActualEisensteinCubic.O,m≠0 →
    let G : Ideal ActualEisensteinCubic.O:=Ideal.span {m*excludedGenerator S}
    (2*K)*(Ideal.absNorm G:ℝ)≤X*F*Z^(-((1:ℝ)/40)) →
    ∃(rays : ℕ) (lengthScale : ℂ),(rays:ℝ)^2*‖lengthScale‖^2≤C*Z^κ ∧
      ∀u : ActualEisensteinCubic.Oˣ,∀f : idealRange F,∀H∈shortCubeRange (Z^((1:ℝ)/1000)),
        AngularDyadicModels.HasExactCompletedDyadicModels angularOrder rays
          (((firstFrequencyDisk (2*K)).erase 0).image (fun z=>Ideal.span {z})) (2*K)
          (X/(Ideal.absNorm H:ℝ)^3) ρ q levelBound f.val (G*f.val)
          (CompletedHeight.normTwistedSource W θ)
          (CompletedUnitRows.unitRowFamily Ψ (m*excludedGenerator S) u f) lengthScale

theorem exactModels_congr (angularOrder rays : ℕ) (rows : Finset (Ideal Eis))
    (K X ρ q level : ℝ) (F Q : Ideal Eis) (W : ℝ → ℂ)
    (Ψ Φ : Ideal Eis → Eis →* ℂ) (scale : ℂ)
    (he : ∀ J ∈ rows, completedT (Ψ J) W X = completedT (Φ J) W X)
    (hmodels : AngularCompletedModels.HasExactCompletedModels angularOrder rays rows K X ρ q
      level F Q W Φ scale) :
    AngularCompletedModels.HasExactCompletedModels angularOrder rays rows K X ρ q
      level F Q W Ψ scale := by
  intro A hA T hT hnonempty
  obtain ⟨I,hI,d,hd⟩ := hmodels A hA T hT hnonempty
  refine ⟨I,hI,d,?_⟩
  intro J hJ
  rw [he J (Finset.mem_filter.mp hJ).1]
  exact hd J hJ

theorem actual_fixedShellModels (χ : AngularCharacter) (angularOrder : ℕ)
    (hk : χ.k = -(angularOrder : ℤ)) :
    let q := orbitConductor χ
    let hq := orbitConductor_ne_zero χ
    HasFixedShellModels angularOrder (reflectionExcludedPrimes q) χ.elementHom.toMonoidHom
      (fixedReflectionRayCount (reflectionConductor q) (reflectionConductor_ne_zero q hq))
      (4*thetaDerivativeScalar⁻¹*fixedRadialCoefficientScalar)
      1 completedRamifiedStep (fixedCuspLevelBound (reflectionConductor q)) := by
  let q := orbitConductor χ
  have hq := orbitConductor_ne_zero χ
  let : Finite (Eis ⧸ Ideal.span {reflectionConductor q}) :=
    ConcreteTraceCRT.finite_quotient_span (reflectionConductor_ne_zero q hq)
  let : Fintype (Eis ⧸ Ideal.span {reflectionConductor q}) := Fintype.ofFinite _
  dsimp only
  intro Ψ hΨ m hm F f u W a b ha hs hW K X hK hX rows hrows
  obtain ⟨ψ,hψk,hψper,hψ⟩ := exists_orbit_character χ Ψ hΨ
  have hactual := AngularPhysicalRowEnergy.actual_exactModels angularOrder q hq ψ
    (hψk.trans hk) hψper m hm f.val (canonicalLabel_squarefree f) u W a b ha hs hW
    K X hX rows hrows
  apply exactModels_congr angularOrder _ rows K X 1 completedRamifiedStep _ f.val
    (maskIdeal q m f.val) W _ _ _ _ hactual
  intro J hJ
  exact hψ m (idealGenerator f.val) (u.val * idealGenerator J) W X

theorem hasCanonicalThetaModels_of_fixed_shell_models (angularOrder : ℕ)
    (S:Finset (Ideal Eis)) (base:Eis→*ℂ) (rays:ℕ) (scale:ℂ) (ρ q level:ℝ)
    (hmodels:HasFixedShellModels angularOrder S base rays scale ρ q level) :
    HasCanonicalThetaModels angularOrder S base ρ q level := by
  intro A hA W hs hW κ hκ
  refine ⟨(rays:ℝ)^2*‖scale‖^2,by positivity,?_⟩
  intro Z K X F θ hZ hK hX hF hFZ Ψ hΨ m hm
  dsimp only
  intro hmargin
  refine ⟨rays,scale,?_,?_⟩
  · exact le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hZ hκ.le)
  · intro u f H hH
    have hH0:H≠0:=((mem_shortCubeRange _ H).mp hH).1
    have hHN:(0:ℝ)<(Ideal.absNorm H:ℝ):=by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hH0)
    have hXH:0<X/(Ideal.absNorm H:ℝ)^3:=by positivity
    have hsTw:Function.support (CompletedHeight.normTwistedSource W θ)⊆
        Set.Icc (Real.exp (-A)) (Real.exp A):=
      (CompletedHeight.normTwistedSource_support W θ).trans hs
    have hTw:=normTwistedSource_contDiff W (Real.exp (-A)) (Real.exp A)
      (Real.exp_pos _) hs hW θ
    let rows:=((firstFrequencyDisk (2*K)).erase 0).image (fun z:Eis=>Ideal.span {z})
    have hrows:∀I∈rows,I≠0:=by
      intro I hI
      obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hI
      exact Ideal.span_singleton_eq_bot.not.mpr (Finset.mem_erase.mp hz).1
    intro j hj
    exact hmodels Ψ hΨ m hm F f u (CompletedHeight.normTwistedSource W θ)
      (Real.exp (-A)) (Real.exp A) (Real.exp_pos _) hsTw hTw
      ((2:ℝ)^j) (X/(Ideal.absNorm H:ℝ)^3) (by positivity) hXH
      (completedRowDyad rows j) (completedRowDyad_bounds rows j hrows)

theorem actual_canonicalThetaModels (χ : AngularCharacter) (angularOrder : ℕ)
    (hk : χ.k = -(angularOrder : ℤ)) :
    HasCanonicalThetaModels angularOrder (reflectionExcludedPrimes (orbitConductor χ))
      χ.elementHom.toMonoidHom 1 completedRamifiedStep
      (fixedCuspLevelBound (reflectionConductor (orbitConductor χ))) :=
  hasCanonicalThetaModels_of_fixed_shell_models angularOrder _ _ _ _ _ _ _
    (actual_fixedShellModels χ angularOrder hk)

end OAI.CubicEisenstein.AngularSieveModels
