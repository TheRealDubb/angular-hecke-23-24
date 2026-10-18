import AngularKernelContour
import OAI.NumberTheory.DirichletL.RowCompletion.PolynomialHeight

/-! Polynomial height control for the actual shifted angular reflection
kernel. The degree is chosen before the live height; the uniform source
certificate also chooses it before the supported smooth source. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff Topology
namespace OAI.CubicEisenstein.AngularHeight
open CompletedHeight CompletedGauss ActualEisensteinCubic CompletedDyadic
open CanonicalQuadraticSieve

def HasPolynomialKernel (angularOrder : ℕ) (P : ℝ→ℝ→ℂ) : Prop :=
  (∀t,ContDiffOn ℝ ∞ (AngularReflectionKernel.paperKernel angularOrder (Vstar (P t))) (Set.Ioi 0)) ∧
  ∀ A K : ℕ,∃n : ℕ,∃C : ℝ,0<C ∧ ∀t : ℝ,∀i≤K,∀x : ℝ,0<x →
    (1+x)^A*‖LocalLogFourier.eulerDeriv (AngularReflectionKernel.paperKernel angularOrder (Vstar (P t))) i x‖≤
      C*(1+‖t‖)^n

theorem normTwistedSource_polynomial_kernel (angularOrder : ℕ) (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    HasPolynomialKernel angularOrder (normTwistedSource W) := by
  let S := vstarSchwartz W a b ha hsupp hW
  have hS : Function.support (S : ℝ→ℂ) ⊆ Set.Icc a b := Vstar_support W a b hsupp
  obtain ⟨G,hG,hbound⟩ := normTwistedSource_schwartz S a b ha hS
  have hlink (t : ℝ) : (G t : ℝ→ℂ)=Vstar (normTwistedSource W t) := by
    funext x
    rw [hG t x]
    change FourierBridge.logPhase t (Real.log x)*((Real.sqrt x:ℂ)*W x)=
      (Real.sqrt x:ℂ)*(FourierBridge.logPhase t (Real.log x)*W x)
    ring
  have hGs (t : ℝ) : Function.support (G t : ℝ→ℂ)⊆Set.Icc a b := by
    intro x hx
    change G t x≠0 at hx
    rw [hG t x] at hx
    exact hS (normTwistedSource_support S t hx)
  constructor
  · intro t
    rw [←hlink t]
    exact AngularReflectionKernel.paperKernel_compact_source_smooth angularOrder (G t) a b ha (hGs t) ((G t).smooth ⊤)
  · intro A K
    obtain ⟨s,D,hD,hkernel⟩ := AngularReflectionKernel.paperKernel_euler_source_uniform_weighted_bound angularOrder a b ha A K
    obtain ⟨n,C,hC,hsource⟩ := hbound s
    refine ⟨n,D*C,mul_pos hD hC,?_⟩
    intro t i hi x hx
    rw [←hlink t]
    exact (hkernel (G t) (hGs t) i hi x hx).trans
      ((mul_le_mul_of_nonneg_left (hsource t) hD.le).trans_eq (by ring))


end OAI.CubicEisenstein.AngularHeight
