/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.MultiblockQuasiLocalFace
import TNLean.MPS.ParentHamiltonian.QuasiLocalGroundStateSupport
import TNLean.MPS.ParentHamiltonian.QuasiLocalParentGroundStateFace
import TNLean.MPS.ParentHamiltonian.LocalParentExpectationFromOpenKernel
import TNLean.MPS.ParentHamiltonian.PrimitiveQuasiLocalPurity

/-!
# Classification of the quasi-local ground-state face

Let a weighted tensor consist of finitely many inequivalent primitive sectors
with faithful invariant matrices. If a positive finite-range interaction has
this tensor's MPS space as its open-chain kernel at every sufficiently large
length, its entire zero-energy state face is the convex hull of the constructed
sector states. Its pure ground states are precisely those sector states.
The state being classified need not be translation invariant. No comparison
between the original interaction range and an injectivity length is assumed.

**Scope restriction (primitive sector families):** The source also permits
more general periodic GVBS presentations. The present classification concerns
the given primitive tensor family; see
`docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex`.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorems 1.1--1.2,
lines 854--947, and the support analysis in Section 3.
-/
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology BigOperators
open SpinChain
namespace MPSTensor
variable {d b R : ℕ} [NeZero d] {D : Fin b → ℕ} [∀ j, NeZero (D j)]

/-- For finitely many inequivalent primitive sectors, the eventual open-chain
kernel identity classifies all locally zero-energy states as convex combinations
of the constructed sector states. The coefficients are derived, and translation
invariance of the state is unnecessary. Source: Nachtergaele,
arXiv:cond-mat/9410110, Theorems 1.1--1.2, lines 854--947, and Section 3. -/
theorem mem_parentGroundStateFace_iff_convex_combination_of_eventually_open_kernel
    (μ : Fin b → ℂ) (A : ∀ j, MPSTensor d (D j)) (hμ : ∀ j, μ j ≠ 0)
    (ρ : ∀ j, Matrix (Fin (D j)) (Fin (D j)) ℂ)
    (hP : ∀ j, IsPrimitiveMPS (A j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ h : D j = D i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i))
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hR : 0 < R) (hh : h.PosSemidef)
    (hker : ∀ᶠ N : ℕ in Filter.atTop,
      LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
        groundSpaceES (toTensorFromBlocks (μ := μ) A) N)
    (φ : QuasiLocalAlgebra d →L[ℂ] ℂ) :
    φ ∈ parentGroundStateFace h ↔
      ∃ w : Fin b → ℝ, (∀ j, 0 ≤ w j) ∧ (∑ j, w j = 1) ∧
        φ = ∑ j, w j • quasiLocalExpectation (A j) (hP j).norm
          (hP j).fixedPoint_psd (hP j).fixedPoint_is_fixed (hP j).trace_ne_zero := by
  constructor
  · intro hφ
    exact exists_convex_combination_quasiLocalExpectation_of_eventually_groundSpace_support
      μ A hμ ρ hP hρ hDistinct φ hφ.1
      (eventually_quasiLocalState_symmetric_groundSpaceProjection_eq_one_of_eventual_kernel
        (toTensorFromBlocks (μ := μ) A) h hR hh hker φ hφ.1 hφ.2)
  · rintro ⟨w, hw, hsum, rfl⟩
    exact (convex_parentGroundStateFace h).sum_mem (fun j _ => hw j) hsum
      (fun j _ => ⟨quasiLocalExpectation_isState (A j) (hP j).norm
        (hP j).fixedPoint_psd (hP j).fixedPoint_is_fixed (hP j).trace_ne_zero,
        quasiLocalExpectation_interval_eq_zero_of_eventually_open_kernel μ A hμ j
          (hP j).norm (hP j).fixedPoint_psd (hP j).fixedPoint_is_fixed
          (hP j).trace_ne_zero h hR hker⟩)
/-- The pure locally zero-energy states are precisely the constructed primitive
sector states. Purity means extremality among all normalized positive states.
Source: Nachtergaele, arXiv:cond-mat/9410110, Theorems 1.1--1.2,
lines 854--947, and the purity discussion at lines 1469--1482. -/
theorem isPure_mem_parentGroundStateFace_iff_sector_of_eventually_open_kernel
    (μ : Fin b → ℂ) (A : ∀ j, MPSTensor d (D j)) (hμ : ∀ j, μ j ≠ 0)
    (ρ : ∀ j, Matrix (Fin (D j)) (Fin (D j)) ℂ)
    (hP : ∀ j, IsPrimitiveMPS (A j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ h : D j = D i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i))
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hR : 0 < R) (hh : h.PosSemidef)
    (hker : ∀ᶠ N : ℕ in Filter.atTop,
      LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
        groundSpaceES (toTensorFromBlocks (μ := μ) A) N)
    (φ : QuasiLocalAlgebra d →L[ℂ] ℂ) :
    (φ ∈ parentGroundStateFace h ∧ IsPureQuasiLocalState d φ) ↔
      ∃ j, φ = quasiLocalExpectation (A j) (hP j).norm
        (hP j).fixedPoint_psd (hP j).fixedPoint_is_fixed (hP j).trace_ne_zero := by
  constructor
  · rintro ⟨hφ, hPure⟩
    obtain ⟨w, hw, hsum, hdecomp⟩ :=
      (mem_parentGroundStateFace_iff_convex_combination_of_eventually_open_kernel
        μ A hμ ρ hP hρ hDistinct h hR hh hker φ).mp hφ
    exact exists_eq_of_isPureQuasiLocalState_of_finite_decomposition φ hPure
      (fun j => quasiLocalExpectation (A j) (hP j).norm (hP j).fixedPoint_psd
        (hP j).fixedPoint_is_fixed (hP j).trace_ne_zero)
      (fun j => quasiLocalExpectation_isState (A j) (hP j).norm (hP j).fixedPoint_psd
        (hP j).fixedPoint_is_fixed (hP j).trace_ne_zero) w hw hsum hdecomp
  · rintro ⟨j, rfl⟩
    exact ⟨⟨quasiLocalExpectation_isState (A j) (hP j).norm
      (hP j).fixedPoint_psd (hP j).fixedPoint_is_fixed (hP j).trace_ne_zero,
      quasiLocalExpectation_interval_eq_zero_of_eventually_open_kernel μ A hμ j
        (hP j).norm (hP j).fixedPoint_psd (hP j).fixedPoint_is_fixed
        (hP j).trace_ne_zero h hR hker⟩,
      (hP j).isPureQuasiLocalState_quasiLocalExpectation (hρ j)⟩

end MPSTensor
