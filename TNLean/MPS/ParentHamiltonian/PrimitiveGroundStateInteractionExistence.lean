/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.PrimitiveBlockOpenGroundSpace
import TNLean.MPS.ParentHamiltonian.MultiblockQuasiLocalGroundStates

import TNLean.MPS.ParentHamiltonian.CanonicalParentInteractionMatrix

/-!
# An interaction realizing the ground-state face of primitive sectors

For finitely many inequivalent primitive tensors with faithful invariant
matrices, choose a sufficiently long canonical parent projection. Its open
Hamiltonian has exactly the joint boundary-condition space as kernel at every
volume at least its interaction range. Its entire zero-energy state face is
the convex hull of the constructed sector states, and its pure zero-energy
states are precisely those sectors. No interaction range or simultaneous
injectivity length is supplied.

The bound on the number of sites is \(N\geq R\), including the single-window
volume. This is stronger than the source convention \(N\geq R+1\), obtained
from \(N_{\mathrm{right}}-N_{\mathrm{left}}\geq R\) on inclusive intervals.

**Scope restriction (primitive sector family):** The source existence theorem
allows arbitrary GVBS states, including more general periodic presentations.
The statements here concern the given finite primitive family; see
docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.
Purity means extremality among all normalized positive quasi-local states;
translation invariance of a state being classified is not assumed.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.1, lines 906--917,
and its finite-family consequence, lines 919--924. The open-kernel threshold
is PGVWC07, arXiv:quant-ph/0608197, Theorem 12, lines 1430--1454.
-/

open Filter SpinChain
open scoped Matrix ComplexOrder BigOperators Topology
namespace MPSTensor
variable {d b : ℕ} {D : Fin b → ℕ} [NeZero d] [∀ i, NeZero (D i)]
/-- A finite inequivalent primitive family admits a positive canonical
parent interaction of a derived range \(R>0\), with exact joint open kernel
for every volume \(N\geq R\). Source: Nachtergaele,
arXiv:cond-mat/9410110, Theorem 1.1, lines 906--917; PGVWC07,
arXiv:quant-ph/0608197, Theorem 12, lines 1430--1454. -/
theorem exists_positive_parent_interaction_of_isPrimitiveMPS
    (μ : Fin b → ℂ) (A : ∀ i, MPSTensor d (D i)) (hμ : ∀ i, μ i ≠ 0)
    (ρ : ∀ i, Matrix (Fin (D i)) (Fin (D i)) ℂ)
    (hP : ∀ i, IsPrimitiveMPS (A i) (ρ i)) (hρ : ∀ i, (ρ i).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ e : D j = D i,
      ¬ GaugePhaseEquiv (e ▸ A j) (A i)) :
    ∃ R : ℕ, 0 < R ∧ ∃ h : Matrix (Cfg d R) (Cfg d R) ℂ,
      h.PosSemidef ∧ ∀ N : ℕ, R ≤ N →
        LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
          groundSpaceES (toTensorFromBlocks (d := d) (μ := μ) A) N := by
  obtain ⟨R, hR, hKernel⟩ :=
    exists_ker_openParentHamiltonianES_toTensorFromBlocks_eq_groundSpaceES_of_isPrimitiveMPS
      μ A hμ ρ hP hρ hDistinct
  let T := toTensorFromBlocks (d := d) (μ := μ) A
  let h := canonicalParentInteractionMatrix T R
  have hmatrix : Matrix.toEuclideanLin h = parentInteractionES T R :=
    toEuclideanLin_canonicalParentInteractionMatrix T R
  refine ⟨R, hR, h, ?_, ?_⟩
  · exact canonicalParentInteractionMatrix_posSemidef T R
  · intro N hN
    rw [hmatrix, openInteractionHamiltonianES_parentInteractionES T hR]
    exact hKernel R N le_rfl hN

/-- One positive interaction realizes both the exact joint open kernels
at all volumes at least its derived range and the entire convex face of
constructed primitive sector states. Its pure zero-energy states are precisely
the sectors, with no translation-invariance assumption on the state.
Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.1,
lines 906--917, and the finite-family consequence, lines 919--924. -/
theorem exists_positive_parent_interaction_groundStateFace_of_isPrimitiveMPS
    (μ : Fin b → ℂ) (A : ∀ i, MPSTensor d (D i)) (hμ : ∀ i, μ i ≠ 0)
    (ρ : ∀ i, Matrix (Fin (D i)) (Fin (D i)) ℂ)
    (hP : ∀ i, IsPrimitiveMPS (A i) (ρ i)) (hρ : ∀ i, (ρ i).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ e : D j = D i,
      ¬ GaugePhaseEquiv (e ▸ A j) (A i)) :
    ∃ R : ℕ, 0 < R ∧ ∃ h : Matrix (Cfg d R) (Cfg d R) ℂ,
      h.PosSemidef ∧
      (∀ N : ℕ, R ≤ N →
        LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
          groundSpaceES (toTensorFromBlocks (d := d) (μ := μ) A) N) ∧
      (∀ᶠ N : ℕ in atTop,
        LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
          groundSpaceES (toTensorFromBlocks (d := d) (μ := μ) A) N) ∧
      let ω := fun j => quasiLocalExpectation (A j) (hP j).norm
        (hP j).fixedPoint_psd (hP j).fixedPoint_is_fixed (hP j).trace_ne_zero
      (∀ φ : QuasiLocalAlgebra d →L[ℂ] ℂ,
        φ ∈ parentGroundStateFace h ↔
          ∃ w : Fin b → ℝ, (∀ j, 0 ≤ w j) ∧ (∑ j, w j = 1) ∧ φ = ∑ j, w j • ω j) ∧
      (∀ φ : QuasiLocalAlgebra d →L[ℂ] ℂ,
        (φ ∈ parentGroundStateFace h ∧ IsPureQuasiLocalState d φ) ↔ ∃ j, φ = ω j) := by
  obtain ⟨R, hR, h, hh, hKernel⟩ := exists_positive_parent_interaction_of_isPrimitiveMPS
    μ A hμ ρ hP hρ hDistinct
  have hEventual : ∀ᶠ N : ℕ in atTop,
      LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
        groundSpaceES (toTensorFromBlocks (d := d) (μ := μ) A) N :=
    (eventually_ge_atTop R).mono fun N hN => hKernel N hN
  refine ⟨R, hR, h, hh, hKernel, hEventual, ?_, ?_⟩
  · exact fun φ => mem_parentGroundStateFace_iff_convex_combination_of_eventually_open_kernel
      μ A hμ ρ hP hρ hDistinct h hR hh hEventual φ
  · exact fun φ => isPure_mem_parentGroundStateFace_iff_sector_of_eventually_open_kernel
      μ A hμ ρ hP hρ hDistinct h hR hh hEventual φ

end MPSTensor
