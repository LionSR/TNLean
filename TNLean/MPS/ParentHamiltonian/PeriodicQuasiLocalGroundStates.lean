/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.PeriodicGroundStatePresentation
import TNLean.MPS.ParentHamiltonian.EventualKernelGroundStateSupport
import TNLean.MPS.ParentHamiltonian.BlockedQuasiLocalFace
import TNLean.MPS.ParentHamiltonian.GaugePhaseSeparationTransport

/-!
# Quasi-local ground states of a periodic MPS tensor

A periodic tensor, blocked by its period, admits a nonempty finite presentation
by inequivalent primitive sectors with faithful invariant matrices. If a
positive interaction of positive range has the original tensor's open MPS
space as its eventual finite-volume kernel, its entire zero-energy state face
is the convex hull of the sector states transported to the original lattice.
Its pure ground states are exactly those transported sector states.

The sector tensors, invariant matrices, and inequivalence are derived from
periodicity. States are not assumed translation invariant. No injectivity
bound is imposed on the original interaction range, and this result makes no
claim about the existence of an interaction or its spectral gap.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorems 1.1--1.2,
lines 907--947, site grouping at lines 825--836, and the local support and
purity discussion in Section 3, lines 1394--1538; DCCSP17,
arXiv:1708.00029, Lemma lem:blocking-arbitrary, lines 434--451.

**Scope restriction (periodic tensor presentations):** The theorem starts
from an explicit periodic MPS tensor. Identifying a general periodic GVBS
presentation with this tensor and its finite support spaces remains separate.
See docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex.
-/

open scoped Matrix MatrixOrder ComplexOrder Topology BigOperators
open SpinChain
namespace MPSTensor
variable {d D m R : ℕ} [NeZero d]

/-- Periodicity derives a finite primitive sector family whose transported
states classify both the entire zero-energy face and its pure states under
the original interaction's eventual open-chain kernel identity.
The output retains faithful invariant matrices, sector inequivalence, and
exact blocked support at every length, including zero.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorems 1.1--1.2,
lines 907--947, site grouping at lines 825--836, and Section 3;
DCCSP17, arXiv:1708.00029, Lemma lem:blocking-arbitrary, lines 434--451. -/
theorem IsPeriodic.exists_parentGroundStateFace_classification_of_eventually_open_kernel
    {A : MPSTensor d D} (hA : IsPeriodic m A)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hR : 0 < R) (hh : h.PosSemidef)
    (hker : ∀ᶠ N : ℕ in Filter.atTop,
      LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
        groundSpaceES A N) :
    let _ : NeZero m := ⟨Nat.ne_of_gt hA.period_pos⟩
    ∃ (g : ℕ), 0 < g ∧
      ∃ (dim : Fin g → ℕ) (hdim : ∀ j, 0 < dim j),
        let _ : ∀ j, NeZero (dim j) := fun j => ⟨Nat.ne_of_gt (hdim j)⟩
        ∃ (B : ∀ j, MPSTensor (blockPhysDim d m) (dim j))
          (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
          (hP : ∀ j, IsPrimitiveMPS (B j) (ρ j)),
          (∀ j, (ρ j).PosDef) ∧ BlocksNotGaugePhaseEquiv B ∧
          (∀ N, groundSpaceES (blockTensor A m) N =
            groundSpaceES (toTensorFromBlocks (μ := fun _ => 1) B) N) ∧
          let ω := fun j => quasiLocalBlockingFunctional d m
            (quasiLocalExpectation (B j) (hP j).norm (hP j).fixedPoint_psd
              (hP j).fixedPoint_is_fixed (hP j).trace_ne_zero)
          (∀ φ : QuasiLocalAlgebra d →L[ℂ] ℂ,
            φ ∈ parentGroundStateFace h ↔ ∃ w : Fin g → ℝ,
              (∀ j, 0 ≤ w j) ∧ (∑ j, w j = 1) ∧ φ = ∑ j, w j • ω j) ∧
          (∀ φ : QuasiLocalAlgebra d →L[ℂ] ℂ,
            (φ ∈ parentGroundStateFace h ∧ IsPureQuasiLocalState d φ) ↔
              ∃ j, φ = ω j) := by
  let : NeZero m := ⟨Nat.ne_of_gt hA.period_pos⟩
  obtain ⟨g, hg, dim, hdim, B, ρ, hP, hρ, hDistinct, hJoint⟩ :=
    hA.exists_inequivalent_primitive_groundStatePresentation
  let : ∀ j, NeZero (dim j) := fun j => ⟨Nat.ne_of_gt (hdim j)⟩
  have hDistinct' : ∀ i j, i ≠ j → ∀ e : dim j = dim i,
      ¬ GaugePhaseEquiv (e ▸ B j) (B i) := hDistinct.forall_ne_transport
  let ω := fun j => quasiLocalBlockingFunctional d m
    (quasiLocalExpectation (B j) (hP j).norm (hP j).fixedPoint_psd
      (hP j).fixedPoint_is_fixed (hP j).trace_ne_zero)
  have hState : ∀ j, ω j ∈ quasiLocalStateSpace d := fun j =>
    (quasiLocalBlockingFunctional_mem_stateSpace_iff d m _).mpr
      (quasiLocalExpectation_isState (B j) (hP j).norm (hP j).fixedPoint_psd
        (hP j).fixedPoint_is_fixed (hP j).trace_ne_zero)
  refine ⟨g, hg, dim, hdim, B, ρ, hP, hρ, hDistinct, hJoint, ?_, ?_⟩
  · refine fun φ => ⟨?_, ?_⟩
    · exact fun hφ =>
        (groundSpace_supported_iff_convex_combination_of_blocked_primitive_family
          A (fun _ => 1) B (fun _ => one_ne_zero) ρ hP hρ hDistinct' hJoint φ hφ.1).mp
            ((mem_parentGroundStateFace_iff_groundSpace_support_of_eventual_kernel
              A h hR hh hker φ).mp hφ).2
    · rintro ⟨w, hw, hsum, hdecomp⟩
      have hφ : φ ∈ quasiLocalStateSpace d := hdecomp.symm ▸
        convex_quasiLocalStateSpace.sum_mem (fun j _ => hw j) hsum (fun j _ => hState j)
      exact (mem_parentGroundStateFace_iff_groundSpace_support_of_eventual_kernel
        A h hR hh hker φ).mpr ⟨hφ,
          (groundSpace_supported_iff_convex_combination_of_blocked_primitive_family
            A (fun _ => 1) B (fun _ => one_ne_zero) ρ hP hρ hDistinct' hJoint φ hφ).mpr
              ⟨w, hw, hsum, hdecomp⟩⟩
  · refine fun φ => ⟨?_, ?_⟩
    · exact fun hφ =>
        (isPure_groundSpace_supported_iff_sector_of_blocked_primitive_family
          A (fun _ => 1) B (fun _ => one_ne_zero) ρ hP hρ hDistinct' hJoint φ hφ.1.1).mp
            ⟨((mem_parentGroundStateFace_iff_groundSpace_support_of_eventual_kernel
              A h hR hh hker φ).mp hφ.1).2, hφ.2⟩
    · rintro ⟨j, rfl⟩
      obtain ⟨hSupport, hPure⟩ :=
        (isPure_groundSpace_supported_iff_sector_of_blocked_primitive_family
          A (fun _ => 1) B (fun _ => one_ne_zero) ρ hP hρ hDistinct' hJoint
            (ω j) (hState j)).mpr ⟨j, rfl⟩
      exact ⟨(mem_parentGroundStateFace_iff_groundSpace_support_of_eventual_kernel
        A h hR hh hker (ω j)).mpr ⟨hState j, hSupport⟩, hPure⟩
end MPSTensor
