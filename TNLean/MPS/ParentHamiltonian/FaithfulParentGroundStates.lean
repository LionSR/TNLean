/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.PeriodicBlockFamilyGroundStates
import TNLean.MPS.Core.PhysicalDimension
import TNLean.MPS.ParentHamiltonian.FaithfulPeriodicGroundSpace
import TNLean.MPS.ParentHamiltonian.PrimitiveQuasiLocalPurity

/-!
# Ground states of parent interactions for faithful stationary generators

A positive interaction with eventual exact open kernels contains the generated
stationary state in its zero-energy face. For faithful normalized stationary
generators, a positive blocking length and a nonempty finite family of faithful
primitive tensors classify that whole face. Every zero-energy state is a convex
combination of their states transported to the original lattice, and every pure
zero-energy state is one such constituent. No translation invariance of a
competing state or purity of the generated state is assumed.

**Scope restriction (supplied stationary generators):** The tensor and stationary
matrix are supplied. Their construction from an arbitrary GVBS boundary-limit
presentation remains separate; see
`docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex`.

Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.1,
lines 907--925, Theorem 1.2, lines 933--947, and Section 3,
lines 1394--1483.
-/

open SpinChain Filter
open scoped Matrix MatrixOrder ComplexOrder Topology BigOperators
namespace MPSTensor
variable {d D R : ℕ}

/-- Eventual exact open kernels imply zero local energy for the generated
stationary state. No primitivity, faithful matrix, or purity is required.
Source: Nachtergaele, arXiv:cond-mat/9410110, Theorems 1.1--1.2,
lines 907--947, and the local support spaces in Section 3. -/
theorem quasiLocalExpectation_mem_parentGroundStateFace_of_eventual_open_kernel
    [NeZero d] (A : MPSTensor d D) (hA : IsLeftCanonical A)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosSemidef)
    (hFix : Kraus.map A ρ = ρ) (htr : Matrix.trace ρ ≠ 0)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hR : 0 < R) (hh : h.PosSemidef)
    (hKernel : ∀ᶠ N in atTop, LinearMap.ker
      (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) = groundSpaceES A N) :
    quasiLocalExpectation A hA hρ hFix htr ∈ parentGroundStateFace h := by
  apply (mem_parentGroundStateFace_iff_groundSpace_support_of_eventual_kernel
    A h hR hh hKernel _).mpr
  exact ⟨quasiLocalExpectation_isState A hA hρ hFix htr,
    fun a N _hN => quasiLocalExpectation_groundSpaceProjection_eq_one A hA hρ hFix htr a N⟩

/-- Faithful normalized stationary generators determine a nonempty finite
primitive family after blocking. Its transported states are exactly the pure
zero-energy states of the supplied positive interaction; their convex hull
is the entire zero-energy state face. The original generated state belongs
to this face. Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.1,
lines 907--925, and Theorem 1.2, lines 933--947, in the supplied generating-data
setting. -/
theorem exists_parentGroundStateFace_classification_of_leftCanonical_of_posDef_fixedPoint
    [NeZero D] (A : MPSTensor d D) (hA : IsLeftCanonical A)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef)
    (hFix : Kraus.map A ρ = ρ)
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hR : 0 < R) (hh : h.PosSemidef)
    (hKernel : ∀ᶠ N in atTop, LinearMap.ker
      (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) = groundSpaceES A N) :
    let _ : NeZero d := ⟨hA.physDim_ne_zero⟩
    quasiLocalExpectation A hA hρ.posSemidef hFix (ne_of_gt hρ.trace_pos) ∈
      parentGroundStateFace h ∧
    ∃ (L : ℕ) (hL : 0 < L),
      let _ : NeZero L := ⟨Nat.ne_of_gt hL⟩
      ∃ (g : ℕ), 0 < g ∧ ∃ (bdim : Fin g → ℕ) (hdim : ∀ j, 0 < bdim j),
        let _ : ∀ j, NeZero (bdim j) := fun j => ⟨Nat.ne_of_gt (hdim j)⟩
        ∃ (B : ∀ j, MPSTensor (blockPhysDim d L) (bdim j))
          (σ : ∀ j, Matrix (Fin (bdim j)) (Fin (bdim j)) ℂ)
          (hP : ∀ j, IsPrimitiveMPS (B j) (σ j)),
          (∀ j, (σ j).PosDef) ∧ BlocksNotGaugePhaseEquiv B ∧
          (∀ N, groundSpaceES (blockTensor A L) N =
            groundSpaceES (toTensorFromBlocks (fun _ => 1) B) N) ∧
          let ω := fun j => quasiLocalBlockingFunctional d L
            (quasiLocalExpectation (B j) (hP j).norm (hP j).fixedPoint_psd
              (hP j).fixedPoint_is_fixed (hP j).trace_ne_zero)
          (∀ φ : QuasiLocalAlgebra d →L[ℂ] ℂ,
            φ ∈ parentGroundStateFace h ↔ ∃ w : Fin g → ℝ,
              (∀ j, 0 ≤ w j) ∧ (∑ j, w j = 1) ∧ φ = ∑ j, w j • ω j) ∧
          (∀ φ : QuasiLocalAlgebra d →L[ℂ] ℂ,
            (φ ∈ parentGroundStateFace h ∧ IsPureQuasiLocalState d φ) ↔
              ∃ j, φ = ω j) := by
  let _ : NeZero d := ⟨hA.physDim_ne_zero⟩
  have hOwn := quasiLocalExpectation_mem_parentGroundStateFace_of_eventual_open_kernel
    A hA hρ.posSemidef hFix (ne_of_gt hρ.trace_pos) h hR hh hKernel
  obtain ⟨b, _hb, dim, _hdim, C, _V, m, hPeriodic, _hV, _hSum, _hOrth,
    _hInt, _hCoInt, _hCorner, hGS⟩ :=
    exists_periodic_groundSpaceDecomposition_of_leftCanonical_of_posDef_fixedPoint
      A hA hρ hFix
  have hJointKernel := hKernel.mono fun N hN => hN.trans (hGS N)
  obtain ⟨L, hL, g, bdim, hdim, B, σ, hP, hσ, hDistinct, hJoint, hFace, hPure⟩ :=
    exists_parentGroundStateFace_classification_of_periodic_family
      (fun _ => 1) C (fun _ => one_ne_zero) m hPeriodic h hR hh hJointKernel
  let _ : NeZero L := ⟨Nat.ne_of_gt hL⟩
  let _ : ∀ j, NeZero (bdim j) := fun j => ⟨Nat.ne_of_gt (hdim j)⟩
  have hg : 0 < g := by
    obtain ⟨w, _hw, hSum, _hDecomp⟩ := (hFace _).mp hOwn
    by_contra hNot
    have hZero : g = 0 := Nat.eq_zero_of_not_pos hNot
    subst g
    simp at hSum
  refine ⟨hOwn, L, hL, g, hg, bdim, hdim, B, σ, hP, hσ, hDistinct, ?_, hFace, hPure⟩
  intro N
  have hBlocked : groundSpaceES (blockTensor A L) N =
      groundSpaceES (blockTensor (toTensorFromBlocks (fun _ => 1) C) L) N := by
    apply Submodule.map_injective_of_injective
      (blockedConfigLinearIsometryEquiv d N L).injective
    rw [groundSpaceES_blockTensor_map, groundSpaceES_blockTensor_map, hGS (N * L)]
  exact hBlocked.trans (hJoint N)

end MPSTensor
