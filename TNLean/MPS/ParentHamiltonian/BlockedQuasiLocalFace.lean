/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.MultiblockQuasiLocalSupport
import TNLean.MPS.ParentHamiltonian.BlockedGroundSpaceProjection
import TNLean.MPS.ParentHamiltonian.BlockedQuasiLocalSupport

/-!
# Supported states from an exact blocked primitive representation

Let \(L>0\). Suppose the MPS spaces of a tensor blocked in groups of
\(L\) sites are exactly the joint spaces of finitely many inequivalent
primitive tensors with faithful invariant matrices. Then all normalized
positive states supported in the original MPS intervals are convex
combinations of the corresponding blocked-sector states transported back
to the original lattice. Their pure states are precisely these transported
sector states. No translation invariance of a competing state is required.

The proof transports full interval support through blocking, applies the
primitive-family classification, and transports the resulting convex
combination. Purity is preserved because blocking identifies the entire
state spaces, not only their translation-invariant subsets.

**Scope restriction (exact blocked representation):** The classification
assumes the displayed equality of every blocked finite-chain space with the
joint primitive-sector space. Existence of this representation from periodic
tensor data is a separate result. Identification with an arbitrary GVBS
construction in the source remains separate; see
`docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex`.
The first two support-transport results require no primitive-sector hypothesis.

Source: Nachtergaele, arXiv:cond-mat/9410110, lines 825--836,
Theorem 1.1, lines 854--926, and Section 3.
-/

open scoped Matrix MatrixOrder ComplexOrder Topology BigOperators
open SpinChain
namespace MPSTensor
variable {d D L : ℕ} [NeZero d] [NeZero L]

/-- Support on every nonempty original interval is equivalent to support
on every blocked interval under inverse transport of the state. This is valid
for arbitrary tensors and normalized positive states. Source: Nachtergaele,
arXiv:cond-mat/9410110, lines 825--836 and Section 3. -/
theorem groundSpace_support_blockTensor_iff
    (A : MPSTensor d D) (φ : QuasiLocalAlgebra d →L[ℂ] ℂ)
    (hφ : φ ∈ quasiLocalStateSpace d) :
    (∀ (a : ℤ) (N : ℕ), 0 < N → φ (quasiLocalIntervalObservable d a N
      (groundSpaceProjectionMatrix A N)) = 1) ↔
    (∀ (a : ℤ) (N : ℕ), 0 < N → (quasiLocalBlockingFunctional d L).symm φ
      (quasiLocalIntervalObservable (blockPhysDim d L) a N
        (groundSpaceProjectionMatrix (blockTensor A L) N)) = 1) := by
  exact (quasiLocalState_groundSpaceProjection_eq_one_iff_aligned A φ hφ
    (NeZero.pos L)).trans
    (groundSpace_support_blockTensor_iff_aligned_of_positive_lengths A L φ).symm

/-- An exact representation of all blocked MPS spaces preserves all
interval-support constraints after state transport. No primitivity or
translation invariance is assumed. Source: Nachtergaele,
arXiv:cond-mat/9410110, lines 825--836 and Section 3. -/
theorem groundSpace_support_blocked_representation_iff {D' : ℕ}
    (A : MPSTensor d D) (C : MPSTensor (blockPhysDim d L) D')
    (hJoint : ∀ N, groundSpaceES (blockTensor A L) N = groundSpaceES C N)
    (φ : QuasiLocalAlgebra d →L[ℂ] ℂ) (hφ : φ ∈ quasiLocalStateSpace d) :
    (∀ (a : ℤ) (N : ℕ), 0 < N → φ (quasiLocalIntervalObservable d a N
      (groundSpaceProjectionMatrix A N)) = 1) ↔
    (∀ (a : ℤ) (N : ℕ), 0 < N → (quasiLocalBlockingFunctional d L).symm φ
      (quasiLocalIntervalObservable (blockPhysDim d L) a N
        (groundSpaceProjectionMatrix C N)) = 1) := by
  simpa only [groundSpaceProjectionMatrix, hJoint] using
    (groundSpace_support_blockTensor_iff (L := L) A φ hφ)

variable {b : ℕ} {E : Fin b → ℕ} [∀ j, NeZero (E j)]

/-- Under an exact blocked primitive-sector representation, all original
supported states are convex combinations of the sector states transported
back to the original lattice. No translation invariance of the state is
assumed. Source: Nachtergaele, arXiv:cond-mat/9410110,
Theorem 1.1, lines 854--926, after the regrouping at lines 825--836. -/
theorem groundSpace_supported_iff_convex_combination_of_blocked_primitive_family
    (A : MPSTensor d D) (μ : Fin b → ℂ)
    (B : ∀ j, MPSTensor (blockPhysDim d L) (E j)) (hμ : ∀ j, μ j ≠ 0)
    (ρ : ∀ j, Matrix (Fin (E j)) (Fin (E j)) ℂ)
    (hP : ∀ j, IsPrimitiveMPS (B j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ e : E j = E i,
      ¬ GaugePhaseEquiv (e ▸ B j) (B i))
    (hJoint : ∀ N, groundSpaceES (blockTensor A L) N =
      groundSpaceES (toTensorFromBlocks (μ := μ) B) N)
    (φ : QuasiLocalAlgebra d →L[ℂ] ℂ) (hφ : φ ∈ quasiLocalStateSpace d) :
    (∀ (a : ℤ) (N : ℕ), 0 < N → φ (quasiLocalIntervalObservable d a N
      (groundSpaceProjectionMatrix A N)) = 1) ↔
      ∃ w : Fin b → ℝ, (∀ j, 0 ≤ w j) ∧ (∑ j, w j = 1) ∧
        φ = ∑ j, w j • quasiLocalBlockingFunctional d L
          (quasiLocalExpectation (B j) (hP j).norm (hP j).fixedPoint_psd
            (hP j).fixedPoint_is_fixed (hP j).trace_ne_zero) := by
  have hState : (quasiLocalBlockingFunctional d L).symm φ ∈
      quasiLocalStateSpace (blockPhysDim d L) :=
    (quasiLocalBlockingFunctional_mem_stateSpace_iff d L
      ((quasiLocalBlockingFunctional d L).symm φ)).mp
        (by simpa only [ContinuousLinearEquiv.apply_symm_apply] using hφ)
  rw [groundSpace_support_blocked_representation_iff A
    (toTensorFromBlocks (μ := μ) B) hJoint φ hφ,
    groundSpace_supported_iff_convex_combination_of_isPrimitiveMPS
      μ B hμ ρ hP hρ hDistinct ((quasiLocalBlockingFunctional d L).symm φ) hState]
  simp only [← (quasiLocalBlockingFunctional d L).injective.eq_iff, map_sum,
    LinearMapClass.map_smul_of_tower (R := ℝ) (S := ℂ)
      (quasiLocalBlockingFunctional d L), ContinuousLinearEquiv.apply_symm_apply]

/-- Under an exact blocked primitive-sector representation, the pure
original supported states are precisely the transported sector states.
Purity is tested against all state decompositions. Source: Nachtergaele,
arXiv:cond-mat/9410110, Theorem 1.1 and lines 1469--1482. -/
theorem isPure_groundSpace_supported_iff_sector_of_blocked_primitive_family
    (A : MPSTensor d D) (μ : Fin b → ℂ)
    (B : ∀ j, MPSTensor (blockPhysDim d L) (E j)) (hμ : ∀ j, μ j ≠ 0)
    (ρ : ∀ j, Matrix (Fin (E j)) (Fin (E j)) ℂ)
    (hP : ∀ j, IsPrimitiveMPS (B j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ e : E j = E i,
      ¬ GaugePhaseEquiv (e ▸ B j) (B i))
    (hJoint : ∀ N, groundSpaceES (blockTensor A L) N =
      groundSpaceES (toTensorFromBlocks (μ := μ) B) N)
    (φ : QuasiLocalAlgebra d →L[ℂ] ℂ) (hφ : φ ∈ quasiLocalStateSpace d) :
    ((∀ (a : ℤ) (N : ℕ), 0 < N → φ (quasiLocalIntervalObservable d a N
      (groundSpaceProjectionMatrix A N)) = 1) ∧ IsPureQuasiLocalState d φ) ↔
      ∃ j, φ = quasiLocalBlockingFunctional d L
        (quasiLocalExpectation (B j) (hP j).norm (hP j).fixedPoint_psd
          (hP j).fixedPoint_is_fixed (hP j).trace_ne_zero) := by
  have hPure : IsPureQuasiLocalState d φ ↔
      IsPureQuasiLocalState (blockPhysDim d L)
        ((quasiLocalBlockingFunctional d L).symm φ) := by
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using
      (isPureQuasiLocalState_quasiLocalBlockingFunctional_iff d L
        ((quasiLocalBlockingFunctional d L).symm φ))
  rw [groundSpace_support_blocked_representation_iff A
    (toTensorFromBlocks (μ := μ) B) hJoint φ hφ, hPure,
    isPure_groundSpace_supported_iff_sector_of_isPrimitiveMPS
      μ B hμ ρ hP hρ hDistinct ((quasiLocalBlockingFunctional d L).symm φ)]
  simp only [← (quasiLocalBlockingFunctional d L).injective.eq_iff,
    ContinuousLinearEquiv.apply_symm_apply]
end MPSTensor
