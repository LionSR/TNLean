/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.PeriodicBlockFamilyGroundStates
import TNLean.MPS.ParentHamiltonian.LocalObservableTranslationInvariance
import TNLean.MPS.ParentHamiltonian.QuasiLocalCommutatorLocality
import TNLean.QCA.BlockingIntervalCoordinates
import TNLean.QCA.BlockingStateTransport
import TNLean.QCA.BlockingTranslation

/-!
# Local expectations of periodic ground-state components

A normalized stationary MPS state on a chain of blocks becomes a state on the
original lattice by inverse blocking of observables. It is invariant under translations
by the block length. Aligned interval expectations are the original
blocked insertion formula. On an interval beginning inside a block, the
observable is first placed in a containing aligned interval and then reindexed
into block coordinates. This formula retains the position within a block.

The existing periodic-family ground-state classification therefore gives one
common positive translation period for every pure zero-energy component.
Neither one-site invariance nor minimality of the resulting period is asserted.

Source: Nachtergaele, arXiv:cond-mat/9410110, lines 825--836 (periodic states
and site grouping), Theorem 1.1, and Section 3, equations (3.1)--(3.2b).

**Scope restriction (tensor presentation):** The ground-state consequence
starts from supplied normalized periodic tensors and an eventual exact open
kernel. The passage from arbitrary GVBS data to such generating tensors remains
separate; see `docs/paper-gaps/nachtergaele96_infinite_volume_ground_projection.tex`.
-/

open scoped Matrix MatrixOrder ComplexOrder BigOperators
open SpinChain
namespace MPSTensor
variable {d D L : ℕ} [NeZero d] [NeZero L]

/-- A blocked stationary expectation is invariant under translations by
integer multiples of the block length. Source: Nachtergaele,
arXiv:cond-mat/9410110, lines 825--836. -/
theorem blockedQuasiLocalExpectation_quasiLocalTranslation
    (B : MPSTensor (blockPhysDim d L) D)
    (hTP : ∑ i, (B i)ᴴ * B i = 1) {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hρ : ρ.PosSemidef) (hfix : Kraus.transferMap B ρ = ρ)
    (htr : Matrix.trace ρ ≠ 0) (b : ℤ) (X : QuasiLocalAlgebra d) :
    quasiLocalBlockingFunctional d L (quasiLocalExpectation B hTP hρ hfix htr)
        (quasiLocalTranslation d (b * L) X) =
      quasiLocalBlockingFunctional d L (quasiLocalExpectation B hTP hρ hfix htr) X := by
  simp only [quasiLocalBlockingFunctional_apply]
  have h := congrArg (quasiLocalBlocking d L).symm
    (quasiLocalBlocking_translation d L b ((quasiLocalBlocking d L).symm X))
  simp only [StarAlgEquiv.symm_apply_apply, StarAlgEquiv.apply_symm_apply] at h
  rw [← h]
  exact quasiLocalExpectation_quasiLocalTranslation B hTP hρ hfix htr b _

/-- On an aligned interval, the transported state is the blocked insertion
expectation after the exact configuration reindexing. Length zero is included.
Source: Nachtergaele, arXiv:cond-mat/9410110, lines 825--836 and
Section 3, equations (3.1)--(3.2b). -/
theorem blockedQuasiLocalExpectation_interval
    (B : MPSTensor (blockPhysDim d L) D)
    (hTP : ∑ i, (B i)ᴴ * B i = 1) {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hρ : ρ.PosSemidef) (hfix : Kraus.transferMap B ρ = ρ)
    (htr : Matrix.trace ρ ≠ 0) (a : ℤ) (N : ℕ)
    (X : Matrix (Cfg (blockPhysDim d L) N) (Cfg (blockPhysDim d L) N) ℂ) :
    quasiLocalBlockingFunctional d L (quasiLocalExpectation B hTP hρ hfix htr)
      (quasiLocalIntervalObservable d (a * L) (N * L)
        (Matrix.reindex (blockedConfigEquiv d N L) (blockedConfigEquiv d N L) X)) =
      observableInsertionExpectation B ρ X := by
  rw [← quasiLocalBlocking_quasiLocalIntervalObservable,
    quasiLocalBlockingFunctional_apply, StarAlgEquiv.symm_apply_apply,
    quasiLocalIntervalObservable_apply, quasiLocalExpectation_interval,
    StarAlgEquiv.apply_symm_apply]

/-- An interval observable has the blocked insertion expectation of its
nonwrapping placement in any containing aligned interval, reindexed into
block coordinates. The position inside a block remains explicit.
Source: Nachtergaele, arXiv:cond-mat/9410110, lines 825--836 and
Section 3, equations (3.1)--(3.2b). -/
theorem blockedQuasiLocalExpectation_window
    (B : MPSTensor (blockPhysDim d L) D)
    (hTP : ∑ i, (B i)ᴴ * B i = 1) {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hρ : ρ.PosSemidef) (hfix : Kraus.transferMap B ρ = ρ)
    (htr : Matrix.trace ρ ≠ 0) (a : ℤ) (N b : ℕ) {k : ℕ}
    (X : Matrix (Cfg d k) (Cfg d k) ℂ) (hk : 0 < k) (hb : b + k ≤ N * L) :
    quasiLocalBlockingFunctional d L (quasiLocalExpectation B hTP hρ hfix htr)
      (quasiLocalIntervalObservable d (a * L + (b : ℤ)) k X) =
      observableInsertionExpectation B ρ
        (Matrix.reindex (blockedConfigEquiv d N L).symm (blockedConfigEquiv d N L).symm
          (chainWindowOperator (N * L) b X)) := by
  rw [← quasiLocalIntervalObservable_chainWindowOperator (a * L) (N * L) b X hk hb]
  have h := blockedQuasiLocalExpectation_interval B hTP hρ hfix htr a N
    (Matrix.reindex (blockedConfigEquiv d N L).symm (blockedConfigEquiv d N L).symm
      (chainWindowOperator (N * L) b X))
  have hidx : Matrix.reindex (blockedConfigEquiv d N L) (blockedConfigEquiv d N L)
      (Matrix.reindex (blockedConfigEquiv d N L).symm (blockedConfigEquiv d N L).symm
        (chainWindowOperator (N * L) b X)) = chainWindowOperator (N * L) b X := by
    ext σ τ
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_symm, Equiv.apply_symm_apply]
  rw [hidx] at h
  exact h

/-- Every pure zero-energy state of a finite periodic tensor family has a
common positive translation period, derived before the state and observable
are chosen. No one-site invariance or minimal-period assertion is made.
Source: Nachtergaele, arXiv:cond-mat/9410110, Theorem 1.1,
lines 907--930, and the grouping convention at lines 825--836. -/
theorem exists_common_translation_period_of_pure_parentGroundStates_of_periodic_family
    {r R : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : ∀ j, MPSTensor d (dim j)) (hμ : ∀ j, μ j ≠ 0)
    (m : Fin r → ℕ) (hPeriodic : ∀ j, IsPeriodic (m j) (A j))
    (h : Matrix (Cfg d R) (Cfg d R) ℂ) (hR : 0 < R) (hh : h.PosSemidef)
    (hker : ∀ᶠ N : ℕ in Filter.atTop,
      LinearMap.ker (openInteractionHamiltonianES (Matrix.toEuclideanLin h) N) =
        groundSpaceES (toTensorFromBlocks μ A) N) :
    ∃ L : ℕ, 0 < L ∧ ∀ φ : QuasiLocalAlgebra d →L[ℂ] ℂ,
      φ ∈ parentGroundStateFace h → IsPureQuasiLocalState d φ →
      ∀ (b : ℤ) (X : QuasiLocalAlgebra d), φ (quasiLocalTranslation d (b * L) X) = φ X := by
  obtain ⟨L, hL, g, bdim, hdim, B, ρ, hP, hρ, hDistinct, hJoint, hConvex, hPure⟩ :=
    exists_parentGroundStateFace_classification_of_periodic_family μ A hμ m hPeriodic h hR hh hker
  let : NeZero L := ⟨Nat.ne_of_gt hL⟩
  let : ∀ j, NeZero (bdim j) := fun j => ⟨Nat.ne_of_gt (hdim j)⟩
  refine ⟨L, hL, ?_⟩
  intro φ hφ hφpure
  obtain ⟨j, rfl⟩ := (hPure φ).mp ⟨hφ, hφpure⟩
  exact blockedQuasiLocalExpectation_quasiLocalTranslation (B j) (hP j).norm
    (hP j).fixedPoint_psd (hP j).fixedPoint_is_fixed (hP j).trace_ne_zero

end MPSTensor
