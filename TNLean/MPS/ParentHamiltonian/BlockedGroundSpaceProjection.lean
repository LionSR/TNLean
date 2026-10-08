/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockedGroundSpaceTransport
import TNLean.MPS.ParentHamiltonian.PrimitiveQuasiLocalUniqueness
import TNLean.QCA.BlockingIntervalCoordinates
import TNLean.QCA.BlockingStateTransport

/-!
# Ground-space projection observables under physical blocking

Physical blocking identifies the finite MPS space on \(N\) blocked sites
with the original MPS space on \(NL\) sites. Its orthogonal projection
therefore transforms by the same configuration reindexing. On integer
intervals, the completed blocking equivalence sends the blocked projection
on \([a,a+N)\) to the original projection on \([aL,(a+N)L)\).

The corresponding expectations agree under functional transport. In
particular, exact interval support on the blocked chain is equivalent to
exact support on aligned original intervals. These statements require no
normality, translation invariance, or spectral-gap assumption. The finite
matrix identity includes block length zero; the quasi-local identities
require positive physical dimension and positive block length. All chain
lengths, including zero, are covered.

Source: arXiv:2011.12127, lines 1815--1820 and 1985--1992; Nachtergaele,
arXiv:cond-mat/9410110, lines 825--836 and Section 3. These are exact
coordinate consequences of site regrouping, not a classification of
periodic GVBS presentations.
-/

open SpinChain WithLp

namespace MPSTensor

variable {d D : ℕ}

/-- The ground-space projection of a blocked tensor, reindexed into original
site coordinates, is exactly the original ground-space projection. No positive
length or injectivity assumption is required. Source: arXiv:2011.12127,
lines 1815--1820 and 1985--1992, physical blocking and local support spaces. -/
theorem groundSpaceProjectionMatrix_blockTensor_reindex
    (A : MPSTensor d D) (L N : ℕ) :
    Matrix.reindex (blockedConfigEquiv d N L) (blockedConfigEquiv d N L)
        (groundSpaceProjectionMatrix (blockTensor A L) N) =
      groundSpaceProjectionMatrix A (N * L) := by
  ext σ τ
  have hcol {d' D' : ℕ} (B : MPSTensor d' D') (n : ℕ) (x y : Cfg d' n) :
      groundSpaceProjectionMatrix B n x y =
        ((groundSpaceES B n).starProjection (toLp 2 (Pi.single y 1))) x := by
    have h := congrArg (fun T => T (toLp 2 (Pi.single y 1)) x)
      ((Matrix.toEuclideanCLM (n := Cfg d' n) (𝕜 := ℂ)).apply_symm_apply
        (groundSpaceES B n).starProjection)
    simpa only [groundSpaceProjectionMatrix, Matrix.toEuclideanCLM_toLp,
      Matrix.mulVec_single_one, Matrix.col_apply] using h
  change groundSpaceProjectionMatrix (blockTensor A L) N
    ((blockedConfigEquiv d N L).symm σ) ((blockedConfigEquiv d N L).symm τ) =
      groundSpaceProjectionMatrix A (N * L) σ τ
  rw [hcol, hcol, starProjection_groundSpaceES_blockTensor_map_apply]
  have hsingle : (blockedConfigLinearIsometryEquiv d N L).symm
      (toLp 2 (Pi.single τ 1)) =
      toLp 2 (Pi.single ((blockedConfigEquiv d N L).symm τ) 1) := by
    ext ν
    simp only [blockedConfigLinearIsometryEquiv_symm_apply_apply,
      Pi.single_apply, ← Equiv.eq_symm_apply]
  rw [hsingle, blockedConfigLinearIsometryEquiv_apply_apply]

variable [NeZero d]

/-- Blocking transports the ground-space projection observable on a blocked
interval to the original projection on its aligned expanded interval. Empty
intervals are included. Source: Nachtergaele, arXiv:cond-mat/9410110,
lines 825--836, regrouping sites; arXiv:2011.12127, lines 1985--1992. -/
theorem quasiLocalBlocking_groundSpaceProjectionMatrix
    (A : MPSTensor d D) (L : ℕ) [NeZero L] (a : ℤ) (N : ℕ) :
    quasiLocalBlocking d L
        (quasiLocalIntervalObservable (blockPhysDim d L) a N
          (groundSpaceProjectionMatrix (blockTensor A L) N)) =
      quasiLocalIntervalObservable d (a * L) (N * L)
        (groundSpaceProjectionMatrix A (N * L)) := by
  rw [quasiLocalBlocking_quasiLocalIntervalObservable,
    groundSpaceProjectionMatrix_blockTensor_reindex]

/-- A functional transported from the blocked chain has the same expectation
of the corresponding aligned ground-space projection. This holds for every
continuous linear functional, without a state or invariance assumption.
Source: Nachtergaele, arXiv:cond-mat/9410110, lines 825--836. -/
theorem quasiLocalBlockingFunctional_groundSpaceProjectionMatrix
    (A : MPSTensor d D) (L : ℕ) [NeZero L]
    (ω : QuasiLocalAlgebra (blockPhysDim d L) →L[ℂ] ℂ) (a : ℤ) (N : ℕ) :
    quasiLocalBlockingFunctional d L ω
        (quasiLocalIntervalObservable d (a * L) (N * L)
          (groundSpaceProjectionMatrix A (N * L))) =
      ω (quasiLocalIntervalObservable (blockPhysDim d L) a N
        (groundSpaceProjectionMatrix (blockTensor A L) N)) := by
  rw [← quasiLocalBlocking_groundSpaceProjectionMatrix A L a N,
    quasiLocalBlockingFunctional_apply, StarAlgEquiv.symm_apply_apply]

/-- Inverse functional transport evaluates a blocked ground-space projection
as the original aligned projection. Source: Nachtergaele,
arXiv:cond-mat/9410110, lines 825--836. -/
theorem quasiLocalBlockingFunctional_symm_groundSpaceProjectionMatrix
    (A : MPSTensor d D) (L : ℕ) [NeZero L]
    (φ : QuasiLocalAlgebra d →L[ℂ] ℂ) (a : ℤ) (N : ℕ) :
    (quasiLocalBlockingFunctional d L).symm φ
        (quasiLocalIntervalObservable (blockPhysDim d L) a N
          (groundSpaceProjectionMatrix (blockTensor A L) N)) =
      φ (quasiLocalIntervalObservable d (a * L) (N * L)
        (groundSpaceProjectionMatrix A (N * L))) := by
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using
    (quasiLocalBlockingFunctional_groundSpaceProjectionMatrix A L
      ((quasiLocalBlockingFunctional d L).symm φ) a N).symm

/-- Exact support in every blocked interval is equivalent to exact support
in every aligned original interval, under inverse functional transport. The
statement includes length zero and requires no primitivity or translation
invariance. Source: Nachtergaele, arXiv:cond-mat/9410110,
lines 825--836 and Section 3, finite-interval support spaces. -/
theorem groundSpace_support_blockTensor_iff_aligned
    (A : MPSTensor d D) (L : ℕ) [NeZero L]
    (φ : QuasiLocalAlgebra d →L[ℂ] ℂ) :
    (∀ (a : ℤ) (N : ℕ), (quasiLocalBlockingFunctional d L).symm φ
      (quasiLocalIntervalObservable (blockPhysDim d L) a N
        (groundSpaceProjectionMatrix (blockTensor A L) N)) = 1) ↔
      ∀ (a : ℤ) (N : ℕ), φ
        (quasiLocalIntervalObservable d (a * L) (N * L)
          (groundSpaceProjectionMatrix A (N * L))) = 1 := by
  simp only [quasiLocalBlockingFunctional_symm_groundSpaceProjectionMatrix]

/-- The support equivalence under blocking restricted to positive interval
lengths. Source: Nachtergaele, arXiv:cond-mat/9410110,
lines 825--836 and Section 3, finite-interval support spaces. -/
theorem groundSpace_support_blockTensor_iff_aligned_of_positive_lengths
    (A : MPSTensor d D) (L : ℕ) [NeZero L]
    (φ : QuasiLocalAlgebra d →L[ℂ] ℂ) :
    (∀ (a : ℤ) (N : ℕ), 0 < N → (quasiLocalBlockingFunctional d L).symm φ
      (quasiLocalIntervalObservable (blockPhysDim d L) a N
        (groundSpaceProjectionMatrix (blockTensor A L) N)) = 1) ↔
      ∀ (a : ℤ) (N : ℕ), 0 < N → φ
        (quasiLocalIntervalObservable d (a * L) (N * L)
          (groundSpaceProjectionMatrix A (N * L))) = 1 := by
  simp only [quasiLocalBlockingFunctional_symm_groundSpaceProjectionMatrix]

end MPSTensor
