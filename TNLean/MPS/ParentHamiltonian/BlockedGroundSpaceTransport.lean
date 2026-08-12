/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.Blocking
import TNLean.MPS.ParentHamiltonian.GroundSpaceGram

/-!
# Transport of ground spaces under physical blocking

Physical blocking groups `p` consecutive original sites into one blocked site.  A chain of
`N` blocked sites therefore has the same configuration basis as a chain of `N * p` original
sites, through `blockedConfigEquiv`.  This file bundles that basis reindexing as a Euclidean
linear isometry and proves exact transport identities for the boundary map, its range, and its
orthogonal projector.

The blocked chain length `N` and the original physical length `N * p` remain explicit in every
statement.  No comparison of parent Hamiltonians is made here.

## Main results

* `MPSTensor.blockedConfigLinearIsometryEquiv` — the computational-basis reindexing between
  `N` blocked sites and `N * p` original sites.
* `MPSTensor.blockedConfigLinearIsometryEquiv_groundSpaceMapES` — intertwining of the
  Euclidean boundary maps.
* `MPSTensor.groundSpaceES_blockTensor_map` — exact transport of the local ground space.
* `MPSTensor.starProjection_groundSpaceES_blockTensor_map_apply` — pointwise conjugacy of
  the orthogonal ground-space projectors.

## References

* arXiv:1606.00608, lines 318–344 (physical blocking and the identification of blocked words).
* arXiv:2011.12127, Section IV.C (parent-Hamiltonian ground spaces after blocking).
-/

open scoped Matrix.Norms.Frobenius

namespace MPSTensor

variable {d D : ℕ}

/-- The Euclidean computational-basis reindexing from a chain of `N` sites blocked in groups
of `p` to the corresponding chain of `N * p` original sites. -/
noncomputable def blockedConfigLinearIsometryEquiv (d N p : ℕ) :
    EuclideanSpace ℂ (Cfg (blockPhysDim d p) N) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Cfg d (N * p)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (blockedConfigEquiv d N p)

@[simp]
theorem blockedConfigLinearIsometryEquiv_apply_apply (d N p : ℕ)
    (v : EuclideanSpace ℂ (Cfg (blockPhysDim d p) N)) (σ : Cfg d (N * p)) :
    blockedConfigLinearIsometryEquiv d N p v σ =
      v ((blockedConfigEquiv d N p).symm σ) :=
  rfl

@[simp]
theorem blockedConfigLinearIsometryEquiv_symm_apply_apply (d N p : ℕ)
    (v : EuclideanSpace ℂ (Cfg d (N * p))) (σ : Cfg (blockPhysDim d p) N) :
    (blockedConfigLinearIsometryEquiv d N p).symm v σ =
      v (blockedConfigEquiv d N p σ) := by
  rw [blockedConfigLinearIsometryEquiv, LinearIsometryEquiv.piLpCongrLeft_symm]
  rfl

/-- The blocked and original algebraic boundary maps have the same coefficient after the
canonical configuration reindexing. -/
@[simp]
theorem groundSpaceMap_blockTensor_blockedConfigEquiv
    (A : MPSTensor d D) (p N : ℕ) (X : Matrix (Fin D) (Fin D) ℂ)
    (σ : Cfg d (N * p)) :
    groundSpaceMap (blockTensor A p) N X ((blockedConfigEquiv d N p).symm σ) =
      groundSpaceMap A (N * p) X σ := by
  simp only [groundSpaceMap_apply, evalWord_blockTensor]
  rw [← ofFn_blockedConfigEquiv d N p ((blockedConfigEquiv d N p).symm σ)]
  simp

/-- The Euclidean boundary map of the blocked tensor intertwines with the canonical
configuration isometry.  The source has `N` blocked sites and the target has `N * p`
original sites. -/
theorem blockedConfigLinearIsometryEquiv_groundSpaceMapES
    (A : MPSTensor d D) (p N : ℕ)
    (x : EuclideanSpace ℂ (Fin D × Fin D)) :
    blockedConfigLinearIsometryEquiv d N p (groundSpaceMapES (blockTensor A p) N x) =
      groundSpaceMapES A (N * p) x := by
  obtain ⟨X, rfl⟩ :=
    (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).toLinearEquiv.surjective x
  change blockedConfigLinearIsometryEquiv d N p
      (groundSpaceMapES (blockTensor A p) N
        (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D) X)) =
    groundSpaceMapES A (N * p) (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D) X)
  rw [groundSpaceMapES_frobeniusEquivEuclidean_apply,
    groundSpaceMapES_frobeniusEquivEuclidean_apply]
  ext σ
  exact groundSpaceMap_blockTensor_blockedConfigEquiv A p N X σ

/-- Physical blocking transports the local ground space on `N` blocked sites exactly to the
local ground space on `N * p` original sites. -/
theorem groundSpaceES_blockTensor_map (A : MPSTensor d D) (p N : ℕ) :
    (groundSpaceES (blockTensor A p) N).map
        (blockedConfigLinearIsometryEquiv d N p).toLinearEquiv.toLinearMap =
      groundSpaceES A (N * p) := by
  rw [← range_groundSpaceMapES, ← range_groundSpaceMapES]
  ext v
  constructor
  · rintro ⟨w, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, (blockedConfigLinearIsometryEquiv_groundSpaceMapES A p N x).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨groundSpaceMapES (blockTensor A p) N x, ⟨x, rfl⟩,
      blockedConfigLinearIsometryEquiv_groundSpaceMapES A p N x⟩

/-- Pointwise conjugacy of orthogonal ground-space projectors under physical blocking. -/
theorem starProjection_groundSpaceES_blockTensor_map_apply
    (A : MPSTensor d D) (p N : ℕ)
    (v : EuclideanSpace ℂ (Cfg d (N * p))) :
    (groundSpaceES A (N * p)).starProjection v =
      blockedConfigLinearIsometryEquiv d N p
        ((groundSpaceES (blockTensor A p) N).starProjection
          ((blockedConfigLinearIsometryEquiv d N p).symm v)) := by
  rw [← groundSpaceES_blockTensor_map A p N]
  exact Submodule.starProjection_map_apply
    (blockedConfigLinearIsometryEquiv d N p) (groundSpaceES (blockTensor A p) N) v

/-- Operator conjugacy of orthogonal ground-space projectors under physical blocking. -/
theorem starProjection_groundSpaceES_blockTensor_conj
    (A : MPSTensor d D) (p N : ℕ) :
    (groundSpaceES A (N * p)).starProjection =
      (blockedConfigLinearIsometryEquiv d N p).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((groundSpaceES (blockTensor A p) N).starProjection.comp
          (ContinuousLinearEquiv.toContinuousLinearMap
            (blockedConfigLinearIsometryEquiv d N p).symm.toContinuousLinearEquiv)) := by
  apply ContinuousLinearMap.ext
  intro v
  exact starProjection_groundSpaceES_blockTensor_map_apply A p N v

set_option synthInstance.maxHeartbeats 100000 in
/-- Three blocked sites correspond to `3 * p` original sites, with exact transport of the
orthogonal ground-space projector.  This is the direct three-block specialization used in
blocked overlap estimates; it does not replace a one-site spectator by one original site. -/
theorem starProjection_groundSpaceES_three_blockTensor_conj
    (A : MPSTensor d D) (p : ℕ) :
    (groundSpaceES A (3 * p)).starProjection =
      (blockedConfigLinearIsometryEquiv d 3 p).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((groundSpaceES (blockTensor A p) 3).starProjection.comp
          (ContinuousLinearEquiv.toContinuousLinearMap
            (blockedConfigLinearIsometryEquiv d 3 p).symm.toContinuousLinearEquiv)) :=
  starProjection_groundSpaceES_blockTensor_conj A p 3

end MPSTensor
