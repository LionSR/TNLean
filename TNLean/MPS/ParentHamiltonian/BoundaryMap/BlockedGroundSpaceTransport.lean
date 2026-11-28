/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.Physical.Blocking
import TNLean.MPS.ParentHamiltonian.BoundaryMap.GroundSpaceGram

/-!
# Transport of ground spaces under physical blocking

Physical blocking groups \(p\) consecutive original sites into one blocked site.  A chain of
\(N\) blocked sites therefore has the same configuration basis as a chain of \(N p\) original
sites, through `Kraus.blockedConfigEquiv`.  This file defines the corresponding Euclidean linear
isometry and proves exact transport identities for the boundary map, its range, and its
orthogonal projector.

The blocked chain length \(N\) and the original physical length \(N p\) remain explicit in every
statement.  No comparison of parent Hamiltonians is made here.  The transport of the two
whole-block spectator spaces needed for the three-block C3-prime estimate remains separate:
the left and tail spaces of the blocked tensor must be identified with their respective
boundary-map ranges on \(3p\) original sites, rather than with an original one-site spectator.

## Main definitions

* `MPSTensor.blockedConfigLinearIsometryEquiv` — the computational-basis reindexing between
  \(N\) blocked sites and \(N p\) original sites.

## Main results

* `MPSTensor.blockedConfigLinearIsometryEquiv_groundSpaceMapES` — intertwining of the
  Euclidean boundary maps.
* `MPSTensor.map_groundSpace_blockTensor_map` — exact transport of the local ground space.
* `MPSTensor.starProjection_map_groundSpace_blockTensor_map_apply` — pointwise conjugacy of
  the orthogonal ground-space projectors.
* `MPSTensor.starProjection_map_groundSpace_blockTensor_conj` — operator-level projector
  conjugacy for an arbitrary number of blocked sites.
* `MPSTensor.starProjection_map_groundSpace_three_blockTensor_conj` — operator-level projector
  conjugacy for three blocked sites.

## References

* arXiv:2011.12127, lines 1815–1820 (blocking consecutive physical sites).
* arXiv:2011.12127, lines 1985–1992 (local parent ground spaces).

The equivalence `Kraus.blockedConfigEquiv` is the project's explicit realization of the
configuration-basis identification implicit in this blocking convention.
-/

open scoped Matrix.Norms.Frobenius

namespace MPSTensor

variable {α : Type*} [Fintype α] [DecidableEq α] {D : ℕ}

/-- The Euclidean computational-basis reindexing from a chain of \(N\) sites blocked in groups
of \(p\) to the corresponding chain of \(N p\) original sites. -/
noncomputable def blockedConfigLinearIsometryEquiv (N p : ℕ) :
    EuclideanSpace ℂ ((Fin N → Fin p → α)) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Fin (N * p) → α) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Kraus.blockConfigEquiv α N p)

@[simp]
theorem blockedConfigLinearIsometryEquiv_apply_apply (N p : ℕ)
    (v : EuclideanSpace ℂ ((Fin N → Fin p → α))) (σ : (Fin (N * p) → α)) :
    blockedConfigLinearIsometryEquiv N p v σ =
      v ((Kraus.blockConfigEquiv α N p).symm σ) :=
  rfl

@[simp]
theorem blockedConfigLinearIsometryEquiv_symm_apply_apply (N p : ℕ)
    (v : EuclideanSpace ℂ (Fin (N * p) → α)) (σ : (Fin N → Fin p → α)) :
    (blockedConfigLinearIsometryEquiv N p).symm v σ =
      v (Kraus.blockConfigEquiv α N p σ) := by
  rw [blockedConfigLinearIsometryEquiv, LinearIsometryEquiv.piLpCongrLeft_symm]
  rfl

/-- The blocked and original algebraic boundary maps have the same coefficient after the
canonical configuration reindexing. -/
@[simp]
theorem groundSpaceMap_blockTensor_blockedConfigEquiv
    (A : MPTensor α (Fin D)) (p N : ℕ) (X : Matrix (Fin D) (Fin D) ℂ)
    (σ : (Fin (N * p) → α)) :
    groundSpaceMap (Kraus.block A p) N X ((Kraus.blockConfigEquiv α N p).symm σ) =
      groundSpaceMap A (N * p) X σ := by
  simp only [groundSpaceMap_apply, Kraus.evalWord_block]
  rw [← Kraus.ofFn_blockConfigEquiv d N p ((Kraus.blockConfigEquiv α N p).symm σ)]
  simp

/-- The Euclidean boundary map of the blocked tensor intertwines with the canonical
configuration isometry.  The source has \(N\) blocked sites and the target has \(N p\)
original sites. -/
theorem blockedConfigLinearIsometryEquiv_groundSpaceMapES
    (A : MPTensor α (Fin D)) (p N : ℕ)
    (x : EuclideanSpace ℂ (Fin D × Fin D)) :
    blockedConfigLinearIsometryEquiv N p (groundSpaceMapES (Kraus.block A p) N x) =
      groundSpaceMapES A (N * p) x := by
  obtain ⟨X, rfl⟩ :=
    (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).toLinearEquiv.surjective x
  change blockedConfigLinearIsometryEquiv N p
      (groundSpaceMapES (Kraus.block A p) N
        (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D) X)) =
    groundSpaceMapES A (N * p) (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D) X)
  rw [groundSpaceMapES_frobeniusEquivEuclidean_apply,
    groundSpaceMapES_frobeniusEquivEuclidean_apply]
  ext σ
  exact groundSpaceMap_blockTensor_blockedConfigEquiv A p N X σ

/-- Physical blocking transports the local ground space on \(N\) blocked sites exactly to the
local ground space on \(N p\) original sites. -/
theorem map_groundSpace_blockTensor_map (A : MPTensor α (Fin D)) (p N : ℕ) :
    ((groundSpace (Kraus.block A p) N).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap).map
        (blockedConfigLinearIsometryEquiv N p).toLinearEquiv.toLinearMap =
      ((groundSpace A (N * p)).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap) := by
  rw [← range_groundSpaceMapES, ← range_groundSpaceMapES]
  ext v
  constructor
  · rintro ⟨w, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, (blockedConfigLinearIsometryEquiv_groundSpaceMapES A p N x).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨groundSpaceMapES (Kraus.block A p) N x, ⟨x, rfl⟩,
      blockedConfigLinearIsometryEquiv_groundSpaceMapES A p N x⟩

/-- Pointwise conjugacy of orthogonal ground-space projectors under physical blocking. -/
theorem starProjection_map_groundSpace_blockTensor_map_apply
    (A : MPTensor α (Fin D)) (p N : ℕ)
    (v : EuclideanSpace ℂ (Fin (N * p) → α)) :
    ((groundSpace A (N * p)).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap).starProjection v =
      blockedConfigLinearIsometryEquiv N p
        (((groundSpace (Kraus.block A p) N).map (WithLp.linearEquiv 2 ℂ
            _).symm.toLinearMap).starProjection
          ((blockedConfigLinearIsometryEquiv N p).symm v)) := by
  rw [← map_groundSpace_blockTensor_map A p N]
  exact Submodule.starProjection_map_apply
    (blockedConfigLinearIsometryEquiv N p) ((groundSpace (Kraus.block A p) N).map
        (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap) v

/-- Operator conjugacy of orthogonal ground-space projectors under physical blocking. -/
theorem starProjection_map_groundSpace_blockTensor_conj
    (A : MPTensor α (Fin D)) (p N : ℕ) :
    ((groundSpace A (N * p)).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap).starProjection =
      (blockedConfigLinearIsometryEquiv N p).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (((groundSpace (Kraus.block A p) N).map (WithLp.linearEquiv 2 ℂ
            _).symm.toLinearMap).starProjection.comp
          (ContinuousLinearEquiv.toContinuousLinearMap
            (blockedConfigLinearIsometryEquiv N p).symm.toContinuousLinearEquiv)) := by
  apply ContinuousLinearMap.ext
  intro v
  exact starProjection_map_groundSpace_blockTensor_map_apply A p N v

set_option synthInstance.maxHeartbeats 100000 in
-- The expanded finite-dimensional projector-conjugacy equality requires extra synthesis budget.
/-- Three blocked sites correspond to \(3p\) original sites, with exact transport of the
orthogonal ground-space projector.  This is the direct three-block specialization used in
blocked overlap estimates; it does not replace a one-site spectator by one original site. -/
theorem starProjection_map_groundSpace_three_blockTensor_conj
    (A : MPTensor α (Fin D)) (p : ℕ) :
    ((groundSpace A (3 * p)).map (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap).starProjection =
      (blockedConfigLinearIsometryEquiv 3 p).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (((groundSpace (Kraus.block A p) 3).map (WithLp.linearEquiv 2 ℂ
            _).symm.toLinearMap).starProjection.comp
          (ContinuousLinearEquiv.toContinuousLinearMap
            (blockedConfigLinearIsometryEquiv 3 p).symm.toContinuousLinearEquiv)) :=
  starProjection_map_groundSpace_blockTensor_conj A p 3

end MPSTensor
