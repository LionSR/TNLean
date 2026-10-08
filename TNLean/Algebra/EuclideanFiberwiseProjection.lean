/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.EuclideanFiberwiseMap
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Orthogonal projections on finite Euclidean families

An operator applied independently to finitely many fibers has range
consisting of the families whose fibers lie in the original range.
Its orthogonal range projection is the corresponding direct sum of the
original range projection. The same identity holds for the joint span
of any family of ranges with a common finite-dimensional target.

Consequently a finite sum of sector projections approximates its joint
projection after adding spectator coordinates with no increase in the
operator-norm error. Empty spectator sets and empty sector families
are included. These are general finite-dimensional identities used for
the residual window comparison in Nachtergaele,
arXiv:cond-mat/9410110, Lemma `commutation` (i), lines 2442--2531;
no tensor or decay hypothesis is involved.
-/

open scoped InnerProductSpace
namespace EuclideanSpace
variable {S I J : Type*} [Fintype S] [Fintype I] [Fintype J]

/-- A family belongs to the range of the fiberwise operator exactly when each fiber belongs to
the original operator range. -/
theorem mem_range_fiberwiseMap_iff (T : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ J)
    (x : EuclideanSpace ℂ (S × J)) :
    x ∈ (fiberwiseMap S T).range ↔ ∀ s, fiberₗ s x ∈ T.range := by
  constructor
  · rintro ⟨y, rfl⟩ s
    exact ⟨fiberₗ s y, rfl⟩
  · intro hx
    choose y hy using hx
    refine ⟨WithLp.toLp 2 (fun p : S × I => y p.1 p.2), ?_⟩
    ext ⟨s, j⟩
    change T (WithLp.toLp 2 (fun i => y s i)) j = x (s, j)
    exact congrArg (fun z : EuclideanSpace ℂ J => z j) (hy s)

/-- A family is orthogonal to the fiberwise range exactly when each fiber is orthogonal to the
original range. -/
theorem mem_orthogonal_range_fiberwiseMap_iff
    (T : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ J)
    (x : EuclideanSpace ℂ (S × J)) :
    x ∈ (fiberwiseMap S T).rangeᗮ ↔ ∀ s, fiberₗ s x ∈ T.rangeᗮ := by
  rw [ContinuousLinearMap.orthogonal_range, fiberwiseMap_adjoint]
  simp only [ContinuousLinearMap.orthogonal_range, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe]
  constructor
  · intro h s
    simpa only [fiberₗ_fiberwiseMap, map_zero] using congrArg (fiberₗ s) h
  · intro h
    ext ⟨s, i⟩
    exact congrArg (fun z : EuclideanSpace ℂ I => z i) (h s)

/-- The orthogonal projection onto a fiberwise range acts independently by the original range
projection on each fiber. -/
theorem fiberwiseMap_range_starProjection
    (S : Type*) [Fintype S] (T : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ J) :
    (fiberwiseMap S T).range.starProjection = fiberwiseMap S T.range.starProjection := by
  apply ContinuousLinearMap.ext
  intro x
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · rw [mem_range_fiberwiseMap_iff]
    intro s
    rw [fiberₗ_fiberwiseMap]
    exact T.range.starProjection_apply_mem _
  · rw [mem_orthogonal_range_fiberwiseMap_iff]
    intro s
    simp only [map_sub, fiberₗ_fiberwiseMap]
    exact T.range.sub_starProjection_mem_orthogonal _

/-- The joint span of fiberwise ranges is the fiberwise range of the joint original-range
projection. The family of operators may have varying finite domains and need not be finite. -/
theorem iSup_range_fiberwiseMap_eq
    (S : Type*) [Fintype S] {ι : Type*} {I : ι → Type*} [∀ j, Fintype (I j)]
    (T : (j : ι) → EuclideanSpace ℂ (I j) →L[ℂ] EuclideanSpace ℂ J) :
    (⨆ j, (fiberwiseMap S (T j)).range) =
      (fiberwiseMap S (⨆ j, (T j).range).starProjection).range := by
  have hOrth : (⨆ j, (fiberwiseMap S (T j)).range)ᗮ =
      (fiberwiseMap S (⨆ j, (T j).range).starProjection).rangeᗮ := by
    ext x
    simp only [← Submodule.iInf_orthogonal, Submodule.mem_iInf,
      mem_orthogonal_range_fiberwiseMap_iff, Submodule.range_starProjection]
    exact forall_comm
  simpa only [Submodule.orthogonal_orthogonal] using
    congrArg (fun W : Submodule ℂ (EuclideanSpace ℂ (S × J)) => Wᗮ) hOrth

/-- Projection onto the joint span of fiberwise ranges is the fiberwise joint original-range
projection. -/
theorem fiberwiseMap_iSup_range_starProjection
    (S : Type*) [Fintype S] {ι : Type*} {I : ι → Type*} [∀ j, Fintype (I j)]
    (T : (j : ι) → EuclideanSpace ℂ (I j) →L[ℂ] EuclideanSpace ℂ J) :
    (⨆ j, (fiberwiseMap S (T j)).range).starProjection =
      fiberwiseMap S (⨆ j, (T j).range).starProjection := by
  rw [iSup_range_fiberwiseMap_eq, fiberwiseMap_range_starProjection]
  simp only [Submodule.range_starProjection]

/-- Finite direct sums of operators preserve a finite sum of operators. -/
theorem fiberwiseMap_sum (S : Type*) [Fintype S] {ι : Type*} [Fintype ι]
    (T : ι → EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ J) :
    fiberwiseMap S (∑ j, T j) = ∑ j, fiberwiseMap S (T j) := by
  ext x ⟨s, j⟩
  simp only [fiberwiseMap_apply, sum_apply, WithLp.ofLp_sum, Finset.sum_apply]

/-- Adding finite spectator coordinates does not increase the error between a finite sum of
range projections and the projection onto their joint span. -/
theorem norm_sum_fiberwiseMap_range_starProjection_sub_iSup_le
    (S : Type*) [Fintype S] {ι : Type*} [Fintype ι]
    {I : ι → Type*} [∀ j, Fintype (I j)]
    (T : (j : ι) → EuclideanSpace ℂ (I j) →L[ℂ] EuclideanSpace ℂ J) :
    ‖(∑ j, (fiberwiseMap S (T j)).range.starProjection) -
      (⨆ j, (fiberwiseMap S (T j)).range).starProjection‖ ≤
      ‖(∑ j, (T j).range.starProjection) - (⨆ j, (T j).range).starProjection‖ := by
  simp only [fiberwiseMap_range_starProjection, fiberwiseMap_iSup_range_starProjection]
  rw [← fiberwiseMap_sum, ← fiberwiseMap_sub]
  exact norm_fiberwiseMap_le _ _
end EuclideanSpace



