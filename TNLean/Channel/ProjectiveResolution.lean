/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.OrthogonalProjection
import TNLean.Channel.KrausCPTP

/-!
# Channels controlled by a projective resolution

This file proves that trace-preserving completely positive maps with a common
domain may be assembled after compression by a projective resolution of the
identity.

## Main declaration

* `isKrausCPTP_sum_comp_singleKrausMap_of_starProjectionResolution`
* `isKrausCPTP_sum_comp_singleKrausMap_of_projectiveResolution`
* `isKrausCP_sum_comp_singleKrausMap`
* `trace_sum_comp_singleKrausMap_of_starProjections`
-/

open scoped Matrix BigOperators

/-- Compressing by finitely many matrices, applying completely positive maps,
and summing gives a completely positive map. No completeness or orthogonality
condition on the compressing matrices is required. -/
theorem isKrausCP_sum_comp_singleKrausMap
    {ι α β : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (P : ι → Matrix α α ℂ)
    (S : ι → Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ)
    (hS : ∀ i, IsKrausCP (S i)) :
    IsKrausCP (∑ i, S i ∘ₗ singleKrausMap (P i)) := by
  classical
  choose r A hA using hS
  let B : (Σ i, Fin (r i)) → Matrix β α ℂ :=
    fun p ↦ A p.1 p.2 * P p.1
  rw [← show Matrix.rectangularKrausMap B =
      ∑ i, S i ∘ₗ singleKrausMap (P i) by
    apply LinearMap.ext
    intro X
    simp only [Matrix.rectangularKrausMap, LinearMap.sum_apply,
      LinearMap.comp_apply, singleKrausMap_apply]
    change (∑ p : Σ i, Fin (r i), B p * X * (B p)ᴴ) =
      ∑ i, S i (P i * X * (P i)ᴴ)
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro i _
    rw [hA i]
    apply Finset.sum_congr rfl
    intro a _
    simp only [B, Matrix.conjTranspose_mul, Matrix.mul_assoc]]
  exact Matrix.rectangularKrausMap_isKrausCP B

/-- The projector-controlled sum of trace-preserving completely positive maps
preserves precisely the trace selected by the sum of the projections. The
projections need not resolve the identity. -/
theorem trace_sum_comp_singleKrausMap_of_starProjections
    {ι α β : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (P : ι → Matrix α α ℂ)
    (S : ι → Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ)
    (hP : ∀ i, IsStarProjection (P i))
    (hS : ∀ i, IsKrausCPTP (S i)) (X : Matrix α α ℂ) :
    Matrix.trace ((∑ i, S i ∘ₗ singleKrausMap (P i)) X) =
      Matrix.trace ((∑ i, P i) * X) := by
  classical
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, Matrix.trace_sum]
  calc
    ∑ i, Matrix.trace (S i (singleKrausMap (P i) X)) =
        ∑ i, Matrix.trace (singleKrausMap (P i) X) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (hS i).trace_map _
    _ = ∑ i, Matrix.trace (P i * X) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [singleKrausMap_apply]
      have hHerm : (P i)ᴴ = P i := by
        simpa [Matrix.star_eq_conjTranspose] using
          (hP i).isSelfAdjoint.star_eq
      rw [hHerm]
      calc
        Matrix.trace (P i * X * P i) =
            Matrix.trace ((P i * P i) * X) := by
          simpa only [Matrix.mul_assoc] using
            Matrix.trace_mul_cycle (P i) X (P i)
        _ = Matrix.trace (P i * X) := by
          rw [(hP i).isIdempotentElem.eq]
    _ = Matrix.trace ((∑ i, P i) * X) := by
      rw [Matrix.sum_mul, Matrix.trace_sum]

/-- Let `(P i)` be a finite resolution of the identity by star projections on
one matrix algebra, and let `(S i)` be trace-preserving completely positive
maps with that common domain. Then the map which first projects onto sector
`i`, applies `S i`, and sums over the sectors is trace-preserving completely
positive.

This type-generic form permits matrix coordinates such as products of finite
index sets. It is the projective-measurement assembly used in
arXiv:1606.00608, Appendix C.2, lines 1810--1817. -/
theorem isKrausCPTP_sum_comp_singleKrausMap_of_starProjectionResolution
    {ι α β : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (P : ι → Matrix α α ℂ)
    (S : ι → Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ)
    (hP : ∀ i, IsStarProjection (P i))
    (hPsum : ∑ i, P i = (1 : Matrix α α ℂ))
    (hS : ∀ i, IsKrausCPTP (S i)) :
    IsKrausCPTP (∑ i, S i ∘ₗ singleKrausMap (P i)) := by
  refine isKrausCPTP_of_isKrausCP_trace_preserving
    (isKrausCP_sum_comp_singleKrausMap P S fun i ↦ (hS i).isKrausCP) fun X ↦ ?_
  rw [trace_sum_comp_singleKrausMap_of_starProjections P S hP hS X, hPsum,
    Matrix.one_mul]

/-- Let `(P i)` be a finite projective resolution of the identity on one
matrix algebra, and let `(S i)` be trace-preserving completely positive maps
with that common domain. Then the map which first projects onto sector `i`,
applies `S i`, and sums over the sectors is trace-preserving completely
positive.

Its Kraus operators are `A i a * P i`, where `(A i a)` is a Kraus family for
`S i`. Pairwise orthogonality of the projections is not needed separately:
idempotence, self-adjointness, and their sum being the identity give the Kraus
resolution directly.

This theorem is a project-derived abstraction of the channel-assembly step in
arXiv:1606.00608, Appendix C.2, lines 1810--1817. -/
theorem isKrausCPTP_sum_comp_singleKrausMap_of_projectiveResolution
    {ι : Type*} [Fintype ι] {D : ℕ}
    {β : Type*} [Fintype β] [DecidableEq β]
    (P : ι → Matrix (Fin D) (Fin D) ℂ)
    (S : ι → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix β β ℂ)
    (hP : ∀ i, IsOrthogonalProjection (P i))
    (hPsum : ∑ i, P i = (1 : Matrix (Fin D) (Fin D) ℂ))
    (hS : ∀ i, IsKrausCPTP (S i)) :
    IsKrausCPTP (∑ i, S i ∘ₗ singleKrausMap (P i)) :=
  isKrausCPTP_sum_comp_singleKrausMap_of_starProjectionResolution
    P S (fun i ↦ (hP i).isStarProjection) hPsum hS
