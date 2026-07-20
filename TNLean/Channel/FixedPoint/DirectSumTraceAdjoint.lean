/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.FixedPoint.DirectSumKraus
import TNLean.Channel.FixedPoint.TraceNonincreasingDirectSum

/-!
# Trace adjoints between finite sums of matrix algebras

The trace pairing on a finite sum of full matrix algebras is the sum of the
ordinary matrix trace pairings. This file defines the adjoint of a linear map
between two such sums, proves the defining trace identity, and establishes its
identity, composition, unitality, positivity, and complete-positivity properties.

These statements provide the rectangular direct-sum trace-adjoint argument for
the classification step in arXiv:1606.00608, Appendix C.4, lines 1995--2003,
where trace-preserving completely positive maps run in opposite directions
between two products of simple matrix algebras.

These are supporting trace-adjoint facts, not a formalization of the
classification conclusion in that passage. The remaining argument is recorded
in `docs/paper-gaps/cpsv16_vertical_sector_invertibility.tex`; it still requires
Schwarz equality, multiplicativity, the relabeling and dimension matching of
simple summands, and their implementation by unitary conjugations.

## Main definitions

* `Matrix.directSumTraceAdjointMapBetween`: the trace adjoint of a map between
  two finite sums of full matrix algebras.

## Main results

* `Matrix.sum_trace_directSumTraceAdjointMapBetween_mul`: the defining trace
  identity.
* `Matrix.directSumTraceAdjointMapBetween_comp`: adjoints reverse composition.
* `Matrix.IsTracePreservingBetweenDirectSums.directSumTraceAdjointMapBetween_one`:
  the adjoint of a trace-preserving map is unital.
* `Matrix.IsKrausDirectSumMap.directSumTraceAdjointMapBetween`: the adjoint of a
  completely positive direct-sum map is completely positive.
-/

open scoped Matrix MatrixOrder ComplexOrder BigOperators

noncomputable section

namespace Matrix

variable {ι κ τ : Type*}
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Fintype τ] [DecidableEq τ]
variable {n : ι → Type*} {m : κ → Type*} {p : τ → Type*}
variable [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
variable [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
variable [∀ l, Fintype (p l)] [∀ l, DecidableEq (p l)]

/-- The adjoint of a linear map between two finite sums of full matrix
algebras, for the pairing given by the sum of the block trace pairings.

It is obtained by embedding the codomain family block-diagonally, taking the
full-matrix trace adjoint, and retaining the diagonal blocks in the domain.
This is the preparatory adjoint construction for arXiv:1606.00608,
Appendix C.4, lines 1995--2003. -/
noncomputable def directSumTraceAdjointMapBetween
    (T : (∀ i, Matrix (n i) (n i) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (m j) (m j) ℂ)) :
    (∀ j, Matrix (m j) (m j) ℂ) →ₗ[ℂ]
      (∀ i, Matrix (n i) (n i) ℂ) :=
  directSumDiagonalCompression.comp
    ((Matrix.traceAdjointMap (directSumMapExtension T)).comp
      directSumDiagonalEmbedding)

omit [Fintype ι] [DecidableEq ι] [(i : ι) → Fintype (n i)]
    [(i : ι) → DecidableEq (n i)] [(j : κ) → DecidableEq (m j)] in
/-- The rectangular direct-sum trace adjoint is diagonal compression after
the full-matrix trace adjoint. -/
@[simp]
theorem directSumTraceAdjointMapBetween_apply
    (T : (∀ i, Matrix (n i) (n i) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (m j) (m j) ℂ))
    (A : ∀ j, Matrix (m j) (m j) ℂ) :
    directSumTraceAdjointMapBetween T A =
      directSumDiagonalCompression
        (Matrix.traceAdjointMap (directSumMapExtension T)
          (directSumDiagonalEmbedding A)) :=
  rfl

omit [DecidableEq ι] [(i : ι) → DecidableEq (n i)]
    [(j : κ) → DecidableEq (m j)] in
/-- The rectangular direct-sum trace adjoint satisfies its defining pairing:

\[
  \sum_i \operatorname{tr}(T^*(A)_i B_i)
  = \sum_j \operatorname{tr}(A_j T(B)_j).
\]

This is the trace-pairing identity needed for the classification argument in
arXiv:1606.00608, Appendix C.4, lines 1995--2003. -/
theorem sum_trace_directSumTraceAdjointMapBetween_mul
    (T : (∀ i, Matrix (n i) (n i) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (m j) (m j) ℂ))
    (A : ∀ j, Matrix (m j) (m j) ℂ)
    (B : ∀ i, Matrix (n i) (n i) ℂ) :
    ∑ i, (directSumTraceAdjointMapBetween T A i * B i).trace =
      ∑ j, (A j * T B j).trace := by
  classical
  calc
    ∑ i, (directSumTraceAdjointMapBetween T A i * B i).trace =
        (directSumDiagonalEmbedding (directSumTraceAdjointMapBetween T A) *
          directSumDiagonalEmbedding B).trace :=
      (trace_directSumDiagonalEmbedding_mul _ _).symm
    _ = (Matrix.traceAdjointMap (directSumMapExtension T)
          (directSumDiagonalEmbedding A) * directSumDiagonalEmbedding B).trace := by
      rw [directSumTraceAdjointMapBetween_apply]
      exact trace_embedding_compression_mul_embedding _ _
    _ = (directSumDiagonalEmbedding A *
          directSumMapExtension T (directSumDiagonalEmbedding B)).trace :=
      Matrix.trace_traceAdjointMap_mul _ _ _
    _ = (directSumDiagonalEmbedding A *
          directSumDiagonalEmbedding (T B)).trace := by
      rw [directSumMapExtension_apply, directSumDiagonalCompression_embedding]
    _ = ∑ j, (A j * T B j).trace :=
      trace_directSumDiagonalEmbedding_mul _ _

omit [DecidableEq ι] [(i : ι) → DecidableEq (n i)] in
private theorem eq_of_sum_trace_mul_eq
    {A B : ∀ i, Matrix (n i) (n i) ℂ}
    (h : ∀ X : ∀ i, Matrix (n i) (n i) ℂ,
      ∑ i, (A i * X i).trace = ∑ i, (B i * X i).trace) :
    A = B := by
  classical
  funext i
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro X
  let Y : ∀ i, Matrix (n i) (n i) ℂ := Function.update 0 i X
  calc
    (A i * X).trace = ∑ k, (A k * Y k).trace := by
      rw [Finset.sum_eq_single i]
      · simp [Y]
      · intro k _ hki
        simp [Y, hki]
      · simp
    _ = ∑ k, (B k * Y k).trace := h Y
    _ = (B i * X).trace := by
      rw [Finset.sum_eq_single i]
      · simp [Y]
      · intro k _ hki
        simp [Y, hki]
      · simp

omit [(i : ι) → DecidableEq (n i)] in
/-- The trace adjoint of the identity on a finite sum of matrix algebras is
the identity. -/
theorem directSumTraceAdjointMapBetween_id :
    directSumTraceAdjointMapBetween
        (LinearMap.id : (∀ i, Matrix (n i) (n i) ℂ) →ₗ[ℂ]
          (∀ i, Matrix (n i) (n i) ℂ)) =
      LinearMap.id := by
  apply LinearMap.ext
  intro A
  apply eq_of_sum_trace_mul_eq
  intro B
  simpa using sum_trace_directSumTraceAdjointMapBetween_mul
    (LinearMap.id : (∀ i, Matrix (n i) (n i) ℂ) →ₗ[ℂ]
      (∀ i, Matrix (n i) (n i) ℂ)) A B

omit [Fintype ι] [DecidableEq ι] [(i : ι) → Fintype (n i)]
    [(i : ι) → DecidableEq (n i)]
    [(j : κ) → DecidableEq (m j)] [(l : τ) → DecidableEq (p l)] in
/-- Taking trace adjoints reverses the composition of maps between finite
sums of matrix algebras. -/
theorem directSumTraceAdjointMapBetween_comp
    [Finite ι] [∀ i, Finite (n i)]
    (T : (∀ i, Matrix (n i) (n i) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (m j) (m j) ℂ))
    (S : (∀ j, Matrix (m j) (m j) ℂ) →ₗ[ℂ]
      (∀ l, Matrix (p l) (p l) ℂ)) :
    directSumTraceAdjointMapBetween (S.comp T) =
      (directSumTraceAdjointMapBetween T).comp
        (directSumTraceAdjointMapBetween S) := by
  classical
  letI := Fintype.ofFinite ι
  letI (i : ι) := Fintype.ofFinite (n i)
  apply LinearMap.ext
  intro A
  apply eq_of_sum_trace_mul_eq
  intro B
  calc
    ∑ i, (directSumTraceAdjointMapBetween (S.comp T) A i * B i).trace =
        ∑ l, (A l * S (T B) l).trace :=
      sum_trace_directSumTraceAdjointMapBetween_mul (S.comp T) A B
    _ = ∑ j, (directSumTraceAdjointMapBetween S A j * T B j).trace :=
      (sum_trace_directSumTraceAdjointMapBetween_mul S A (T B)).symm
    _ = ∑ i, (directSumTraceAdjointMapBetween T
          (directSumTraceAdjointMapBetween S A) i * B i).trace :=
      (sum_trace_directSumTraceAdjointMapBetween_mul T _ B).symm
    _ = ∑ i, (((directSumTraceAdjointMapBetween T).comp
          (directSumTraceAdjointMapBetween S)) A i * B i).trace := rfl

omit [(i : ι) → DecidableEq (n i)] in
/-- For an endomorphism of one finite sum, the rectangular trace adjoint
agrees with the previously defined endomorphism trace adjoint. -/
theorem directSumTraceAdjointMapBetween_self
    (T : (∀ i, Matrix (n i) (n i) ℂ) →ₗ[ℂ]
      (∀ i, Matrix (n i) (n i) ℂ)) :
    directSumTraceAdjointMapBetween T = directSumTraceAdjointMap T :=
  rfl

omit [DecidableEq ι] in
/-- The trace adjoint of a total-trace-preserving map between finite sums of
matrix algebras is unital.

This is the Schrödinger--Heisenberg duality needed for the classification
argument in arXiv:1606.00608, Appendix C.4, lines 1995--2003. -/
theorem IsTracePreservingBetweenDirectSums.directSumTraceAdjointMapBetween_one
    {T : (∀ i, Matrix (n i) (n i) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (m j) (m j) ℂ)}
    (hT : IsTracePreservingBetweenDirectSums T) :
    directSumTraceAdjointMapBetween T 1 = 1 := by
  apply eq_of_sum_trace_mul_eq
  intro B
  calc
    ∑ i, (directSumTraceAdjointMapBetween T 1 i * B i).trace =
        ∑ j, ((1 : ∀ j, Matrix (m j) (m j) ℂ) j * T B j).trace :=
      sum_trace_directSumTraceAdjointMapBetween_mul T 1 B
    _ = ∑ j, (T B j).trace := by simp
    _ = ∑ i, (B i).trace := hT B
    _ = ∑ i, ((1 : ∀ i, Matrix (n i) (n i) ℂ) i * B i).trace := by simp

omit [Fintype ι] [(i : ι) → Fintype (n i)]
    [(i : ι) → DecidableEq (n i)] [(j : κ) → DecidableEq (m j)] in
/-- Taking the full-matrix trace adjoint commutes with the rectangular
canonical extension of a map between finite sums of matrix algebras. -/
theorem traceAdjointMap_directSumMapExtension
    [Finite ι] [∀ i, Finite (n i)]
    (T : (∀ i, Matrix (n i) (n i) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (m j) (m j) ℂ)) :
    Matrix.traceAdjointMap (directSumMapExtension T) =
      directSumMapExtension (directSumTraceAdjointMapBetween T) := by
  classical
  letI := Fintype.ofFinite ι
  letI (i : ι) := Fintype.ofFinite (n i)
  apply LinearMap.ext
  intro A
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro B
  calc
    (Matrix.traceAdjointMap (directSumMapExtension T) A * B).trace =
        (A * directSumMapExtension T B).trace :=
      Matrix.trace_traceAdjointMap_mul _ _ _
    _ = (A * directSumDiagonalEmbedding
          (T (directSumDiagonalCompression B))).trace := rfl
    _ = (directSumDiagonalEmbedding (directSumDiagonalCompression A) *
          directSumDiagonalEmbedding
            (T (directSumDiagonalCompression B))).trace :=
      (trace_embedding_compression_mul_embedding _ _).symm
    _ = ∑ j, (directSumDiagonalCompression A j *
          T (directSumDiagonalCompression B) j).trace :=
      trace_directSumDiagonalEmbedding_mul _ _
    _ = ∑ i, (directSumTraceAdjointMapBetween T
          (directSumDiagonalCompression A) i *
            directSumDiagonalCompression B i).trace :=
      (sum_trace_directSumTraceAdjointMapBetween_mul T _ _).symm
    _ = ∑ i, (directSumDiagonalCompression B i *
          directSumTraceAdjointMapBetween T
            (directSumDiagonalCompression A) i).trace := by
      apply Finset.sum_congr rfl
      intro i _
      exact Matrix.trace_mul_comm _ _
    _ = (directSumDiagonalEmbedding (directSumDiagonalCompression B) *
          directSumDiagonalEmbedding
            (directSumTraceAdjointMapBetween T
              (directSumDiagonalCompression A))).trace :=
      (trace_directSumDiagonalEmbedding_mul _ _).symm
    _ = (B * directSumDiagonalEmbedding
          (directSumTraceAdjointMapBetween T
            (directSumDiagonalCompression A))).trace :=
      trace_embedding_compression_mul_embedding _ _
    _ = (directSumDiagonalEmbedding
          (directSumTraceAdjointMapBetween T
            (directSumDiagonalCompression A)) * B).trace :=
      Matrix.trace_mul_comm _ _
    _ = (directSumMapExtension (directSumTraceAdjointMapBetween T) A * B).trace := rfl

/-- The trace adjoint of a completely positive map between finite sums of
full matrix algebras is completely positive.

At the full-matrix level, a Kraus family \(K_a\) for the original map gives
the Kraus family \(K_a^*\) for its trace adjoint. This is the complete-
positivity passage needed for the classification argument in arXiv:1606.00608,
Appendix C.4, lines 1995--2003. -/
theorem IsKrausDirectSumMap.directSumTraceAdjointMapBetween
    {T : (∀ i, Matrix (n i) (n i) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (m j) (m j) ℂ)}
    (hT : IsKrausDirectSumMap T) :
    IsKrausDirectSumMap (directSumTraceAdjointMapBetween T) := by
  rw [IsKrausDirectSumMap, ← traceAdjointMap_directSumMapExtension]
  exact IsKrausCP.traceAdjointMap (S := directSumMapExtension T) hT

end Matrix
