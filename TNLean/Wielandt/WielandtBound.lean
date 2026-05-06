/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Authors]
-/

import TNLean.Wielandt.RankOne.Products
import TNLean.Wielandt.SpanGrowth.EigenvectorSpreading

/-!
# Quantum Wielandt bound: cumulative span consequences

This file collects the main results of the quantum Wielandt bound
from arXiv:0909.5347 (Sanz, Pérez-García, Wolf, Cirac).

## Main theorem (paper)

For a primitive quantum channel `E_A` on `M_D(ℂ)` with `d` Kraus operators:
  `i(A) ≤ (D² − d + 1) · D²`

where `i(A) = min{n : S_n(A) = M_D(ℂ)}` (the "full Kraus rank index").

## Cumulative-span consequences

Normality gives the following cumulative-span data:

1. **Cumulative span reaches ⊤**: Under `IsNormal`, `T_{D²}(A) = M_D(ℂ)`

2. **Nonzero trace product exists**: Under `IsNormal`, ∃ word `w₀` of length
   ≤ D² with `tr(evalWord A w₀) ≠ 0`

3. **Eigenvalue/eigenvector extraction**: A matrix with nonzero trace has a
   nonzero eigenvalue and eigenvector

4. **Eigenvector spreading**: The cumulative vector span reaches ⊤ in D-1 steps

5. **Cumulative conclusion**: these facts imply the cumulative span bound.

The fixed-length matrix-spanning form of Lemma 2(b) is obtained by continuing
with rank-one extraction and exact word-length padding. The results below record
the cumulative span and eigenvector-spreading part of the argument.

## References

- [Sanz, Pérez-García, Wolf, Cirac, *A quantum version of Wielandt's
  inequality*, arXiv:0909.5347](https://arxiv.org/abs/0909.5347)
-/

open scoped Matrix
open MPSTensor Module

namespace MPSTensor

variable {d D : ℕ}

/-! ## Part 1: Eigenvalue extraction data

For a normal tensor, the following data are available:
1. `cumulativeSpan A (D²) = ⊤`
2. `∃ w₀, |w₀| ≤ D² ∧ tr(evalWord A w₀) ≠ 0`
3. `∃ μ ≠ 0, ∃ φ ≠ 0, evalWord A w₀ *ᵥ φ = μ • φ`
4. `cumulativeVectorSpan A φ (D-1) = ⊤`

These facts are combined into a single analysis structure. -/

/-- Wielandt analysis data for a normal MPS tensor.

Given `IsNormal A`, we extract:
- A word `w₀` of bounded length with nonzero trace
- A nonzero eigenvalue `μ` and eigenvector `φ`
- Vector spanning in D-1 steps

This collects Lemma 1 + eigenvalue extraction + Lemma 2(a) from
arXiv:0909.5347. -/
structure WielandtAnalysis [NeZero D] (A : MPSTensor d D) where
  /-- The word with nonzero trace. -/
  w₀ : List (Fin d)
  /-- The nonzero eigenvalue. -/
  μ : ℂ
  /-- The eigenvector. -/
  φ : Fin D → ℂ
  /-- Word length bound. -/
  hw₀_len : w₀.length ≤ D ^ 2
  /-- Eigenvalue is nonzero. -/
  hμ : μ ≠ 0
  /-- Eigenvector is nonzero. -/
  hφ : φ ≠ 0
  /-- Eigenvector equation: `evalWord A w₀ *ᵥ φ = μ • φ`. -/
  heig : evalWord A w₀ *ᵥ φ = μ • φ

/-- Every normal MPS tensor admits Wielandt analysis data.

This combines Lemma 1 (`exists_nonzero_trace_word`) with eigenvalue extraction
(`exists_eigenvector_of_trace_ne_zero`) to produce the complete analysis
structure.

Paper: arXiv:0909.5347, Theorem 1 proof, first paragraph. -/
lemma wielandtAnalysis [NeZero D]
    (A : MPSTensor d D) (hN : IsNormal A) :
    Nonempty (WielandtAnalysis A) := by
  obtain ⟨w₀, μ, φ, hw₀, hμ, hφ, heig⟩ := exists_word_eigenvector A hN
  exact ⟨⟨w₀, μ, φ, hw₀, hμ, hφ, heig⟩⟩

/-! ## Part 2: Eigenvector spreading for word products

The paper's Lemma 2(a) says: if one Kraus operator has eigenvector φ with
eigenvalue μ ≠ 0, then applying all word products to φ spans ℂ^D in D-1 steps.

Our `eigenvector_spreading` from `EigenvectorSpreading.lean` proves this for
a single-index eigenvector (`A i₀ *ᵥ φ = μ • φ`). To apply it to a word
product eigenvector (`evalWord A w₀ *ᵥ φ = μ • φ`), we use the fact that
`cumulativeVectorSpan_eq_top_of_cumulativeSpan_eq_top` already handles this:
if the matrix span is ⊤, so is the vector span for any nonzero φ.

This gives the spreading result directly without needing to work with
the "n-th power channel". -/

/-- **Vector spreading from matrix spanning.**

If `cumulativeSpan A N = ⊤` (all matrices are reachable) and `φ ≠ 0`,
then `cumulativeVectorSpan A φ N = ⊤` (all vectors are reachable).

This is the key step connecting Lemma 1 to Lemma 2(a):
once we know word products span all matrices (at cumulative level D²),
they also span all vectors when applied to any nonzero φ.

Paper: implicit in the proof — the spanning of all matrices trivially implies
the spanning of all vectors.
(arXiv:0909.5347, between Lemma 1 and Lemma 2) -/
lemma vector_spanning_from_normality [NeZero D]
    (A : MPSTensor d D) (hN : IsNormal A)
    (φ : Fin D → ℂ) (hφ : φ ≠ 0) :
    cumulativeVectorSpan A φ (D ^ 2) = ⊤ :=
  cumulativeVectorSpan_eq_top_of_cumulativeSpan_eq_top A φ hφ
    (cumulativeSpan_eq_top A hN)

/-! ## Part 3: Wielandt bound - main statements

The fixed-length inequality additionally requires rank-one extraction and exact
word-length padding. The cumulative statements below supply the
normality-to-spanning input for that fixed-length passage.

### What we prove:
- `cumulative_wielandt_bound`: T_{D²}(A) = ⊤ for normal tensors
- `isNormal_implies_cumulativeSpan_eq_top'`: eventual cumulative spanning
  from normality

### Fixed-length passage:
The conversion from vector spanning to fixed-length matrix spanning is the
Lemma 2(b) passage from the paper.
-/

/-- **Cumulative Wielandt bound**: Under `IsNormal`, the cumulative word
product span reaches the full matrix algebra by step D².

This is the direct consequence of Lemma 1: the dimension-counting argument
shows that T_n strictly grows until it reaches ⊤.

Paper: arXiv:0909.5347, Lemma 1 (cumulative version). -/
theorem cumulative_wielandt_bound [NeZero D]
    (A : MPSTensor d D) (hN : IsNormal A) :
    cumulativeSpan A (D ^ 2) = ⊤ :=
  cumulativeSpan_eq_top A hN

@[deprecated (since := "2026-05-06")]
alias isNormal_implies_cumulativeSpan := cumulative_wielandt_bound

/-- **Normality implies cumulative spanning.**

If `IsNormal A` (word products of a single fixed length span M_D(ℂ)),
then the cumulative span `T_N` eventually reaches ⊤.

Note: the converse (cumulative spanning → fixed-length spanning) is also
true but requires the algebra structure of the word span. The key point
is that if T_N = ⊤, then the identity is in the cumulative span, and by
multiplying word products of different lengths we can eventually fill a
single-length word span. This is essentially Lemma 2(b) of the paper.

Paper: arXiv:0909.5347, Section II. -/
lemma isNormal_implies_cumulativeSpan_eq_top'
    (A : MPSTensor d D) (hN : IsNormal A) :
    ∃ N, cumulativeSpan A N = ⊤ :=
  cumulativeSpan_eq_top_of_isNormal A hN

/-! ## Part 4: Cumulative Wielandt analysis

The paper states the pieces below as Lemma 1, eigenvector extraction in the proof
of Theorem 1, and Lemma 2(a).  The following lemma collects these cumulative
consequences; it is not an additional paper theorem. -/

/-- Cumulative Wielandt analysis consequences.

Given `IsNormal A`:
1. Cumulative span reaches ⊤ at level D²
2. There exists a word of length ≤ D² with nonzero trace
3. This word product has a nonzero eigenvalue μ and eigenvector φ
4. All vectors are reachable from φ using word products of length ≤ D²
5. (Needs Lemma 2(b)) All matrices are reachable using word products of
   a single fixed length ≤ D⁴

This lemma covers steps 1-4. -/
lemma wielandt_chain [NeZero D]
    (A : MPSTensor d D) (hN : IsNormal A) :
    -- Step 1: Cumulative span = ⊤
    cumulativeSpan A (D ^ 2) = ⊤ ∧
    -- Step 2: Nonzero trace word exists
    (∃ (w₀ : List (Fin d)),
      w₀.length ≤ D ^ 2 ∧ Matrix.trace (evalWord A w₀) ≠ 0) ∧
    -- Step 3: Eigenvalue and eigenvector exist
    (∃ (w₀ : List (Fin d)) (μ : ℂ) (φ : Fin D → ℂ),
      w₀.length ≤ D ^ 2 ∧ μ ≠ 0 ∧ φ ≠ 0 ∧
      evalWord A w₀ *ᵥ φ = μ • φ) ∧
    -- Step 4: Vector spanning
    (∀ (φ : Fin D → ℂ), φ ≠ 0 →
      cumulativeVectorSpan A φ (D ^ 2) = ⊤) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact cumulativeSpan_eq_top A hN
  · exact exists_nonzero_trace_word A hN
  · exact exists_word_eigenvector A hN
  · intro φ hφ
    exact vector_spanning_from_normality A hN φ hφ

/-! ## Part 5: Relation with the fixed-length bound -/

/-
Summary of the cumulative chain and fixed-length bound.

### Cumulative chain:
1. `cumulativeSpan_eq_top`: T_{D²}(A) = M_D(ℂ) for normal A
2. `exists_nonzero_trace_word`: Lemma 1 — ∃ word with nonzero trace, length ≤ D²
3. `exists_eigenvector_of_trace_ne_zero`: Nonzero trace → eigenvalue/eigenvector
4. `exists_word_eigenvector`: Combined extraction chain
5. `eigenvector_spreading`: K_{D-1}(A,φ) = ℂ^D (Lemma 2(a))
6. `vector_spanning_from_normality`: Matrix spanning → vector spanning
7. `FittingDecomposition`: Invertible/nilpotent decomposition
8. `evalWord_append_eigenvector`: Pumping lemma for eigenvectors
9. `evalWord_replicate_eigenvector`: Iterated pumping

### Fixed-length bound route:
The fixed-length argument continues from this cumulative chain by extracting
rank-one matrices from eigenvectors, padding them to one exact word length, and
assembling a full matrix span at the Wielandt index bound.
-/

end MPSTensor
