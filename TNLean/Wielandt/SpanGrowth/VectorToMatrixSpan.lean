/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.Wielandt.SpanGrowth.VectorToMatrixSpan
import TNLean.Wielandt.SpanGrowth.EigenvectorSpreading
import TNLean.MPS.Core.Blocking

/-!
# Vector-to-matrix span results for MPS tensors

This file preserves the established `MPSTensor` interface to the channel-generic
vector-to-matrix span results in `Kraus`. The blocking results remain here because
they use the tensor-network blocking operation.
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- The linear map `M ↦ M *ᵥ φ` for a fixed vector `φ`. -/
noncomputable abbrev mulVecLinearMap (φ : Fin D → ℂ) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] (Fin D → ℂ) :=
  Kraus.mulVecLinearMap φ

/-- Mapping `wordSpan` along `M ↦ M *ᵥ φ` yields `vectorSpreadSpan`. -/
theorem map_wordSpan_eq_vectorSpreadSpan
    (A : MPSTensor d D) (φ : Fin D → ℂ) (n : ℕ) :
    Submodule.map (mulVecLinearMap (D := D) φ) (wordSpan A n) =
      vectorSpreadSpan A φ n :=
  Kraus.map_wordSpan_eq_vectorSpreadSpan A φ n

/-- Products of length-`m` and length-`n` word spans lie in the length-`m+n` word span. -/
theorem wordSpan_mul_le (A : MPSTensor d D) (m n : ℕ) :
    wordSpan A m * wordSpan A n ≤ wordSpan A (m + n) :=
  Kraus.wordSpan_mul_le A m n

/-- If `wordSpan A N = ⊤`, then `wordSpan A (k * N) = ⊤` for any `k ≥ 1`. -/
theorem wordSpan_top_of_mul (A : MPSTensor d D) {N : ℕ}
    (htop : wordSpan A N = ⊤) :
    ∀ k : ℕ, 1 ≤ k → wordSpan A (k * N) = ⊤ :=
  Kraus.wordSpan_top_of_mul A htop

/-! ## Blocking transfer: word spans for blocked tensors -/

/-- A blocked word product of length `n` is an ordinary word product of length `n*L`. -/
theorem wordSpan_blockTensor_le (A : MPSTensor d D) (L n : ℕ) :
    wordSpan (blockTensor (d := d) (D := D) A L) n ≤ wordSpan A (n * L) := by
  classical
  apply Submodule.span_le.mpr
  rintro M ⟨σ, rfl⟩
  have hblock :
      evalWord (blockTensor (d := d) (D := D) A L) (List.ofFn σ) =
        evalWord A (flattenBlockedWord d L (List.ofFn σ)) :=
    evalWord_blockTensor (A := A) (L := L) (List.ofFn σ)
  have hlen : (flattenBlockedWord d L (List.ofFn σ)).length = n * L := by
    simpa [List.length_ofFn] using
      (length_flattenBlockedWord (d := d) (L := L) (List.ofFn σ))
  simpa [hblock, hlen] using (evalWord_mem_wordSpan A (flattenBlockedWord d L (List.ofFn σ)))

/-- If the blocked tensor has full word span at level `n`, then the original tensor
has full word span at level `n*L`. -/
theorem wordSpan_eq_top_of_blockTensor_wordSpan_eq_top
    (A : MPSTensor d D) (L n : ℕ)
    (h : wordSpan (blockTensor (d := d) (D := D) A L) n = ⊤) :
    wordSpan A (n * L) = ⊤ := by
  refine eq_top_iff.mpr ?_
  simpa [h] using (wordSpan_blockTensor_le (A := A) (L := L) (n := n))

/-- Under a nonzero-eigenvalue hypothesis, cumulative vector span lies in exact span. -/
theorem cumulativeVectorSpan_le_vectorSpreadSpan_of_eigenvector
    (A : MPSTensor d D) (φ : Fin D → ℂ) (n : ℕ)
    (i₀ : Fin d) (μ : ℂ) (hμ : μ ≠ 0)
    (heig : A i₀ *ᵥ φ = μ • φ) :
    cumulativeVectorSpan A φ n ≤ vectorSpreadSpan A φ n :=
  Kraus.cumulativeVectorSpan_le_vectorSpreadSpan_of_eigenvector A φ n i₀ μ hμ heig

/-- Under the eigenvector hypothesis, cumulative and fixed-length vector spans coincide. -/
theorem cumulativeVectorSpan_eq_vectorSpreadSpan_of_eigenvector
    (A : MPSTensor d D) (φ : Fin D → ℂ) (n : ℕ)
    (i₀ : Fin d) (μ : ℂ) (hμ : μ ≠ 0)
    (heig : A i₀ *ᵥ φ = μ • φ) :
    cumulativeVectorSpan A φ n = vectorSpreadSpan A φ n :=
  Kraus.cumulativeVectorSpan_eq_vectorSpreadSpan_of_eigenvector A φ n i₀ μ hμ heig

/-- A full cumulative vector span is already exact under the eigenvector hypothesis. -/
theorem vectorSpreadSpan_eq_top_of_cumulativeVectorSpan_eq_top_of_eigenvector
    (A : MPSTensor d D) (φ : Fin D → ℂ) (n : ℕ)
    (i₀ : Fin d) (μ : ℂ) (hμ : μ ≠ 0)
    (heig : A i₀ *ᵥ φ = μ • φ)
    (htop : cumulativeVectorSpan A φ n = ⊤) :
    vectorSpreadSpan A φ n = ⊤ :=
  Kraus.vectorSpreadSpan_eq_top_of_cumulativeVectorSpan_eq_top_of_eigenvector
    A φ n i₀ μ hμ heig htop

/-- Vector spanning and a basis of rank-one operators imply full matrix spanning.

The channel-generic statement `Kraus.wordSpan_eq_top_of_vectorSpreadSpan_eq_top_of_rankOneBasis`
records the connection with arXiv:0909.5347, Lemma 2(b). -/
theorem wordSpan_eq_top_of_vectorSpreadSpan_eq_top_of_rankOneBasis
    (A : MPSTensor d D) (φ : Fin D → ℂ) {n m : ℕ}
    (hVec : vectorSpreadSpan A φ n = ⊤)
    (hRankOne : ∀ j : Fin D,
      Matrix.vecMulVec φ (Pi.single j (1 : ℂ)) ∈ wordSpan A m) :
    wordSpan A (n + m) = ⊤ :=
  Kraus.wordSpan_eq_top_of_vectorSpreadSpan_eq_top_of_rankOneBasis A φ hVec hRankOne

end MPSTensor
