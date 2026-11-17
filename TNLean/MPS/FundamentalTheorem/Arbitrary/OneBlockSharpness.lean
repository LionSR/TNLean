/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.MultiBlock.SharpnessOneBlockGeneral
import TNLean.MPS.FundamentalTheorem.Arbitrary.ReductionPairOneBlock

/-!
# Sharpness of the one-block threshold for the embeddings

For every `z ≥ 1`, `MultiBlockExamples.SharpnessOneBlock` gives a tensor `B` on `ℂ^{1+z}` with one
letter, `B e₀ = e₀` and `B e_j = e_{j-1}`, and two reduction pairs onto the block `(1)`, with
projections `e₀ᵀ` (`rowE0`) and `e₀ᵀ + ⋯ + e_zᵀ` (`rowOnes`) and the common embedding `e₀`
(`colE0`); the identity `Ŵ B^w = μ W B^w` of the one-block theorem fails at `|w| = z - 1`
(`MultiBlockExamples.SharpnessOneBlock.exists_length_eq_sub_one_not_exists_smul`). Transposing, the
pairs `(colE0ᵀ, rowE0ᵀ)` and `(colE0ᵀ, rowOnesᵀ)` are reduction pairs from `Bᵀ` to `(1)` whose
embeddings violate `(Bᵀ)^w V̂ = μ (Bᵀ)^w V` at `|w| = z - 1`. So the threshold `|w| ≥ D - c` of the
one-block theorem cannot be lowered for the embeddings either.

## Main results

* `MultiBlockExamples.SharpnessOneBlock.isReduction_transpose_colE0_rowE0`,
  `MultiBlockExamples.SharpnessOneBlock.isReduction_transpose_colE0_rowOnes`: the transposed pairs.
* `MultiBlockExamples.SharpnessOneBlock.exists_length_eq_and_not_exists_evalWord_mul_eq_smul`:
  the failure at
  length `z - 1`.
-/

open scoped Matrix

namespace MultiBlockExamples.SharpnessOneBlock

open MPSTensor

variable (z : ℕ)

/-- **The transposed first pair**. For the tensor `B`
of the example, the transpose of the pair with projection `e₀ᵀ` and embedding `e₀`, that is the
projection `colE0ᵀ = e₀ᵀ` and the embedding `rowE0ᵀ = e₀`, is a reduction pair from `Bᵀ` to
`(1)`. -/
theorem isReduction_transpose_colE0_rowE0 :
    IsReduction (fun i => (tensorBGen z i)ᵀ) (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℂ))
      (colE0 z)ᵀ (rowE0 z)ᵀ := by
  obtain ⟨P, -, -, hl, hr, -⟩ := exists_multiBlockCompression_block_first (z := z)
  have h := P.isReduction oneSlotMem
  rw [hl, hr] at h
  simpa only [blockC, Matrix.transpose_one] using h.transpose

/-- **The transposed second pair**. For the tensor
`B` of the example, the transpose of the pair with projection `e₀ᵀ + ⋯ + e_zᵀ` and embedding `e₀`,
that is the projection `colE0ᵀ = e₀ᵀ` and the embedding `rowOnesᵀ = e₀ + ⋯ + e_z`, is a reduction
pair from `Bᵀ` to `(1)`. -/
theorem isReduction_transpose_colE0_rowOnes :
    IsReduction (fun i => (tensorBGen z i)ᵀ) (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℂ))
      (colE0 z)ᵀ (rowOnes z)ᵀ := by
  obtain ⟨Q, -, -, hl, hr, -⟩ := exists_multiBlockCompression_block_last (z := z)
  have h := Q.isReduction oneSlotMem
  rw [hl, hr] at h
  simpa only [blockC, Matrix.transpose_one] using h.transpose

/-- **Sharpness for the embeddings**. For `z ≥ 1`,
the embeddings `rowOnesᵀ` and `rowE0ᵀ` of the two reduction pairs from `Bᵀ` to `(1)` satisfy no
identity `(Bᵀ)^w rowOnesᵀ = μ (Bᵀ)^w rowE0ᵀ` at some word of length `z - 1 = D - c - 1`, so the
threshold `|w| ≥ D - c` of the one-block theorem cannot be lowered for the embeddings. -/
theorem exists_length_eq_and_not_exists_evalWord_mul_eq_smul (hz : 0 < z) :
    ∃ w : List (Fin 1), w.length = z - 1 ∧
      ¬ ∃ μ : ℂ, Kraus.evalWord (fun i => (tensorBGen z i)ᵀ) w * (rowOnes z)ᵀ =
        μ • (Kraus.evalWord (fun i => (tensorBGen z i)ᵀ) w * (rowE0 z)ᵀ) := by
  obtain ⟨w, hw, hne⟩ := exists_length_eq_sub_one_not_exists_smul (z := z) hz
  refine ⟨w.reverse, by rw [List.length_reverse, hw], fun ⟨μ, hμ⟩ => hne ⟨μ, ?_⟩⟩
  have h2 := congrArg Matrix.transpose hμ
  simp only [Matrix.transpose_mul, Matrix.transpose_smul, Matrix.transpose_transpose,
    Kraus.evalWord_transpose, List.reverse_reverse] at h2
  exact h2

end MultiBlockExamples.SharpnessOneBlock
