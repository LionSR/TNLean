/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import QICLean.Algebra.OrthogonalProjection
import TNLean.MPS.FundamentalTheorem.Reduction.AbsorbingCompression
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.CZXReviewTensor
import TNLean.MPS.MPDO.OperatorFromWordTrace
import TNLean.MPS.MPDO.SimpleScaling
import TNLean.MPS.MPDO.StackedLayers

/-!
# The CZX matrix product unitary of the review: canonical form of its square

**Source.** Cirac, Pérez-García, Schuch, Verstraete 2021 (arXiv:2011.12127), Appendix A,
"The CZX MPU", `Papers/2011.12127/TN-Review-main.tex` lines 2596–2601: the bond-four square
`B` of the CZX operator has the invariant subspace of the projector `P = diag(0,1,1,0)`; the
canonical-form construction of Section IV replaces `B` by the block
`B^{00} = [[-1,1],[0,0]]`, `B^{11} = [[0,0],[1,-1]]`; for this block the review names the
projector `Q = ½ [[1,-1],[-1,1]]`, and a second step gives the canonical form
`B^{ij} = (-1) δ_{ij}`, "which globally means `O(A)^2 = (-1)^N I`".
The construction of Section IV is at lines 1784–1797: an invariant subspace `S₁` with
orthogonal projector `P₁` and `Q₁ = 1 - P₁` satisfies `B^i P₁ = P₁ B^i P₁`,
`Q₁ B^i = Q₁ B^i Q₁` (lines 1784–1787), and `B^i` is replaced by `P₁ B^i P₁ + Q₁ B^i Q₁`
(lines 1793–1797).
Review: arXiv:2011.12127, Appendix A, "The CZX MPU".

**Formalized here.** Both projections, the Section IV relations for each of them, the printed
block and the printed canonical form, the equality of all word traces along the two reduction
steps, and the operator identity `O(A)^2 = (-1)^N I` at every positive length, obtained from
these word traces.

For `P` the relations are those of `P₁`: `P B^{ij} = B^{ij}`, so the range of `P` contains the
range of every letter and is invariant, and the complementary diagonal block vanishes.

**Side of the second projector.** The review does not say on which side the range of the printed
`Q` is invariant. Line 1788 notes that a nontrivial subspace invariant under the letters acting
on column vectors exists if and only if one invariant under their action on row vectors exists,
since the orthogonal complement of the first is the second. The printed `Q` is of the second
kind: `Q B^{ij} = Q B^{ij} Q`, so the row space of `Q` is invariant under right multiplication,
while its column range is not (`B^{00} (1,-1)ᵀ = (-2,0)ᵀ`). Equivalently `Q` plays the role of
`Q₁` of Section IV, with `P₁ = 1 - Q` the projector onto the column-invariant subspace, since
`B^{ij} Q = B^{ij}`. The block on the range of `P₁` vanishes and the block on the range of `Q`
is the printed canonical form.

## Main definitions

* `CZXCompression.reviewP`, `CZXCompression.reviewQ`: the two printed projections.
* `CZXCompression.reviewBlockInt`, `CZXCompression.reviewBlock`: the printed bond-two block.

## Main results

* `CZXCompression.reviewCZXSquare_mul_reviewP`: the range of `P` is invariant.
* `CZXCompression.reviewQ_mul_reviewBlock`: `Q` satisfies the relation of `Q₁`.
* `CZXCompression.trace_evalWord_reviewCZXSquare_eq_reviewBlock`: the square and the block have
  the same word traces.
* `CZXCompression.reviewQ_conj_reviewBlock`: the canonical form `Q B^{ij} Q = (-1) δ_{ij} Q`.
* `CZXCompression.reviewCZXSquare_trace_evalWord`: the word traces of the square are those of
  `(-1) δ_{ij}`.
* `CZXCompression.mpo_mulTensor_reviewCZXTensor`: `O(A)^2 = (-1)^N I`.

## References

- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- J. I. Cirac, D. Pérez-García,
  N. Schuch, F. Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*
-/

noncomputable section

open scoped Matrix

namespace CZXCompression

open MPSTensor

/-! ### The first projection -/

/-- The integer matrix of the projection `P = diag(0,1,1,0)`. -/
def reviewPInt : Matrix (Fin 4) (Fin 4) ℤ := Matrix.diagonal ![0, 1, 1, 0]

/-- The projection `P = diag(0,1,1,0)` onto the invariant subspace of the square.

Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` line 2597. -/
def reviewP : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal ![0, 1, 1, 0]

theorem reviewP_eq : reviewP = complexOfInt reviewPInt := by
  ext p q
  fin_cases p <;> fin_cases q <;> simp [reviewP, reviewPInt]

/-- `P` is an orthogonal projection. -/
theorem reviewP_isOrthogonalProjection : IsOrthogonalProjection reviewP := by
  refine ⟨?_, ?_⟩
  · rw [reviewP]
    exact Matrix.isHermitian_diagonal_of_self_adjoint _
      (funext fun i => by fin_cases i <;> simp)
  · rw [reviewP_eq, ← complexOfInt_mul]
    congr 1
    decide

/-- The range of `P` contains the range of every letter of the square. -/
theorem reviewP_mul_reviewCZXSquare (a : Fin 4) :
    reviewP * reviewCZXSquare a = reviewCZXSquare a := by
  rw [reviewP_eq, reviewCZXSquare_eq, ← complexOfInt_mul]
  congr 1
  revert a
  decide

/-- **The range of `P` is invariant under every letter of the square**, `B^{ij} P = P B^{ij} P`.

Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2596–2597, in the form
of the invariance condition at lines 1784–1787. -/
theorem reviewCZXSquare_mul_reviewP (a : Fin 4) :
    reviewCZXSquare a * reviewP = reviewP * reviewCZXSquare a * reviewP := by
  rw [reviewP_mul_reviewCZXSquare]

/-- The diagonal block of the square on the complement of the range of `P` vanishes. -/
theorem reviewCZXSquare_complement_block (a : Fin 4) :
    (1 - reviewP) * reviewCZXSquare a * (1 - reviewP) = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, reviewP_mul_reviewCZXSquare, sub_self, Matrix.zero_mul]

/-! ### The block -/

/-- The integer matrices of the block `B^{00} = [[-1,1],[0,0]]`, `B^{11} = [[0,0],[1,-1]]`,
in the pair alphabet. -/
def reviewBlockInt : Fin 4 → Matrix (Fin 2) (Fin 2) ℤ
  | 0 => !![-1, 1; 0, 0]
  | 1 => 0
  | 2 => 0
  | 3 => !![0, 0; 1, -1]

/-- The block of the square on the range of `P`, in the pair alphabet.

Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2598–2599. -/
def reviewBlock : MPSTensor 4 2 := fun a => complexOfInt (reviewBlockInt a)

/-- The printed block is the restriction of the square to the coordinates `1, 2` spanning the
range of `P`.

Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2596–2599. -/
theorem reviewCZXSquare_submatrix (a : Fin 4) :
    (reviewCZXSquare a).submatrix ![1, 2] ![1, 2] = reviewBlock a := by
  rw [reviewCZXSquare_eq]
  change complexOfInt ((reviewCZXSquareInt a).submatrix ![1, 2] ![1, 2]) =
    complexOfInt (reviewBlockInt a)
  congr 1
  revert a
  decide

/-- The isometry from the range of `P` onto the coordinates `1, 2`, as integer matrix. -/
def reviewW₁Int : Matrix (Fin 2) (Fin 4) ℤ := !![0, 1, 0, 0; 0, 0, 1, 0]

/-- The coordinate isometry onto the range of `P`, `W₁ = [[0,1,0,0],[0,0,1,0]]`. -/
def reviewW₁ : Matrix (Fin 2) (Fin 4) ℂ := complexOfInt reviewW₁Int

/-- The adjoint of the coordinate isometry, `V₁ = W₁ᵀ`. -/
def reviewV₁ : Matrix (Fin 4) (Fin 2) ℂ := complexOfInt reviewW₁Intᵀ

theorem reviewV₁_mul_reviewW₁ : reviewV₁ * reviewW₁ = reviewP := by
  rw [reviewV₁, reviewW₁, ← complexOfInt_mul, reviewP_eq]
  congr 1
  decide

theorem reviewBlock_eq_compress (a : Fin 4) :
    reviewBlock a = reviewW₁ * reviewCZXSquare a * reviewV₁ := by
  rw [reviewBlock, reviewW₁, reviewV₁, reviewCZXSquare_eq, ← complexOfInt_mul,
    ← complexOfInt_mul]
  congr 1
  revert a
  decide

/-- **The square and the block have the same word traces**: the first step of the review's
canonical-form reduction.

Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2598–2599, by the block
replacement of lines 1793–1797. -/
theorem trace_evalWord_reviewCZXSquare_eq_reviewBlock (w : List (Fin 4)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord reviewCZXSquare w) =
      Matrix.trace (Kraus.evalWord reviewBlock w) := by
  have h : reviewBlock = fun a => reviewW₁ * reviewCZXSquare a * reviewV₁ :=
    funext reviewBlock_eq_compress
  rw [h, Kraus.trace_evalWord_compress_of_left_absorb _ _ _ (fun a => by
    rw [reviewV₁_mul_reviewW₁, reviewP_mul_reviewCZXSquare]) w hw]

/-! ### The second projection -/

/-- The projection `Q = ½ [[1,-1],[-1,1]]`.

Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` line 2600. -/
def reviewQ : Matrix (Fin 2) (Fin 2) ℂ := (1 / 2 : ℂ) • !![1, -1; -1, 1]

/-- `Q` is an orthogonal projection. -/
theorem reviewQ_isOrthogonalProjection : IsOrthogonalProjection reviewQ := by
  refine ⟨?_, ?_⟩
  · ext p q
    fin_cases p <;> fin_cases q <;> simp [reviewQ, Matrix.conjTranspose_apply]
  · ext p q
    fin_cases p <;> fin_cases q <;>
      norm_num [reviewQ, Matrix.mul_apply, Fin.sum_univ_two]

/-- Every letter of the block annihilates the range of `1 - Q`: `B^{ij} Q = B^{ij}`. -/
theorem reviewBlock_mul_reviewQ (a : Fin 4) : reviewBlock a * reviewQ = reviewBlock a := by
  ext p q
  fin_cases a <;> fin_cases p <;> fin_cases q <;>
    norm_num [reviewBlock, reviewBlockInt, reviewQ, complexOfInt, Matrix.mul_apply,
      Fin.sum_univ_two]

/-- **`Q` satisfies the relation of `Q₁`**, `Q B^{ij} = Q B^{ij} Q`: the range of `1 - Q` is
invariant under the letters of the block. In the notation of the review's Section IV, the
printed `Q` is `Q₁ = 1 - P₁`, with `P₁ = 1 - Q` the projector onto the invariant subspace, and
the row space of `Q` is invariant under right multiplication by the letters (see the module
docstring on the side of the second projector).

Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` line 2600, read with the
relations at lines 1784–1788. -/
theorem reviewQ_mul_reviewBlock (a : Fin 4) :
    reviewQ * reviewBlock a = reviewQ * reviewBlock a * reviewQ := by
  rw [Matrix.mul_assoc, reviewBlock_mul_reviewQ]

/-- **The canonical form `B^{ij} = (-1) δ_{ij}`**: compressed by `Q`, the letters `B^{00}` and
`B^{11}` act as `-1` and the others as zero.

Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` line 2601. -/
theorem reviewQ_conj_reviewBlock (a : Fin 4) :
    reviewQ * reviewBlock a * reviewQ = (if a = 0 ∨ a = 3 then (-1 : ℂ) else 0) • reviewQ := by
  ext p q
  fin_cases a <;> fin_cases p <;> fin_cases q <;>
    norm_num [reviewBlock, reviewBlockInt, reviewQ, complexOfInt, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.vecMul, dotProduct, complexOfRing, Fin.ext_iff]

/-- The row vector `W₂ = ½ (1, -1)`. -/
def reviewW₂ : Matrix (Fin 1) (Fin 2) ℂ := (1 / 2 : ℂ) • !![1, -1]

/-- The column vector `V₂ = (1, -1)ᵀ`, with `V₂ W₂ = Q`. -/
def reviewV₂ : Matrix (Fin 2) (Fin 1) ℂ := !![1; -1]

theorem reviewV₂_mul_reviewW₂ : reviewV₂ * reviewW₂ = reviewQ := by
  ext p q
  fin_cases p <;> fin_cases q <;> norm_num [reviewV₂, reviewW₂, reviewQ, Matrix.mul_apply]

/-- **The block compresses onto the canonical form** `(-1) δ_{ij}`, the bond-one tensor
`czxSquareTarget` of `CZXSquare`.

Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` line 2601. -/
theorem reviewBlock_compress (a : Fin 4) :
    reviewW₂ * reviewBlock a * reviewV₂ = czxSquareTarget () a := by
  rw [czxSquareTarget_eq]
  ext p q
  fin_cases a <;> fin_cases p <;> fin_cases q <;>
    norm_num [reviewBlock, reviewBlockInt, reviewW₂, reviewV₂, negIdentityIntMPS,
      identityIntMPS, complexOfInt, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul,
      dotProduct, complexOfRing]

/-- **The block has the word traces of the canonical form** `(-1) δ_{ij}`: the second step of
the review's canonical-form reduction.

Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2600–2601. -/
theorem trace_evalWord_reviewBlock (w : List (Fin 4)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord reviewBlock w) =
      (-1 : ℂ) ^ w.length * Matrix.trace (Kraus.evalWord identityMPS w) := by
  rw [← Kraus.trace_evalWord_compress_of_right_absorb reviewBlock reviewW₂ reviewV₂
    (fun a => by rw [reviewV₂_mul_reviewW₂, reviewBlock_mul_reviewQ]) w hw]
  have h : (fun a => reviewW₂ * reviewBlock a * reviewV₂) = fun a => (-1 : ℂ) • identityMPS a :=
    funext reviewBlock_compress
  rw [h, Kraus.evalWord_smul, Matrix.trace_smul, smul_eq_mul]

/-- **The word traces of the square are those of `(-1) δ_{ij}`**, obtained along the review's
two reduction steps.

Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` lines 2596–2601. -/
theorem reviewCZXSquare_trace_evalWord (w : List (Fin 4)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord reviewCZXSquare w) =
      (-1 : ℂ) ^ w.length * Matrix.trace (Kraus.evalWord identityMPS w) := by
  rw [trace_evalWord_reviewCZXSquare_eq_reviewBlock w hw, trace_evalWord_reviewBlock w hw]

/-- **`O(A)^2 = (-1)^N I`** as the operator of the bond-four square, at every positive length,
obtained from the word traces of the canonical form `(-1) δ_{ij}`.

Source: arXiv:2011.12127, `Papers/2011.12127/TN-Review-main.tex` line 2601 ("which globally
means `O(A)^2 = (-1)^N I`"). -/
theorem mpo_mulTensor_reviewCZXTensor {N : ℕ} [NeZero N] :
    MPOTensor.mpo (MPOTensor.mulTensor reviewCZXTensor reviewCZXTensor) N =
      ((-1 : ℂ) ^ N) • 1 := by
  have hid : identityTensor = MPOTensor.idTensor 2 := by
    funext i j
    ext p q
    fin_cases i <;> fin_cases j <;>
      simp [identityTensor, identityIntTensor, MPOTensor.idTensor, Matrix.one_apply]
  have hneg : ((-1 : ℂ) • identityTensor).toMPSTensor = fun a => (-1 : ℂ) • identityMPS a := rfl
  rw [MPOTensor.mpo_eq_of_trace_evalWord _ ((-1 : ℂ) • identityTensor) (fun w hw => ?_) N
    (NeZero.pos N), MPOTensor.mpo_smul, hid, MPOTensor.mpo_idTensor]
  rw [hneg, Kraus.evalWord_smul, Matrix.trace_smul, smul_eq_mul]
  exact reviewCZXSquare_trace_evalWord w hw

end CZXCompression
