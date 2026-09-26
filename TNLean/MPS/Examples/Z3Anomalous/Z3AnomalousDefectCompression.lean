/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Examples.MultiBlock.OneSlotGauge
import TNLean.MPS.Examples.Z3Anomalous.Z3AnomalousDefect
import TNLean.MPS.FundamentalTheorem.Reduction.MultiBlockDirectSum

/-!
# Anomalous `ℤ/3` example: compression of the stacked square of the condensation defect

**Source.** Construction of this development: no source prints the `ℤ/3` tensors of
`Z3AnomalousTensor.lean` or the compression data below. Garre-Rubio and Schuch
(arXiv:2405.00439), subsection "Example: `G = ℤ_n` with fully symmetry breaking",
`Papers/2405.00439/MPU-DW.tex` lines 2038–2040, print the cyclic `3`-cocycles
`ω_j(a, b, c) = exp(2πi j a (b + c - [b + c]) / n²)` of `ℤ/n`; the representative used here has
class `j = 1` for `n = 3`, a fact checked only in the verification script and not formalized.
Garre-Rubio, Lootens and Molnár (arXiv:2203.12563), subsubsection "Periodic boundary condition
case", `Papers/2203.12563/REsubmission.tex` lines 2202–2224, construct periodic matrix product
operator representations of a finite group with a `3`-cocycle and print the `ℤ/2` instance
`∏ CZ_{i,i+1} Z_i ∏ X_i` (line 2222); the phase-decorated shift used here is a `ℤ/3` operator of
the same kind, not the operator of that construction.

The name *condensation defect* follows Roumpedakis, Seifnashri and Shao (arXiv:2204.02407),
subsection "Higher gauging and condensation defects",
`References/2204.02407/source/condensation_draft.tex` lines 145–150, where a condensation
defect is a sum over insertions of symmetry defects on a submanifold. That paper treats
`1`-form symmetries of `2+1`-dimensional quantum field theories; the lattice defect
`A = 1 ⊕ U ⊕ U†`, the sum of the three group operators, and its fusion `A² = 3A` are
constructions of this development.

**Formalized here.** An instance of the multi-block asymmetric compression theorem of this
development (P5 note, `Notes/OpenProblemsTN/problems/p5_asymmetric_fundamental_theorem.tex`,
theorem `thm:p5-asymmetric-compression`, lines 495–569) for the stacked square of the
condensation defect `A = 1 ⊕ U ⊕ U†` of `Z3AnomalousDefect.lean`. Because the representation is
exact, the defect satisfies `A² = 3A` at every positive length: its structure constants are
constant, every weight equal to one, in contrast with the length-dependent coefficients of the
non-anomalous clock symmetry of the data file (§3) and of the `ℤ/2` Example E. The stacked
square compresses onto nine slots, three copies each of `δ`, `U` and `U†`, with `z = 10` zero
slots. The datum is the direct sum (`MultiBlockCompression.directSum`) of the nine pair-block
data: the identity gauge with no zero slot on the five pairs involving the identity summand, and
the four block data of the fusion files; the dimension count reads `25 = 15 + 10`. Its remainder
is the direct sum of the pair remainders, so it is nilpotent of order exactly three, the order
of the four nontrivial fusion blocks, instead of the generic bound `|S| + z = 19` of the
compression theorem.

## Main definitions

* `Z3Anomalous.pairTarget`: the target of the pair `(g, h)`, the summand `U_{g+h}`.
* `Z3Anomalous.pairStackMPS`, `Z3Anomalous.pairCompression`: the nine pair blocks of the square
  and their compression data.
* `Z3Anomalous.defectSquare_compression`: the multi-block compression datum of the square.

## Main results

* `Z3Anomalous.defectSquare_trace_evalWord`, `Z3Anomalous.mpo_defect_mul_defect`: the identity
  `A² = 3A`, at the level of word traces and of periodic operators.
* `Z3Anomalous.defectSquare_isReduction`, `Z3Anomalous.defectSquare_left_mul_right_of_ne`: the
  nine biorthogonal compression pairs.
* `Z3Anomalous.defectSquare_dim_eq`: the dimension count `25 = 15 + 10`.
* `Z3Anomalous.defectSquare_eq_blockDiagonal`: the square is block diagonal over the nine pairs.
* `Z3Anomalous.defectSquare_evalWord_remainder_eq_zero`,
  `Z3Anomalous.defectSquare_remainder_mul_ne_zero`: the remainder is nilpotent of order exactly
  three.

## References

- [arXiv:2405.00439](https://arxiv.org/abs/2405.00439) -- J. Garre-Rubio, N. Schuch,
  *Fractional domain wall statistics in spin chains with anomalous symmetries*
- [arXiv:2203.12563](https://arxiv.org/abs/2203.12563) -- J. Garre-Rubio, L. Lootens,
  A. Molnár, *Classifying phases protected by matrix product operator symmetries using matrix
  product states*
- [arXiv:2204.02407](https://arxiv.org/abs/2204.02407) -- K. Roumpedakis, S. Seifnashri,
  S.-H. Shao, *Higher Gauging and Non-invertible Condensation Defects*

## Provenance

The compression datum and the exact-arithmetic certificates were first recorded in
`Notes/OpenProblemsTN/checks/asym_z3_anomalous_data.md`, §2.5, and checked over `ℤ[ω]` by
`Notes/OpenProblemsTN/checks/asym_z3_anomalous_verify.py`; they are verification records, not the
source.
-/

noncomputable section

open scoped Matrix

namespace Z3Anomalous

open EisensteinInt MPSTensor

/-! ### The slots and the targets -/

/-- The bond dimension of the target of the pair `(g, h)`: that of the summand `U_{g+h}`. -/
abbrev pairTargetDim (ab : Fin 3 × Fin 3) : ℕ := summandDim (ab.1 + ab.2)

/-- The target of the pair `(g, h)`: the summand `U_{g+h}`, with multiplicity one and weight
one (data file §2.5). -/
def pairTarget (ab : Fin 3 × Fin 3) : MPSTensor 9 (pairTargetDim ab) := summandMPS (ab.1 + ab.2)

/-- The Eisenstein matrices of the target of the pair `(g, h)`. -/
def pairTargetEis (ab : Fin 3 × Fin 3) :
    Fin 9 → Matrix (Fin (pairTargetDim ab)) (Fin (pairTargetDim ab)) EisensteinInt :=
  summandEisMPS (ab.1 + ab.2)

theorem pairTarget_eq (ab : Fin 3 × Fin 3) (i : Fin 9) :
    pairTarget ab i = complexOfEisenstein (pairTargetEis ab i) :=
  summandMPS_eq _ i

/-- The slots of the square: all nine pairs of summands. -/
abbrev squareSlots : Finset (Fin 3 × Fin 3) := Finset.univ

/-! ### The pair blocks and their compression data -/

/-- The stacked product `U_g ⊗ U_h` of two summands: the stacked tensors of the four nontrivial
fusions, and the stacked products with the identity summand on the other five pairs. -/
def pairStackMPS : (ab : Fin 3 × Fin 3) → MPSTensor 9 (pairBlockDim ab)
  | (0, 0) => fun a => complexOfEisenstein (pairStackEis (0, 0) a)
  | (0, 1) => fun a => complexOfEisenstein (pairStackEis (0, 1) a)
  | (0, 2) => fun a => complexOfEisenstein (pairStackEis (0, 2) a)
  | (1, 0) => fun a => complexOfEisenstein (pairStackEis (1, 0) a)
  | (1, 1) => uuStack
  | (1, 2) => udStack
  | (2, 0) => fun a => complexOfEisenstein (pairStackEis (2, 0) a)
  | (2, 1) => duStack
  | (2, 2) => ddStack

theorem pairStackMPS_eq (ab : Fin 3 × Fin 3) (a : Fin 9) :
    pairStackMPS ab a = complexOfEisenstein (pairStackEis ab a) := by
  obtain ⟨g, h⟩ := ab
  fin_cases g <;> fin_cases h
  exacts [rfl, rfl, rfl, rfl, uuStack_eq a, udStack_eq a, rfl, duStack_eq a, ddStack_eq a]

/-- **The stacked square is block diagonal over the nine pairs of summands**, the `(g, h)`
block being the stacked product `U_g ⊗ U_h` (data file §2.5). -/
theorem defectSquare_eq_blockDiagonal (a : Fin 9) :
    defectSquare a =
      (Matrix.blockDiagonal' fun ab => pairStackMPS ab a).submatrix squareBond.symm
        squareBond.symm := by
  rw [defectSquare_eq, defectSquareEis_eq, complexOfEisenstein_submatrix,
    complexOfEisenstein_blockDiagonal']
  congr 2
  funext ab
  exact (pairStackMPS_eq ab a).symm

/-! On the five pairs involving the identity summand, the stacked product is the target itself
under the natural bond identification (data file §2.5). -/

private theorem stack00_eq (a : Fin 9) :
    (pairStackEis (0, 0) a : Matrix (Fin 1) (Fin 1) EisensteinInt) = identityEisMPS a := by
  refine Matrix.ext fun i j => ?_
  fin_cases a <;> fin_cases i <;> fin_cases j <;> rfl

private theorem pairStack00_eq (a : Fin 9) : pairStackMPS (0, 0) a = pairTarget (0, 0) a :=
  (congrArg complexOfEisenstein (stack00_eq a)).trans (identityMPS_eq a).symm

private theorem stack01_eq (a : Fin 9) :
    (pairStackEis (0, 1) a : Matrix (Fin 2) (Fin 2) EisensteinInt) = uEisMPS a := by
  refine Matrix.ext fun i j => ?_
  fin_cases a <;> fin_cases i <;> fin_cases j <;> rfl

private theorem pairStack01_eq (a : Fin 9) : pairStackMPS (0, 1) a = pairTarget (0, 1) a :=
  (congrArg complexOfEisenstein (stack01_eq a)).trans (uMPS_eq a).symm

private theorem stack02_eq (a : Fin 9) :
    (pairStackEis (0, 2) a : Matrix (Fin 2) (Fin 2) EisensteinInt) = uDagEisMPS a := by
  refine Matrix.ext fun i j => ?_
  fin_cases a <;> fin_cases i <;> fin_cases j <;> rfl

private theorem pairStack02_eq (a : Fin 9) : pairStackMPS (0, 2) a = pairTarget (0, 2) a :=
  (congrArg complexOfEisenstein (stack02_eq a)).trans (uDagMPS_eq a).symm

private theorem stack10_eq (a : Fin 9) :
    (pairStackEis (1, 0) a : Matrix (Fin 2) (Fin 2) EisensteinInt) = uEisMPS a := by
  refine Matrix.ext fun i j => ?_
  fin_cases a <;> fin_cases i <;> fin_cases j <;> rfl

private theorem pairStack10_eq (a : Fin 9) : pairStackMPS (1, 0) a = pairTarget (1, 0) a :=
  (congrArg complexOfEisenstein (stack10_eq a)).trans (uMPS_eq a).symm

private theorem stack20_eq (a : Fin 9) :
    (pairStackEis (2, 0) a : Matrix (Fin 2) (Fin 2) EisensteinInt) = uDagEisMPS a := by
  refine Matrix.ext fun i j => ?_
  fin_cases a <;> fin_cases i <;> fin_cases j <;> rfl

private theorem pairStack20_eq (a : Fin 9) : pairStackMPS (2, 0) a = pairTarget (2, 0) a :=
  (congrArg complexOfEisenstein (stack20_eq a)).trans (uDagMPS_eq a).symm

/-- The compression datum of each pair block: the data of the four nontrivial fusions
(`Z3AnomalousFusion.lean`, `Z3AnomalousInverseFusion.lean`), and, on the five pairs involving the
identity summand, the identity gauge with no zero slot, the pair block being equal to its target
(data file §2.5). -/
def pairCompression :
    (ab : Fin 3 × Fin 3) → MultiBlockCompression (pairStackMPS ab) oneSlot
      (fun _ : Unit => pairTarget ab)
  | (0, 0) => MultiBlockCompression.ofEq pairStack00_eq
  | (0, 1) => MultiBlockCompression.ofEq pairStack01_eq
  | (0, 2) => MultiBlockCompression.ofEq pairStack02_eq
  | (1, 0) => MultiBlockCompression.ofEq pairStack10_eq
  | (1, 1) => uu_compression
  | (1, 2) => ud_compression
  | (2, 0) => MultiBlockCompression.ofEq pairStack20_eq
  | (2, 1) => du_compression
  | (2, 2) => dd_compression

/-- **Every word of length at least three vanishes in the remainder of each pair block**: the
four nontrivial fusions have remainders nilpotent of order three, and the five pairs involving
the identity summand have zero remainder. -/
theorem pairCompression_evalWord_remainder_eq_zero (ab : Fin 3 × Fin 3) (w : List (Fin 9))
    (hw : 3 ≤ w.length) : Kraus.evalWord (pairCompression ab).remainder w = 0 := by
  have htriv : ∀ ab, (pairCompression ab).remainder = 0 →
      Kraus.evalWord (pairCompression ab).remainder w = 0 := by
    intro ab h
    obtain ⟨a, w, rfl⟩ : ∃ a w', w = a :: w' := w.exists_cons_of_length_pos (by omega)
    rw [h]
    simp [Kraus.evalWord]
  obtain ⟨g, h⟩ := ab
  fin_cases g <;> fin_cases h
  · exact htriv _ (MultiBlockCompression.remainder_ofEq pairStack00_eq)
  · exact htriv _ (MultiBlockCompression.remainder_ofEq pairStack01_eq)
  · exact htriv _ (MultiBlockCompression.remainder_ofEq pairStack02_eq)
  · exact htriv _ (MultiBlockCompression.remainder_ofEq pairStack10_eq)
  · exact uu_evalWord_remainder_eq_zero w hw
  · exact ud_evalWord_remainder_eq_zero w hw
  · exact htriv _ (MultiBlockCompression.remainder_ofEq pairStack20_eq)
  · exact du_evalWord_remainder_eq_zero w hw
  · exact dd_evalWord_remainder_eq_zero w hw

/-- **The multi-block asymmetric compression datum of the stacked square of the defect** (P5
note, Theorem 7.7, clauses (i)–(iii); data file §2.5): `A ⊗ A` compresses onto the nine targets
`U_{g+h}`, `(g, h) ∈ ℤ/3 × ℤ/3`. It is the direct sum of the nine pair-block data, transported
along the block-diagonal form of the square. -/
def defectSquare_compression : MultiBlockCompression defectSquare squareSlots pairTarget :=
  MultiBlockCompression.directSum pairCompression squareBond defectSquare_eq_blockDiagonal

/-- The assembled datum has ten zero slots: two in each of the blocks `U ⊗ U` and `U† ⊗ U†`,
three in each of the blocks `U ⊗ U†` and `U† ⊗ U`, and none elsewhere (data file §2.5). -/
theorem defectSquare_compression_z : defectSquare_compression.z = 10 := rfl

/-! ### Consequences -/

/-- **The identity `A² = 3A` at the level of word traces** (data file §2.5): at every positive
length the stacked square has three times the word traces of each summand. -/
theorem defectSquare_trace_evalWord (w : List (Fin 9)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord defectSquare w) =
      3 * (Matrix.trace (Kraus.evalWord identityMPS w) + Matrix.trace (Kraus.evalWord uMPS w) +
        Matrix.trace (Kraus.evalWord uDagMPS w)) := by
  have h := defectSquare_compression.trace_evalWord_eq_sum w hw
  rw [Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three,
    Fin.sum_univ_three] at h
  have e00 : Matrix.trace (Kraus.evalWord (pairTarget (0, 0)) w) =
      Matrix.trace (Kraus.evalWord identityMPS w) := rfl
  have e01 : Matrix.trace (Kraus.evalWord (pairTarget (0, 1)) w) =
      Matrix.trace (Kraus.evalWord uMPS w) := rfl
  have e02 : Matrix.trace (Kraus.evalWord (pairTarget (0, 2)) w) =
      Matrix.trace (Kraus.evalWord uDagMPS w) := rfl
  have e10 : Matrix.trace (Kraus.evalWord (pairTarget (1, 0)) w) =
      Matrix.trace (Kraus.evalWord uMPS w) := rfl
  have e11 : Matrix.trace (Kraus.evalWord (pairTarget (1, 1)) w) =
      Matrix.trace (Kraus.evalWord uDagMPS w) := rfl
  have e12 : Matrix.trace (Kraus.evalWord (pairTarget (1, 2)) w) =
      Matrix.trace (Kraus.evalWord identityMPS w) := rfl
  have e20 : Matrix.trace (Kraus.evalWord (pairTarget (2, 0)) w) =
      Matrix.trace (Kraus.evalWord uDagMPS w) := rfl
  have e21 : Matrix.trace (Kraus.evalWord (pairTarget (2, 1)) w) =
      Matrix.trace (Kraus.evalWord identityMPS w) := rfl
  have e22 : Matrix.trace (Kraus.evalWord (pairTarget (2, 2)) w) =
      Matrix.trace (Kraus.evalWord uMPS w) := rfl
  rw [h, e00, e01, e02, e10, e11, e12, e20, e21, e22]
  ring

/-- **The condensation defect squares to three times itself**, `A² = 3A`, as an identity of
periodic operators at every positive length (data file §0 and §2.5): the structure constants of
the defect are constant, every weight equal to one, because the representation is exact. -/
theorem mpo_defect_mul_defect (L : ℕ) (hL : 0 < L) :
    MPOTensor.mpo defectTensor L * MPOTensor.mpo defectTensor L =
      (3 : ℂ) • MPOTensor.mpo defectTensor L := by
  rw [← MPOTensor.mpo_mulTensor]
  ext σ τ
  rw [Matrix.smul_apply, MPOTensor.mpo_apply_toMPSTensor, MPOTensor.mpo_apply_toMPSTensor,
    smul_eq_mul]
  exact (defectSquare_trace_evalWord _ (MPOTensor.ofFn_pairConfig_ne_nil hL σ τ)).trans
    (congrArg (fun t => 3 * t) (defectMPS_trace_evalWord _)).symm

/-- **Biorthogonal compression onto each of the nine slots** (P5 note, Theorem 7.7(iv)–(v)). -/
theorem defectSquare_isReduction (s : {s // s ∈ squareSlots}) :
    IsReduction defectSquare (pairTarget s.1) (defectSquare_compression.left s)
      (defectSquare_compression.right s) :=
  defectSquare_compression.isReduction s

/-- Two distinct slots of the square are biorthogonal (P5 note, Theorem 7.7(iv)). -/
theorem defectSquare_left_mul_right_of_ne {s t : {s // s ∈ squareSlots}} (h : s ≠ t) :
    defectSquare_compression.left s * defectSquare_compression.right t = 0 :=
  defectSquare_compression.left_mul_right_of_ne h

/-- The nine targets have total bond dimension `3 · (1 + 2 + 2) = 15`. -/
theorem sum_pairTargetDim : ∑ s ∈ squareSlots, pairTargetDim s = 15 := by decide

/-- **The dimension count** `25 = 15 + 10` (P5 note, Theorem 7.7(vii)). -/
theorem defectSquare_dim_eq : (25 : ℕ) = ∑ s ∈ squareSlots, pairTargetDim s + 10 :=
  defectSquare_compression_z ▸ defectSquare_compression.dim_eq

/-- **Nilpotency of the remainder, of order three** (P5 note, Theorem 7.7(vi); data file
§2.5): every word of length at least three vanishes in the remainder, sharpening the generic
bound `|S| + z = 9 + 10 = 19` of clause (vi). The remainder is the direct sum of the remainders
of the nine pair blocks, each of which vanishes on words of length three. -/
theorem defectSquare_evalWord_remainder_eq_zero (w : List (Fin 9)) (hw : 3 ≤ w.length) :
    Kraus.evalWord defectSquare_compression.remainder w = 0 :=
  MultiBlockCompression.evalWord_remainder_directSum_eq_zero _ _ _ w fun ab =>
    pairCompression_evalWord_remainder_eq_zero ab w hw

/-- **The nilpotency order three is exact** (data file §2.5): the product of the remainder
letters `1` and `5` does not vanish, because it does not vanish in the block `U ⊗ U`. -/
theorem defectSquare_remainder_mul_ne_zero :
    defectSquare_compression.remainder 1 * defectSquare_compression.remainder 5 ≠ 0 := by
  have h := MultiBlockCompression.evalWord_remainder_directSum_ne_zero pairCompression squareBond
    defectSquare_eq_blockDiagonal [1, 5] (1, 1) (by
      change uu_compression.remainder 1 *
        (uu_compression.remainder 5 * (1 : Matrix (Fin 4) (Fin 4) ℂ)) ≠ 0
      rw [Matrix.mul_one]
      exact uu_remainder_mul_ne_zero)
  change defectSquare_compression.remainder 1 *
    (defectSquare_compression.remainder 5 * (1 : Matrix (Fin 25) (Fin 25) ℂ)) ≠ 0 at h
  rwa [Matrix.mul_one] at h

end Z3Anomalous
