/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Examples.Z3Anomalous.Z3AnomalousDefect

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
`∏ CZ_{i,i+1} Z_i ∏ X_i` (line 2224); the phase-decorated shift used here is a `ℤ/3` operator of
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
slots. The gauge is the direct sum of the identity on the five pairs involving the identity
summand and of the four block gauges of the fusion files, and the dimension count reads
`25 = 15 + 10`.

The gauge and the conjugated letters are identified with reindexed block-diagonal matrices, so
the only decided identities of size twenty-five are the clauses of the compression theorem,
each of which evaluates a single explicit small block.

## Main definitions

* `Z3Anomalous.pairTarget`: the target of the pair `(g, h)`, the summand `U_{g+h}`.
* `Z3Anomalous.squareGaugeEis`, `Z3Anomalous.squareCoord`, `Z3Anomalous.squareOrd`: the gauge
  of the square, the labelling of its bond coordinates by the block space, and the flag order.
* `Z3Anomalous.defectSquare_compression`: the multi-block compression datum of the square.

## Main results

* `Z3Anomalous.defectSquare_trace_evalWord`, `Z3Anomalous.mpo_defect_mul_defect`: the identity
  `A² = 3A`, at the level of word traces and of periodic operators.
* `Z3Anomalous.defectSquare_isReduction`, `Z3Anomalous.defectSquare_left_mul_right_of_ne`: the
  nine biorthogonal compression pairs.
* `Z3Anomalous.defectSquare_dim_eq`: the dimension count `25 = 15 + 10`.
* `Z3Anomalous.defectSquare_evalWord_remainder_eq_zero`: the remainder is nilpotent of length
  nineteen.

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

/-! ### The gauge -/

/-- The gauge of each pair block: the block gauges of the four nontrivial fusions, and the
identity on the five pairs involving the identity summand (data file §2.5). -/
def pairGaugeEis :
    (ab : Fin 3 × Fin 3) → Matrix (Fin (pairBlockDim ab)) (Fin (pairBlockDim ab)) EisensteinInt
  | (1, 1) => uuGaugeEis
  | (1, 2) => udGaugeEis
  | (2, 1) => duGaugeEis
  | (2, 2) => ddGaugeEis
  | _ => 1

/-- The inverse gauge of each pair block. -/
def pairGaugeInvEis :
    (ab : Fin 3 × Fin 3) → Matrix (Fin (pairBlockDim ab)) (Fin (pairBlockDim ab)) EisensteinInt
  | (1, 1) => uuGaugeInvEis
  | (1, 2) => udGaugeInvEis
  | (2, 1) => duGaugeInvEis
  | (2, 2) => ddGaugeInvEis
  | _ => 1

theorem pairGauge_mul_inv : ∀ ab, pairGaugeEis ab * pairGaugeInvEis ab = 1 := by decide +kernel

theorem pairGaugeInv_mul : ∀ ab, pairGaugeInvEis ab * pairGaugeEis ab = 1 := by decide +kernel

/-- The gauge of the square: the direct sum of the pair gauges in the bond coordinates of the
square (data file §2.5). -/
def squareGaugeEis : Matrix (Fin 25) (Fin 25) EisensteinInt :=
  (Matrix.blockDiagonal' pairGaugeEis).submatrix squareBond.symm squareBond.symm

/-- The inverse gauge of the square. -/
def squareGaugeInvEis : Matrix (Fin 25) (Fin 25) EisensteinInt :=
  (Matrix.blockDiagonal' pairGaugeInvEis).submatrix squareBond.symm squareBond.symm

theorem squareGauge_mul_inv : squareGaugeEis * squareGaugeInvEis = 1 := by
  rw [squareGaugeEis, squareGaugeInvEis, Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal'_mul,
    show (fun ab => pairGaugeEis ab * pairGaugeInvEis ab) = 1 from funext pairGauge_mul_inv,
    Matrix.blockDiagonal'_one, Matrix.submatrix_one_equiv]

theorem squareGaugeInv_mul : squareGaugeInvEis * squareGaugeEis = 1 := by
  rw [squareGaugeEis, squareGaugeInvEis, Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal'_mul,
    show (fun ab => pairGaugeInvEis ab * pairGaugeEis ab) = 1 from funext pairGaugeInv_mul,
    Matrix.blockDiagonal'_one, Matrix.submatrix_one_equiv]

/-- The letters of a pair block in its block coordinates. -/
def pairConjEis (ab : Fin 3 × Fin 3) (i : Fin 9) :
    Matrix (Fin (pairBlockDim ab)) (Fin (pairBlockDim ab)) EisensteinInt :=
  pairGaugeEis ab * pairStackEis ab i * pairGaugeInvEis ab

/-- The recorded letters of each pair block in its block coordinates: the conjugated letters of
the four nontrivial fusions, and the stacked products themselves on the five pairs involving the
identity summand. -/
def pairConjTable (ab : Fin 3 × Fin 3) (i : Fin 9) :
    Matrix (Fin (pairBlockDim ab)) (Fin (pairBlockDim ab)) EisensteinInt :=
  match ab with
  | (1, 1) => uuConjEis i
  | (1, 2) => udConjEis i
  | (2, 1) => duConjEis i
  | (2, 2) => ddConjEis i
  | ab => pairStackEis ab i

theorem pairConjEis_eq : ∀ ab i, pairConjEis ab i = pairConjTable ab i := by decide +kernel

/-- **The conjugated letters of the square are block diagonal**, with the conjugated letters of
the pair blocks on the diagonal. -/
theorem square_conj (i : Fin 9) :
    squareGaugeEis * defectSquareEis i * squareGaugeInvEis =
      (Matrix.blockDiagonal' fun ab => pairConjTable ab i).submatrix squareBond.symm
        squareBond.symm := by
  rw [defectSquareEis_eq, squareGaugeEis, squareGaugeInvEis, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
  congr 2
  funext ab
  exact pairConjEis_eq ab i

/-! ### The slots, the targets and the block coordinates -/

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

/-- The position in the flag of the target block of each pair (data file §2.5, flag order). -/
def pairOrdTable : Fin 3 × Fin 3 → Fin 19
  | (0, 0) => 0
  | (0, 1) => 1
  | (0, 2) => 2
  | (1, 0) => 3
  | (1, 1) => 5
  | (1, 2) => 9
  | (2, 0) => 11
  | (2, 1) => 14
  | (2, 2) => 17

/-- The block ordering of the square: the nine target blocks and the ten zero slots in the flag
order of the data file (§2.5), pair by pair. -/
def squareOrd : BlockIndex squareSlots 10 ≃ Fin 19 where
  toFun := Sum.elim (fun s => pairOrdTable s.1) ![4, 6, 7, 8, 10, 12, 13, 15, 16, 18]
  invFun :=
    ![Sum.inl ⟨(0, 0), Finset.mem_univ _⟩,
      Sum.inl ⟨(0, 1), Finset.mem_univ _⟩,
      Sum.inl ⟨(0, 2), Finset.mem_univ _⟩,
      Sum.inl ⟨(1, 0), Finset.mem_univ _⟩,
      Sum.inr 0,
      Sum.inl ⟨(1, 1), Finset.mem_univ _⟩,
      Sum.inr 1,
      Sum.inr 2,
      Sum.inr 3,
      Sum.inl ⟨(1, 2), Finset.mem_univ _⟩,
      Sum.inr 4,
      Sum.inl ⟨(2, 0), Finset.mem_univ _⟩,
      Sum.inr 5,
      Sum.inr 6,
      Sum.inl ⟨(2, 1), Finset.mem_univ _⟩,
      Sum.inr 7,
      Sum.inr 8,
      Sum.inl ⟨(2, 2), Finset.mem_univ _⟩,
      Sum.inr 9]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- The first column of the target inside the adapted basis of each pair block: the target of a
nontrivial fusion sits after one or two zero columns (data file §2.1–§2.4). -/
def targetOffset : Fin 3 × Fin 3 → ℕ
  | (1, 1) => 1
  | (1, 2) => 2
  | (2, 1) => 2
  | (2, 2) => 1
  | _ => 0

theorem targetOffset_add_lt (s : Fin 3 × Fin 3) (p : Fin (pairTargetDim s)) :
    targetOffset s + (p : ℕ) < pairBlockDim s := by
  revert s p
  decide

/-- The coordinate of each zero slot inside the adapted basis of its pair block (data file
§2.5). -/
def zeroSlotSigma : Fin 10 → Σ ab : Fin 3 × Fin 3, Fin (pairBlockDim ab)
  | 0 => ⟨(1, 1), ⟨0, by decide⟩⟩
  | 1 => ⟨(1, 1), ⟨3, by decide⟩⟩
  | 2 => ⟨(1, 2), ⟨0, by decide⟩⟩
  | 3 => ⟨(1, 2), ⟨1, by decide⟩⟩
  | 4 => ⟨(1, 2), ⟨3, by decide⟩⟩
  | 5 => ⟨(2, 1), ⟨0, by decide⟩⟩
  | 6 => ⟨(2, 1), ⟨1, by decide⟩⟩
  | 7 => ⟨(2, 1), ⟨3, by decide⟩⟩
  | 8 => ⟨(2, 2), ⟨0, by decide⟩⟩
  | 9 => ⟨(2, 2), ⟨3, by decide⟩⟩

/-- The coordinate in the adapted basis of a pair block attached to a graded coordinate of the
square. -/
def blockSigma :
    BlockSpace pairTargetDim squareSlots 10 → Σ ab : Fin 3 × Fin 3, Fin (pairBlockDim ab)
  | ⟨Sum.inl s, p⟩ => ⟨s.1, ⟨targetOffset s.1 + p, targetOffset_add_lt s.1 p⟩⟩
  | ⟨Sum.inr t, _⟩ => zeroSlotSigma t

/-- The graded coordinate of the square attached to each bond coordinate. -/
def blockOfBond : Fin 25 → BlockSpace pairTargetDim squareSlots 10 :=
  ![⟨Sum.inl ⟨(0, 0), Finset.mem_univ _⟩, ⟨0, by decide⟩⟩,
    ⟨Sum.inl ⟨(0, 1), Finset.mem_univ _⟩, ⟨0, by decide⟩⟩,
    ⟨Sum.inl ⟨(0, 1), Finset.mem_univ _⟩, ⟨1, by decide⟩⟩,
    ⟨Sum.inl ⟨(0, 2), Finset.mem_univ _⟩, ⟨0, by decide⟩⟩,
    ⟨Sum.inl ⟨(0, 2), Finset.mem_univ _⟩, ⟨1, by decide⟩⟩,
    ⟨Sum.inl ⟨(1, 0), Finset.mem_univ _⟩, ⟨0, by decide⟩⟩,
    ⟨Sum.inr 0, ⟨0, by decide⟩⟩,
    ⟨Sum.inl ⟨(1, 1), Finset.mem_univ _⟩, ⟨0, by decide⟩⟩,
    ⟨Sum.inr 2, ⟨0, by decide⟩⟩,
    ⟨Sum.inr 3, ⟨0, by decide⟩⟩,
    ⟨Sum.inl ⟨(1, 0), Finset.mem_univ _⟩, ⟨1, by decide⟩⟩,
    ⟨Sum.inl ⟨(1, 1), Finset.mem_univ _⟩, ⟨1, by decide⟩⟩,
    ⟨Sum.inr 1, ⟨0, by decide⟩⟩,
    ⟨Sum.inl ⟨(1, 2), Finset.mem_univ _⟩, ⟨0, by decide⟩⟩,
    ⟨Sum.inr 4, ⟨0, by decide⟩⟩,
    ⟨Sum.inl ⟨(2, 0), Finset.mem_univ _⟩, ⟨0, by decide⟩⟩,
    ⟨Sum.inr 5, ⟨0, by decide⟩⟩,
    ⟨Sum.inr 6, ⟨0, by decide⟩⟩,
    ⟨Sum.inr 8, ⟨0, by decide⟩⟩,
    ⟨Sum.inl ⟨(2, 2), Finset.mem_univ _⟩, ⟨0, by decide⟩⟩,
    ⟨Sum.inl ⟨(2, 0), Finset.mem_univ _⟩, ⟨1, by decide⟩⟩,
    ⟨Sum.inl ⟨(2, 1), Finset.mem_univ _⟩, ⟨0, by decide⟩⟩,
    ⟨Sum.inr 7, ⟨0, by decide⟩⟩,
    ⟨Sum.inl ⟨(2, 2), Finset.mem_univ _⟩, ⟨1, by decide⟩⟩,
    ⟨Sum.inr 9, ⟨0, by decide⟩⟩]

/-- The labelling of the twenty-five bond coordinates of the square by the graded block space:
a graded coordinate is sent to its coordinate in the adapted basis of its pair block, then to
the bond coordinate of the square. -/
def squareCoord : BlockSpace pairTargetDim squareSlots 10 ≃ Fin 25 where
  toFun x := squareBond (blockSigma x)
  invFun := blockOfBond
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-! ### The compression datum -/

private theorem square_triangular (i : Fin 9) (x y : BlockSpace pairTargetDim squareSlots 10)
    (h : squareOrd y.1 < squareOrd x.1) :
    (squareGaugeEis * defectSquareEis i * squareGaugeInvEis) (squareCoord x) (squareCoord y) =
      0 := by
  rw [square_conj]
  revert i x y h
  decide +kernel

private theorem square_matched (i : Fin 9) (s : Fin 3 × Fin 3) :
    (Matrix.of fun p q : Fin (pairTargetDim s) =>
      (Matrix.blockDiagonal' fun ab => pairConjTable ab i).submatrix squareBond.symm
        squareBond.symm (squareCoord ⟨Sum.inl ⟨s, Finset.mem_univ s⟩, p⟩)
        (squareCoord ⟨Sum.inl ⟨s, Finset.mem_univ s⟩, q⟩)) = pairTargetEis s i := by
  revert i s
  decide +kernel

private theorem square_unmatched (i : Fin 9) (t : Fin 10) :
    (Matrix.of fun p q : Fin 1 =>
      (Matrix.blockDiagonal' fun ab => pairConjTable ab i).submatrix squareBond.symm
        squareBond.symm (squareCoord ⟨Sum.inr t, p⟩) (squareCoord ⟨Sum.inr t, q⟩)) = 0 := by
  revert i t
  decide +kernel

/-- **The multi-block asymmetric compression datum of the stacked square of the defect** (P5
note, Theorem 7.7, clauses (i)–(iii); data file §2.5): `A ⊗ A` compresses onto the nine targets
`U_{g+h}`, `(g, h) ∈ ℤ/3 × ℤ/3`, with ten zero slots. -/
def defectSquare_compression : MultiBlockCompression defectSquare squareSlots pairTarget :=
  MultiBlockCompression.ofEisenstein defectSquareEis defectSquare_eq pairTargetEis pairTarget_eq
    10 squareOrd squareCoord squareGaugeEis squareGaugeInvEis squareGauge_mul_inv
    squareGaugeInv_mul square_triangular
    (fun i s p q => by
      rw [square_conj]
      exact congrFun (congrFun (square_matched i s.1) p) q)
    (fun i t p q => by
      rw [square_conj]
      exact congrFun (congrFun (square_unmatched i t) p) q)

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
  defectSquare_compression.dim_eq

/-- **Nilpotency of the remainder** (P5 note, Theorem 7.7(vi)): a product of nineteen remainder
matrices vanishes. -/
theorem defectSquare_evalWord_remainder_eq_zero (w : List (Fin 9)) (hw : 19 ≤ w.length) :
    Kraus.evalWord defectSquare_compression.remainder w = 0 := by
  refine defectSquare_compression.evalWord_remainder_eq_zero w ?_
  change (9 : ℕ) + 10 ≤ w.length
  omega

end Z3Anomalous
