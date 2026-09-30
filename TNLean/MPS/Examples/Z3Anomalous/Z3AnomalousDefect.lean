/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Examples.Z3Anomalous.Z3AnomalousInverseFusion

/-!
# Anomalous `ℤ/3` example: the condensation defect `1 ⊕ U ⊕ U†` and its stacked square

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

**Formalized here.** The defect is the block-diagonal tensor of bond dimension five whose
blocks are the identity tensor and the two nontrivial group elements, and its periodic operator
is the sum of the three group operators. The stacked square `A ⊗ A` of bond dimension
twenty-five is block diagonal over the nine pairs of summands, the `(g, h)` block being the
stacked product `U_g ⊗ U_h`. This file sets the square up for the multi-block asymmetric
compression theorem of this development (P5 note,
`Notes/OpenProblemsTN/problems/p5_asymmetric_fundamental_theorem.tex`, theorem
`thm:p5-asymmetric-compression`, lines 495–569); the compression datum and the identity
`A² = 3A` are in `Z3AnomalousDefectCompression.lean`. Because the representation is exact, the
structure constants of `A²` are constant, every weight equal to one, in contrast with the
length-dependent coefficients of the non-anomalous clock symmetry of the data file (§3) and of
the `ℤ/2` Example E.

The assembly is carried out abstractly: the defect is defined as a reindexed block-diagonal
tensor, and its square is identified with the reindexed block-diagonal tensor of the nine
stacked products by an entrywise decision, so that no product of matrices of size twenty-five
is ever decided.

## Main definitions

* `Z3Anomalous.summandDim`, `Z3Anomalous.summandMPS`: the three summands `δ`, `U`, `U†`.
* `Z3Anomalous.defectTensor`, `Z3Anomalous.defectMPS`: the condensation defect `1 ⊕ U ⊕ U†`.
* `Z3Anomalous.defectSquare`: its stacked square, of bond dimension twenty-five.
* `Z3Anomalous.pairStackEis`, `Z3Anomalous.squareBond`: the nine pair blocks and the labelling
  of the bond coordinates of the square by their coordinates.

## Main results

* `Z3Anomalous.defectMPS_trace_evalWord`, `Z3Anomalous.mpo_defectTensor`: the defect is the sum
  of its three summands.
* `Z3Anomalous.defectSquareEis_eq`: the square is block diagonal over the nine pairs of
  summands.

## References

- [arXiv:2405.00439](https://arxiv.org/abs/2405.00439) -- J. Garre-Rubio, N. Schuch,
  *Fractional domain wall statistics in spin chains with anomalous symmetries*
- [arXiv:2203.12563](https://arxiv.org/abs/2203.12563) -- J. Garre-Rubio, L. Lootens,
  A. Molnár, *Classifying phases protected by matrix product operator symmetries using matrix
  product states*
- [arXiv:2204.02407](https://arxiv.org/abs/2204.02407) -- K. Roumpedakis, S. Seifnashri,
  S.-H. Shao, *Higher Gauging and Non-invertible Condensation Defects*

## Provenance

The defect data were first recorded in `Notes/OpenProblemsTN/checks/asym_z3_anomalous_data.md`,
§2.5, and checked over `ℤ[ω]` by `Notes/OpenProblemsTN/checks/asym_z3_anomalous_verify.py`;
they are verification records, not the source.
-/

noncomputable section

open scoped Matrix

namespace Z3Anomalous

open EisensteinInt MPSTensor

/-! ### The three summands and the defect -/

/-- The bond dimensions of the three summands `δ`, `U`, `U†`. -/
def summandDim : Fin 3 → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 2

/-- The three summands over `ℤ[ω]`, as matrix product operator tensors: the group elements
`U_0 = 1`, `U_1 = U`, `U_2 = U†` of the representation. -/
def summandEis :
    (k : Fin 3) → Fin 3 → Fin 3 → Matrix (Fin (summandDim k)) (Fin (summandDim k)) EisensteinInt
  | 0 => identityEis
  | 1 => uEis
  | 2 => uDagEis

/-- The three summands as pair-alphabet tensors. -/
def summandMPS : (k : Fin 3) → MPSTensor 9 (summandDim k)
  | 0 => identityMPS
  | 1 => uMPS
  | 2 => uDagMPS

/-- The Eisenstein matrices of the pair-alphabet summands. -/
def summandEisMPS (k : Fin 3) :
    Fin 9 → Matrix (Fin (summandDim k)) (Fin (summandDim k)) EisensteinInt :=
  fun a => summandEis k (Fin.divNat (m := 3) (n := 3) a) (Fin.modNat (m := 3) (n := 3) a)

theorem summandMPS_eq (k : Fin 3) (a : Fin 9) :
    summandMPS k a = complexOfEisenstein (summandEisMPS k a) := by
  fin_cases k <;> rfl

/-- The first bond coordinate of each summand inside the bond space of the defect: `δ` occupies
the coordinate `0`, `U` the coordinates `1, 2` and `U†` the coordinates `3, 4` (data file
§2.5). -/
def summandOffset : Fin 3 → ℕ := ![0, 1, 3]

/-- The bond coordinate of the defect attached to a coordinate of a summand. -/
def defectBondNat (x : Σ k : Fin 3, Fin (summandDim k)) : ℕ := summandOffset x.1 + (x.2 : ℕ)

theorem defectBondNat_lt (x : Σ k : Fin 3, Fin (summandDim k)) : defectBondNat x < 5 := by
  revert x
  decide

/-- The labelling of the five bond coordinates of the defect by the coordinates of its
summands. -/
def defectBond : (Σ k : Fin 3, Fin (summandDim k)) ≃ Fin 5 where
  toFun x := ⟨defectBondNat x, defectBondNat_lt x⟩
  invFun
    | 0 => ⟨0, ⟨0, by decide⟩⟩
    | 1 => ⟨1, ⟨0, by decide⟩⟩
    | 2 => ⟨1, ⟨1, by decide⟩⟩
    | 3 => ⟨2, ⟨0, by decide⟩⟩
    | 4 => ⟨2, ⟨1, by decide⟩⟩
  left_inv := by decide
  right_inv := by decide

/-- The condensation defect `A = 1 ⊕ U ⊕ U†` over `ℤ[ω]`: the block-diagonal tensor of bond
dimension five with the three summands on its diagonal (data file §2.5). -/
def defectEis (i j : Fin 3) : Matrix (Fin 5) (Fin 5) EisensteinInt :=
  (Matrix.blockDiagonal' fun k => summandEis k i j).submatrix defectBond.symm defectBond.symm

/-- The condensation defect as a matrix product operator tensor. -/
def defectTensor : MPOTensor 3 5 := fun i j => complexOfEisenstein (defectEis i j)

/-- The condensation defect read as a tensor over the pair alphabet `Fin 9`. -/
def defectMPS : MPSTensor 9 5 := defectTensor.toMPSTensor

/-- The Eisenstein matrices of the pair-alphabet defect. -/
def defectEisMPS : Fin 9 → Matrix (Fin 5) (Fin 5) EisensteinInt :=
  fun a => defectEis (Fin.divNat (m := 3) (n := 3) a) (Fin.modNat (m := 3) (n := 3) a)

theorem defectMPS_eq (a : Fin 9) : defectMPS a = complexOfEisenstein (defectEisMPS a) := rfl

/-- The letter `(1, 0)` of the defect is the recorded one: the column `(1, 1)ᵀ` of `U` in the
coordinates `1, 2` (data file §2.5). -/
theorem defectEis_apply_one_zero :
    defectEis 1 0 =
      !![0, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0] := by
  decide +kernel

theorem defectMPS_eq_blockDiagonal (a : Fin 9) :
    defectMPS a =
      (Matrix.blockDiagonal' fun k => summandMPS k a).submatrix defectBond.symm
        defectBond.symm := by
  rw [defectMPS_eq]
  change complexOfEisenstein ((Matrix.blockDiagonal' fun k => summandEisMPS k a).submatrix
    defectBond.symm defectBond.symm) = _
  rw [complexOfEisenstein_submatrix, complexOfEisenstein_blockDiagonal']
  congr 2
  funext k
  exact (summandMPS_eq k a).symm

/-- **The defect is the sum of its summands at the level of word traces.** -/
theorem defectMPS_trace_evalWord (w : List (Fin 9)) :
    Matrix.trace (Kraus.evalWord defectMPS w) =
      Matrix.trace (Kraus.evalWord identityMPS w) + Matrix.trace (Kraus.evalWord uMPS w) +
        Matrix.trace (Kraus.evalWord uDagMPS w) := by
  have h := trace_evalWord_blockDiagonal'_submatrix defectBond (fun a k => summandMPS k a) w
  rw [show (fun a => (Matrix.blockDiagonal' fun k => summandMPS k a).submatrix
      defectBond.symm defectBond.symm) = defectMPS from
    funext fun a => (defectMPS_eq_blockDiagonal a).symm] at h
  rw [h, Fin.sum_univ_three]
  rfl

/-- **The defect is the sum of its summands as periodic operators**: `A = 1 + U + U†` at every
length. -/
theorem mpo_defectTensor (L : ℕ) :
    MPOTensor.mpo defectTensor L =
      MPOTensor.mpo identityTensor L + MPOTensor.mpo uTensor L + MPOTensor.mpo uDagTensor L := by
  ext σ τ
  rw [Matrix.add_apply, Matrix.add_apply, MPOTensor.mpo_apply_toMPSTensor,
    MPOTensor.mpo_apply_toMPSTensor, MPOTensor.mpo_apply_toMPSTensor,
    MPOTensor.mpo_apply_toMPSTensor]
  exact defectMPS_trace_evalWord _

/-! ### The stacked square and its pair blocks -/

/-- The stacked square `A ⊗ A` of the defect, of bond dimension twenty-five (data file §2.5). -/
def defectSquare : MPSTensor 9 25 := (MPOTensor.mulTensor defectTensor defectTensor).toMPSTensor

/-- The Eisenstein matrices of the stacked square, in the bond order `5 p₁ + p₂`. -/
def defectSquareEis : Fin 9 → Matrix (Fin 25) (Fin 25) EisensteinInt :=
  fun a => mulTensorR defectEis defectEis (Fin.divNat (m := 3) (n := 3) a)
    (Fin.modNat (m := 3) (n := 3) a)

theorem defectSquare_eq (a : Fin 9) : defectSquare a = complexOfEisenstein (defectSquareEis a) :=
  mulTensor_complexOfRing _ defectEis defectEis _ _

/-- The bond dimension of the pair block `U_g ⊗ U_h`. -/
abbrev pairBlockDim (ab : Fin 3 × Fin 3) : ℕ := summandDim ab.1 * summandDim ab.2

/-- The stacked product `U_g ⊗ U_h` of two summands, over `ℤ[ω]`. -/
def pairStackEis (ab : Fin 3 × Fin 3) :
    Fin 9 → Matrix (Fin (pairBlockDim ab)) (Fin (pairBlockDim ab)) EisensteinInt :=
  fun a => mulTensorR (summandEis ab.1) (summandEis ab.2)
    (Fin.divNat (m := 3) (n := 3) a) (Fin.modNat (m := 3) (n := 3) a)

/-- The bond coordinate of the square attached to a coordinate of a pair block, in the bond
order `5 p₁ + p₂` of `A ⊗ A`. -/
def squareBondNat (x : Σ ab : Fin 3 × Fin 3, Fin (pairBlockDim ab)) : ℕ :=
  5 * (summandOffset x.1.1 + (x.2 : ℕ) / summandDim x.1.2) + summandOffset x.1.2 +
    (x.2 : ℕ) % summandDim x.1.2

theorem squareBondNat_lt (x : Σ ab : Fin 3 × Fin 3, Fin (pairBlockDim ab)) :
    squareBondNat x < 25 := by
  revert x
  decide

/-- The labelling of the twenty-five bond coordinates of the square by the coordinates of the
nine pair blocks. -/
def squareBond : (Σ ab : Fin 3 × Fin 3, Fin (pairBlockDim ab)) ≃ Fin 25 where
  toFun x := ⟨squareBondNat x, squareBondNat_lt x⟩
  invFun :=
    ![⟨(0, 0), ⟨0, by decide⟩⟩,
      ⟨(0, 1), ⟨0, by decide⟩⟩,
      ⟨(0, 1), ⟨1, by decide⟩⟩,
      ⟨(0, 2), ⟨0, by decide⟩⟩,
      ⟨(0, 2), ⟨1, by decide⟩⟩,
      ⟨(1, 0), ⟨0, by decide⟩⟩,
      ⟨(1, 1), ⟨0, by decide⟩⟩,
      ⟨(1, 1), ⟨1, by decide⟩⟩,
      ⟨(1, 2), ⟨0, by decide⟩⟩,
      ⟨(1, 2), ⟨1, by decide⟩⟩,
      ⟨(1, 0), ⟨1, by decide⟩⟩,
      ⟨(1, 1), ⟨2, by decide⟩⟩,
      ⟨(1, 1), ⟨3, by decide⟩⟩,
      ⟨(1, 2), ⟨2, by decide⟩⟩,
      ⟨(1, 2), ⟨3, by decide⟩⟩,
      ⟨(2, 0), ⟨0, by decide⟩⟩,
      ⟨(2, 1), ⟨0, by decide⟩⟩,
      ⟨(2, 1), ⟨1, by decide⟩⟩,
      ⟨(2, 2), ⟨0, by decide⟩⟩,
      ⟨(2, 2), ⟨1, by decide⟩⟩,
      ⟨(2, 0), ⟨1, by decide⟩⟩,
      ⟨(2, 1), ⟨2, by decide⟩⟩,
      ⟨(2, 1), ⟨3, by decide⟩⟩,
      ⟨(2, 2), ⟨2, by decide⟩⟩,
      ⟨(2, 2), ⟨3, by decide⟩⟩]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- **The stacked square is block diagonal over the nine pairs of summands**, the `(g, h)` block
being the stacked product `U_g ⊗ U_h` (data file §2.5). -/
theorem defectSquareEis_eq (a : Fin 9) :
    defectSquareEis a =
      (Matrix.blockDiagonal' fun ab => pairStackEis ab a).submatrix squareBond.symm
        squareBond.symm := by
  revert a
  decide +kernel

end Z3Anomalous
