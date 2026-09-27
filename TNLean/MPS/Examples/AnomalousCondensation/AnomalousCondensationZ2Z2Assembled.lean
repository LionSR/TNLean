/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Examples.AnomalousCondensation.AnomalousCondensationZ2Z2Defect
import TNLean.MPS.FundamentalTheorem.Reduction.AssemblyLemmas
import TNLean.MPS.FundamentalTheorem.Reduction.MultiBlockDirectSum
import TNLean.MPS.MPDO.OperatorProductBlockDiagonal

/-!
# Anomalous `ℤ/2 × ℤ/2` symmetry: the explicit assembled compression of the stacked defect

**Source.** Construction of this development; no source prints these tensors.
Garre-Rubio, Lootens and Molnár (arXiv:2203.12563), Section "Examples of explicit MPSs and
MPO representations", subsubsection "Periodic boundary condition case",
`Papers/2203.12563/REsubmission.tex` lines 2202–2224, build periodic matrix product operator
representations of a finite group from a three-cocycle and print only the `ℤ/2` example
`U_g = ∏ CZ_{i,i+1} Z_i ∏ X_i`. The term *condensation defect* follows Roumpedakis, Seifnashri
and Shao (arXiv:2204.02407), Section "Higher gauging and condensation defects",
`References/2204.02407/source/condensation_draft.tex` lines 145–148.

**Formalized here.** An explicit multi-block compression datum of the stacked defect tensor
`N · N`, `N = M_e ⊕ M_x ⊕ M_y ⊕ M_xy`, onto the sixteen weighted targets `λ(g,h) M_{gh}`, and the
exact nilpotency order of its remainder. The letters of `N · N` are block diagonal over the
sixteen pairs `(g, h)`, the block of `(g, h)` being the stacked tensor `M_g · M_h`, so the datum
is the direct sum of the sixteen pair-block data of the companion files. Its remainder is the
direct sum of the pair remainders: the twelve split pairs contribute nothing, and each of the
four non-split pairs `(x, x)`, `(x, xy)`, `(xy, x)`, `(xy, xy)` has a remainder nilpotent of
order exactly three. Hence every word of length at least three vanishes in the assembled
remainder, and some word of length two does not; the generic bound of Theorem 7.7(vi) is
`|S| + z = 16 + 12 = 28`.

## Main definitions

* `Z2Z2Condensation.condensationBond`: the labelling of the six bond coordinates of `N` by the
  bond coordinates of the four summands.
* `Z2Z2Condensation.pairCompression`: the sixteen pair-block compression data.
* `Z2Z2Condensation.condensationSquare_compression`: the assembled compression datum.

## Main results

* `Z2Z2Condensation.condensationTensor_eq_blockDiagonal`,
  `Z2Z2Condensation.condensationSquare_eq_blockDiagonal`: the defect tensor and its stacked
  square are block diagonal over the group elements and over the pairs.
* `Z2Z2Condensation.xX_remainder_triple_mul_eq_zero`, ...: every product of three remainder
  letters of a non-split pair vanishes.
* `Z2Z2Condensation.condensationSquare_evalWord_remainder_eq_zero`,
  `Z2Z2Condensation.condensationSquare_remainder_mul_ne_zero`: the assembled remainder is
  nilpotent of order exactly three.

## References

- [arXiv:2203.12563](https://arxiv.org/abs/2203.12563) -- J. Garre-Rubio, L. Lootens,
  A. Molnár, *Classifying phases protected by matrix product operator symmetries using matrix
  product states*
- [arXiv:2204.02407](https://arxiv.org/abs/2204.02407) -- K. Roumpedakis, S. Seifnashri,
  S.-H. Shao, *Higher Gauging and Non-invertible Condensation Defects*

## Provenance

The pair decomposition and the remainder orders were first recorded in
`Notes/OpenProblemsTN/checks/asym_z2z2_typeIII_data.md`, Section 4 (remainder order three for
the four non-split pairs, order one for the twelve split pairs), and checked exactly by
`Notes/OpenProblemsTN/checks/asym_z2z2_typeIII_verify.py`; they are verification records, not
the source.
-/

noncomputable section

open scoped Matrix

namespace Z2Z2Condensation

open MPSTensor MPOTensor

/-! ### The block-diagonal form of the defect and of its stacked square -/

/-- The integer tensors of the four group elements, indexed by their site labels. -/
def symIntTensor : (g : Fin 4) → Fin 4 → Fin 4 → Matrix (Fin (bondDim g)) (Fin (bondDim g)) ℤ
  | 0 => eIntTensor
  | 1 => yIntTensor
  | 2 => xIntTensor
  | 3 => xyIntTensor

theorem symTensor_eq (g : Fin 4) (i j : Fin 4) :
    symTensor g i j = complexOfInt (symIntTensor g i j) := by
  fin_cases g <;> rfl

/-- The first bond coordinate of each summand inside the bond space of `N = M_e ⊕ M_x ⊕ M_y ⊕
M_xy`: `M_e` occupies `0`, `M_y` occupies `3`, `M_x` occupies `1, 2` and `M_xy` occupies
`4, 5`. -/
def condensationOffset : Fin 4 → ℕ := ![0, 3, 1, 4]

theorem condensationOffset_add_lt (x : Σ g : Fin 4, Fin (bondDim g)) :
    condensationOffset x.1 + (x.2 : ℕ) < 6 := by
  revert x
  decide

/-- The labelling of the six bond coordinates of the defect by the bond coordinates of the four
summands. -/
def condensationBond : (Σ g : Fin 4, Fin (bondDim g)) ≃ Fin 6 where
  toFun x := ⟨condensationOffset x.1 + x.2, condensationOffset_add_lt x⟩
  invFun
    | 0 => ⟨0, ⟨0, by decide⟩⟩
    | 1 => ⟨2, ⟨0, by decide⟩⟩
    | 2 => ⟨2, ⟨1, by decide⟩⟩
    | 3 => ⟨1, ⟨0, by decide⟩⟩
    | 4 => ⟨3, ⟨0, by decide⟩⟩
    | 5 => ⟨3, ⟨1, by decide⟩⟩
  left_inv := by decide
  right_inv := by decide

private theorem condensationInt_eq (i j : Fin 4) :
    (Matrix.fromBlocks
        ((Matrix.fromBlocks
          ((Matrix.fromBlocks (eIntTensor i j) 0 0 (xIntTensor i j)).submatrix
            finSumFinEquiv.symm finSumFinEquiv.symm) 0 0 (yIntTensor i j)).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm) 0 0 (xyIntTensor i j)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm =
      (Matrix.blockDiagonal' fun g => symIntTensor g i j).submatrix condensationBond.symm
        condensationBond.symm := by
  revert i j
  decide +kernel

/-- **The defect tensor is block diagonal over the group elements**: every letter of
`N = M_e ⊕ M_x ⊕ M_y ⊕ M_xy` is the block-diagonal matrix of the four summands, relabelled along
`condensationBond`. -/
theorem condensationTensor_eq_blockDiagonal (i j : Fin 4) :
    condensationTensor i j =
      (Matrix.blockDiagonal' fun g => symTensor g i j).submatrix condensationBond.symm
        condensationBond.symm := by
  have h1 : directSum eTensor xTensor = fun i j => complexOfInt
      ((Matrix.fromBlocks (eIntTensor i j) 0 0 (xIntTensor i j)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm) :=
    funext fun i => funext fun j => directSum_complexOfRing _ eIntTensor xIntTensor i j
  have h2 : directSum (directSum eTensor xTensor) yTensor = fun i j => complexOfInt
      ((Matrix.fromBlocks ((Matrix.fromBlocks (eIntTensor i j) 0 0 (xIntTensor i j)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm) 0 0 (yIntTensor i j)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm) := by
    rw [h1]
    exact funext fun i => funext fun j => directSum_complexOfRing _ _ yIntTensor i j
  have h : condensationTensor i j = complexOfInt ((Matrix.fromBlocks
      ((Matrix.fromBlocks
        ((Matrix.fromBlocks (eIntTensor i j) 0 0 (xIntTensor i j)).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm) 0 0 (yIntTensor i j)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm) 0 0 (xyIntTensor i j)).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm) := by
    rw [condensationTensor, h2]
    exact directSum_complexOfRing _ _ xyIntTensor i j
  rw [h, condensationInt_eq, complexOfInt, complexOfRing_submatrix, complexOfRing_blockDiagonal']
  congr 2
  funext g
  exact (symTensor_eq g i j).symm

/-- The bond dimension of the pair block `(g, h)`. -/
abbrev pairBlockDim (p : Fin 4 × Fin 4) : ℕ := bondDim p.1 * bondDim p.2

/-- The stacked tensor `M_g · M_h` of the pair `(g, h)`, over the pair alphabet. -/
def pairStack (p : Fin 4 × Fin 4) : MPSTensor 16 (pairBlockDim p) :=
  (mulTensor (symTensor p.1) (symTensor p.2)).toMPSTensor

/-- **The stacked defect tensor is block diagonal over the sixteen pairs** (data file,
Section 4), the block of `(g, h)` being the stacked tensor `M_g · M_h`. -/
theorem condensationSquare_eq_blockDiagonal (a : Fin 16) :
    condensationSquare a =
      (Matrix.blockDiagonal' fun p => pairStack p a).submatrix
        (mulBond condensationBond condensationBond).symm
        (mulBond condensationBond condensationBond).symm :=
  mulTensor_blockDiagonal' symTensor symTensor condensationBond condensationBond
    condensationTensor_eq_blockDiagonal condensationTensor_eq_blockDiagonal _ _

/-! ### Remainders of the four non-split pairs -/

/-- The integer remainder letters of the pair `(x, x)`: `R^a = B^a - V C^a W`. -/
def xXRemainderInt (a : Fin 16) : Matrix (Fin 4) (Fin 4) ℤ :=
  xXInt a - !![1; -1; -1; 1] * eIntMPS a *
    (!![0, 0, 0, 1] : Matrix (Fin 1) (Fin 4) ℤ)

/-- The integer remainder letters of the pair `(x, xy)`. -/
def xXyRemainderInt (a : Fin 16) : Matrix (Fin 4) (Fin 4) ℤ :=
  xXyInt a - !![-1; -1; 1; 1] * negYIntMPS a *
    (!![0, 0, 1, 0] : Matrix (Fin 1) (Fin 4) ℤ)

/-- The integer remainder letters of the pair `(xy, x)`. -/
def xyXRemainderInt (a : Fin 16) : Matrix (Fin 4) (Fin 4) ℤ :=
  xyXInt a - !![-1; -1; -1; -1] * yIntMPS a *
    (!![-1, 0, 0, 0] : Matrix (Fin 1) (Fin 4) ℤ)

/-- The integer remainder letters of the pair `(xy, xy)`. -/
def xyXyRemainderInt (a : Fin 16) : Matrix (Fin 4) (Fin 4) ℤ :=
  xyXyInt a - !![-1; 1; -1; 1] * negEIntMPS a *
    (!![0, 1, 0, 0] : Matrix (Fin 1) (Fin 4) ℤ)

theorem xX_remainder_eq (a : Fin 16) :
    xXCompression.remainder a = complexOfInt (xXRemainderInt a) := by
  rw [MultiBlockCompression.remainder_oneSlot _ oneSlotMem, xX_left_eq, xX_right_eq,
    xXStacked_eq, eMPS_eq, xXLeft, xXRight, ← complexOfInt_mul, ← complexOfInt_mul,
    xXRemainderInt]
  exact (complexOfRing_sub _ _ _).symm

theorem xXy_remainder_eq (a : Fin 16) :
    xXyCompression.remainder a = complexOfInt (xXyRemainderInt a) := by
  rw [MultiBlockCompression.remainder_oneSlot _ oneSlotMem, xXy_left_eq, xXy_right_eq,
    xXyStacked_eq, negYMPS_eq, xXyLeft, xXyRight, ← complexOfInt_mul, ← complexOfInt_mul,
    xXyRemainderInt]
  exact (complexOfRing_sub _ _ _).symm

theorem xyX_remainder_eq (a : Fin 16) :
    xyXCompression.remainder a = complexOfInt (xyXRemainderInt a) := by
  rw [MultiBlockCompression.remainder_oneSlot _ oneSlotMem, xyX_left_eq, xyX_right_eq,
    xyXStacked_eq, yMPS_eq, xyXLeft, xyXRight, ← complexOfInt_mul, ← complexOfInt_mul,
    xyXRemainderInt]
  exact (complexOfRing_sub _ _ _).symm

theorem xyXy_remainder_eq (a : Fin 16) :
    xyXyCompression.remainder a = complexOfInt (xyXyRemainderInt a) := by
  rw [MultiBlockCompression.remainder_oneSlot _ oneSlotMem, xyXy_left_eq, xyXy_right_eq,
    xyXyStacked_eq, negEMPS_eq, xyXyLeft, xyXyRight, ← complexOfInt_mul, ← complexOfInt_mul,
    xyXyRemainderInt]
  exact (complexOfRing_sub _ _ _).symm

/-- **Every product of three remainder letters of the pair `(x, x)` vanishes** (data file,
Section 4). -/
theorem xX_remainder_triple_mul_eq_zero (a b c : Fin 16) :
    xXRemainderInt a * xXRemainderInt b * xXRemainderInt c = 0 :=
  triple_mul_eq_zero_of_support _ ![0, 10] (by decide +kernel) (by decide +kernel) a b c

/-- **Every product of three remainder letters of the pair `(x, xy)` vanishes** (data file,
Section 4). -/
theorem xXy_remainder_triple_mul_eq_zero (a b c : Fin 16) :
    xXyRemainderInt a * xXyRemainderInt b * xXyRemainderInt c = 0 :=
  triple_mul_eq_zero_of_support _ ![1, 11] (by decide +kernel) (by decide +kernel) a b c

/-- **Every product of three remainder letters of the pair `(xy, x)` vanishes** (data file,
Section 4). -/
theorem xyX_remainder_triple_mul_eq_zero (a b c : Fin 16) :
    xyXRemainderInt a * xyXRemainderInt b * xyXRemainderInt c = 0 :=
  triple_mul_eq_zero_of_support _ ![1, 11] (by decide +kernel) (by decide +kernel) a b c

/-- **Every product of three remainder letters of the pair `(xy, xy)` vanishes** (data file,
Section 4). -/
theorem xyXy_remainder_triple_mul_eq_zero (a b c : Fin 16) :
    xyXyRemainderInt a * xyXyRemainderInt b * xyXyRemainderInt c = 0 :=
  triple_mul_eq_zero_of_support _ ![0, 10] (by decide +kernel) (by decide +kernel) a b c

/-- The square of the remainder letter `0` of the pair `(x, x)` does not vanish, so its
nilpotency order is exactly three (data file, Section 4). -/
theorem xX_remainder_mul_ne_zero : xXRemainderInt 0 * xXRemainderInt 0 ≠ 0 := by
  decide +kernel

/-! ### The assembled datum -/

/-- The sixteen pair-block compression data, read against the weighted targets `λ(g,h) M_{gh}`:
the twelve split pairs of `AnomalousCondensationZ2Z2Split.lean` and the four non-split pairs of
`AnomalousCondensationZ2Z2NonSplit.lean` (data file, Section 4). -/
def pairCompression :
    (p : Fin 4 × Fin 4) → MultiBlockCompression (pairStack p) oneSlot
      (fun _ : Unit => pairTarget p)
  | (0, 0) => eECompression.ofTargetEq fun _ _ => (one_smul ℂ _).symm
  | (0, 1) => eYCompression.ofTargetEq fun _ _ => (one_smul ℂ _).symm
  | (0, 2) => eXCompression.ofTargetEq fun _ _ => (one_smul ℂ _).symm
  | (0, 3) => eXyCompression.ofTargetEq fun _ _ => (one_smul ℂ _).symm
  | (1, 0) => yECompression.ofTargetEq fun _ _ => (one_smul ℂ _).symm
  | (1, 1) => yYCompression.ofTargetEq fun _ _ => (one_smul ℂ _).symm
  | (1, 2) => yXCompression.ofTargetEq fun _ _ => (one_smul ℂ _).symm
  | (1, 3) => yXyCompression.ofTargetEq fun _ _ => (one_smul ℂ _).symm
  | (2, 0) => xECompression.ofTargetEq fun _ _ => (one_smul ℂ _).symm
  | (2, 1) => xYCompression
  | (2, 2) => xXCompression.ofTargetEq fun _ _ => (one_smul ℂ _).symm
  | (2, 3) => xXyCompression
  | (3, 0) => xyECompression.ofTargetEq fun _ _ => (one_smul ℂ _).symm
  | (3, 1) => xyYCompression
  | (3, 2) => xyXCompression.ofTargetEq fun _ _ => (one_smul ℂ _).symm
  | (3, 3) => xyXyCompression

/-- **The explicit assembled compression datum of the stacked defect tensor** (P5 note,
Theorem 7.7; data file, Section 4): the direct sum of the sixteen pair-block data. -/
def condensationSquare_compression :
    MultiBlockCompression condensationSquare pairSlots pairTarget :=
  MultiBlockCompression.directSum pairCompression (mulBond condensationBond condensationBond)
    condensationSquare_eq_blockDiagonal

/-- The assembled datum has twelve zero slots, three in each non-split pair. -/
theorem condensationSquare_compression_z_eq : condensationSquare_compression.z = 12 :=
  condensationSquare_compression_z _

/-- A compression datum read against its target carried with the weight one has the same
remainder. -/
private theorem remainder_ofTargetEq_one {D DB : ℕ} {B : MPSTensor 16 DB} {C : MPSTensor 16 D}
    (P : MultiBlockCompression B oneSlot (fun _ : Unit => C)) :
    (P.ofTargetEq (C' := fun _ => (1 : ℂ) • C) fun _ _ => (one_smul ℂ _).symm).remainder =
      P.remainder :=
  MultiBlockCompression.remainder_ofTargetEq _ _

private theorem evalWord_eq_zero_of_int {D : ℕ} {R : MPSTensor 16 D}
    (RI : Fin 16 → Matrix (Fin D) (Fin D) ℤ) (hR : ∀ a, R a = complexOfInt (RI a))
    (h : ∀ a b c, RI a * RI b * RI c = 0) (w : List (Fin 16)) (hw : 3 ≤ w.length) :
    Kraus.evalWord R w = 0 :=
  evalWord_eq_zero_of_triple_mul_eq_zero R (fun a b c => by
    rw [hR, hR, hR, ← complexOfInt_mul, ← complexOfInt_mul, h, complexOfInt_zero]) w hw

/-- **Every word of length at least three vanishes in the remainder of each pair block**
(data file, Section 4): the twelve split pairs have zero remainder, and the four non-split pairs
have remainders nilpotent of order three. -/
theorem pairCompression_evalWord_remainder_eq_zero (p : Fin 4 × Fin 4) (w : List (Fin 16))
    (hw : 3 ≤ w.length) : Kraus.evalWord (pairCompression p).remainder w = 0 := by
  have hzero : ∀ {D : ℕ} (R : MPSTensor 16 D), R = 0 → Kraus.evalWord R w = 0 := by
    intro D R hR
    obtain ⟨a, w, rfl⟩ : ∃ a w', w = a :: w' := w.exists_cons_of_length_pos (by omega)
    subst hR
    simp [Kraus.evalWord]
  obtain ⟨g, h⟩ := p
  fin_cases g <;> fin_cases h
  · exact hzero _ ((remainder_ofTargetEq_one _).trans eE_remainder_eq_zero)
  · exact hzero _ ((remainder_ofTargetEq_one _).trans eY_remainder_eq_zero)
  · exact hzero _ ((remainder_ofTargetEq_one _).trans eX_remainder_eq_zero)
  · exact hzero _ ((remainder_ofTargetEq_one _).trans eXy_remainder_eq_zero)
  · exact hzero _ ((remainder_ofTargetEq_one _).trans yE_remainder_eq_zero)
  · exact hzero _ ((remainder_ofTargetEq_one _).trans yY_remainder_eq_zero)
  · exact hzero _ ((remainder_ofTargetEq_one _).trans yX_remainder_eq_zero)
  · exact hzero _ ((remainder_ofTargetEq_one _).trans yXy_remainder_eq_zero)
  · exact hzero _ ((remainder_ofTargetEq_one _).trans xE_remainder_eq_zero)
  · exact hzero _ xY_remainder_eq_zero
  · exact (congrArg (fun R => Kraus.evalWord R w) (remainder_ofTargetEq_one xXCompression)).trans
      (evalWord_eq_zero_of_int _ xX_remainder_eq xX_remainder_triple_mul_eq_zero w hw)
  · exact evalWord_eq_zero_of_int _ xXy_remainder_eq xXy_remainder_triple_mul_eq_zero w hw
  · exact hzero _ ((remainder_ofTargetEq_one _).trans xyE_remainder_eq_zero)
  · exact hzero _ xyY_remainder_eq_zero
  · exact (congrArg (fun R => Kraus.evalWord R w) (remainder_ofTargetEq_one xyXCompression)).trans
      (evalWord_eq_zero_of_int _ xyX_remainder_eq xyX_remainder_triple_mul_eq_zero w hw)
  · exact evalWord_eq_zero_of_int _ xyXy_remainder_eq xyXy_remainder_triple_mul_eq_zero w hw

/-- **Nilpotency of the assembled remainder, of order three** (P5 note, Theorem 7.7(vi); data
file, Section 4): every word of length at least three vanishes in the remainder of the stacked
defect tensor, against the generic bound `|S| + z = 16 + 12 = 28` of clause (vi). -/
theorem condensationSquare_evalWord_remainder_eq_zero (w : List (Fin 16)) (hw : 3 ≤ w.length) :
    Kraus.evalWord condensationSquare_compression.remainder w = 0 :=
  MultiBlockCompression.evalWord_remainder_directSum_eq_zero _ _ _ w fun p =>
    pairCompression_evalWord_remainder_eq_zero p w hw

/-- **The nilpotency order three is exact**: the square of the remainder letter `0` of the
assembled datum does not vanish, because it does not vanish in the pair `(x, x)`. -/
theorem condensationSquare_remainder_mul_ne_zero :
    condensationSquare_compression.remainder 0 * condensationSquare_compression.remainder 0 ≠
      0 := by
  have hxx : (pairCompression (2, 2)).remainder = xXCompression.remainder :=
    remainder_ofTargetEq_one xXCompression
  have h := MultiBlockCompression.evalWord_remainder_directSum_ne_zero pairCompression
    (mulBond condensationBond condensationBond) condensationSquare_eq_blockDiagonal [0, 0]
    (2, 2) (by
      rw [hxx]
      change xXCompression.remainder 0 *
        (xXCompression.remainder 0 * (1 : Matrix (Fin 4) (Fin 4) ℂ)) ≠ 0
      rw [Matrix.mul_one, xX_remainder_eq, ← complexOfInt_mul]
      intro h0
      refine xX_remainder_mul_ne_zero (Matrix.ext fun i j => ?_)
      simpa using congrFun (congrFun h0 i) j)
  change condensationSquare_compression.remainder 0 *
    (condensationSquare_compression.remainder 0 * (1 : Matrix (Fin 36) (Fin 36) ℂ)) ≠ 0 at h
  rwa [Matrix.mul_one] at h

end Z2Z2Condensation
