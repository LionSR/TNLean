/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.Algebra.GeneralizeDecide
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.AnomalousCondensationZ2Z2

/-!
# Anomalous `ℤ/2 × ℤ/2` symmetry: the four non-split pair blocks of the condensation defect

**Source.** Construction of this development; no source prints these tensors.
Garre-Rubio, Lootens and Molnár (arXiv:2203.12563), Section "Examples of explicit MPSs and
MPO representations", subsubsection "Periodic boundary condition case",
`Papers/2203.12563/REsubmission.tex` lines 2202–2224, build periodic matrix product operator
representations of a finite group from a three-cocycle and print only the `ℤ/2` example
`U_g = ∏ CZ_{i,i+1} Z_i ∏ X_i`; Garre-Rubio and Schuch (arXiv:2405.00439), Section "The simplest
example", `Papers/2405.00439/MPU-DW.tex` lines 1123–1134, print only the CZX matrix product
unitary of `ℤ/2`. The `ℤ/2 × ℤ/2` tensors used here are built from the CZX letters and carry
the mixed (type-II) class `(-1)^{a_1 b_2 c_2}` of `H^3(ℤ/2 × ℤ/2, U(1))`.
The term *condensation defect* for the sum of the operators of a finite symmetry follows
Roumpedakis, Seifnashri and Shao (arXiv:2204.02407), Section "Higher gauging and condensation
defects", `References/2204.02407/source/condensation_draft.tex` lines 145–148, where it is the
sum over insertions of the symmetry defects; lines 1415–1417 of the same file note that for a
`ℤ/2` operator `U` the sum `P_+ = 1 + U` obeys `P_+ × P_+ = 2 P_+`.

**Formalized here.** The four pair blocks `M_g ⊗ M_h` with both `g, h ∈ {x, xy}`, the two
elements whose tensors carry the controlled-`Z` dressing, are the blocks in which the anomaly of
the `ℤ/2 × ℤ/2` symmetry shows. Each has bond dimension four and compresses onto the
one-dimensional target `λ(g,h) M_{gh}` with `z = 3` zero slots: the flag has two zero slots
below the target and one above, the gauge is a unimodular integer matrix, every product of four
remainder letters vanishes, and both sitewise intertwiner spaces vanish, exactly as in Example D
of the P5 note (`Notes/OpenProblemsTN/strategies/p5_asymmetric_compression_theorem.tex`,
`ex:p5ft-czx`). The block `(x, x)` is the stacked CZX tensor of that example with its letters
relabelled into the sixteen-letter pair alphabet.

The targets are `M_e` for `(x, x)`, `-M_y` for `(x, xy)`, `M_y` for `(xy, x)` and `-M_e` for
`(xy, xy)`, the signs being the periodic fusion signs `λ(g,h) = (-1)^{g_1 h_2}`.

Only the vanishing of the remainder words of length at least four is stated here, which is the
nilpotency clause of Theorem 7.7 with the bound `1 + z = 4`.

## Main results

* `Z2Z2Condensation.xXCompression`, `Z2Z2Condensation.xXyCompression`,
  `Z2Z2Condensation.xyXCompression`, `Z2Z2Condensation.xyXyCompression`: the four compression
  data of Theorem 7.7.
* `Z2Z2Condensation.xX_trace_evalWord`, ...: the word-trace identities
  `U_g U_h = λ(g,h)^L U_{gh}`.
* `Z2Z2Condensation.xX_isReduction`, ...: the explicit compression pairs read off from the
  gauges.
* `Z2Z2Condensation.xX_evalWord_remainder_eq_zero`, ...: the remainders are nilpotent of
  length four.
* `Z2Z2Condensation.xX_right_intertwiner_eq_zero`,
  `Z2Z2Condensation.xX_left_intertwiner_eq_zero`, ...: both sitewise intertwiner spaces of each
  block vanish.

## References

- [arXiv:2203.12563](https://arxiv.org/abs/2203.12563) -- J. Garre-Rubio, L. Lootens,
  A. Molnár, *Classifying phases protected by matrix product operator symmetries using matrix
  product states*
- [arXiv:2405.00439](https://arxiv.org/abs/2405.00439) -- J. Garre-Rubio, N. Schuch,
  *Fractional domain wall statistics in spin chains with anomalous symmetries*
- [arXiv:2204.02407](https://arxiv.org/abs/2204.02407) -- K. Roumpedakis, S. Seifnashri,
  S.-H. Shao, *Higher Gauging and Non-invertible Condensation Defects*

## Provenance

The gauges, flags and remainders were first recorded in
`Notes/OpenProblemsTN/checks/asym_z2z2_typeIII_data.md`, Sections 4 and 5, and checked exactly by
`Notes/OpenProblemsTN/checks/asym_z2z2_typeIII_verify.py`; they are verification records, not
the source. The data file (Section 4) also records each of these remainders as nonzero and
nilpotent of order three.
-/

noncomputable section

open scoped Matrix

namespace Z2Z2Condensation

open MPSTensor

/-! ### The block `(x, x)` -/

/-- The stacked tensor of `U_x U_x`. -/
def xXStacked : MPSTensor 16 4 := (MPOTensor.mulTensor xTensor xTensor).toMPSTensor

/-- The integer matrices of the stacked tensor of `U_x U_x` (data file, appendix). -/
def xXInt : Fin 16 → Matrix (Fin 4) (Fin 4) ℤ
  | 0 => !![1, 0, 0, 0; 1, 0, 0, 0; 1, 0, 0, 0; 1, 0, 0, 0]
  | 5 => !![0, 0, 0, 1; 0, 0, 0, -1; 0, 0, 0, -1; 0, 0, 0, 1]
  | 10 => !![1, 0, 0, 0; 1, 0, 0, 0; 1, 0, 0, 0; 1, 0, 0, 0]
  | 15 => !![0, 0, 0, 1; 0, 0, 0, -1; 0, 0, 0, -1; 0, 0, 0, 1]
  | _ => 0

private theorem xX_int (b : Fin 16) : stackedInt xIntTensor xIntTensor b = xXInt b := by
  revert_decide_kernel b

theorem xXStacked_eq (a : Fin 16) : xXStacked a = complexOfInt (xXInt a) := by
  rw [← xX_int]
  exact toMPSTensor_mulTensor_complexOfInt xIntTensor xIntTensor a

/-- The change of bond coordinates of the block `(x, x)` (data file, appendix). -/
def xXGaugeInt : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 1, 0, 1; 0, 0, 1, 1; 0, 0, 0, 1; 1, 0, 0, -1]

/-- The inverse change of bond coordinates of the block `(x, x)`; its columns are the basis
adapted to the flag. -/
def xXGaugeInvInt : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 0, 1, 1; 1, 0, -1, 0; 0, 1, -1, 0; 0, 0, 1, 0]

/-- The letters of the block `(x, x)` in the flag coordinates. -/
def xXConjInt : Fin 16 → Matrix (Fin 4) (Fin 4) ℤ
  | 0 => !![0, 0, 2, 2; 0, 0, 2, 2; 0, 0, 1, 1; 0, 0, 0, 0]
  | 5 => !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0]
  | 10 => !![0, 0, 2, 2; 0, 0, 2, 2; 0, 0, 1, 1; 0, 0, 0, 0]
  | 15 => !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0]
  | _ => 0

/-- **The compression datum of the block `(x, x)`**: the stacked tensor of `U_x U_x` compresses
onto the tensor of `U_e` with three zero slots (data file, Section 5; P5 note,
Theorem 7.7(i)–(iii)). -/
def xXCompression : MultiBlockCompression xXStacked oneSlot (fun _ => eMPS) :=
  MultiBlockCompression.ofScalarFlagFour xXInt eIntMPS xXStacked_eq eMPS_eq xXGaugeInt
    xXGaugeInvInt (by decide) (by decide) xXConjInt (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- **`U_x U_x = U_e` at the level of word traces.** -/
theorem xX_trace_evalWord (w : List (Fin 16)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord xXStacked w) = Matrix.trace (Kraus.evalWord eMPS w) :=
  xXCompression.trace_evalWord_oneSlot w hw

/-- The left compression witness of the block `(x, x)`: the third row of the gauge. -/
def xXLeft : Matrix (Fin 1) (Fin 4) ℂ := complexOfInt !![0, 0, 0, 1]

/-- The right compression witness of the block `(x, x)`: the third column of the inverse
gauge. -/
def xXRight : Matrix (Fin 4) (Fin 1) ℂ := complexOfInt !![1; -1; -1; 1]

theorem xX_left_eq : xXCompression.left oneSlotMem = xXLeft := by
  rw [xXCompression, MultiBlockCompression.left_ofScalarFlagFour]
  ext i j
  simp only [Matrix.of_apply, xXLeft, complexOfInt_apply, Int.cast_inj]
  revert i j
  decide

theorem xX_right_eq : xXCompression.right oneSlotMem = xXRight := by
  rw [xXCompression, MultiBlockCompression.right_ofScalarFlagFour]
  ext i j
  simp only [Matrix.of_apply, xXRight, complexOfInt_apply, Int.cast_inj]
  revert i j
  decide

/-- **The explicit compression pair of the block `(x, x)`** (P5 note, Theorem 7.7(iv)–(v)). -/
theorem xX_isReduction : IsReduction xXStacked eMPS xXLeft xXRight := by
  have h := xXCompression.isReduction oneSlotMem
  rwa [xX_left_eq, xX_right_eq] at h

/-- **Nilpotency of the remainder of the block `(x, x)`** (P5 note, Theorem 7.7(vi)). -/
theorem xX_evalWord_remainder_eq_zero (w : List (Fin 16)) (hw : 4 ≤ w.length) :
    Kraus.evalWord xXCompression.remainder w = 0 :=
  xXCompression.evalWord_remainder_eq_zero w (by change (1 : ℕ) + 3 ≤ w.length; omega)

/-- **The dimension count of the block `(x, x)`**: `4 = 1 + 3`. -/
theorem xX_dim_eq : (4 : ℕ) = ∑ _s ∈ oneSlot, 1 + 3 :=
  xXCompression.dim_eq

/-- **No nonzero right sitewise intertwiner in the block `(x, x)`** (data file, Section 5). -/
theorem xX_right_intertwiner_eq_zero (v : Fin 4 → ℂ)
    (h : ∀ i, xXStacked i *ᵥ v = eMPS i 0 0 • v) : v = 0 :=
  right_intertwiner_eq_zero_of_int xXInt eIntMPS xXStacked_eq eMPS_eq ![0, 0, 0, 5]
    ![1, 2, 3, 1] !![-1, 0, -1, 1; 1, 0, -1, 1; -1, 2, -1, 1; -1, 0, 1, 1] (-2) (by decide)
    (by decide +kernel) v h

/-- **No nonzero left sitewise intertwiner in the block `(x, x)`** (data file, Section 5). -/
theorem xX_left_intertwiner_eq_zero (u : Fin 4 → ℂ)
    (h : ∀ i, u ᵥ* xXStacked i = eMPS i 0 0 • u) : u = 0 :=
  left_intertwiner_eq_zero_of_int xXInt eIntMPS xXStacked_eq eMPS_eq ![0, 0, 0, 5]
    ![0, 1, 2, 0] !![0, 0, 0, -1; 0, -1, 0, 0; 0, 0, -1, 0; 1, 1, 1, 0] 1 (by decide)
    (by decide +kernel) u h

/-! ### The block `(x, xy)` -/

/-- The stacked tensor of `U_x U_xy`. -/
def xXyStacked : MPSTensor 16 4 := (MPOTensor.mulTensor xTensor xyTensor).toMPSTensor

/-- The integer matrices of the stacked tensor of `U_x U_xy` (data file, appendix). -/
def xXyInt : Fin 16 → Matrix (Fin 4) (Fin 4) ℤ
  | 1 => !![0, 1, 0, 0; 0, -1, 0, 0; 0, 1, 0, 0; 0, -1, 0, 0]
  | 4 => !![0, 0, 1, 0; 0, 0, 1, 0; 0, 0, -1, 0; 0, 0, -1, 0]
  | 11 => !![0, 1, 0, 0; 0, -1, 0, 0; 0, 1, 0, 0; 0, -1, 0, 0]
  | 14 => !![0, 0, 1, 0; 0, 0, 1, 0; 0, 0, -1, 0; 0, 0, -1, 0]
  | _ => 0

private theorem xXy_int (b : Fin 16) : stackedInt xIntTensor xyIntTensor b = xXyInt b := by
  revert_decide_kernel b

theorem xXyStacked_eq (a : Fin 16) : xXyStacked a = complexOfInt (xXyInt a) := by
  rw [← xXy_int]
  exact toMPSTensor_mulTensor_complexOfInt xIntTensor xyIntTensor a

/-- The change of bond coordinates of the block `(x, xy)` (data file, appendix). -/
def xXyGaugeInt : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 0, 1, 0; 0, 0, -1, 1; 0, 0, 1, 0; 0, 1, 1, 0]

/-- The inverse change of bond coordinates of the block `(x, xy)`. -/
def xXyGaugeInvInt : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 0, -1, 0; 0, 0, -1, 1; 0, 0, 1, 0; 0, 1, 1, 0]

/-- The letters of the block `(x, xy)` in the flag coordinates. -/
def xXyConjInt : Fin 16 → Matrix (Fin 4) (Fin 4) ℤ
  | 1 => !![0, 0, -2, 2; 0, 0, 2, -2; 0, 0, -1, 1; 0, 0, 0, 0]
  | 4 => !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, -1, 0; 0, 0, 0, 0]
  | 11 => !![0, 0, -2, 2; 0, 0, 2, -2; 0, 0, -1, 1; 0, 0, 0, 0]
  | 14 => !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, -1, 0; 0, 0, 0, 0]
  | _ => 0

/-- **The compression datum of the block `(x, xy)`**: the stacked tensor of `U_x U_xy`
compresses onto the tensor of `U_y` carried with the weight `-1`, with three zero slots (data
file, Section 5; P5 note, Theorem 7.7(i)–(iii)). -/
def xXyCompression : MultiBlockCompression xXyStacked oneSlot (fun _ => (-1 : ℂ) • yMPS) :=
  MultiBlockCompression.ofScalarFlagFour xXyInt negYIntMPS xXyStacked_eq negYMPS_eq xXyGaugeInt
    xXyGaugeInvInt (by decide) (by decide) xXyConjInt (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- **`U_x U_xy = (-1)^L U_y` at the level of word traces** (data file, Section 2). -/
theorem xXy_trace_evalWord (w : List (Fin 16)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord xXyStacked w) =
      (-1 : ℂ) ^ w.length * Matrix.trace (Kraus.evalWord yMPS w) :=
  xXyCompression.trace_evalWord_oneSlot_smul w hw

/-- The left compression witness of the block `(x, xy)`. -/
def xXyLeft : Matrix (Fin 1) (Fin 4) ℂ := complexOfInt !![0, 0, 1, 0]

/-- The right compression witness of the block `(x, xy)`. -/
def xXyRight : Matrix (Fin 4) (Fin 1) ℂ := complexOfInt !![-1; -1; 1; 1]

theorem xXy_left_eq : xXyCompression.left oneSlotMem = xXyLeft := by
  rw [xXyCompression, MultiBlockCompression.left_ofScalarFlagFour]
  ext i j
  simp only [Matrix.of_apply, xXyLeft, complexOfInt_apply, Int.cast_inj]
  revert i j
  decide

theorem xXy_right_eq : xXyCompression.right oneSlotMem = xXyRight := by
  rw [xXyCompression, MultiBlockCompression.right_ofScalarFlagFour]
  ext i j
  simp only [Matrix.of_apply, xXyRight, complexOfInt_apply, Int.cast_inj]
  revert i j
  decide

/-- **The explicit compression pair of the block `(x, xy)`** (P5 note,
Theorem 7.7(iv)–(v)). -/
theorem xXy_isReduction : IsReduction xXyStacked ((-1 : ℂ) • yMPS) xXyLeft xXyRight := by
  have h := xXyCompression.isReduction oneSlotMem
  rwa [xXy_left_eq, xXy_right_eq] at h

/-- **Nilpotency of the remainder of the block `(x, xy)`** (P5 note, Theorem 7.7(vi)). -/
theorem xXy_evalWord_remainder_eq_zero (w : List (Fin 16)) (hw : 4 ≤ w.length) :
    Kraus.evalWord xXyCompression.remainder w = 0 :=
  xXyCompression.evalWord_remainder_eq_zero w (by change (1 : ℕ) + 3 ≤ w.length; omega)

/-- **No nonzero right sitewise intertwiner in the block `(x, xy)`** (data file,
Section 5). -/
theorem xXy_right_intertwiner_eq_zero (v : Fin 4 → ℂ)
    (h : ∀ i, xXyStacked i *ᵥ v = ((-1 : ℂ) • yMPS) i 0 0 • v) : v = 0 :=
  right_intertwiner_eq_zero_of_int xXyInt negYIntMPS xXyStacked_eq negYMPS_eq ![1, 1, 1, 4]
    ![0, 2, 3, 0] !![-1, 1, 0, -1; -1, -1, 0, 1; 1, -1, 0, -1; -1, -1, -2, 1] (-2) (by decide)
    (by decide +kernel) v h

/-- **No nonzero left sitewise intertwiner in the block `(x, xy)`** (data file, Section 5). -/
theorem xXy_left_intertwiner_eq_zero (u : Fin 4 → ℂ)
    (h : ∀ i, u ᵥ* xXyStacked i = ((-1 : ℂ) • yMPS) i 0 0 • u) : u = 0 :=
  left_intertwiner_eq_zero_of_int xXyInt negYIntMPS xXyStacked_eq negYMPS_eq ![1, 1, 1, 4]
    ![0, 1, 2, 1] !![1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0; 1, -1, 1, 0] 1 (by decide)
    (by decide +kernel) u h

/-! ### The block `(xy, x)` -/

/-- The stacked tensor of `U_xy U_x`. -/
def xyXStacked : MPSTensor 16 4 := (MPOTensor.mulTensor xyTensor xTensor).toMPSTensor

/-- The integer matrices of the stacked tensor of `U_xy U_x` (data file, appendix). -/
def xyXInt : Fin 16 → Matrix (Fin 4) (Fin 4) ℤ
  | 1 => !![0, 0, 0, 1; 0, 0, 0, -1; 0, 0, 0, -1; 0, 0, 0, 1]
  | 4 => !![1, 0, 0, 0; 1, 0, 0, 0; 1, 0, 0, 0; 1, 0, 0, 0]
  | 11 => !![0, 0, 0, 1; 0, 0, 0, -1; 0, 0, 0, -1; 0, 0, 0, 1]
  | 14 => !![1, 0, 0, 0; 1, 0, 0, 0; 1, 0, 0, 0; 1, 0, 0, 0]
  | _ => 0

private theorem xyX_int (b : Fin 16) : stackedInt xyIntTensor xIntTensor b = xyXInt b := by
  revert_decide_kernel b

theorem xyXStacked_eq (a : Fin 16) : xyXStacked a = complexOfInt (xyXInt a) := by
  rw [← xyX_int]
  exact toMPSTensor_mulTensor_complexOfInt xyIntTensor xIntTensor a

/-- The change of bond coordinates of the block `(xy, x)` (data file, appendix). -/
def xyXGaugeInt : Matrix (Fin 4) (Fin 4) ℤ :=
  !![-1, 1, 0, 0; -1, 0, 1, 0; -1, 0, 0, 0; 1, 0, 0, -1]

/-- The inverse change of bond coordinates of the block `(xy, x)`. -/
def xyXGaugeInvInt : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 0, -1, 0; 1, 0, -1, 0; 0, 1, -1, 0; 0, 0, -1, -1]

/-- The letters of the block `(xy, x)` in the flag coordinates. -/
def xyXConjInt : Fin 16 → Matrix (Fin 4) (Fin 4) ℤ
  | 1 => !![0, 0, 2, 2; 0, 0, 2, 2; 0, 0, 1, 1; 0, 0, 0, 0]
  | 4 => !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0]
  | 11 => !![0, 0, 2, 2; 0, 0, 2, 2; 0, 0, 1, 1; 0, 0, 0, 0]
  | 14 => !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0]
  | _ => 0

/-- **The compression datum of the block `(xy, x)`**: the stacked tensor of `U_xy U_x`
compresses onto the tensor of `U_y` with three zero slots (data file, Section 5; P5 note,
Theorem 7.7(i)–(iii)). -/
def xyXCompression : MultiBlockCompression xyXStacked oneSlot (fun _ => yMPS) :=
  MultiBlockCompression.ofScalarFlagFour xyXInt yIntMPS xyXStacked_eq yMPS_eq xyXGaugeInt
    xyXGaugeInvInt (by decide) (by decide) xyXConjInt (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- **`U_xy U_x = U_y` at the level of word traces.** -/
theorem xyX_trace_evalWord (w : List (Fin 16)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord xyXStacked w) = Matrix.trace (Kraus.evalWord yMPS w) :=
  xyXCompression.trace_evalWord_oneSlot w hw

/-- The left compression witness of the block `(xy, x)`. -/
def xyXLeft : Matrix (Fin 1) (Fin 4) ℂ := complexOfInt !![-1, 0, 0, 0]

/-- The right compression witness of the block `(xy, x)`. -/
def xyXRight : Matrix (Fin 4) (Fin 1) ℂ := complexOfInt !![-1; -1; -1; -1]

theorem xyX_left_eq : xyXCompression.left oneSlotMem = xyXLeft := by
  rw [xyXCompression, MultiBlockCompression.left_ofScalarFlagFour]
  ext i j
  simp only [Matrix.of_apply, xyXLeft, complexOfInt_apply, Int.cast_inj]
  revert i j
  decide

theorem xyX_right_eq : xyXCompression.right oneSlotMem = xyXRight := by
  rw [xyXCompression, MultiBlockCompression.right_ofScalarFlagFour]
  ext i j
  simp only [Matrix.of_apply, xyXRight, complexOfInt_apply, Int.cast_inj]
  revert i j
  decide

/-- **The explicit compression pair of the block `(xy, x)`** (P5 note,
Theorem 7.7(iv)–(v)). -/
theorem xyX_isReduction : IsReduction xyXStacked yMPS xyXLeft xyXRight := by
  have h := xyXCompression.isReduction oneSlotMem
  rwa [xyX_left_eq, xyX_right_eq] at h

/-- **Nilpotency of the remainder of the block `(xy, x)`** (P5 note, Theorem 7.7(vi)). -/
theorem xyX_evalWord_remainder_eq_zero (w : List (Fin 16)) (hw : 4 ≤ w.length) :
    Kraus.evalWord xyXCompression.remainder w = 0 :=
  xyXCompression.evalWord_remainder_eq_zero w (by change (1 : ℕ) + 3 ≤ w.length; omega)

/-- **No nonzero right sitewise intertwiner in the block `(xy, x)`** (data file,
Section 5). -/
theorem xyX_right_intertwiner_eq_zero (v : Fin 4 → ℂ)
    (h : ∀ i, xyXStacked i *ᵥ v = yMPS i 0 0 • v) : v = 0 :=
  right_intertwiner_eq_zero_of_int xyXInt yIntMPS xyXStacked_eq yMPS_eq ![1, 1, 1, 4]
    ![0, 1, 2, 1] !![1, 1, 0, -1; 1, 1, 0, 1; 1, -1, 2, 1; -1, 1, 0, -1] (-2) (by decide)
    (by decide +kernel) v h

/-- **No nonzero left sitewise intertwiner in the block `(xy, x)`** (data file, Section 5). -/
theorem xyX_left_intertwiner_eq_zero (u : Fin 4 → ℂ)
    (h : ∀ i, u ᵥ* xyXStacked i = yMPS i 0 0 • u) : u = 0 :=
  left_intertwiner_eq_zero_of_int xyXInt yIntMPS xyXStacked_eq yMPS_eq ![1, 1, 1, 4]
    ![0, 1, 2, 0] !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, -1, -1, -1] (-1) (by decide)
    (by decide +kernel) u h

/-! ### The block `(xy, xy)` -/

/-- The stacked tensor of `U_xy U_xy`. -/
def xyXyStacked : MPSTensor 16 4 := (MPOTensor.mulTensor xyTensor xyTensor).toMPSTensor

/-- The integer matrices of the stacked tensor of `U_xy U_xy` (data file, appendix). -/
def xyXyInt : Fin 16 → Matrix (Fin 4) (Fin 4) ℤ
  | 0 => !![0, 0, 1, 0; 0, 0, 1, 0; 0, 0, -1, 0; 0, 0, -1, 0]
  | 5 => !![0, 1, 0, 0; 0, -1, 0, 0; 0, 1, 0, 0; 0, -1, 0, 0]
  | 10 => !![0, 0, 1, 0; 0, 0, 1, 0; 0, 0, -1, 0; 0, 0, -1, 0]
  | 15 => !![0, 1, 0, 0; 0, -1, 0, 0; 0, 1, 0, 0; 0, -1, 0, 0]
  | _ => 0

private theorem xyXy_int (b : Fin 16) : stackedInt xyIntTensor xyIntTensor b = xyXyInt b := by
  revert_decide_kernel b

theorem xyXyStacked_eq (a : Fin 16) : xyXyStacked a = complexOfInt (xyXyInt a) := by
  rw [← xyXy_int]
  exact toMPSTensor_mulTensor_complexOfInt xyIntTensor xyIntTensor a

/-- The change of bond coordinates of the block `(xy, xy)` (data file, appendix). -/
def xyXyGaugeInt : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 1, 0, 0; 0, -1, 0, 1; 0, 1, 0, 0; 0, 1, 1, 0]

/-- The inverse change of bond coordinates of the block `(xy, xy)`. -/
def xyXyGaugeInvInt : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 0, -1, 0; 0, 0, 1, 0; 0, 0, -1, 1; 0, 1, 1, 0]

/-- The letters of the block `(xy, xy)` in the flag coordinates. -/
def xyXyConjInt : Fin 16 → Matrix (Fin 4) (Fin 4) ℤ
  | 0 => !![0, 0, -2, 2; 0, 0, 2, -2; 0, 0, -1, 1; 0, 0, 0, 0]
  | 5 => !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, -1, 0; 0, 0, 0, 0]
  | 10 => !![0, 0, -2, 2; 0, 0, 2, -2; 0, 0, -1, 1; 0, 0, 0, 0]
  | 15 => !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, -1, 0; 0, 0, 0, 0]
  | _ => 0

/-- **The compression datum of the block `(xy, xy)`**: the stacked tensor of `U_xy U_xy`
compresses onto the tensor of `U_e` carried with the weight `-1`, with three zero slots (data
file, Section 5; P5 note, Theorem 7.7(i)–(iii)). -/
def xyXyCompression : MultiBlockCompression xyXyStacked oneSlot (fun _ => (-1 : ℂ) • eMPS) :=
  MultiBlockCompression.ofScalarFlagFour xyXyInt negEIntMPS xyXyStacked_eq negEMPS_eq
    xyXyGaugeInt xyXyGaugeInvInt (by decide) (by decide) xyXyConjInt (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- **`U_xy U_xy = (-1)^L U_e` at the level of word traces** (data file, Section 2): the
restriction of the symmetry to the diagonal element `xy` is the CZX symmetry of Example D. -/
theorem xyXy_trace_evalWord (w : List (Fin 16)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord xyXyStacked w) =
      (-1 : ℂ) ^ w.length * Matrix.trace (Kraus.evalWord eMPS w) :=
  xyXyCompression.trace_evalWord_oneSlot_smul w hw

/-- The left compression witness of the block `(xy, xy)`. -/
def xyXyLeft : Matrix (Fin 1) (Fin 4) ℂ := complexOfInt !![0, 1, 0, 0]

/-- The right compression witness of the block `(xy, xy)`. -/
def xyXyRight : Matrix (Fin 4) (Fin 1) ℂ := complexOfInt !![-1; 1; -1; 1]

theorem xyXy_left_eq : xyXyCompression.left oneSlotMem = xyXyLeft := by
  rw [xyXyCompression, MultiBlockCompression.left_ofScalarFlagFour]
  ext i j
  simp only [Matrix.of_apply, xyXyLeft, complexOfInt_apply, Int.cast_inj]
  revert i j
  decide

theorem xyXy_right_eq : xyXyCompression.right oneSlotMem = xyXyRight := by
  rw [xyXyCompression, MultiBlockCompression.right_ofScalarFlagFour]
  ext i j
  simp only [Matrix.of_apply, xyXyRight, complexOfInt_apply, Int.cast_inj]
  revert i j
  decide

/-- **The explicit compression pair of the block `(xy, xy)`** (P5 note,
Theorem 7.7(iv)–(v)). -/
theorem xyXy_isReduction : IsReduction xyXyStacked ((-1 : ℂ) • eMPS) xyXyLeft xyXyRight := by
  have h := xyXyCompression.isReduction oneSlotMem
  rwa [xyXy_left_eq, xyXy_right_eq] at h

/-- **Nilpotency of the remainder of the block `(xy, xy)`** (P5 note, Theorem 7.7(vi)). -/
theorem xyXy_evalWord_remainder_eq_zero (w : List (Fin 16)) (hw : 4 ≤ w.length) :
    Kraus.evalWord xyXyCompression.remainder w = 0 :=
  xyXyCompression.evalWord_remainder_eq_zero w (by change (1 : ℕ) + 3 ≤ w.length; omega)

/-- **No nonzero right sitewise intertwiner in the block `(xy, xy)`** (data file,
Section 5). -/
theorem xyXy_right_intertwiner_eq_zero (v : Fin 4 → ℂ)
    (h : ∀ i, xyXyStacked i *ᵥ v = ((-1 : ℂ) • eMPS) i 0 0 • v) : v = 0 :=
  right_intertwiner_eq_zero_of_int xyXyInt negEIntMPS xyXyStacked_eq negEMPS_eq ![0, 0, 0, 5]
    ![0, 1, 3, 0] !![1, -1, 0, 1; -1, 1, 0, 1; 1, 1, 0, -1; 1, 1, 2, -1] 2 (by decide)
    (by decide +kernel) v h

/-- **No nonzero left sitewise intertwiner in the block `(xy, xy)`** (data file,
Section 5). -/
theorem xyXy_left_intertwiner_eq_zero (u : Fin 4 → ℂ)
    (h : ∀ i, u ᵥ* xyXyStacked i = ((-1 : ℂ) • eMPS) i 0 0 • u) : u = 0 :=
  left_intertwiner_eq_zero_of_int xyXyInt negEIntMPS xyXyStacked_eq negEMPS_eq ![0, 0, 0, 5]
    ![0, 1, 2, 1] !![1, 0, 0, 0; 0, 1, 0, 0; 0, 1, -1, 1; 1, 1, -1, 0] 1 (by decide)
    (by decide +kernel) u h

end Z2Z2Condensation
