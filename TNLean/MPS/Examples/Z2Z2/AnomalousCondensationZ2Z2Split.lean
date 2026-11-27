/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import QICLean.Algebra.Combinatorics.GeneralizeDecide
import TNLean.MPS.Examples.Z2Z2.AnomalousCondensationZ2Z2

/-!
# Anomalous `ℤ/2 × ℤ/2` symmetry: the twelve split pair blocks of the condensation defect

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

**Formalized here.** The stacked product `A ⊗ A` of the condensation defect `A = ∑_g U_g` of
the anomalous `ℤ/2 × ℤ/2` symmetry is block diagonal over the sixteen pairs `(g, h)`, the block
of `(g, h)` being the stacked tensor `M_g ⊗ M_h` of the product `U_g U_h`. Twelve of the
sixteen blocks split: each is conjugate, by an integer gauge with no zero slots, to the target
`λ(g,h) M_{gh}` with the periodic fusion sign `λ(g,h) = (-1)^{g_1 h_2}`. Ten of them, the pairs
with at most one factor from `{x, xy}` and with `λ = +1`, are literally equal to their targets;
the two pairs `(x, y)` and `(xy, y)` carry the weight `-1` and are conjugate to `-M_xy` and
`-M_x` by the sign gauge `[[0, -1], [1, 0]]`.

Each block is a one-slot compression datum with `z = 0`, whose remainder vanishes; its word
traces reproduce the fusion rule `U_g U_h = λ(g,h)^L U_{gh}` at the level of traces. The
operator-level fusion rules are derived in
`TNLean.MPS.Examples.AnomalousCondensation.AnomalousCondensationZ2Z2Defect`.

## Choice of explicit pair data

The twelve entries instantiate two existing constructions: ten use
`MultiBlockCompression.ofEq`, and `(x, y)` and `(xy, y)` use
`MultiBlockCompression.ofConjInt` with the same displayed sign gauge. The source
and target bond dimensions vary between one and two. The trace and remainder
results are projections of those shared constructions; they do not repeat their
proofs. A single `Fin 4 × Fin 4` family would therefore replace these data entries
by dependent dimension cases and gauge cases without removing a compression
argument. The complete assembly already uses `pairTarget` and the generic
compression existence theorem in the defect module. Keep the explicit entries
for their dimension-specific equalities and integer certificates. The audit
`docs/audits/2026-10-29_condensation_pair_certificates.md` records this choice.
The shared constructions own the repeated proof pattern.

## Main definitions

* `Z2Z2Condensation.eEStacked`, ..., `Z2Z2Condensation.xyYStacked`: the twelve stacked tensors.
* `Z2Z2Condensation.eECompression`, ..., `Z2Z2Condensation.xyYCompression`: their one-slot
  compression data.

## Main results

* `Z2Z2Condensation.eEStacked_eq`, ..., `Z2Z2Condensation.xyEStacked_eq`: the ten unweighted
  blocks are equal to their targets.
* `Z2Z2Condensation.eE_trace_evalWord`, ..., `Z2Z2Condensation.xyY_trace_evalWord`: the
  word-trace identities, with the weight `(-1)^L` for the pairs `(x, y)` and `(xy, y)`.
* `Z2Z2Condensation.eE_remainder_eq_zero`, ..., `Z2Z2Condensation.xyY_remainder_eq_zero`: all
  twelve remainders vanish.

## References

- [arXiv:2203.12563](https://arxiv.org/abs/2203.12563) -- J. Garre-Rubio, L. Lootens,
  A. Molnár, *Classifying phases protected by matrix product operator symmetries using matrix
  product states*
- [arXiv:2405.00439](https://arxiv.org/abs/2405.00439) -- J. Garre-Rubio, N. Schuch,
  *Fractional domain wall statistics in spin chains with anomalous symmetries*
- [arXiv:2204.02407](https://arxiv.org/abs/2204.02407) -- K. Roumpedakis, S. Seifnashri,
  S.-H. Shao, *Higher Gauging and Non-invertible Condensation Defects*

## Provenance

The block decomposition and the gauges were first recorded in
`Notes/OpenProblemsTN/checks/asym_z2z2_typeIII_data.md`, Sections 4 and 5, and checked exactly by
`Notes/OpenProblemsTN/checks/asym_z2z2_typeIII_verify.py`; they are verification records, not
the source.
-/

noncomputable section

open scoped Matrix

namespace Z2Z2Condensation

open MPSTensor

/-! ### The ten blocks equal to their targets -/

/-- The stacked tensor of `U_e U_e`. -/
def eEStacked : MPOTensor 4 1 := MPOTensor.mulTensor eTensor eTensor

/-- The stacked tensor of `U_e U_y`. -/
def eYStacked : MPOTensor 4 1 := MPOTensor.mulTensor eTensor yTensor

/-- The stacked tensor of `U_e U_x`. -/
def eXStacked : MPOTensor 4 2 := MPOTensor.mulTensor eTensor xTensor

/-- The stacked tensor of `U_e U_xy`. -/
def eXyStacked : MPOTensor 4 2 := MPOTensor.mulTensor eTensor xyTensor

/-- The stacked tensor of `U_y U_e`. -/
def yEStacked : MPOTensor 4 1 := MPOTensor.mulTensor yTensor eTensor

/-- The stacked tensor of `U_y U_y`. -/
def yYStacked : MPOTensor 4 1 := MPOTensor.mulTensor yTensor yTensor

/-- The stacked tensor of `U_y U_x`. -/
def yXStacked : MPOTensor 4 2 := MPOTensor.mulTensor yTensor xTensor

/-- The stacked tensor of `U_y U_xy`. -/
def yXyStacked : MPOTensor 4 2 := MPOTensor.mulTensor yTensor xyTensor

/-- The stacked tensor of `U_x U_e`. -/
def xEStacked : MPOTensor 4 2 := MPOTensor.mulTensor xTensor eTensor

/-- The stacked tensor of `U_xy U_e`. -/
def xyEStacked : MPOTensor 4 2 := MPOTensor.mulTensor xyTensor eTensor

private theorem eE_int (b : Fin 4 × Fin 4) :
    mulIntTensor eIntTensor eIntTensor b = eIntTensor b := by
  revert_decide_kernel b

private theorem eY_int (b : Fin 4 × Fin 4) :
    mulIntTensor eIntTensor yIntTensor b = yIntTensor b := by
  revert_decide_kernel b

private theorem eX_int (b : Fin 4 × Fin 4) :
    mulIntTensor eIntTensor xIntTensor b = xIntTensor b := by
  revert_decide_kernel b

private theorem eXy_int (b : Fin 4 × Fin 4) :
    mulIntTensor eIntTensor xyIntTensor b = xyIntTensor b := by
  revert_decide_kernel b

private theorem yE_int (b : Fin 4 × Fin 4) :
    mulIntTensor yIntTensor eIntTensor b = yIntTensor b := by
  revert_decide_kernel b

private theorem yY_int (b : Fin 4 × Fin 4) :
    mulIntTensor yIntTensor yIntTensor b = eIntTensor b := by
  revert_decide_kernel b

private theorem yX_int (b : Fin 4 × Fin 4) :
    mulIntTensor yIntTensor xIntTensor b = xyIntTensor b := by
  revert_decide_kernel b

private theorem yXy_int (b : Fin 4 × Fin 4) :
    mulIntTensor yIntTensor xyIntTensor b = xIntTensor b := by
  revert_decide_kernel b

private theorem xE_int (b : Fin 4 × Fin 4) :
    mulIntTensor xIntTensor eIntTensor b = xIntTensor b := by
  revert_decide_kernel b

private theorem xyE_int (b : Fin 4 × Fin 4) :
    mulIntTensor xyIntTensor eIntTensor b = xyIntTensor b := by
  revert_decide_kernel b

/-- **`U_e U_e`**: the stacked tensor is the tensor of `U_e` (data file, Section 5). -/
theorem eEStacked_eq (a : Fin 4 × Fin 4) : eEStacked a = eTensor a := by
  change _ = complexOfInt (eIntTensor a)
  rw [← eE_int]
  exact mulTensor_complexOfRing _ eIntTensor eIntTensor a

/-- **`U_e U_y`**: the stacked tensor is the tensor of `U_y` (data file, Section 5). -/
theorem eYStacked_eq (a : Fin 4 × Fin 4) : eYStacked a = yTensor a := by
  change _ = complexOfInt (yIntTensor a)
  rw [← eY_int]
  exact mulTensor_complexOfRing _ eIntTensor yIntTensor a

/-- **`U_e U_x`**: the stacked tensor is the tensor of `U_x` (data file, Section 5). -/
theorem eXStacked_eq (a : Fin 4 × Fin 4) : eXStacked a = xTensor a := by
  change _ = complexOfInt (xIntTensor a)
  rw [← eX_int]
  exact mulTensor_complexOfRing _ eIntTensor xIntTensor a

/-- **`U_e U_xy`**: the stacked tensor is the tensor of `U_xy` (data file, Section 5). -/
theorem eXyStacked_eq (a : Fin 4 × Fin 4) : eXyStacked a = xyTensor a := by
  change _ = complexOfInt (xyIntTensor a)
  rw [← eXy_int]
  exact mulTensor_complexOfRing _ eIntTensor xyIntTensor a

/-- **`U_y U_e`**: the stacked tensor is the tensor of `U_y` (data file, Section 5). -/
theorem yEStacked_eq (a : Fin 4 × Fin 4) : yEStacked a = yTensor a := by
  change _ = complexOfInt (yIntTensor a)
  rw [← yE_int]
  exact mulTensor_complexOfRing _ yIntTensor eIntTensor a

/-- **`U_y U_y`**: the stacked tensor is the tensor of `U_e` (data file, Section 5). -/
theorem yYStacked_eq (a : Fin 4 × Fin 4) : yYStacked a = eTensor a := by
  change _ = complexOfInt (eIntTensor a)
  rw [← yY_int]
  exact mulTensor_complexOfRing _ yIntTensor yIntTensor a

/-- **`U_y U_x`**: the stacked tensor is the tensor of `U_xy` (data file, Section 5). -/
theorem yXStacked_eq (a : Fin 4 × Fin 4) : yXStacked a = xyTensor a := by
  change _ = complexOfInt (xyIntTensor a)
  rw [← yX_int]
  exact mulTensor_complexOfRing _ yIntTensor xIntTensor a

/-- **`U_y U_xy`**: the stacked tensor is the tensor of `U_x` (data file, Section 5). -/
theorem yXyStacked_eq (a : Fin 4 × Fin 4) : yXyStacked a = xTensor a := by
  change _ = complexOfInt (xIntTensor a)
  rw [← yXy_int]
  exact mulTensor_complexOfRing _ yIntTensor xyIntTensor a

/-- **`U_x U_e`**: the stacked tensor is the tensor of `U_x` (data file, Section 5). -/
theorem xEStacked_eq (a : Fin 4 × Fin 4) : xEStacked a = xTensor a := by
  change _ = complexOfInt (xIntTensor a)
  rw [← xE_int]
  exact mulTensor_complexOfRing _ xIntTensor eIntTensor a

/-- **`U_xy U_e`**: the stacked tensor is the tensor of `U_xy` (data file, Section 5). -/
theorem xyEStacked_eq (a : Fin 4 × Fin 4) : xyEStacked a = xyTensor a := by
  change _ = complexOfInt (xyIntTensor a)
  rw [← xyE_int]
  exact mulTensor_complexOfRing _ xyIntTensor eIntTensor a

/-- The compression datum of the pair `(e, e)`. -/
def eECompression : MultiBlockCompression eEStacked oneSlot (fun _ => eTensor) :=
  MultiBlockCompression.ofEq eEStacked_eq

/-- The compression datum of the pair `(e, y)`. -/
def eYCompression : MultiBlockCompression eYStacked oneSlot (fun _ => yTensor) :=
  MultiBlockCompression.ofEq eYStacked_eq

/-- The compression datum of the pair `(e, x)`. -/
def eXCompression : MultiBlockCompression eXStacked oneSlot (fun _ => xTensor) :=
  MultiBlockCompression.ofEq eXStacked_eq

/-- The compression datum of the pair `(e, xy)`. -/
def eXyCompression : MultiBlockCompression eXyStacked oneSlot (fun _ => xyTensor) :=
  MultiBlockCompression.ofEq eXyStacked_eq

/-- The compression datum of the pair `(y, e)`. -/
def yECompression : MultiBlockCompression yEStacked oneSlot (fun _ => yTensor) :=
  MultiBlockCompression.ofEq yEStacked_eq

/-- The compression datum of the pair `(y, y)`. -/
def yYCompression : MultiBlockCompression yYStacked oneSlot (fun _ => eTensor) :=
  MultiBlockCompression.ofEq yYStacked_eq

/-- The compression datum of the pair `(y, x)`. -/
def yXCompression : MultiBlockCompression yXStacked oneSlot (fun _ => xyTensor) :=
  MultiBlockCompression.ofEq yXStacked_eq

/-- The compression datum of the pair `(y, xy)`. -/
def yXyCompression : MultiBlockCompression yXyStacked oneSlot (fun _ => xTensor) :=
  MultiBlockCompression.ofEq yXyStacked_eq

/-- The compression datum of the pair `(x, e)`. -/
def xECompression : MultiBlockCompression xEStacked oneSlot (fun _ => xTensor) :=
  MultiBlockCompression.ofEq xEStacked_eq

/-- The compression datum of the pair `(xy, e)`. -/
def xyECompression : MultiBlockCompression xyEStacked oneSlot (fun _ => xyTensor) :=
  MultiBlockCompression.ofEq xyEStacked_eq

/-! ### The two blocks with the sign gauge -/

/-- The sign gauge of the two weight `-1` split blocks (data file, appendix). -/
def signGaugeInt : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; 1, 0]

/-- The inverse of the sign gauge. -/
def signGaugeInvInt : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; -1, 0]

/-- The stacked tensor of `U_x U_y`. -/
def xYStacked : MPOTensor 4 2 := MPOTensor.mulTensor xTensor yTensor

/-- The stacked tensor of `U_xy U_y`. -/
def xyYStacked : MPOTensor 4 2 := MPOTensor.mulTensor xyTensor yTensor

/-- The integer matrices of the stacked tensor of `U_x U_y` (data file, appendix). -/
def xYInt : Fin 4 × Fin 4 → Matrix (Fin 2) (Fin 2) ℤ
  | (0, 3) => !![1, 0; 1, 0]
  | (1, 2) => !![0, 1; 0, -1]
  | (2, 1) => !![1, 0; 1, 0]
  | (3, 0) => !![0, 1; 0, -1]
  | _ => 0

/-- The integer matrices of the stacked tensor of `U_xy U_y` (data file, appendix). -/
def xyYInt : Fin 4 × Fin 4 → Matrix (Fin 2) (Fin 2) ℤ
  | (0, 2) => !![0, 1; 0, -1]
  | (1, 3) => !![1, 0; 1, 0]
  | (2, 0) => !![0, 1; 0, -1]
  | (3, 1) => !![1, 0; 1, 0]
  | _ => 0

private theorem xY_int (b : Fin 4 × Fin 4) : mulIntTensor xIntTensor yIntTensor b = xYInt b := by
  revert_decide_kernel b

private theorem xyY_int (b : Fin 4 × Fin 4) : mulIntTensor xyIntTensor yIntTensor b = xyYInt b := by
  revert_decide_kernel b

theorem xYStacked_eq (a : Fin 4 × Fin 4) : xYStacked a = complexOfInt (xYInt a) := by
  rw [← xY_int]
  exact mulTensor_complexOfRing _ xIntTensor yIntTensor a

theorem xyYStacked_eq (a : Fin 4 × Fin 4) : xyYStacked a = complexOfInt (xyYInt a) := by
  rw [← xyY_int]
  exact mulTensor_complexOfRing _ xyIntTensor yIntTensor a

/-- **The pair `(x, y)`**: the stacked tensor is conjugate by the sign gauge to the tensor of
`U_xy` carried with the weight `-1` (data file, Section 5). -/
def xYCompression : MultiBlockCompression xYStacked oneSlot (fun _ => (-1 : ℂ) • xyTensor) :=
  MultiBlockCompression.ofConjInt xYInt negXYIntMPS xYStacked_eq negXYMPS_eq signGaugeInt
    signGaugeInvInt (by decide) (by decide) (by decide +kernel)

/-- **The pair `(xy, y)`**: the stacked tensor is conjugate by the sign gauge to the tensor of
`U_x` carried with the weight `-1` (data file, Section 5). -/
def xyYCompression : MultiBlockCompression xyYStacked oneSlot (fun _ => (-1 : ℂ) • xTensor) :=
  MultiBlockCompression.ofConjInt xyYInt negXIntMPS xyYStacked_eq negXMPS_eq signGaugeInt
    signGaugeInvInt (by decide) (by decide) (by decide +kernel)

/-! ### Word traces -/

/-- **`U_e U_e = U_e` at the level of word traces.** -/
theorem eE_trace_evalWord (w : List (Fin 4 × Fin 4)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord eEStacked w) = Matrix.trace (Kraus.evalWord eTensor w) :=
  eECompression.trace_evalWord_oneSlot w hw

/-- **`U_e U_y = U_y` at the level of word traces.** -/
theorem eY_trace_evalWord (w : List (Fin 4 × Fin 4)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord eYStacked w) = Matrix.trace (Kraus.evalWord yTensor w) :=
  eYCompression.trace_evalWord_oneSlot w hw

/-- **`U_e U_x = U_x` at the level of word traces.** -/
theorem eX_trace_evalWord (w : List (Fin 4 × Fin 4)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord eXStacked w) = Matrix.trace (Kraus.evalWord xTensor w) :=
  eXCompression.trace_evalWord_oneSlot w hw

/-- **`U_e U_xy = U_xy` at the level of word traces.** -/
theorem eXy_trace_evalWord (w : List (Fin 4 × Fin 4)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord eXyStacked w) = Matrix.trace (Kraus.evalWord xyTensor w) :=
  eXyCompression.trace_evalWord_oneSlot w hw

/-- **`U_y U_e = U_y` at the level of word traces.** -/
theorem yE_trace_evalWord (w : List (Fin 4 × Fin 4)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord yEStacked w) = Matrix.trace (Kraus.evalWord yTensor w) :=
  yECompression.trace_evalWord_oneSlot w hw

/-- **`U_y U_y = U_e` at the level of word traces.** -/
theorem yY_trace_evalWord (w : List (Fin 4 × Fin 4)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord yYStacked w) = Matrix.trace (Kraus.evalWord eTensor w) :=
  yYCompression.trace_evalWord_oneSlot w hw

/-- **`U_y U_x = U_xy` at the level of word traces.** -/
theorem yX_trace_evalWord (w : List (Fin 4 × Fin 4)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord yXStacked w) = Matrix.trace (Kraus.evalWord xyTensor w) :=
  yXCompression.trace_evalWord_oneSlot w hw

/-- **`U_y U_xy = U_x` at the level of word traces.** -/
theorem yXy_trace_evalWord (w : List (Fin 4 × Fin 4)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord yXyStacked w) = Matrix.trace (Kraus.evalWord xTensor w) :=
  yXyCompression.trace_evalWord_oneSlot w hw

/-- **`U_x U_e = U_x` at the level of word traces.** -/
theorem xE_trace_evalWord (w : List (Fin 4 × Fin 4)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord xEStacked w) = Matrix.trace (Kraus.evalWord xTensor w) :=
  xECompression.trace_evalWord_oneSlot w hw

/-- **`U_xy U_e = U_xy` at the level of word traces.** -/
theorem xyE_trace_evalWord (w : List (Fin 4 × Fin 4)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord xyEStacked w) = Matrix.trace (Kraus.evalWord xyTensor w) :=
  xyECompression.trace_evalWord_oneSlot w hw

/-- **`U_x U_y = (-1)^L U_xy` at the level of word traces** (data file, Section 2). -/
theorem xY_trace_evalWord (w : List (Fin 4 × Fin 4)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord xYStacked w) =
      (-1 : ℂ) ^ w.length * Matrix.trace (Kraus.evalWord xyTensor w) :=
  xYCompression.trace_evalWord_oneSlot_smul w hw

/-- **`U_xy U_y = (-1)^L U_x` at the level of word traces** (data file, Section 2). -/
theorem xyY_trace_evalWord (w : List (Fin 4 × Fin 4)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord xyYStacked w) =
      (-1 : ℂ) ^ w.length * Matrix.trace (Kraus.evalWord xTensor w) :=
  xyYCompression.trace_evalWord_oneSlot_smul w hw

/-! ### Vanishing remainders -/

theorem eE_remainder_eq_zero : eECompression.remainder = 0 :=
  MultiBlockCompression.remainder_ofEq eEStacked_eq

theorem eY_remainder_eq_zero : eYCompression.remainder = 0 :=
  MultiBlockCompression.remainder_ofEq eYStacked_eq

theorem eX_remainder_eq_zero : eXCompression.remainder = 0 :=
  MultiBlockCompression.remainder_ofEq eXStacked_eq

theorem eXy_remainder_eq_zero : eXyCompression.remainder = 0 :=
  MultiBlockCompression.remainder_ofEq eXyStacked_eq

theorem yE_remainder_eq_zero : yECompression.remainder = 0 :=
  MultiBlockCompression.remainder_ofEq yEStacked_eq

theorem yY_remainder_eq_zero : yYCompression.remainder = 0 :=
  MultiBlockCompression.remainder_ofEq yYStacked_eq

theorem yX_remainder_eq_zero : yXCompression.remainder = 0 :=
  MultiBlockCompression.remainder_ofEq yXStacked_eq

theorem yXy_remainder_eq_zero : yXyCompression.remainder = 0 :=
  MultiBlockCompression.remainder_ofEq yXyStacked_eq

theorem xE_remainder_eq_zero : xECompression.remainder = 0 :=
  MultiBlockCompression.remainder_ofEq xEStacked_eq

theorem xyE_remainder_eq_zero : xyECompression.remainder = 0 :=
  MultiBlockCompression.remainder_ofEq xyEStacked_eq

theorem xY_remainder_eq_zero : xYCompression.remainder = 0 := by
  unfold xYCompression
  exact MultiBlockCompression.remainder_ofConjInt _ _ _ _ _ _ _ _ _

theorem xyY_remainder_eq_zero : xyYCompression.remainder = 0 := by
  unfold xyYCompression
  exact MultiBlockCompression.remainder_ofConjInt _ _ _ _ _ _ _ _ _

end Z2Z2Condensation
