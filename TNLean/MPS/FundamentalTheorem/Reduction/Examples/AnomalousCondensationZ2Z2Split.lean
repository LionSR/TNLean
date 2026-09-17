/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.Algebra.GeneralizeDecide
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.AnomalousCondensationZ2Z2

/-!
# The twelve split pair blocks of the `ℤ/2 × ℤ/2` condensation defect

The stacked product `A ⊗ A` of the condensation defect `A = ∑_g U_g` of the anomalous
`ℤ/2 × ℤ/2` symmetry is block diagonal over the sixteen pairs `(g, h)`, the block of `(g, h)`
being the stacked tensor `M_g ⊗ M_h` of the product `U_g U_h`
(`Notes/OpenProblemsTN/checks/asym_z2z2_typeIII_data.md`, Sections 4 and 5). Twelve of the
sixteen blocks split: each is conjugate, by an integer gauge with no zero slots, to the target
`λ(g,h) M_{gh}` with the periodic fusion sign `λ(g,h) = (-1)^{g_1 h_2}`. Ten of them, the pairs
with at most one factor from `{x, xy}` and with `λ = +1`, are literally equal to their targets; the
two pairs `(x, y)` and `(xy, y)` carry the weight `-1` and are conjugate to `-M_xy` and `-M_x` by
the sign gauge `[[0, -1], [1, 0]]`.

Each block is a one-slot compression datum with `z = 0`, whose remainder vanishes; its word
traces reproduce the fusion rule `U_g U_h = λ(g,h)^L U_{gh}` at the level of traces. The
operator-level fusion rules are derived in
`TNLean.MPS.FundamentalTheorem.Reduction.Examples.AnomalousCondensationZ2Z2Defect`.

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
-/

noncomputable section

open scoped Matrix

namespace Z2Z2Condensation

open MPSTensor

/-! ### The ten blocks equal to their targets -/

/-- The stacked tensor of `U_e U_e`. -/
def eEStacked : MPSTensor 16 1 := (MPOTensor.mulTensor eTensor eTensor).toMPSTensor

/-- The stacked tensor of `U_e U_y`. -/
def eYStacked : MPSTensor 16 1 := (MPOTensor.mulTensor eTensor yTensor).toMPSTensor

/-- The stacked tensor of `U_e U_x`. -/
def eXStacked : MPSTensor 16 2 := (MPOTensor.mulTensor eTensor xTensor).toMPSTensor

/-- The stacked tensor of `U_e U_xy`. -/
def eXyStacked : MPSTensor 16 2 := (MPOTensor.mulTensor eTensor xyTensor).toMPSTensor

/-- The stacked tensor of `U_y U_e`. -/
def yEStacked : MPSTensor 16 1 := (MPOTensor.mulTensor yTensor eTensor).toMPSTensor

/-- The stacked tensor of `U_y U_y`. -/
def yYStacked : MPSTensor 16 1 := (MPOTensor.mulTensor yTensor yTensor).toMPSTensor

/-- The stacked tensor of `U_y U_x`. -/
def yXStacked : MPSTensor 16 2 := (MPOTensor.mulTensor yTensor xTensor).toMPSTensor

/-- The stacked tensor of `U_y U_xy`. -/
def yXyStacked : MPSTensor 16 2 := (MPOTensor.mulTensor yTensor xyTensor).toMPSTensor

/-- The stacked tensor of `U_x U_e`. -/
def xEStacked : MPSTensor 16 2 := (MPOTensor.mulTensor xTensor eTensor).toMPSTensor

/-- The stacked tensor of `U_xy U_e`. -/
def xyEStacked : MPSTensor 16 2 := (MPOTensor.mulTensor xyTensor eTensor).toMPSTensor

private theorem eE_int (b : Fin 16) : stackedInt eIntTensor eIntTensor b = eIntMPS b := by
  revert_decide_kernel b

private theorem eY_int (b : Fin 16) : stackedInt eIntTensor yIntTensor b = yIntMPS b := by
  revert_decide_kernel b

private theorem eX_int (b : Fin 16) : stackedInt eIntTensor xIntTensor b = xIntMPS b := by
  revert_decide_kernel b

private theorem eXy_int (b : Fin 16) : stackedInt eIntTensor xyIntTensor b = xyIntMPS b := by
  revert_decide_kernel b

private theorem yE_int (b : Fin 16) : stackedInt yIntTensor eIntTensor b = yIntMPS b := by
  revert_decide_kernel b

private theorem yY_int (b : Fin 16) : stackedInt yIntTensor yIntTensor b = eIntMPS b := by
  revert_decide_kernel b

private theorem yX_int (b : Fin 16) : stackedInt yIntTensor xIntTensor b = xyIntMPS b := by
  revert_decide_kernel b

private theorem yXy_int (b : Fin 16) : stackedInt yIntTensor xyIntTensor b = xIntMPS b := by
  revert_decide_kernel b

private theorem xE_int (b : Fin 16) : stackedInt xIntTensor eIntTensor b = xIntMPS b := by
  revert_decide_kernel b

private theorem xyE_int (b : Fin 16) : stackedInt xyIntTensor eIntTensor b = xyIntMPS b := by
  revert_decide_kernel b

/-- **`U_e U_e`**: the stacked tensor is the tensor of `U_e` (data file, Section 5). -/
theorem eEStacked_eq (a : Fin 16) : eEStacked a = eMPS a := by
  rw [eMPS_eq, ← eE_int]
  exact toMPSTensor_mulTensor_complexOfInt eIntTensor eIntTensor a

/-- **`U_e U_y`**: the stacked tensor is the tensor of `U_y` (data file, Section 5). -/
theorem eYStacked_eq (a : Fin 16) : eYStacked a = yMPS a := by
  rw [yMPS_eq, ← eY_int]
  exact toMPSTensor_mulTensor_complexOfInt eIntTensor yIntTensor a

/-- **`U_e U_x`**: the stacked tensor is the tensor of `U_x` (data file, Section 5). -/
theorem eXStacked_eq (a : Fin 16) : eXStacked a = xMPS a := by
  rw [xMPS_eq, ← eX_int]
  exact toMPSTensor_mulTensor_complexOfInt eIntTensor xIntTensor a

/-- **`U_e U_xy`**: the stacked tensor is the tensor of `U_xy` (data file, Section 5). -/
theorem eXyStacked_eq (a : Fin 16) : eXyStacked a = xyMPS a := by
  rw [xyMPS_eq, ← eXy_int]
  exact toMPSTensor_mulTensor_complexOfInt eIntTensor xyIntTensor a

/-- **`U_y U_e`**: the stacked tensor is the tensor of `U_y` (data file, Section 5). -/
theorem yEStacked_eq (a : Fin 16) : yEStacked a = yMPS a := by
  rw [yMPS_eq, ← yE_int]
  exact toMPSTensor_mulTensor_complexOfInt yIntTensor eIntTensor a

/-- **`U_y U_y`**: the stacked tensor is the tensor of `U_e` (data file, Section 5). -/
theorem yYStacked_eq (a : Fin 16) : yYStacked a = eMPS a := by
  rw [eMPS_eq, ← yY_int]
  exact toMPSTensor_mulTensor_complexOfInt yIntTensor yIntTensor a

/-- **`U_y U_x`**: the stacked tensor is the tensor of `U_xy` (data file, Section 5). -/
theorem yXStacked_eq (a : Fin 16) : yXStacked a = xyMPS a := by
  rw [xyMPS_eq, ← yX_int]
  exact toMPSTensor_mulTensor_complexOfInt yIntTensor xIntTensor a

/-- **`U_y U_xy`**: the stacked tensor is the tensor of `U_x` (data file, Section 5). -/
theorem yXyStacked_eq (a : Fin 16) : yXyStacked a = xMPS a := by
  rw [xMPS_eq, ← yXy_int]
  exact toMPSTensor_mulTensor_complexOfInt yIntTensor xyIntTensor a

/-- **`U_x U_e`**: the stacked tensor is the tensor of `U_x` (data file, Section 5). -/
theorem xEStacked_eq (a : Fin 16) : xEStacked a = xMPS a := by
  rw [xMPS_eq, ← xE_int]
  exact toMPSTensor_mulTensor_complexOfInt xIntTensor eIntTensor a

/-- **`U_xy U_e`**: the stacked tensor is the tensor of `U_xy` (data file, Section 5). -/
theorem xyEStacked_eq (a : Fin 16) : xyEStacked a = xyMPS a := by
  rw [xyMPS_eq, ← xyE_int]
  exact toMPSTensor_mulTensor_complexOfInt xyIntTensor eIntTensor a

/-- The compression datum of the pair `(e, e)`. -/
def eECompression : MultiBlockCompression eEStacked oneSlot (fun _ => eMPS) :=
  MultiBlockCompression.ofEq eEStacked_eq

/-- The compression datum of the pair `(e, y)`. -/
def eYCompression : MultiBlockCompression eYStacked oneSlot (fun _ => yMPS) :=
  MultiBlockCompression.ofEq eYStacked_eq

/-- The compression datum of the pair `(e, x)`. -/
def eXCompression : MultiBlockCompression eXStacked oneSlot (fun _ => xMPS) :=
  MultiBlockCompression.ofEq eXStacked_eq

/-- The compression datum of the pair `(e, xy)`. -/
def eXyCompression : MultiBlockCompression eXyStacked oneSlot (fun _ => xyMPS) :=
  MultiBlockCompression.ofEq eXyStacked_eq

/-- The compression datum of the pair `(y, e)`. -/
def yECompression : MultiBlockCompression yEStacked oneSlot (fun _ => yMPS) :=
  MultiBlockCompression.ofEq yEStacked_eq

/-- The compression datum of the pair `(y, y)`. -/
def yYCompression : MultiBlockCompression yYStacked oneSlot (fun _ => eMPS) :=
  MultiBlockCompression.ofEq yYStacked_eq

/-- The compression datum of the pair `(y, x)`. -/
def yXCompression : MultiBlockCompression yXStacked oneSlot (fun _ => xyMPS) :=
  MultiBlockCompression.ofEq yXStacked_eq

/-- The compression datum of the pair `(y, xy)`. -/
def yXyCompression : MultiBlockCompression yXyStacked oneSlot (fun _ => xMPS) :=
  MultiBlockCompression.ofEq yXyStacked_eq

/-- The compression datum of the pair `(x, e)`. -/
def xECompression : MultiBlockCompression xEStacked oneSlot (fun _ => xMPS) :=
  MultiBlockCompression.ofEq xEStacked_eq

/-- The compression datum of the pair `(xy, e)`. -/
def xyECompression : MultiBlockCompression xyEStacked oneSlot (fun _ => xyMPS) :=
  MultiBlockCompression.ofEq xyEStacked_eq

/-! ### The two blocks with the sign gauge -/

/-- The sign gauge of the two weight `-1` split blocks (data file, appendix). -/
def signGaugeInt : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; 1, 0]

/-- The inverse of the sign gauge. -/
def signGaugeInvInt : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; -1, 0]

/-- The stacked tensor of `U_x U_y`. -/
def xYStacked : MPSTensor 16 2 := (MPOTensor.mulTensor xTensor yTensor).toMPSTensor

/-- The stacked tensor of `U_xy U_y`. -/
def xyYStacked : MPSTensor 16 2 := (MPOTensor.mulTensor xyTensor yTensor).toMPSTensor

/-- The integer matrices of the stacked tensor of `U_x U_y` (data file, appendix). -/
def xYInt : Fin 16 → Matrix (Fin 2) (Fin 2) ℤ
  | 3 => !![1, 0; 1, 0]
  | 6 => !![0, 1; 0, -1]
  | 9 => !![1, 0; 1, 0]
  | 12 => !![0, 1; 0, -1]
  | _ => 0

/-- The integer matrices of the stacked tensor of `U_xy U_y` (data file, appendix). -/
def xyYInt : Fin 16 → Matrix (Fin 2) (Fin 2) ℤ
  | 2 => !![0, 1; 0, -1]
  | 7 => !![1, 0; 1, 0]
  | 8 => !![0, 1; 0, -1]
  | 13 => !![1, 0; 1, 0]
  | _ => 0

private theorem xY_int (b : Fin 16) : stackedInt xIntTensor yIntTensor b = xYInt b := by
  revert_decide_kernel b

private theorem xyY_int (b : Fin 16) : stackedInt xyIntTensor yIntTensor b = xyYInt b := by
  revert_decide_kernel b

theorem xYStacked_eq (a : Fin 16) : xYStacked a = complexOfInt (xYInt a) := by
  rw [← xY_int]
  exact toMPSTensor_mulTensor_complexOfInt xIntTensor yIntTensor a

theorem xyYStacked_eq (a : Fin 16) : xyYStacked a = complexOfInt (xyYInt a) := by
  rw [← xyY_int]
  exact toMPSTensor_mulTensor_complexOfInt xyIntTensor yIntTensor a

/-- **The pair `(x, y)`**: the stacked tensor is conjugate by the sign gauge to the tensor of
`U_xy` carried with the weight `-1` (data file, Section 5). -/
def xYCompression : MultiBlockCompression xYStacked oneSlot (fun _ => (-1 : ℂ) • xyMPS) :=
  MultiBlockCompression.ofConjInt xYInt negXYIntMPS xYStacked_eq negXYMPS_eq signGaugeInt
    signGaugeInvInt (by decide) (by decide) (by decide +kernel)

/-- **The pair `(xy, y)`**: the stacked tensor is conjugate by the sign gauge to the tensor of
`U_x` carried with the weight `-1` (data file, Section 5). -/
def xyYCompression : MultiBlockCompression xyYStacked oneSlot (fun _ => (-1 : ℂ) • xMPS) :=
  MultiBlockCompression.ofConjInt xyYInt negXIntMPS xyYStacked_eq negXMPS_eq signGaugeInt
    signGaugeInvInt (by decide) (by decide) (by decide +kernel)

/-! ### Word traces -/

/-- **`U_e U_e = U_e` at the level of word traces.** -/
theorem eE_trace_evalWord (w : List (Fin 16)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord eEStacked w) = Matrix.trace (Kraus.evalWord eMPS w) :=
  eECompression.trace_evalWord_oneSlot w hw

/-- **`U_e U_y = U_y` at the level of word traces.** -/
theorem eY_trace_evalWord (w : List (Fin 16)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord eYStacked w) = Matrix.trace (Kraus.evalWord yMPS w) :=
  eYCompression.trace_evalWord_oneSlot w hw

/-- **`U_e U_x = U_x` at the level of word traces.** -/
theorem eX_trace_evalWord (w : List (Fin 16)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord eXStacked w) = Matrix.trace (Kraus.evalWord xMPS w) :=
  eXCompression.trace_evalWord_oneSlot w hw

/-- **`U_e U_xy = U_xy` at the level of word traces.** -/
theorem eXy_trace_evalWord (w : List (Fin 16)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord eXyStacked w) = Matrix.trace (Kraus.evalWord xyMPS w) :=
  eXyCompression.trace_evalWord_oneSlot w hw

/-- **`U_y U_e = U_y` at the level of word traces.** -/
theorem yE_trace_evalWord (w : List (Fin 16)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord yEStacked w) = Matrix.trace (Kraus.evalWord yMPS w) :=
  yECompression.trace_evalWord_oneSlot w hw

/-- **`U_y U_y = U_e` at the level of word traces.** -/
theorem yY_trace_evalWord (w : List (Fin 16)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord yYStacked w) = Matrix.trace (Kraus.evalWord eMPS w) :=
  yYCompression.trace_evalWord_oneSlot w hw

/-- **`U_y U_x = U_xy` at the level of word traces.** -/
theorem yX_trace_evalWord (w : List (Fin 16)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord yXStacked w) = Matrix.trace (Kraus.evalWord xyMPS w) :=
  yXCompression.trace_evalWord_oneSlot w hw

/-- **`U_y U_xy = U_x` at the level of word traces.** -/
theorem yXy_trace_evalWord (w : List (Fin 16)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord yXyStacked w) = Matrix.trace (Kraus.evalWord xMPS w) :=
  yXyCompression.trace_evalWord_oneSlot w hw

/-- **`U_x U_e = U_x` at the level of word traces.** -/
theorem xE_trace_evalWord (w : List (Fin 16)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord xEStacked w) = Matrix.trace (Kraus.evalWord xMPS w) :=
  xECompression.trace_evalWord_oneSlot w hw

/-- **`U_xy U_e = U_xy` at the level of word traces.** -/
theorem xyE_trace_evalWord (w : List (Fin 16)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord xyEStacked w) = Matrix.trace (Kraus.evalWord xyMPS w) :=
  xyECompression.trace_evalWord_oneSlot w hw

/-- **`U_x U_y = (-1)^L U_xy` at the level of word traces** (data file, Section 2). -/
theorem xY_trace_evalWord (w : List (Fin 16)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord xYStacked w) =
      (-1 : ℂ) ^ w.length * Matrix.trace (Kraus.evalWord xyMPS w) :=
  xYCompression.trace_evalWord_oneSlot_smul w hw

/-- **`U_xy U_y = (-1)^L U_x` at the level of word traces** (data file, Section 2). -/
theorem xyY_trace_evalWord (w : List (Fin 16)) (hw : w ≠ []) :
    Matrix.trace (Kraus.evalWord xyYStacked w) =
      (-1 : ℂ) ^ w.length * Matrix.trace (Kraus.evalWord xMPS w) :=
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
