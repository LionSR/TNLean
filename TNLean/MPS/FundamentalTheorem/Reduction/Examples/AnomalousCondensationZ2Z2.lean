/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.OneSlotGauge
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.StackedPairGauge

/-!
# The anomalous `ℤ/2 × ℤ/2` symmetry with the mixed three-cocycle

This file sets up the four matrix product operator tensors of an anomalous `ℤ/2 × ℤ/2`
symmetry on a periodic chain of two-qubit sites, the object behind the condensation-defect
example of the multi-block asymmetric compression theorem
(`Notes/OpenProblemsTN/checks/asym_z2z2_typeIII_data.md`, Sections 1 and 2; verified exactly by
`checks/asym_z2z2_typeIII_verify.py`). Writing `x = (1,0)`, `y = (0,1)` and `xy = (1,1)` for the
generators and `a = (a_1, a_2)` for a site label with basis index `2 a_1 + a_2`, the four
periodic operators on `L` sites are
`U_x = (∏_k CZ(2_k, 2_{k+1})) ∏_k X_k^{(1)}`, `U_y = ∏_k X_k^{(2)}`,
`U_xy = (∏_k CZ(2_k, 2_{k+1})) ∏_k X_k^{(1)} X_k^{(2)}` and `U_e = id`, where `CZ(2_k, 2_{k+1})`
couples the second qubits of neighbouring sites. Each is the periodic trace of the tensor
`M_g^{(o,i)}[α, β] = δ_{o, g + i} δ_{β, π_g(i)} f_g(α, i)` with bond label `π_g(i) = i_2`
and phase `f_g(α, i) = (-1)^{α i_2}` for `g ∈ {x, xy}`, and with bond dimension one and no
phase for `g ∈ {e, y}`. The restriction of `M_x` to the second qubit is the CZX tensor of
`TNLean.MPS.FundamentalTheorem.Reduction.Examples.CZXTensor`.

The symmetry carries the mixed (type-II) class `(-1)^{a_1 b_2 c_2}` of
`H^3(ℤ/2 × ℤ/2, U(1))`, computed in the data file both from the fusion phases of the tensors
and from the Else--Nayak associator of truncated operators (Section 3): its restriction to `x`
and to `y` is trivial and its restriction to `xy` is the CZX class. The periodic fusion rule of the
four operators is `U_g U_h = λ(g,h)^L U_{gh}` with the sign `λ(g,h) = (-1)^{g_1 h_2}` (Section 2);
these signs are the weights of the compression data in the companion files, not the
three-cocycle itself. No cocycle class is computed in this development: the statements below
and in the companion files are the normality of the tensors, the fusion rules of the periodic
operators, and the compression data, and the class is taken from the data file.

Every matrix has entries in `{0, ±1}`, so the tensors are entrywise coercions of integer
matrices, and every later verification is a decidable identity between integer matrices.

## Main definitions

* `Z2Z2Condensation.eTensor`, `Z2Z2Condensation.yTensor`, `Z2Z2Condensation.xTensor`,
  `Z2Z2Condensation.xyTensor`: the four matrix product operator tensors, of bond dimensions
  `1, 1, 2, 2`.
* `Z2Z2Condensation.eMPS`, `Z2Z2Condensation.yMPS`, `Z2Z2Condensation.xMPS`,
  `Z2Z2Condensation.xyMPS`: the same tensors over the sixteen-letter pair alphabet, with their
  integer matrices `eIntMPS`, `yIntMPS`, `xIntMPS`, `xyIntMPS`.

## Main results

* `Z2Z2Condensation.eMPS_isNormal`, `Z2Z2Condensation.yMPS_isNormal`: the bond-one tensors are
  normal at blocking length one.
* `Z2Z2Condensation.xMPS_isNBlkInjective_two`, `Z2Z2Condensation.xyMPS_isNBlkInjective_two`,
  `Z2Z2Condensation.xMPS_isNormal`, `Z2Z2Condensation.xyMPS_isNormal`: the bond-two tensors
  are normal at blocking length two.
* `Z2Z2Condensation.xMPS_not_isNBlkInjective_one`,
  `Z2Z2Condensation.xyMPS_not_isNBlkInjective_one`: they are not injective at length one.
-/

noncomputable section

open scoped Matrix

namespace Z2Z2Condensation

open MPSTensor

/-! ### The four tensors -/

/-- The integer tensor of the identity `U_e`, of bond dimension one: `M_e^{(o,i)} = δ_{o,i}`
(data file, Section 1). -/
def eIntTensor : Fin 4 → Fin 4 → Matrix (Fin 1) (Fin 1) ℤ :=
  fun o i => if o = i then 1 else 0

/-- The integer tensor of `U_y = ∏_k X_k^{(2)}`, of bond dimension one:
`M_y^{(o,i)} = δ_{o, y + i}` (data file, Section 1). -/
def yIntTensor : Fin 4 → Fin 4 → Matrix (Fin 1) (Fin 1) ℤ
  | 0, 1 => 1
  | 1, 0 => 1
  | 2, 3 => 1
  | 3, 2 => 1
  | _, _ => 0

/-- The integer tensor of `U_x = (∏_k CZ(2_k, 2_{k+1})) ∏_k X_k^{(1)}`, of bond dimension two:
`M_x^{(o,i)} = δ_{o, x + i} T_{i_2}` with `T_0 = [[1, 0], [1, 0]]` and `T_1 = [[0, 1], [0, -1]]`
(data file, Section 1). -/
def xIntTensor : Fin 4 → Fin 4 → Matrix (Fin 2) (Fin 2) ℤ
  | 0, 2 => !![1, 0; 1, 0]
  | 2, 0 => !![1, 0; 1, 0]
  | 1, 3 => !![0, 1; 0, -1]
  | 3, 1 => !![0, 1; 0, -1]
  | _, _ => 0

/-- The integer tensor of `U_xy = (∏_k CZ(2_k, 2_{k+1})) ∏_k X_k^{(1)} X_k^{(2)}`, of bond
dimension two: `M_xy^{(o,i)} = δ_{o, xy + i} T_{i_2}` (data file, Section 1). -/
def xyIntTensor : Fin 4 → Fin 4 → Matrix (Fin 2) (Fin 2) ℤ
  | 1, 2 => !![1, 0; 1, 0]
  | 3, 0 => !![1, 0; 1, 0]
  | 0, 3 => !![0, 1; 0, -1]
  | 2, 1 => !![0, 1; 0, -1]
  | _, _ => 0

/-- The tensor of `U_e` as a matrix product operator tensor. -/
def eTensor : MPOTensor 4 1 := fun o i => complexOfInt (eIntTensor o i)

/-- The tensor of `U_y` as a matrix product operator tensor. -/
def yTensor : MPOTensor 4 1 := fun o i => complexOfInt (yIntTensor o i)

/-- The tensor of `U_x` as a matrix product operator tensor. -/
def xTensor : MPOTensor 4 2 := fun o i => complexOfInt (xIntTensor o i)

/-- The tensor of `U_xy` as a matrix product operator tensor. -/
def xyTensor : MPOTensor 4 2 := fun o i => complexOfInt (xyIntTensor o i)

/-! ### The pair-alphabet view -/

/-- The tensor of `U_e` over the pair alphabet `Fin 16`, letter `a = 4 o + i`. -/
def eMPS : MPSTensor 16 1 := eTensor.toMPSTensor

/-- The tensor of `U_y` over the pair alphabet. -/
def yMPS : MPSTensor 16 1 := yTensor.toMPSTensor

/-- The tensor of `U_x` over the pair alphabet. -/
def xMPS : MPSTensor 16 2 := xTensor.toMPSTensor

/-- The tensor of `U_xy` over the pair alphabet. -/
def xyMPS : MPSTensor 16 2 := xyTensor.toMPSTensor

/-- The integer matrices of `eMPS`: the letters `(o, o)` carry `1`. -/
def eIntMPS : Fin 16 → Matrix (Fin 1) (Fin 1) ℤ
  | 0 => 1
  | 5 => 1
  | 10 => 1
  | 15 => 1
  | _ => 0

/-- The integer matrices of `yMPS`: the letters `(y + i, i)` carry `1`. -/
def yIntMPS : Fin 16 → Matrix (Fin 1) (Fin 1) ℤ
  | 1 => 1
  | 4 => 1
  | 11 => 1
  | 14 => 1
  | _ => 0

/-- The integer matrices of `xMPS`: the letters `(x + i, i)` carry `T_{i_2}`. -/
def xIntMPS : Fin 16 → Matrix (Fin 2) (Fin 2) ℤ
  | 2 => !![1, 0; 1, 0]
  | 7 => !![0, 1; 0, -1]
  | 8 => !![1, 0; 1, 0]
  | 13 => !![0, 1; 0, -1]
  | _ => 0

/-- The integer matrices of `xyMPS`: the letters `(xy + i, i)` carry `T_{i_2}`. -/
def xyIntMPS : Fin 16 → Matrix (Fin 2) (Fin 2) ℤ
  | 3 => !![0, 1; 0, -1]
  | 6 => !![1, 0; 1, 0]
  | 9 => !![0, 1; 0, -1]
  | 12 => !![1, 0; 1, 0]
  | _ => 0

theorem eMPS_eq (a : Fin 16) : eMPS a = complexOfInt (eIntMPS a) := by
  fin_cases a <;> rfl

theorem yMPS_eq (a : Fin 16) : yMPS a = complexOfInt (yIntMPS a) := by
  fin_cases a <;> rfl

theorem xMPS_eq (a : Fin 16) : xMPS a = complexOfInt (xIntMPS a) := by
  fin_cases a <;> rfl

theorem xyMPS_eq (a : Fin 16) : xyMPS a = complexOfInt (xyIntMPS a) := by
  fin_cases a <;> rfl

/-- The integer matrices of `eMPS` carried with the weight `-1`. -/
def negEIntMPS (a : Fin 16) : Matrix (Fin 1) (Fin 1) ℤ := -eIntMPS a

/-- The integer matrices of `yMPS` carried with the weight `-1`. -/
def negYIntMPS (a : Fin 16) : Matrix (Fin 1) (Fin 1) ℤ := -yIntMPS a

/-- The integer matrices of `xMPS` carried with the weight `-1`. -/
def negXIntMPS (a : Fin 16) : Matrix (Fin 2) (Fin 2) ℤ := -xIntMPS a

/-- The integer matrices of `xyMPS` carried with the weight `-1`. -/
def negXYIntMPS (a : Fin 16) : Matrix (Fin 2) (Fin 2) ℤ := -xyIntMPS a

theorem negEMPS_eq (a : Fin 16) : ((-1 : ℂ) • eMPS) a = complexOfInt (negEIntMPS a) := by
  rw [negEIntMPS, complexOfInt_neg, ← eMPS_eq]
  simp

theorem negYMPS_eq (a : Fin 16) : ((-1 : ℂ) • yMPS) a = complexOfInt (negYIntMPS a) := by
  rw [negYIntMPS, complexOfInt_neg, ← yMPS_eq]
  simp

theorem negXMPS_eq (a : Fin 16) : ((-1 : ℂ) • xMPS) a = complexOfInt (negXIntMPS a) := by
  rw [negXIntMPS, complexOfInt_neg, ← xMPS_eq]
  simp

theorem negXYMPS_eq (a : Fin 16) : ((-1 : ℂ) • xyMPS) a = complexOfInt (negXYIntMPS a) := by
  rw [negXYIntMPS, complexOfInt_neg, ← xyMPS_eq]
  simp

/-! ### Normality -/

/-- **The tensor of `U_e` is normal at length one**: its bond dimension is one and the letter
`(0, 0)` acts by `1` (data file, Section 1). -/
theorem eMPS_isNormal : Kraus.IsNormal eMPS :=
  P6Compression.isNormal_of_single_eq_smul eIntMPS (c := 1) one_ne_zero
    (fun a => by rw [eMPS_eq, one_smul]) (fun _ _ => 0) (fun _ _ => 1) (fun _ _ => one_ne_zero)
    (by decide)

/-- **The tensor of `U_y` is normal at length one**: its bond dimension is one and the letter
`(0, 1)` acts by `1` (data file, Section 1). -/
theorem yMPS_isNormal : Kraus.IsNormal yMPS :=
  P6Compression.isNormal_of_single_eq_smul yIntMPS (c := 1) one_ne_zero
    (fun a => by rw [yMPS_eq, one_smul]) (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => one_ne_zero)
    (by decide)

/-- The integer certificate of `xMPS_isNBlkInjective_two`: the coefficients expressing twice
each matrix unit through the four length-two words `(2,2), (7,2), (2,7), (7,7)`. -/
def xSpanCoeff : Fin 2 → Fin 2 → Fin 4 → ℤ
  | 0, 0 => ![1, 1, 0, 0]
  | 0, 1 => ![0, 0, 1, -1]
  | 1, 0 => ![1, -1, 0, 0]
  | 1, 1 => ![0, 0, 1, 1]

/-- **The tensor of `U_x` is injective at blocking length two**: its length-two words span the
full two-by-two matrix algebra (data file, Section 1). -/
theorem xMPS_isNBlkInjective_two : Kraus.IsNBlkInjective xMPS 2 :=
  isNBlkInjective_two_of_int xIntMPS xMPS_eq ![2, 7, 2, 7] ![2, 2, 7, 7] xSpanCoeff 2
    two_ne_zero (by decide)

/-- The integer certificate of `xyMPS_isNBlkInjective_two`, for the length-two words
`(3,3), (6,3), (3,6), (6,6)`. -/
def xySpanCoeff : Fin 2 → Fin 2 → Fin 4 → ℤ
  | 0, 0 => ![0, 0, 1, 1]
  | 0, 1 => ![-1, 1, 0, 0]
  | 1, 0 => ![0, 0, -1, 1]
  | 1, 1 => ![1, 1, 0, 0]

/-- **The tensor of `U_xy` is injective at blocking length two** (data file, Section 1). -/
theorem xyMPS_isNBlkInjective_two : Kraus.IsNBlkInjective xyMPS 2 :=
  isNBlkInjective_two_of_int xyIntMPS xyMPS_eq ![3, 6, 3, 6] ![3, 3, 6, 6] xySpanCoeff 2
    two_ne_zero (by decide)

/-- **The tensor of `U_x` is normal.** -/
theorem xMPS_isNormal : Kraus.IsNormal xMPS :=
  ⟨2, two_pos, xMPS_isNBlkInjective_two⟩

/-- **The tensor of `U_xy` is normal.** -/
theorem xyMPS_isNormal : Kraus.IsNormal xyMPS :=
  ⟨2, two_pos, xyMPS_isNBlkInjective_two⟩

/-- The functional `X ↦ X_{00} - X_{10}` annihilating every letter of `xMPS` and of
`xyMPS`. -/
private def rowDifference : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] ℂ :=
  Matrix.entryLinearMap ℂ ℂ 0 0 - Matrix.entryLinearMap ℂ ℂ 1 0

private theorem rowDifference_apply (X : Matrix (Fin 2) (Fin 2) ℂ) :
    rowDifference X = X 0 0 - X 1 0 := rfl

/-- **The tensor of `U_x` is not injective at length one**: its four nonzero letters span only
a two-dimensional space of matrices (data file, Section 1). -/
theorem xMPS_not_isNBlkInjective_one : ¬ Kraus.IsNBlkInjective xMPS 1 := by
  refine Kraus.not_isNBlkInjective_of_linearMap rowDifference (fun σ => ?_)
    (Matrix.single 0 0 1) (by simp [rowDifference_apply])
  rw [rowDifference_apply]
  simp only [Kraus.evalWord, List.ofFn_succ, List.ofFn_zero, Matrix.mul_one]
  generalize σ 0 = a
  fin_cases a <;> simp [xMPS_eq, xIntMPS, complexOfInt]

/-- **The tensor of `U_xy` is not injective at length one** (data file, Section 1). -/
theorem xyMPS_not_isNBlkInjective_one : ¬ Kraus.IsNBlkInjective xyMPS 1 := by
  refine Kraus.not_isNBlkInjective_of_linearMap rowDifference (fun σ => ?_)
    (Matrix.single 0 0 1) (by simp [rowDifference_apply])
  rw [rowDifference_apply]
  simp only [Kraus.evalWord, List.ofFn_succ, List.ofFn_zero, Matrix.mul_one]
  generalize σ 0 = a
  fin_cases a <;> simp [xyMPS_eq, xyIntMPS, complexOfInt]

end Z2Z2Condensation
