/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Examples.MultiBlock.OneSlotGauge
import TNLean.MPS.Examples.MultiBlock.StackedPairGauge

/-!
# The anomalous `ℤ/2 × ℤ/2` symmetry with the mixed three-cocycle

**Source.** Garre-Rubio, Lootens, Molnár 2023 (arXiv:2203.12563),
`Papers/2203.12563/REsubmission.tex` lines 2200–2224: the periodic matrix product operator
representation of a finite group built from a three-cocycle; lines 1845–1888: the three-cocycles
of `ℤ₂ × ℤ₂`, among them the type-II component `ω_II(a b^i, a^j b, a^k b) = −1` (line 1848),
which in the coordinates `a = (1,0)`, `b = (0,1)` is `(−1)^{a₁ b₂ c₂}`, of class `(0,0,1)` in
the table of lines 1856–1872, and a periodic single-qubit realization of that class,
`U_a = ∏_i CZ_{i,i+1} Z_i`, `U_b = ∏_i X_i` (line 1884). The two-qubit tensors below are
representatives of the same class constructed in this development;
`AnomalousCondensationZ2Z2Instance` identifies their periodic operators with those of the
cocycle construction for `(−1)^{a₁ b₂ c₂}` up to an on-site dressing.

This file sets up the four matrix product operator tensors of an anomalous `ℤ/2 × ℤ/2`
symmetry on a periodic chain of two-qubit sites, the object behind the condensation-defect
example of the multi-block asymmetric compression theorem
(`Notes/OpenProblemsTN/checks/asym_z2z2_typeIII_data.md`, Sections 1 and 2; verified exactly by
`checks/asym_z2z2_typeIII_verify.py`). Writing `x = (1,0)`, `y = (0,1)` and `xy = (1,1)` for the
generators and `a = (a_1, a_2)` for a site label with basis index `2 a_1 + a_2`, the four
periodic operators on `L` sites are
`U_x = (∏_k CZ(2_k, 2_{k+1})) ∏_k X_k^{(1)}`, `U_y = ∏_k X_k^{(2)}`,
`U_xy = (∏_k X_k^{(1)} X_k^{(2)}) (∏_k CZ(2_k, 2_{k+1}))` and `U_e = id`, where `CZ(2_k, 2_{k+1})`
couples the second qubits of neighbouring sites. Each is the periodic trace of the tensor
`M_g^{(o,i)}[α, β] = δ_{o, g + i} δ_{β, π_g(i)} f_g(α, i)` with bond label `π_g(i) = i_2`
and phase `f_g(α, i) = (-1)^{α i_2}` for `g ∈ {x, xy}`, and with bond dimension one and no
phase for `g ∈ {e, y}`. For `L > 0`, in the computational basis this means
`U_g |i⟩ = (-1)^{g_1 ∑_k i_{k,2} i_{k+1,2}} |i+g⟩`.
In particular the phase is evaluated on the input second bits, before either bit is flipped.
Writing that diagonal phase as `D_{2,L}`, we have `U_xy = (X_1 X_2)^{⊗ L} D_{2,L}`;
reversing these factors changes the sign by `(-1)^L`.
The bond matrices `T_j` are the same as in `CZXTensor`, but `M_x` flips only the first
qubit, not the second, so it is not a restriction of the CZX spin-flip tensor.

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
  `1, 1, 2, 2`, with their integer matrices `eIntTensor`, `yIntTensor`, `xIntTensor`,
  `xyIntTensor`.

## Main results

* `Z2Z2Condensation.eMPS_isNormal`, `Z2Z2Condensation.yMPS_isNormal`: the bond-one tensors are
  normal at blocking length one.
* `Z2Z2Condensation.xMPS_isNBlkInjective_two`, `Z2Z2Condensation.xyMPS_isNBlkInjective_two`,
  `Z2Z2Condensation.xMPS_isNormal`, `Z2Z2Condensation.xyMPS_isNormal`: the bond-two tensors
  are normal at blocking length two.
* `Z2Z2Condensation.xMPS_not_isNBlkInjective_one`,
  `Z2Z2Condensation.xyMPS_not_isNBlkInjective_one`: they are not injective at length one.

## References
- [arXiv:2203.12563](https://arxiv.org/abs/2203.12563) -- Garre-Rubio, Lootens, Molnár,
  *Classifying phases protected by matrix product operator symmetries using matrix product
  states*

## Provenance
The tensors and the exact certificates were first recorded in
`Notes/OpenProblemsTN/checks/asym_z2z2_typeIII_data.md`, Sections 1 and 2; they are
verification records, not the source.
-/

noncomputable section

open scoped Matrix

namespace Z2Z2Condensation

open MPSTensor

/-! ### The four tensors -/

/-- The integer tensor of the identity `U_e`, of bond dimension one: `M_e^{(o,i)} = δ_{o,i}`
(data file, Section 1). -/
def eIntTensor : Fin 4 × Fin 4 → Matrix (Fin 1) (Fin 1) ℤ :=
  fun oi => if oi.1 = oi.2 then 1 else 0

/-- The integer tensor of `U_y = ∏_k X_k^{(2)}`, of bond dimension one:
`M_y^{(o,i)} = δ_{o, y + i}` (data file, Section 1). -/
def yIntTensor : Fin 4 × Fin 4 → Matrix (Fin 1) (Fin 1) ℤ
  | (0, 1) => 1
  | (1, 0) => 1
  | (2, 3) => 1
  | (3, 2) => 1
  | _ => 0

/-- The integer tensor of `U_x = (∏_k CZ(2_k, 2_{k+1})) ∏_k X_k^{(1)}`, of bond dimension two:
`M_x^{(o,i)} = δ_{o, x + i} T_{i_2}` with `T_0 = [[1, 0], [1, 0]]` and `T_1 = [[0, 1], [0, -1]]`
(data file, Section 1). -/
def xIntTensor : Fin 4 × Fin 4 → Matrix (Fin 2) (Fin 2) ℤ
  | (0, 2) => !![1, 0; 1, 0]
  | (2, 0) => !![1, 0; 1, 0]
  | (1, 3) => !![0, 1; 0, -1]
  | (3, 1) => !![0, 1; 0, -1]
  | _ => 0

/-- The integer tensor of `U_xy = (∏_k X_k^{(1)} X_k^{(2)}) (∏_k CZ(2_k, 2_{k+1}))`, of bond
dimension two: `M_xy^{(o,i)} = δ_{o, xy + i} T_{i_2}` (data file, Section 1). -/
def xyIntTensor : Fin 4 × Fin 4 → Matrix (Fin 2) (Fin 2) ℤ
  | (1, 2) => !![1, 0; 1, 0]
  | (3, 0) => !![1, 0; 1, 0]
  | (0, 3) => !![0, 1; 0, -1]
  | (2, 1) => !![0, 1; 0, -1]
  | _ => 0

/-- The tensor of `U_e` as a matrix product operator tensor. -/
def eTensor : MPOTensor 4 1 := fun oi => complexOfInt (eIntTensor oi)

/-- The tensor of `U_y` as a matrix product operator tensor. -/
def yTensor : MPOTensor 4 1 := fun oi => complexOfInt (yIntTensor oi)

/-- The tensor of `U_x` as a matrix product operator tensor. -/
def xTensor : MPOTensor 4 2 := fun oi => complexOfInt (xIntTensor oi)

/-- The tensor of `U_xy` as a matrix product operator tensor. -/
def xyTensor : MPOTensor 4 2 := fun oi => complexOfInt (xyIntTensor oi)

theorem eTensor_eq (a : Fin 4 × Fin 4) : eTensor a = complexOfInt (eIntTensor a) := rfl

theorem yTensor_eq (a : Fin 4 × Fin 4) : yTensor a = complexOfInt (yIntTensor a) := rfl

theorem xTensor_eq (a : Fin 4 × Fin 4) : xTensor a = complexOfInt (xIntTensor a) := rfl

theorem xyTensor_eq (a : Fin 4 × Fin 4) : xyTensor a = complexOfInt (xyIntTensor a) := rfl

/-- The integer matrices of `eTensor` carried with the weight `-1`. -/
def negEIntMPS (a : Fin 4 × Fin 4) : Matrix (Fin 1) (Fin 1) ℤ := -eIntTensor a

/-- The integer matrices of `yTensor` carried with the weight `-1`. -/
def negYIntMPS (a : Fin 4 × Fin 4) : Matrix (Fin 1) (Fin 1) ℤ := -yIntTensor a

/-- The integer matrices of `xTensor` carried with the weight `-1`. -/
def negXIntMPS (a : Fin 4 × Fin 4) : Matrix (Fin 2) (Fin 2) ℤ := -xIntTensor a

/-- The integer matrices of `xyTensor` carried with the weight `-1`. -/
def negXYIntMPS (a : Fin 4 × Fin 4) : Matrix (Fin 2) (Fin 2) ℤ := -xyIntTensor a

theorem negEMPS_eq (a : Fin 4 × Fin 4) :
    ((-1 : ℂ) • eTensor) a = complexOfInt (negEIntMPS a) := by
  rw [negEIntMPS, complexOfInt_neg]
  simp [eTensor]

theorem negYMPS_eq (a : Fin 4 × Fin 4) :
    ((-1 : ℂ) • yTensor) a = complexOfInt (negYIntMPS a) := by
  rw [negYIntMPS, complexOfInt_neg]
  simp [yTensor]

theorem negXMPS_eq (a : Fin 4 × Fin 4) :
    ((-1 : ℂ) • xTensor) a = complexOfInt (negXIntMPS a) := by
  rw [negXIntMPS, complexOfInt_neg]
  simp [xTensor]

theorem negXYMPS_eq (a : Fin 4 × Fin 4) :
    ((-1 : ℂ) • xyTensor) a = complexOfInt (negXYIntMPS a) := by
  rw [negXYIntMPS, complexOfInt_neg]
  simp [xyTensor]

/-! ### Normality -/

/-- **The tensor of `U_e` is normal at length one**: its bond dimension is one and the letter
`(0, 0)` acts by `1` (data file, Section 1). -/
theorem eMPS_isNormal : Kraus.IsNormal eTensor :=
  P6Compression.isNormal_of_single_eq_smul eIntTensor (c := 1) one_ne_zero
    (fun _ => (one_smul ℂ _).symm) (fun _ _ => (0, 0)) (fun _ _ => 1) (fun _ _ => one_ne_zero)
    (by decide)

/-- **The tensor of `U_y` is normal at length one**: its bond dimension is one and the letter
`(0, 1)` acts by `1` (data file, Section 1). -/
theorem yMPS_isNormal : Kraus.IsNormal yTensor :=
  P6Compression.isNormal_of_single_eq_smul yIntTensor (c := 1) one_ne_zero
    (fun _ => (one_smul ℂ _).symm) (fun _ _ => (0, 1)) (fun _ _ => 1) (fun _ _ => one_ne_zero)
    (by decide)

/-- The integer certificate of `xMPS_isNBlkInjective_two`: the coefficients expressing twice
each matrix unit through the four length-two words in the letters `(0, 2)` and `(1, 3)`. -/
def xSpanCoeff : Fin 2 → Fin 2 → Fin 4 → ℤ
  | 0, 0 => ![1, 1, 0, 0]
  | 0, 1 => ![0, 0, 1, -1]
  | 1, 0 => ![1, -1, 0, 0]
  | 1, 1 => ![0, 0, 1, 1]

/-- **The tensor of `U_x` is injective at blocking length two**: its length-two words span the
full two-by-two matrix algebra (data file, Section 1). -/
theorem xMPS_isNBlkInjective_two : Kraus.IsNBlkInjective xTensor 2 :=
  isNBlkInjective_two_of_int xIntTensor xTensor_eq ![(0, 2), (1, 3), (0, 2), (1, 3)]
    ![(0, 2), (0, 2), (1, 3), (1, 3)] xSpanCoeff 2
    two_ne_zero (by decide)

/-- The integer certificate of `xyMPS_isNBlkInjective_two`, for the length-two words
in the letters `(0, 3)` and `(1, 2)`. -/
def xySpanCoeff : Fin 2 → Fin 2 → Fin 4 → ℤ
  | 0, 0 => ![0, 0, 1, 1]
  | 0, 1 => ![-1, 1, 0, 0]
  | 1, 0 => ![0, 0, -1, 1]
  | 1, 1 => ![1, 1, 0, 0]

/-- **The tensor of `U_xy` is injective at blocking length two** (data file, Section 1). -/
theorem xyMPS_isNBlkInjective_two : Kraus.IsNBlkInjective xyTensor 2 :=
  isNBlkInjective_two_of_int xyIntTensor xyTensor_eq ![(0, 3), (1, 2), (0, 3), (1, 2)]
    ![(0, 3), (0, 3), (1, 2), (1, 2)] xySpanCoeff 2
    two_ne_zero (by decide)

/-- **The tensor of `U_x` is normal.** -/
theorem xMPS_isNormal : Kraus.IsNormal xTensor :=
  ⟨2, two_pos, xMPS_isNBlkInjective_two⟩

/-- **The tensor of `U_xy` is normal.** -/
theorem xyMPS_isNormal : Kraus.IsNormal xyTensor :=
  ⟨2, two_pos, xyMPS_isNBlkInjective_two⟩

/-- The functional `X ↦ X_{00} - X_{10}` annihilating every letter of `xTensor` and of
`xyTensor`. -/
private def rowDifference : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] ℂ :=
  Matrix.entryLinearMap ℂ ℂ 0 0 - Matrix.entryLinearMap ℂ ℂ 1 0

private theorem rowDifference_apply (X : Matrix (Fin 2) (Fin 2) ℂ) :
    rowDifference X = X 0 0 - X 1 0 := rfl

/-- **The tensor of `U_x` is not injective at length one**: its four nonzero letters span only
a two-dimensional space of matrices (data file, Section 1). -/
theorem xMPS_not_isNBlkInjective_one : ¬ Kraus.IsNBlkInjective xTensor 1 := by
  refine Kraus.not_isNBlkInjective_of_linearMap rowDifference (fun σ => ?_)
    (Matrix.single 0 0 1) (by simp [rowDifference_apply])
  rw [rowDifference_apply]
  simp only [Kraus.evalWord, List.ofFn_succ, List.ofFn_zero, Matrix.mul_one]
  generalize σ 0 = a
  fin_cases a <;> simp [xTensor, xIntTensor, complexOfInt]

/-- **The tensor of `U_xy` is not injective at length one** (data file, Section 1). -/
theorem xyMPS_not_isNBlkInjective_one : ¬ Kraus.IsNBlkInjective xyTensor 1 := by
  refine Kraus.not_isNBlkInjective_of_linearMap rowDifference (fun σ => ?_)
    (Matrix.single 0 0 1) (by simp [rowDifference_apply])
  rw [rowDifference_apply]
  simp only [Kraus.evalWord, List.ofFn_succ, List.ofFn_zero, Matrix.mul_one]
  generalize σ 0 = a
  fin_cases a <;> simp [xyTensor, xyIntTensor, complexOfInt]

end Z2Z2Condensation
