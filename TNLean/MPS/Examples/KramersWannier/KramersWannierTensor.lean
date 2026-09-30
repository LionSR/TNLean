/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.Algebra.ComplexOfInt
import TNLean.MPS.MPDO.Defs

/-!
# Kramers–Wannier duality and translation tensors

The bond-two duality tensor has periodic kernel
`∏_j (-1)^{s'_j (s_j + s_{j+1})}` at positive length. The translation and
flipped-translation tensors have letters `E_{s,s'}` and `E_{s,1-s'}`.
The explicit entries are recorded in
`Notes/OpenProblemsTN/checks/p5_more_examples_data.md`, §1.1–1.2.
-/

noncomputable section

open scoped Matrix Kronecker

namespace KWExample

open MPSTensor

/-! ### The duality kernel and the two shift tensors -/

/-- The integer entries of the duality kernel `W^{s' s}` of the note (construction note,
`Notes/OpenProblemsTN/checks/p5_more_examples_data.md`, §1.1). The first argument is the
outgoing physical label `s'` and the second the incoming label `s`, matching the convention of
`MPOTensor`. -/
def kwIntTensor : Fin 2 → Fin 2 → Matrix (Fin 2) (Fin 2) ℤ
  | 0, 0 => !![1, 1; 0, 0]
  | 0, 1 => !![0, 0; 1, 1]
  | 1, 0 => !![1, -1; 0, 0]
  | 1, 1 => !![0, 0; -1, 1]

/-- The Kramers–Wannier duality kernel `W` as a matrix product operator tensor (construction note, §1.1). -/
def kwTensor : MPOTensor 2 2 := fun i j => complexOfInt (kwIntTensor i j)

/-- The integer entries of the one-site left-translation tensor `T^{s' s} = E_{s, s'}` (construction note,
§1.2): the matrix unit with a `1` in row `s`, column `s'`. -/
def shiftIntTensor : Fin 2 → Fin 2 → Matrix (Fin 2) (Fin 2) ℤ
  | 0, 0 => !![1, 0; 0, 0]
  | 0, 1 => !![0, 0; 1, 0]
  | 1, 0 => !![0, 1; 0, 0]
  | 1, 1 => !![0, 0; 0, 1]

/-- The one-site left-translation tensor `T`, of bond dimension two (construction note, §1.2). -/
def shiftTensor : MPOTensor 2 2 := fun i j => complexOfInt (shiftIntTensor i j)

/-- The integer entries of the flipped translation tensor `(η T)^{s' s} = E_{s, 1 - s'}`
(construction note, §1.2). -/
def flipShiftIntTensor : Fin 2 → Fin 2 → Matrix (Fin 2) (Fin 2) ℤ
  | 0, 0 => !![0, 1; 0, 0]
  | 0, 1 => !![0, 0; 0, 1]
  | 1, 0 => !![1, 0; 0, 0]
  | 1, 1 => !![0, 0; 1, 0]

/-- The flipped-translation tensor `η T`, of bond dimension two (construction note, §1.2). -/
def flipShiftTensor : MPOTensor 2 2 := fun i j => complexOfInt (flipShiftIntTensor i j)

/-- The pair-alphabet integer entries of `shiftTensor.toMPSTensor`, in the letter order
`(0,0), (0,1), (1,0), (1,1)`. -/
def shiftIntMPS : Fin 4 → Matrix (Fin 2) (Fin 2) ℤ
  | 0 => !![1, 0; 0, 0]
  | 1 => !![0, 0; 1, 0]
  | 2 => !![0, 1; 0, 0]
  | 3 => !![0, 0; 0, 1]

theorem shiftMPS_eq (a : Fin 4) : shiftTensor.toMPSTensor a = complexOfInt (shiftIntMPS a) := by
  fin_cases a <;> rfl

/-- The pair-alphabet integer entries of `flipShiftTensor.toMPSTensor`. -/
def flipShiftIntMPS : Fin 4 → Matrix (Fin 2) (Fin 2) ℤ
  | 0 => !![0, 1; 0, 0]
  | 1 => !![0, 0; 0, 1]
  | 2 => !![1, 0; 0, 0]
  | 3 => !![0, 0; 1, 0]

theorem flipShiftMPS_eq (a : Fin 4) :
    flipShiftTensor.toMPSTensor a = complexOfInt (flipShiftIntMPS a) := by
  fin_cases a <;> rfl

end KWExample
