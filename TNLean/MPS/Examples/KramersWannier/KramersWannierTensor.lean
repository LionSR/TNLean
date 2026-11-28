/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.Algebra.ComplexOfInt
import TNLean.MPS.Operator.Defs

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
def kwIntTensor : Fin 2 × Fin 2 → Matrix (Fin 2) (Fin 2) ℤ
  | (0, 0) => !![1, 1; 0, 0]
  | (0, 1) => !![0, 0; 1, 1]
  | (1, 0) => !![1, -1; 0, 0]
  | (1, 1) => !![0, 0; -1, 1]

/-- The Kramers–Wannier duality kernel `W` as a matrix product operator tensor
(construction note, §1.1). -/
def kwTensor : MPOTensor 2 2 := fun ij => complexOfInt (kwIntTensor ij)

/-- The integer entries of the one-site left-translation tensor `T^{s' s} = E_{s, s'}`
(construction note, §1.2): the matrix unit with a `1` in row `s`, column `s'`. -/
def shiftIntTensor : Fin 2 × Fin 2 → Matrix (Fin 2) (Fin 2) ℤ
  | (0, 0) => !![1, 0; 0, 0]
  | (0, 1) => !![0, 0; 1, 0]
  | (1, 0) => !![0, 1; 0, 0]
  | (1, 1) => !![0, 0; 0, 1]

/-- The one-site left-translation tensor `T`, of bond dimension two (construction note, §1.2). -/
def shiftTensor : MPOTensor 2 2 := fun ij => complexOfInt (shiftIntTensor ij)

/-- The integer entries of the flipped translation tensor `(η T)^{s' s} = E_{s, 1 - s'}`
(construction note, §1.2). -/
def flipShiftIntTensor : Fin 2 × Fin 2 → Matrix (Fin 2) (Fin 2) ℤ
  | (0, 0) => !![0, 1; 0, 0]
  | (0, 1) => !![0, 0; 0, 1]
  | (1, 0) => !![1, 0; 0, 0]
  | (1, 1) => !![0, 0; 1, 0]

/-- The flipped-translation tensor `η T`, of bond dimension two (construction note, §1.2). -/
def flipShiftTensor : MPOTensor 2 2 :=
    fun ij => complexOfInt (flipShiftIntTensor ij)

end KWExample
