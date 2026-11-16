/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.PhysicalMatrixEquivalence
import TNLean.MPS.MPU.Examples.SwapSymmetryStabilization

/-!
# Stabilized equivalence retaining the labelled physical symmetry

The physical matrix is retained while identity ancillas are adjoined. A
common positive ancilla and a common positive blocking length are allowed;
blocking uses the canonical finite-chain operation from `Equivalence`.
The original tensors must be MPUs, and the existing strict predicate
provides canonical endpoints and a path in a common virtual dimension.

**Scope restriction (fixed labelled physical space):** this is the
labelled-spin reading of arXiv:1703.09188, `def:equivalent-symmetry`,
lines 1356--1366. It does not replace the general commensurate-dimension
predicate `EquivalentUnderSymmetry` or assume a global dimension family.
See `docs/paper-gaps/mpu_symmetry_ancilla_transport.tex` for the remaining
source-equivalence gap. The comparisons use full operator actions;
no invariance-transport certificate is a public hypothesis.

**Local fix (one-sided swap):** the output multiplication follows the
source-defined `threeMPU2`, rather than the two-sided expression in the
printed proof. See `docs/paper-gaps/mpu_swap_symmetry_one_sided.tex`.

-/

open scoped Matrix

namespace MPOTensor

variable {d Da Db : ℕ}

/-- The labelled-spin stabilized swap/adjunction comparison is equivalent
to ordinary adjunction of the swap-transformed tensors. The same positive
ancilla and blocking witnesses work in both directions.
Source: arXiv:1703.09188, Lemma `lemma:sym-trafo-swap`, lines 2065--2085. -/
theorem equivalentUnderPhysicalMatrixSymmetry_swap_dagger_iff
    (U : MPOTensor (d * d) Da) (V : MPOTensor (d * d) Db) :
    EquivalentUnderPhysicalMatrixSymmetry .dagger (shiftPhysicalSwap d) U V ↔
      EquivalentUnderPhysicalMatrixSymmetry .dagger 1
        (U.ketLeftMul (shiftPhysicalSwap d)) (V.ketLeftMul (shiftPhysicalSwap d)) := by
  apply equivalentUnderPhysicalMatrixSymmetry_dagger_iff (shiftPhysicalSwap d)
    (shiftPhysicalSwap_mem_unitaryGroup d) (shiftPhysicalSwap_mul_self d)
  simp only [shiftPhysicalSwap, Matrix.conjTranspose_permMatrix,
    Equiv.Perm.inv_def, bondPairSwapEquiv_symm]

/-- The labelled-spin stabilized swap/transposition comparison is equivalent
to ordinary transposition of the swap-transformed tensors.
Source: arXiv:1703.09188, Lemma `lemma:sym-trafo-swap`, lines 2065--2085. -/
theorem equivalentUnderPhysicalMatrixSymmetry_swap_transpose_iff
    (U : MPOTensor (d * d) Da) (V : MPOTensor (d * d) Db) :
    EquivalentUnderPhysicalMatrixSymmetry .transpose (shiftPhysicalSwap d) U V ↔
      EquivalentUnderPhysicalMatrixSymmetry .transpose 1
        (U.ketLeftMul (shiftPhysicalSwap d)) (V.ketLeftMul (shiftPhysicalSwap d)) := by
  apply equivalentUnderPhysicalMatrixSymmetry_transpose_iff (shiftPhysicalSwap d)
    (shiftPhysicalSwap_mem_unitaryGroup d) (shiftPhysicalSwap_mul_self d)
  simp only [shiftPhysicalSwap, Matrix.transpose_permMatrix,
    Equiv.Perm.inv_def, bondPairSwapEquiv_symm]

/-- Swap multiplication preserves the labelled-spin stabilized conjugation
comparison. This concerns the same full conjugation action on each enlarged
blocked chain.
Source: arXiv:1703.09188, Lemma `lemma:sym-trafo-swap`, lines 2065--2085. -/
theorem equivalentUnderPhysicalMatrixSymmetry_swap_conjugation_iff
    (U : MPOTensor (d * d) Da) (V : MPOTensor (d * d) Db) :
    EquivalentUnderPhysicalMatrixSymmetry .conjugation (shiftPhysicalSwap d) U V ↔
      EquivalentUnderPhysicalMatrixSymmetry .conjugation 1
        (U.ketLeftMul (shiftPhysicalSwap d)) (V.ketLeftMul (shiftPhysicalSwap d)) := by
  apply equivalentUnderPhysicalMatrixSymmetry_conjugation_iff (shiftPhysicalSwap d)
    (shiftPhysicalSwap_mem_unitaryGroup d) (shiftPhysicalSwap_mul_self d)
  ext i j
  simp [shiftPhysicalSwap, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]

/-- Virtual dimensions of the three source examples, indexed in their
printed order. Source: arXiv:1703.09188, equation `threeMPU`, lines 2011--2022. -/
def shiftExampleFamilyBondDim (d : ℕ) (i : Fin 3) : ℕ :=
  Fin.cases 1 (fun _ => d * d) i

/-- The three source tensors as one finite dependent family.
Source: arXiv:1703.09188, equation `threeMPU`, lines 2011--2022. -/
noncomputable def shiftExampleFamily (d : ℕ) (i : Fin 3) :
    MPOTensor (d * d) (shiftExampleFamilyBondDim d i) :=
  Fin.cases (motive := fun j : Fin 3 => MPOTensor (d * d) (shiftExampleFamilyBondDim d j))
    (shiftExampleU₁ d)
    (fun j => Fin.cases (shiftExampleU₂ d) (fun _ => shiftExampleU₃ d) j) i

/-- The three swap-transformed source tensors in the same order.
Source: arXiv:1703.09188, equation `threeMPU2`, lines 2053--2063. -/
noncomputable def shiftExampleTildeFamily (d : ℕ) (i : Fin 3) :
    MPOTensor (d * d) (shiftExampleFamilyBondDim d i) :=
  Fin.cases (motive := fun j : Fin 3 => MPOTensor (d * d) (shiftExampleFamilyBondDim d j))
    (shiftExampleTildeU₁ d)
    (fun j => Fin.cases (shiftExampleTildeU₂ d) (fun _ => shiftExampleTildeU₃ d) j) i

private theorem shiftExampleTildeFamily_eq (d : ℕ) (i : Fin 3) :
    shiftExampleTildeFamily d i =
      (shiftExampleFamily d i).ketLeftMul (shiftPhysicalSwap d) := by
  fin_cases i <;> rfl

/-- For every pair of the three examples, labelled-spin equivalence
under swap-combined adjunction is ordinary adjunction equivalence of the
corresponding transformed examples.
Source: arXiv:1703.09188, Lemma `lemma:sym-trafo-swap`, lines 2065--2085. -/
theorem labelledShiftExamples_swap_dagger_iff (d : ℕ) (i j : Fin 3) :
    EquivalentUnderPhysicalMatrixSymmetry .dagger (shiftPhysicalSwap d)
      (shiftExampleFamily d i) (shiftExampleFamily d j) ↔
      EquivalentUnderPhysicalMatrixSymmetry .dagger 1
        (shiftExampleTildeFamily d i) (shiftExampleTildeFamily d j) := by
  simpa only [shiftExampleTildeFamily_eq] using
    equivalentUnderPhysicalMatrixSymmetry_swap_dagger_iff
      (shiftExampleFamily d i) (shiftExampleFamily d j)

/-- The labelled-spin transposition comparison for every pair of the
three source examples and their printed transformed examples.
Source: arXiv:1703.09188, Lemma `lemma:sym-trafo-swap`, lines 2065--2085. -/
theorem labelledShiftExamples_swap_transpose_iff (d : ℕ) (i j : Fin 3) :
    EquivalentUnderPhysicalMatrixSymmetry .transpose (shiftPhysicalSwap d)
      (shiftExampleFamily d i) (shiftExampleFamily d j) ↔
      EquivalentUnderPhysicalMatrixSymmetry .transpose 1
        (shiftExampleTildeFamily d i) (shiftExampleTildeFamily d j) := by
  simpa only [shiftExampleTildeFamily_eq] using
    equivalentUnderPhysicalMatrixSymmetry_swap_transpose_iff
      (shiftExampleFamily d i) (shiftExampleFamily d j)

/-- The labelled-spin conjugation comparison for every pair of the
three source examples and their printed transformed examples.
Source: arXiv:1703.09188, Lemma `lemma:sym-trafo-swap`, lines 2065--2085. -/
theorem labelledShiftExamples_swap_conjugation_iff (d : ℕ) (i j : Fin 3) :
    EquivalentUnderPhysicalMatrixSymmetry .conjugation (shiftPhysicalSwap d)
      (shiftExampleFamily d i) (shiftExampleFamily d j) ↔
      EquivalentUnderPhysicalMatrixSymmetry .conjugation 1
        (shiftExampleTildeFamily d i) (shiftExampleTildeFamily d j) := by
  simpa only [shiftExampleTildeFamily_eq] using
    equivalentUnderPhysicalMatrixSymmetry_swap_conjugation_iff
      (shiftExampleFamily d i) (shiftExampleFamily d j)

end MPOTensor
