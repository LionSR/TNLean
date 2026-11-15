/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.PhysicalMatrixBlocking
import TNLean.MPS.MPU.Examples.SwapSymmetryStabilization

/-!
# Stabilized equivalence retaining the labelled physical symmetry

The physical matrix is retained while identity ancillas are adjoined. A
common positive ancilla and a common positive blocking length are allowed;
blocking uses the canonical finite-chain operation from `Equivalence`.
The original tensors must be MPUs, and the existing strict predicate
provides canonical endpoints and a path in a common virtual dimension.

This is the labelled-spin reading of arXiv:1703.09188,
`def:equivalent-symmetry`, lines 1356--1366. It compares tensors on the same
labelled physical space and does not replace the general commensurate-
dimension predicate `EquivalentUnderSymmetry`. No global dimension family
is assumed. The swap comparison below is derived from the actual full
operator actions; no invariance-transport certificate is a public hypothesis.
-/

open scoped Matrix

namespace MPOTensor

variable {d Da Db : ℕ}

/-- The three finite-chain symmetry operations compared in
arXiv:1703.09188, Lemma `lemma:sym-trafo-swap`, lines 2065--2085. -/
inductive PhysicalSymmetryKind where
  | dagger
  | transpose
  | conjugation

/-- Specify the full action using the retained physical matrix. Ordinary
conjugation is independent of that matrix.
Source: arXiv:1703.09188, `SSymmetries`, lines 1301--1322. -/
noncomputable def PhysicalSymmetryKind.withMatrix (kind : PhysicalSymmetryKind)
    (Q : Matrix (Fin d) (Fin d) ℂ) : FiniteChainOperatorSymmetry d :=
  match kind with
  | .dagger => .daggerWithPhysicalMatrix Q
  | .transpose => .transposeWithPhysicalMatrix Q
  | .conjugation => conjugationSymmetry d

/-- Equivalence on a fixed labelled physical space, retaining its physical
matrix through arbitrary common positive identity ancillas and canonical
positive blocking. The original endpoints are MPUs; canonical form of the
blocked endpoints and arbitrary common virtual dimension are supplied by
the existing strict-equivalence predicate.

This states the concrete labelled-spin convention in arXiv:1703.09188,
`def:equivalent-symmetry`, lines 1356--1366, including the additional labelled
ancillary spin in `prop:U1-U2-equiv-ancillatrick`, lines 2210--2234.
It makes no assertion about the general dimension-indexed family convention. -/
def EquivalentUnderPhysicalMatrixSymmetry (kind : PhysicalSymmetryKind)
    (Q : Matrix (Fin d) (Fin d) ℂ) (U : MPOTensor d Da) (V : MPOTensor d Db) : Prop :=
  IsMPU U ∧ IsMPU V ∧ ∃ x > 0, ∃ k > 0,
    StrictlyEquivalentUnderSymmetry ((kind.withMatrix (physicalIdMatrix Q x)).block k)
      (blockTensor (tensorPhysicalId U x) k) (blockTensor (tensorPhysicalId V x) k) rfl

private theorem isMPU_ketLeftMul_swap_iff {D : ℕ} (U : MPOTensor (d * d) D) :
    IsMPU U ↔ IsMPU (U.ketLeftMul (shiftPhysicalSwap d)) := by
  constructor
  · intro hU
    exact hU.ketLeftMul (shiftPhysicalSwap_mem_unitaryGroup d)
  · intro hU
    simpa only [ketLeftMul_involutive (shiftPhysicalSwap d)
      (shiftPhysicalSwap_mul_self d) U] using
      hU.ketLeftMul (shiftPhysicalSwap_mem_unitaryGroup d)

private theorem equivalent_of_strict_comparisons
    (kind : PhysicalSymmetryKind) (Q R : Matrix (Fin (d * d)) (Fin (d * d)) ℂ)
    (U : MPOTensor (d * d) Da) (V : MPOTensor (d * d) Db)
    (hstrict : ∀ x k : ℕ, 0 < k →
      (StrictlyEquivalentUnderSymmetry ((kind.withMatrix (physicalIdMatrix Q x)).block k)
        (blockTensor (tensorPhysicalId U x) k) (blockTensor (tensorPhysicalId V x) k) rfl ↔
      StrictlyEquivalentUnderSymmetry ((kind.withMatrix (physicalIdMatrix R x)).block k)
        (blockTensor (tensorPhysicalId (U.ketLeftMul (shiftPhysicalSwap d)) x) k)
        (blockTensor (tensorPhysicalId (V.ketLeftMul (shiftPhysicalSwap d)) x) k) rfl)) :
    EquivalentUnderPhysicalMatrixSymmetry kind Q U V ↔
      EquivalentUnderPhysicalMatrixSymmetry kind R
        (U.ketLeftMul (shiftPhysicalSwap d)) (V.ketLeftMul (shiftPhysicalSwap d)) := by
  unfold EquivalentUnderPhysicalMatrixSymmetry
  refine and_congr (isMPU_ketLeftMul_swap_iff U)
    (and_congr (isMPU_ketLeftMul_swap_iff V) ?_)
  exact exists_congr fun x => and_congr_right fun _ =>
    exists_congr fun k => and_congr_right fun hk => hstrict x k hk

/-- The labelled-spin stabilized swap/adjunction comparison is equivalent
to ordinary adjunction of the swap-transformed tensors. The same positive
ancilla and blocking witnesses work in both directions.
Source: arXiv:1703.09188, Lemma `lemma:sym-trafo-swap`, lines 2065--2085. -/
theorem equivalentUnderPhysicalMatrixSymmetry_swap_dagger_iff
    (U : MPOTensor (d * d) Da) (V : MPOTensor (d * d) Db) :
    EquivalentUnderPhysicalMatrixSymmetry .dagger (shiftPhysicalSwap d) U V ↔
      EquivalentUnderPhysicalMatrixSymmetry .dagger 1
        (U.ketLeftMul (shiftPhysicalSwap d)) (V.ketLeftMul (shiftPhysicalSwap d)) := by
  apply equivalent_of_strict_comparisons
  intro x k hk
  simp only [PhysicalSymmetryKind.withMatrix]
  rw [FiniteChainOperatorSymmetry.daggerWithPhysicalMatrix_block _ hk,
    FiniteChainOperatorSymmetry.daggerWithPhysicalMatrix_block _ hk,
    physicalIdMatrix_one, MPSTensor.blockKron_one,
    FiniteChainOperatorSymmetry.daggerWithPhysicalMatrix_one]
  exact strictlyEquivalentUnderSymmetry_ancillaSwapDagger_iff U V x k

/-- The labelled-spin stabilized swap/transposition comparison is equivalent
to ordinary transposition of the swap-transformed tensors.
Source: arXiv:1703.09188, Lemma `lemma:sym-trafo-swap`, lines 2065--2085. -/
theorem equivalentUnderPhysicalMatrixSymmetry_swap_transpose_iff
    (U : MPOTensor (d * d) Da) (V : MPOTensor (d * d) Db) :
    EquivalentUnderPhysicalMatrixSymmetry .transpose (shiftPhysicalSwap d) U V ↔
      EquivalentUnderPhysicalMatrixSymmetry .transpose 1
        (U.ketLeftMul (shiftPhysicalSwap d)) (V.ketLeftMul (shiftPhysicalSwap d)) := by
  apply equivalent_of_strict_comparisons
  intro x k hk
  simp only [PhysicalSymmetryKind.withMatrix]
  rw [FiniteChainOperatorSymmetry.transposeWithPhysicalMatrix_block _ hk,
    FiniteChainOperatorSymmetry.transposeWithPhysicalMatrix_block _ hk,
    physicalIdMatrix_one, MPSTensor.blockKron_one,
    FiniteChainOperatorSymmetry.transposeWithPhysicalMatrix_one]
  exact strictlyEquivalentUnderSymmetry_ancillaSwapTranspose_iff U V x k

/-- Swap multiplication preserves the labelled-spin stabilized conjugation
comparison. This concerns the same full conjugation action on each enlarged
blocked chain.
Source: arXiv:1703.09188, Lemma `lemma:sym-trafo-swap`, lines 2065--2085. -/
theorem equivalentUnderPhysicalMatrixSymmetry_swap_conjugation_iff
    (U : MPOTensor (d * d) Da) (V : MPOTensor (d * d) Db) :
    EquivalentUnderPhysicalMatrixSymmetry .conjugation (shiftPhysicalSwap d) U V ↔
      EquivalentUnderPhysicalMatrixSymmetry .conjugation 1
        (U.ketLeftMul (shiftPhysicalSwap d)) (V.ketLeftMul (shiftPhysicalSwap d)) := by
  apply equivalent_of_strict_comparisons
  intro x k hk
  simp only [PhysicalSymmetryKind.withMatrix, conjugationSymmetry_block hk]
  exact strictlyEquivalentUnderSymmetry_ancillaSwapConjugation_iff U V x k

/-- Virtual dimensions of the three source examples, indexed in their
printed order. Source: arXiv:1703.09188, equation `threeMPU`, lines 2011--2022. -/
def shiftExampleFamilyBondDim (d : ℕ) (i : Fin 3) : ℕ :=
  if i = 0 then 1 else d * d

/-- The three actual source tensors as one finite dependent family.
Source: arXiv:1703.09188, equation `threeMPU`, lines 2011--2022. -/
noncomputable def shiftExampleFamily (d : ℕ) (i : Fin 3) :
    MPOTensor (d * d) (shiftExampleFamilyBondDim d i) := by
  fin_cases i
  · exact shiftExampleU₁ d
  · exact shiftExampleU₂ d
  · exact shiftExampleU₃ d

/-- The three actual swap-transformed source tensors in the same order.
Source: arXiv:1703.09188, equation `threeMPU2`, lines 2053--2063. -/
noncomputable def shiftExampleTildeFamily (d : ℕ) (i : Fin 3) :
    MPOTensor (d * d) (shiftExampleFamilyBondDim d i) := by
  fin_cases i
  · exact shiftExampleTildeU₁ d
  · exact shiftExampleTildeU₂ d
  · exact shiftExampleTildeU₃ d

/-- For every pair of the actual three examples, labelled-spin equivalence
under swap-combined adjunction is ordinary adjunction equivalence of the
corresponding actual transformed examples.
Source: arXiv:1703.09188, Lemma `lemma:sym-trafo-swap`, lines 2065--2085. -/
theorem labelledShiftExamples_swap_dagger_iff (d : ℕ) (i j : Fin 3) :
    EquivalentUnderPhysicalMatrixSymmetry .dagger (shiftPhysicalSwap d)
      (shiftExampleFamily d i) (shiftExampleFamily d j) ↔
      EquivalentUnderPhysicalMatrixSymmetry .dagger 1
        (shiftExampleTildeFamily d i) (shiftExampleTildeFamily d j) := by
  fin_cases i <;> fin_cases j <;>
    exact equivalentUnderPhysicalMatrixSymmetry_swap_dagger_iff _ _

/-- The labelled-spin transposition comparison for every pair of the actual
three source examples and their printed transformed examples.
Source: arXiv:1703.09188, Lemma `lemma:sym-trafo-swap`, lines 2065--2085. -/
theorem labelledShiftExamples_swap_transpose_iff (d : ℕ) (i j : Fin 3) :
    EquivalentUnderPhysicalMatrixSymmetry .transpose (shiftPhysicalSwap d)
      (shiftExampleFamily d i) (shiftExampleFamily d j) ↔
      EquivalentUnderPhysicalMatrixSymmetry .transpose 1
        (shiftExampleTildeFamily d i) (shiftExampleTildeFamily d j) := by
  fin_cases i <;> fin_cases j <;>
    exact equivalentUnderPhysicalMatrixSymmetry_swap_transpose_iff _ _

/-- The labelled-spin conjugation comparison for every pair of the actual
three source examples and their printed transformed examples.
Source: arXiv:1703.09188, Lemma `lemma:sym-trafo-swap`, lines 2065--2085. -/
theorem labelledShiftExamples_swap_conjugation_iff (d : ℕ) (i j : Fin 3) :
    EquivalentUnderPhysicalMatrixSymmetry .conjugation (shiftPhysicalSwap d)
      (shiftExampleFamily d i) (shiftExampleFamily d j) ↔
      EquivalentUnderPhysicalMatrixSymmetry .conjugation 1
        (shiftExampleTildeFamily d i) (shiftExampleTildeFamily d j) := by
  fin_cases i <;> fin_cases j <;>
    exact equivalentUnderPhysicalMatrixSymmetry_swap_conjugation_iff _ _

end MPOTensor
