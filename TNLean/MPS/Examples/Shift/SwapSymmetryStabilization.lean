/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.Shift.SwapSymmetryTransport
import TNLean.MPS.MPU.Equivalence.PhysicalMatrixSymmetryTransport

/-!
# Swap comparisons with an identity ancilla

For a distinguished site \((\mathbb C^d\otimes\mathbb C^d)\otimes\mathbb C^x\),
use the full physical matrix \(Q_x=\mathbb S\otimes I_x\). After blocking
\(k\) sites, use \(Q_x^{\otimes k}\). The two swap-combined actions are
defined on every operator in this enlarged and blocked space, so the path
comparisons allow intermediate tensors outside the identity-ancilla image.

**Scope restriction (specified ancilla action):** the comparisons use the
explicit extension that fixes the ancilla and exchanges the two original
physical species. They are explicit existential statements about common
positive ancillas and blocking, not `EquivalentUnderSymmetry`. This is the
natural labelled-spin reading of the source's later ancilla construction.
An abstract original-dimension action without the distinguished physical
data does not determine its enlarged action. The general equivalence
convention remains open; see `docs/paper-gaps/mpu_symmetry_ancilla_transport.tex`.

**Local fix (one-sided swap):** the transformation is the output action in
`threeMPU2`, not the two-sided expression in the printed proof paragraph.
See `docs/paper-gaps/mpu_swap_symmetry_one_sided.tex`.

Source: arXiv:1703.09188, `def:equivalent-symmetry`, lines 1356--1366,
and `lemma:sym-trafo-swap`, lines 2065--2085.
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d Da Db : ℕ}

/-- The physical swap on the original species, with the identity on the
ancilla. The full matrix acts on arbitrary enlarged operators.
Source: arXiv:1703.09188, `SSymmetries` and `def:equivalent-symmetry`. -/
noncomputable def ancillaSwapMatrix (d x : ℕ) :
    Matrix (Fin (d * d * x)) (Fin (d * d * x)) ℂ :=
  physicalIdMatrix (shiftPhysicalSwap d) x

private theorem ancillaSwapMatrix_unitary (d x : ℕ) :
    ancillaSwapMatrix d x ∈ Matrix.unitaryGroup (Fin (d * d * x)) ℂ := by
  exact physicalIdMatrix_mem_unitaryGroup _ x (shiftPhysicalSwap_mem_unitaryGroup d)

private theorem ancillaSwapMatrix_involution (d x : ℕ) :
    ancillaSwapMatrix d x * ancillaSwapMatrix d x = 1 := by
  simp only [ancillaSwapMatrix, physicalIdMatrix_mul, shiftPhysicalSwap_mul_self,
    physicalIdMatrix_one]

private theorem ancillaSwapMatrix_conjTranspose (d x : ℕ) :
    (ancillaSwapMatrix d x)ᴴ = ancillaSwapMatrix d x := by
  simp only [ancillaSwapMatrix, physicalIdMatrix_conjTranspose, shiftPhysicalSwap,
    Matrix.conjTranspose_permMatrix, Equiv.Perm.inv_def, bondPairSwapEquiv_symm]

private theorem ancillaSwapMatrix_transpose (d x : ℕ) :
    (ancillaSwapMatrix d x)ᵀ = ancillaSwapMatrix d x := by
  simp only [ancillaSwapMatrix, physicalIdMatrix_transpose, shiftPhysicalSwap,
    Matrix.transpose_permMatrix, Equiv.Perm.inv_def, bondPairSwapEquiv_symm]

private theorem ancillaSwapMatrix_map_star (d x : ℕ) :
    (ancillaSwapMatrix d x).map (starRingEnd ℂ) = ancillaSwapMatrix d x := by
  apply physicalIdMatrix_map_star
  ext i j
  simp [shiftPhysicalSwap, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]

/-- Canonical blocking of swap-combined adjunction, retaining applicability
on all positive blocked chain lengths even when the blocking length is zero.
Source: arXiv:1703.09188, `SSymmetries-dagger`, with the specified extension
\(Q_x=\mathbb S\otimes I_x\). -/
noncomputable def ancillaSwapDaggerSymmetry (d x k : ℕ) :
    FiniteChainOperatorSymmetry (Kraus.blockPhysDim (d * d * x) k) :=
  .blockedDaggerWithPhysicalMatrix (ancillaSwapMatrix d x) k

/-- Canonical blocking of swap-combined transposition, with the same
positive-chain convention at blocking length zero as the explicit matrix.
Source: arXiv:1703.09188, `SSymmetries-transpose`, with the specified extension
\(Q_x=\mathbb S\otimes I_x\). -/
noncomputable def ancillaSwapTransposeSymmetry (d x k : ℕ) :
    FiniteChainOperatorSymmetry (Kraus.blockPhysDim (d * d * x) k) :=
  .blockedTransposeWithPhysicalMatrix (ancillaSwapMatrix d x) k

/-- For each fixed common ancilla and blocking length, the specified
swap-combined adjunction comparison is the ordinary adjunction comparison
of the transformed endpoints, with arbitrary virtual dimensions.
Source: arXiv:1703.09188, Lemma `lemma:sym-trafo-swap`, lines 2065--2085. -/
theorem strictlyEquivalentUnderSymmetry_ancillaSwapDagger_iff
    (U : MPOTensor (d * d) Da) (V : MPOTensor (d * d) Db) (x k : ℕ) :
    StrictlyEquivalentUnderSymmetry (ancillaSwapDaggerSymmetry d x k)
      (blockTensor (tensorPhysicalId U x) k) (blockTensor (tensorPhysicalId V x) k) rfl ↔
      StrictlyEquivalentUnderSymmetry (daggerSymmetry _)
        (blockTensor (tensorPhysicalId (U.ketLeftMul (shiftPhysicalSwap d)) x) k)
        (blockTensor (tensorPhysicalId (V.ketLeftMul (shiftPhysicalSwap d)) x) k) rfl := by
  simpa only [ancillaSwapDaggerSymmetry, ancillaSwapMatrix, ketLeftMul_tensorPhysicalId] using
    strictlyEquivalentUnderSymmetry_blockedDaggerWithPhysicalMatrix_iff
      (ancillaSwapMatrix d x) (ancillaSwapMatrix_unitary d x)
      (ancillaSwapMatrix_involution d x) (ancillaSwapMatrix_conjTranspose d x)
      (tensorPhysicalId U x) (tensorPhysicalId V x) k

/-- The same common ancilla and blocking length identify swap-combined
transposition with ordinary transposition of the transformed endpoints.
Source: arXiv:1703.09188, Lemma `lemma:sym-trafo-swap`, lines 2065--2085. -/
theorem strictlyEquivalentUnderSymmetry_ancillaSwapTranspose_iff
    (U : MPOTensor (d * d) Da) (V : MPOTensor (d * d) Db) (x k : ℕ) :
    StrictlyEquivalentUnderSymmetry (ancillaSwapTransposeSymmetry d x k)
      (blockTensor (tensorPhysicalId U x) k) (blockTensor (tensorPhysicalId V x) k) rfl ↔
      StrictlyEquivalentUnderSymmetry (transposeSymmetry _)
        (blockTensor (tensorPhysicalId (U.ketLeftMul (shiftPhysicalSwap d)) x) k)
        (blockTensor (tensorPhysicalId (V.ketLeftMul (shiftPhysicalSwap d)) x) k) rfl := by
  simpa only [ancillaSwapTransposeSymmetry, ancillaSwapMatrix, ketLeftMul_tensorPhysicalId] using
    strictlyEquivalentUnderSymmetry_blockedTransposeWithPhysicalMatrix_iff
      (ancillaSwapMatrix d x) (ancillaSwapMatrix_unitary d x)
      (ancillaSwapMatrix_involution d x) (ancillaSwapMatrix_transpose d x)
      (tensorPhysicalId U x) (tensorPhysicalId V x) k

/-- The same common ancilla and blocking length preserve the conjugation
comparison of the transformed endpoints.
Source: arXiv:1703.09188, Lemma `lemma:sym-trafo-swap`, lines 2065--2085. -/
theorem strictlyEquivalentUnderSymmetry_ancillaSwapConjugation_iff
    (U : MPOTensor (d * d) Da) (V : MPOTensor (d * d) Db) (x k : ℕ) :
    StrictlyEquivalentUnderSymmetry (conjugationSymmetry _)
      (blockTensor (tensorPhysicalId U x) k) (blockTensor (tensorPhysicalId V x) k) rfl ↔
      StrictlyEquivalentUnderSymmetry (conjugationSymmetry _)
        (blockTensor (tensorPhysicalId (U.ketLeftMul (shiftPhysicalSwap d)) x) k)
        (blockTensor (tensorPhysicalId (V.ketLeftMul (shiftPhysicalSwap d)) x) k) rfl := by
  simpa only [ancillaSwapMatrix, ketLeftMul_tensorPhysicalId] using
    strictlyEquivalentUnderSymmetry_blockedConjugationWithPhysicalMatrix_iff
      (ancillaSwapMatrix d x) (ancillaSwapMatrix_unitary d x)
      (ancillaSwapMatrix_involution d x) (ancillaSwapMatrix_map_star d x)
      (tensorPhysicalId U x) (tensorPhysicalId V x) k

/-- Common positive identity-ancilla stabilization and blocking preserve the
specified swap/adjunction comparison, using the same witnesses both ways.
Source: arXiv:1703.09188, `def:equivalent-symmetry` and `lemma:sym-trafo-swap`. -/
theorem exists_strictlyEquivalentUnderSymmetry_ancillaSwapDagger_iff
    (U : MPOTensor (d * d) Da) (V : MPOTensor (d * d) Db) :
    (∃ x > 0, ∃ k > 0, StrictlyEquivalentUnderSymmetry (ancillaSwapDaggerSymmetry d x k)
      (blockTensor (tensorPhysicalId U x) k) (blockTensor (tensorPhysicalId V x) k) rfl) ↔
      (∃ x > 0, ∃ k > 0, StrictlyEquivalentUnderSymmetry (daggerSymmetry _)
        (blockTensor (tensorPhysicalId (U.ketLeftMul (shiftPhysicalSwap d)) x) k)
        (blockTensor (tensorPhysicalId (V.ketLeftMul (shiftPhysicalSwap d)) x) k) rfl) := by
  exact exists_congr fun x => and_congr_right fun _ =>
    exists_congr fun k => and_congr_right fun _ =>
      strictlyEquivalentUnderSymmetry_ancillaSwapDagger_iff U V x k

/-- Common positive identity-ancilla stabilization and blocking preserve the
specified swap/transposition comparison, using the same witnesses both ways.
Source: arXiv:1703.09188, `def:equivalent-symmetry` and `lemma:sym-trafo-swap`. -/
theorem exists_strictlyEquivalentUnderSymmetry_ancillaSwapTranspose_iff
    (U : MPOTensor (d * d) Da) (V : MPOTensor (d * d) Db) :
    (∃ x > 0, ∃ k > 0, StrictlyEquivalentUnderSymmetry (ancillaSwapTransposeSymmetry d x k)
      (blockTensor (tensorPhysicalId U x) k) (blockTensor (tensorPhysicalId V x) k) rfl) ↔
      (∃ x > 0, ∃ k > 0, StrictlyEquivalentUnderSymmetry (transposeSymmetry _)
        (blockTensor (tensorPhysicalId (U.ketLeftMul (shiftPhysicalSwap d)) x) k)
        (blockTensor (tensorPhysicalId (V.ketLeftMul (shiftPhysicalSwap d)) x) k) rfl) := by
  exact exists_congr fun x => and_congr_right fun _ =>
    exists_congr fun k => and_congr_right fun _ =>
      strictlyEquivalentUnderSymmetry_ancillaSwapTranspose_iff U V x k

/-- Common positive identity-ancilla stabilization and blocking preserve
conjugation comparison, using the same witnesses both ways.
Source: arXiv:1703.09188, `def:equivalent-symmetry` and `lemma:sym-trafo-swap`. -/
theorem exists_strictlyEquivalentUnderSymmetry_ancillaSwapConjugation_iff
    (U : MPOTensor (d * d) Da) (V : MPOTensor (d * d) Db) :
    (∃ x > 0, ∃ k > 0, StrictlyEquivalentUnderSymmetry (conjugationSymmetry _)
      (blockTensor (tensorPhysicalId U x) k) (blockTensor (tensorPhysicalId V x) k) rfl) ↔
      (∃ x > 0, ∃ k > 0, StrictlyEquivalentUnderSymmetry (conjugationSymmetry _)
        (blockTensor (tensorPhysicalId (U.ketLeftMul (shiftPhysicalSwap d)) x) k)
        (blockTensor (tensorPhysicalId (V.ketLeftMul (shiftPhysicalSwap d)) x) k) rfl) := by
  exact exists_congr fun x => and_congr_right fun _ =>
    exists_congr fun k => and_congr_right fun _ =>
      strictlyEquivalentUnderSymmetry_ancillaSwapConjugation_iff U V x k

end MPOTensor
