/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Examples.SwapSymmetryTransport
import TNLean.MPS.MPU.PhysicalAncillaLeftMul

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
positive ancillas and blocking, not `EquivalentUnderSymmetry`. The source
does not determine an enlarged action from its original-dimension action.
Its unrestricted comparison and the general equivalence convention remain
open; see `docs/paper-gaps/mpu_symmetry_ancilla_transport.tex`.

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

private noncomputable def blockedAncillaSwap (d x k : ℕ) :
    Matrix (Fin (MPSTensor.blockPhysDim (d * d * x) k))
      (Fin (MPSTensor.blockPhysDim (d * d * x) k)) ℂ :=
  MPSTensor.blockKron k (ancillaSwapMatrix d x)

private theorem blockedAncillaSwap_mul_self (d x k : ℕ) :
    blockedAncillaSwap d x k * blockedAncillaSwap d x k = 1 := by
  simp only [blockedAncillaSwap, ← MPSTensor.blockKron_mul, ancillaSwapMatrix,
    physicalIdMatrix_mul, shiftPhysicalSwap_mul_self, physicalIdMatrix_one,
    MPSTensor.blockKron_one]

private theorem blockedAncillaSwap_conjTranspose (d x k : ℕ) :
    (blockedAncillaSwap d x k)ᴴ = blockedAncillaSwap d x k := by
  simp only [blockedAncillaSwap, MPSTensor.blockKron_conjTranspose,
    ancillaSwapMatrix, physicalIdMatrix_conjTranspose, shiftPhysicalSwap,
    Matrix.conjTranspose_permMatrix, Equiv.Perm.inv_def, bondPairSwapEquiv_symm]

private theorem blockedAncillaSwap_mem_unitaryGroup (d x k : ℕ) :
    blockedAncillaSwap d x k ∈
      Matrix.unitaryGroup (Fin (MPSTensor.blockPhysDim (d * d * x) k)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    blockedAncillaSwap_conjTranspose, blockedAncillaSwap_mul_self]

private theorem blockedAncillaSwap_transpose (d x k : ℕ) :
    (blockedAncillaSwap d x k)ᵀ = blockedAncillaSwap d x k := by
  have hQ : (ancillaSwapMatrix d x)ᵀ = ancillaSwapMatrix d x := by
    simp only [ancillaSwapMatrix, physicalIdMatrix_transpose, shiftPhysicalSwap,
      Matrix.transpose_permMatrix, Equiv.Perm.inv_def, bondPairSwapEquiv_symm]
  ext i j
  change (∏ n, ancillaSwapMatrix d x
    (MPSTensor.decodeBlock (d * d * x) k j n)
    (MPSTensor.decodeBlock (d * d * x) k i n)) = _
  exact Finset.prod_congr rfl fun n _ => congrFun (congrFun hQ _) _

private theorem blockedAncillaSwap_map_star (d x k : ℕ) :
    (blockedAncillaSwap d x k).map (starRingEnd ℂ) = blockedAncillaSwap d x k := by
  have hQ : (ancillaSwapMatrix d x).map (starRingEnd ℂ) = ancillaSwapMatrix d x := by
    apply physicalIdMatrix_map_star
    ext i j
    simp [shiftPhysicalSwap, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  ext i j
  simp only [Matrix.map_apply, blockedAncillaSwap, MPSTensor.blockKron, map_prod]
  exact Finset.prod_congr rfl fun n _ => congrFun (congrFun hQ _) _

private theorem chainBlockedAncillaSwap_mul_self (d x k N : ℕ) :
    sitewisePhysicalMatrix (blockedAncillaSwap d x k) N *
      sitewisePhysicalMatrix (blockedAncillaSwap d x k) N = 1 := by
  rw [sitewisePhysicalMatrix_mul, blockedAncillaSwap_mul_self,
    sitewisePhysicalMatrix_one]

private theorem chainBlockedAncillaSwap_transpose (d x k N : ℕ) :
    (sitewisePhysicalMatrix (blockedAncillaSwap d x k) N)ᵀ =
      sitewisePhysicalMatrix (blockedAncillaSwap d x k) N := by
  ext σ τ
  change (∏ n, blockedAncillaSwap d x k (τ n) (σ n)) = _
  exact Finset.prod_congr rfl fun n _ =>
    congrFun (congrFun (blockedAncillaSwap_transpose d x k) _) _

private theorem chainBlockedAncillaSwap_map_star (d x k N : ℕ) :
    (sitewisePhysicalMatrix (blockedAncillaSwap d x k) N).map (starRingEnd ℂ) =
      sitewisePhysicalMatrix (blockedAncillaSwap d x k) N := by
  ext σ τ
  simp only [Matrix.map_apply, sitewisePhysicalMatrix, map_prod]
  exact Finset.prod_congr rfl fun n _ =>
    congrFun (congrFun (blockedAncillaSwap_map_star d x k) _) _

/-- Swap-combined adjunction on the full ancilla-enlarged operator space
after blocking. Source: arXiv:1703.09188, `SSymmetries-dagger`, with the
specified extension \(Q_x=\mathbb S\otimes I_x\). -/
noncomputable def ancillaSwapDaggerSymmetry (d x k : ℕ) :
    FiniteChainOperatorSymmetry (MPSTensor.blockPhysDim (d * d * x) k) where
  applicable := {N | 0 < N}
  action := fun {N} X ↦
    sitewisePhysicalMatrix (blockedAncillaSwap d x k) N * Xᴴ *
      sitewisePhysicalMatrix (blockedAncillaSwap d x k) N

/-- Swap-combined transposition on the full ancilla-enlarged operator space
after blocking. Source: arXiv:1703.09188, `SSymmetries-transpose`, with the
specified extension \(Q_x=\mathbb S\otimes I_x\). -/
noncomputable def ancillaSwapTransposeSymmetry (d x k : ℕ) :
    FiniteChainOperatorSymmetry (MPSTensor.blockPhysDim (d * d * x) k) where
  applicable := {N | 0 < N}
  action := fun {N} X ↦
    sitewisePhysicalMatrix (blockedAncillaSwap d x k) N * Xᵀ *
      sitewisePhysicalMatrix (blockedAncillaSwap d x k) N

private theorem ancillaSwapDagger_invariance_iff (d x k : ℕ) {E : ℕ}
    (W : MPOTensor (MPSTensor.blockPhysDim (d * d * x) k) E) :
    IsInvariantUnderSymmetry (ancillaSwapDaggerSymmetry d x k) W ↔
      IsInvariantUnderSymmetry (daggerSymmetry _)
        (W.ketLeftMul (blockedAncillaSwap d x k)) := by
  apply isInvariantUnderSymmetry_iff_of_pointwise
    (ancillaSwapDaggerSymmetry d x k) (daggerSymmetry _) _ _ rfl
  intro N
  change _ ↔ (mpo (W.ketLeftMul (blockedAncillaSwap d x k)) N)ᴴ = _
  rw [mpo_ketLeftMul]
  apply Matrix.swapCombined_fixed_iff_leftMul _ _
    (chainBlockedAncillaSwap_mul_self d x k N)
  rw [Matrix.conjTranspose_mul, sitewisePhysicalMatrix_conjTranspose,
    blockedAncillaSwap_conjTranspose]

private theorem ancillaSwapTranspose_invariance_iff (d x k : ℕ) {E : ℕ}
    (W : MPOTensor (MPSTensor.blockPhysDim (d * d * x) k) E) :
    IsInvariantUnderSymmetry (ancillaSwapTransposeSymmetry d x k) W ↔
      IsInvariantUnderSymmetry (transposeSymmetry _)
        (W.ketLeftMul (blockedAncillaSwap d x k)) := by
  apply isInvariantUnderSymmetry_iff_of_pointwise
    (ancillaSwapTransposeSymmetry d x k) (transposeSymmetry _) _ _ rfl
  intro N
  change _ ↔ (mpo (W.ketLeftMul (blockedAncillaSwap d x k)) N)ᵀ = _
  rw [mpo_ketLeftMul]
  apply Matrix.swapCombined_fixed_iff_leftMul _ _
    (chainBlockedAncillaSwap_mul_self d x k N)
  rw [Matrix.transpose_mul, chainBlockedAncillaSwap_transpose]

private theorem ancillaSwapConjugation_invariance_iff (d x k : ℕ) {E : ℕ}
    (W : MPOTensor (MPSTensor.blockPhysDim (d * d * x) k) E) :
    IsInvariantUnderSymmetry (conjugationSymmetry _) W ↔
      IsInvariantUnderSymmetry (conjugationSymmetry _)
        (W.ketLeftMul (blockedAncillaSwap d x k)) := by
  apply isInvariantUnderSymmetry_iff_of_pointwise _ _ _ _ rfl
  intro N
  change (mpo W N).map (starRingEnd ℂ) = _ ↔
    (mpo (W.ketLeftMul (blockedAncillaSwap d x k)) N).map (starRingEnd ℂ) = _
  rw [mpo_ketLeftMul, Matrix.map_mul, chainBlockedAncillaSwap_map_star]
  constructor
  · exact congrArg (fun X ↦ sitewisePhysicalMatrix (blockedAncillaSwap d x k) N * X)
  · intro h
    simpa only [← Matrix.mul_assoc, chainBlockedAncillaSwap_mul_self,
      Matrix.one_mul] using
      congrArg (fun X ↦ sitewisePhysicalMatrix (blockedAncillaSwap d x k) N * X) h

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
  simpa only [blockedAncillaSwap, ← blockTensor_ketLeftMul, ancillaSwapMatrix,
    ketLeftMul_tensorPhysicalId] using
    strictlyEquivalentUnderSymmetry_iff_ketLeftMul _ _ (blockedAncillaSwap d x k)
      (blockedAncillaSwap_mem_unitaryGroup d x k) (blockedAncillaSwap_mul_self d x k)
      (ancillaSwapDagger_invariance_iff d x k)
      (blockTensor (tensorPhysicalId U x) k) (blockTensor (tensorPhysicalId V x) k)

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
  simpa only [blockedAncillaSwap, ← blockTensor_ketLeftMul, ancillaSwapMatrix,
    ketLeftMul_tensorPhysicalId] using
    strictlyEquivalentUnderSymmetry_iff_ketLeftMul _ _ (blockedAncillaSwap d x k)
      (blockedAncillaSwap_mem_unitaryGroup d x k) (blockedAncillaSwap_mul_self d x k)
      (ancillaSwapTranspose_invariance_iff d x k)
      (blockTensor (tensorPhysicalId U x) k) (blockTensor (tensorPhysicalId V x) k)

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
  simpa only [blockedAncillaSwap, ← blockTensor_ketLeftMul, ancillaSwapMatrix,
    ketLeftMul_tensorPhysicalId] using
    strictlyEquivalentUnderSymmetry_iff_ketLeftMul _ _ (blockedAncillaSwap d x k)
      (blockedAncillaSwap_mem_unitaryGroup d x k) (blockedAncillaSwap_mul_self d x k)
      (ancillaSwapConjugation_invariance_iff d x k)
      (blockTensor (tensorPhysicalId U x) k) (blockTensor (tensorPhysicalId V x) k)

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
