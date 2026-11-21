/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixInvolutionConjugation
import TNLean.MPS.MPU.PhysicalMatrixBlocking

/-!
# Path transport by a retained physical involution

The path comparison uses an arbitrary specified unitary involution, rather
than a particular species swap. Blocking preserves its matrix properties,
and the same output action identifies the full invariant operator spaces.
The blocked sandwich actions test every positive blocked chain length,
including when the blocking length is zero. Thus the zero-length convention
of the explicit blocked local matrix is preserved.

**Scope restriction (specified physical matrix):** these are strict path
comparisons for an explicit matrix and its canonical blocked powers, not a
claim about a globally dimension-indexed symmetry family. Ancillas may be
included in that matrix; no restriction on intermediate paths is imposed.
See `docs/paper-gaps/mpu_symmetry_ancilla_transport.tex`.

Source: arXiv:1703.09188, `SSymmetries`, lines 1301--1322, and
`lemma:sym-trafo-swap`, lines 2065--2085.
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d Da Db : ℕ}

private theorem blockKron_unitary (Q : Matrix (Fin d) (Fin d) ℂ)
    (hQ : Q ∈ Matrix.unitaryGroup (Fin d) ℂ) (k : ℕ) :
    MPSTensor.blockKron k Q ∈
      Matrix.unitaryGroup (Fin (Kraus.blockPhysDim d k)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  exact MPSTensor.blockKron_mul_conjTranspose k Q
    (by simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hQ)

private theorem blockKron_involution (Q : Matrix (Fin d) (Fin d) ℂ)
    (hQQ : Q * Q = 1) (k : ℕ) :
    MPSTensor.blockKron k Q * MPSTensor.blockKron k Q = 1 := by
  rw [← MPSTensor.blockKron_mul, hQQ, MPSTensor.blockKron_one]

private theorem blockKron_transpose (Q : Matrix (Fin d) (Fin d) ℂ) (k : ℕ) :
    (MPSTensor.blockKron k Q)ᵀ = MPSTensor.blockKron k Qᵀ := rfl

private theorem blockKron_map_star (Q : Matrix (Fin d) (Fin d) ℂ) (k : ℕ) :
    (MPSTensor.blockKron k Q).map (starRingEnd ℂ) =
      MPSTensor.blockKron k (Q.map (starRingEnd ℂ)) := by
  ext i j
  simp only [Matrix.map_apply, MPSTensor.blockKron, map_prod]

private theorem sitewise_transpose (Q : Matrix (Fin d) (Fin d) ℂ) (N : ℕ) :
    (Matrix.tensorPower N Q)ᵀ = Matrix.tensorPower N Qᵀ := rfl

private theorem sitewise_map_star (Q : Matrix (Fin d) (Fin d) ℂ) (N : ℕ) :
    (Matrix.tensorPower N Q).map (starRingEnd ℂ) =
      Matrix.tensorPower N (Q.map (starRingEnd ℂ)) := by
  ext σ τ
  simp only [Matrix.map_apply, Matrix.tensorPower_apply, map_prod]

private theorem dagger_invariance_iff (Q : Matrix (Fin d) (Fin d) ℂ)
    (hQQ : Q * Q = 1) (hH : Qᴴ = Q) {E : ℕ} (W : MPOTensor d E) :
    IsInvariantUnderSymmetry (.daggerWithPhysicalMatrix Q) W ↔
      IsInvariantUnderSymmetry (daggerSymmetry d) (W.ketLeftMul Q) := by
  apply isInvariantUnderSymmetry_iff_of_pointwise
    (.daggerWithPhysicalMatrix Q) (daggerSymmetry d) _ _ rfl
  intro N
  change _ ↔ (mpo (W.ketLeftMul Q) N)ᴴ = _
  rw [mpo_ketLeftMul]
  apply Matrix.swapCombined_fixed_iff_leftMul _ _
    (by rw [Matrix.tensorPower_mul, hQQ, Matrix.tensorPower_one])
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_tensorPower, hH]

private theorem transpose_invariance_iff (Q : Matrix (Fin d) (Fin d) ℂ)
    (hQQ : Q * Q = 1) (hT : Qᵀ = Q) {E : ℕ} (W : MPOTensor d E) :
    IsInvariantUnderSymmetry (.transposeWithPhysicalMatrix Q) W ↔
      IsInvariantUnderSymmetry (transposeSymmetry d) (W.ketLeftMul Q) := by
  apply isInvariantUnderSymmetry_iff_of_pointwise
    (.transposeWithPhysicalMatrix Q) (transposeSymmetry d) _ _ rfl
  intro N
  change _ ↔ (mpo (W.ketLeftMul Q) N)ᵀ = _
  rw [mpo_ketLeftMul]
  apply Matrix.swapCombined_fixed_iff_leftMul _ _
    (by rw [Matrix.tensorPower_mul, hQQ, Matrix.tensorPower_one])
  rw [Matrix.transpose_mul, sitewise_transpose, hT]

private theorem conjugation_invariance_iff (Q : Matrix (Fin d) (Fin d) ℂ)
    (hQQ : Q * Q = 1) (hR : Q.map (starRingEnd ℂ) = Q)
    {E : ℕ} (W : MPOTensor d E) :
    IsInvariantUnderSymmetry (conjugationSymmetry d) W ↔
      IsInvariantUnderSymmetry (conjugationSymmetry d) (W.ketLeftMul Q) := by
  apply isInvariantUnderSymmetry_iff_of_pointwise _ _ _ _ rfl
  intro N
  change (mpo W N).map (starRingEnd ℂ) = _ ↔
    (mpo (W.ketLeftMul Q) N).map (starRingEnd ℂ) = _
  rw [mpo_ketLeftMul, Matrix.map_mul, sitewise_map_star, hR]
  constructor
  · exact congrArg (fun X ↦ Matrix.tensorPower N Q * X)
  · intro h
    have hQN : Matrix.tensorPower N Q * Matrix.tensorPower N Q = 1 := by
      rw [Matrix.tensorPower_mul, hQQ, Matrix.tensorPower_one]
    simpa only [← Matrix.mul_assoc, hQN, Matrix.one_mul] using
      congrArg (fun X ↦ Matrix.tensorPower N Q * X) h

/-- An arbitrary self-adjoint unitary involution identifies blocked sandwich
adjunction with ordinary adjunction of the transformed tensors. Every natural
blocking length is allowed, and the endpoint virtual dimensions may differ.
Source: arXiv:1703.09188, `SSymmetries-dagger` and `lemma:sym-trafo-swap`. -/
theorem strictlyEquivalentUnderSymmetry_blockedDaggerWithPhysicalMatrix_iff
    (Q : Matrix (Fin d) (Fin d) ℂ) (hQ : Q ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hQQ : Q * Q = 1) (hH : Qᴴ = Q)
    (U : MPOTensor d Da) (V : MPOTensor d Db) (k : ℕ) :
    StrictlyEquivalentUnderSymmetry (.blockedDaggerWithPhysicalMatrix Q k)
      (blockTensor U k) (blockTensor V k) rfl ↔
      StrictlyEquivalentUnderSymmetry (daggerSymmetry _)
        (blockTensor (U.ketLeftMul Q) k) (blockTensor (V.ketLeftMul Q) k) rfl := by
  rw [FiniteChainOperatorSymmetry.blockedDaggerWithPhysicalMatrix_eq]
  simpa only [← blockTensor_ketLeftMul] using
    strictlyEquivalentUnderSymmetry_iff_ketLeftMul _ _ (MPSTensor.blockKron k Q)
      (blockKron_unitary Q hQ k) (blockKron_involution Q hQQ k)
      (dagger_invariance_iff _ (blockKron_involution Q hQQ k)
        (by rw [MPSTensor.blockKron_conjTranspose, hH])) (blockTensor U k) (blockTensor V k)

/-- A symmetric unitary involution identifies blocked sandwich transposition
with ordinary transposition of the transformed tensors, including length zero.
Source: arXiv:1703.09188, `SSymmetries-transpose` and `lemma:sym-trafo-swap`. -/
theorem strictlyEquivalentUnderSymmetry_blockedTransposeWithPhysicalMatrix_iff
    (Q : Matrix (Fin d) (Fin d) ℂ) (hQ : Q ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hQQ : Q * Q = 1) (hT : Qᵀ = Q)
    (U : MPOTensor d Da) (V : MPOTensor d Db) (k : ℕ) :
    StrictlyEquivalentUnderSymmetry (.blockedTransposeWithPhysicalMatrix Q k)
      (blockTensor U k) (blockTensor V k) rfl ↔
      StrictlyEquivalentUnderSymmetry (transposeSymmetry _)
        (blockTensor (U.ketLeftMul Q) k) (blockTensor (V.ketLeftMul Q) k) rfl := by
  rw [FiniteChainOperatorSymmetry.blockedTransposeWithPhysicalMatrix_eq]
  simpa only [← blockTensor_ketLeftMul] using
    strictlyEquivalentUnderSymmetry_iff_ketLeftMul _ _ (MPSTensor.blockKron k Q)
      (blockKron_unitary Q hQ k) (blockKron_involution Q hQQ k)
      (transpose_invariance_iff _ (blockKron_involution Q hQQ k)
        (by rw [blockKron_transpose, hT])) (blockTensor U k) (blockTensor V k)

/-- A real unitary involution preserves the conjugation path comparison
through every natural blocking length and arbitrary endpoint virtual dimensions.
Source: arXiv:1703.09188, `SSymmetries` and `lemma:sym-trafo-swap`. -/
theorem strictlyEquivalentUnderSymmetry_blockedConjugationWithPhysicalMatrix_iff
    (Q : Matrix (Fin d) (Fin d) ℂ) (hQ : Q ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hQQ : Q * Q = 1) (hR : Q.map (starRingEnd ℂ) = Q)
    (U : MPOTensor d Da) (V : MPOTensor d Db) (k : ℕ) :
    StrictlyEquivalentUnderSymmetry (conjugationSymmetry _)
      (blockTensor U k) (blockTensor V k) rfl ↔
      StrictlyEquivalentUnderSymmetry (conjugationSymmetry _)
        (blockTensor (U.ketLeftMul Q) k) (blockTensor (V.ketLeftMul Q) k) rfl := by
  simpa only [← blockTensor_ketLeftMul] using
    strictlyEquivalentUnderSymmetry_iff_ketLeftMul _ _ (MPSTensor.blockKron k Q)
      (blockKron_unitary Q hQ k) (blockKron_involution Q hQQ k)
      (conjugation_invariance_iff _ (blockKron_involution Q hQQ k)
        (by rw [blockKron_map_star, hR])) (blockTensor U k) (blockTensor V k)

end MPOTensor
