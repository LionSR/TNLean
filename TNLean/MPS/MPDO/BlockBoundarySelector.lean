/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.Boundary
import TNLean.MPS.SharedInfra.BlockAssembly

/-!
# Boundary selectors for finite direct sums of MPO tensors

Each summand of an unweighted block-diagonal MPO tensor has a virtual boundary
projection that commutes with every tensor letter. Closing the assembled tensor
with that projection gives precisely the periodic operator of the selected
summand, at every chain length.
-/

open scoped Matrix BigOperators

noncomputable section

namespace MPOTensor

variable {d r : ℕ} {dim : Fin r → ℕ}

/-- The unweighted direct sum of a finite family of MPO tensors, with the
dependent virtual direct sum flattened to a single finite index. -/
def blockSum (O : (a : Fin r) → MPOTensor d (dim a)) :
    MPOTensor d (∑ a : Fin r, dim a) :=
  fun i j ↦ Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv
    (Matrix.blockDiagonal' fun a ↦ O a i j)

/-- The doubled-index MPS tensor of an MPO direct sum is the unweighted
assembly of its doubled-index component tensors. -/
@[simp] theorem blockSum_toMPSTensor (O : (a : Fin r) → MPOTensor d (dim a)) :
    (blockSum O).toMPSTensor =
      MPSTensor.toTensorFromBlocks (fun _ ↦ 1) (fun a ↦ (O a).toMPSTensor) := by
  funext ij
  simp only [toMPSTensor, blockSum, MPSTensor.toTensorFromBlocks, one_smul]

/-- Word evaluation of a finite MPO direct sum is the flattened block
diagonal of the component word evaluations. -/
theorem evalWord_blockSum (O : (a : Fin r) → MPOTensor d (dim a))
    {N : ℕ} (σ τ : Fin N → Fin d) :
    evalWord (blockSum O) (List.ofFn σ) (List.ofFn τ) =
      Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv
        (Matrix.blockDiagonal' fun a ↦ evalWord (O a) (List.ofFn σ) (List.ofFn τ)) := by
  rw [← evalWord_toMPSTensor_pairConfig (blockSum O) σ τ,
    blockSum_toMPSTensor, MPSTensor.evalWord_toTensorFromBlocks_eq_reindex_blockDiagonal]
  simp only [one_pow, one_smul, evalWord_toMPSTensor_pairConfig]

/-- The virtual boundary projection onto one summand of a flattened
dependent direct sum. -/
def blockBoundarySelector (dim : Fin r → ℕ) (a : Fin r) :
    Matrix (Fin (∑ b : Fin r, dim b)) (Fin (∑ b : Fin r, dim b)) ℂ :=
  Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv
    (Matrix.sigmaBlockInclusion (fun b ↦ Fin (dim b)) a *
      (Matrix.sigmaBlockInclusion (fun b ↦ Fin (dim b)) a)ᴴ)

/-- A summand boundary selector commutes with every letter of the assembled
MPO tensor, so it is an admissible commuting boundary. -/
theorem blockBoundarySelector_mem_commutingBoundaryAlgebra
    (O : (a : Fin r) → MPOTensor d (dim a)) (a : Fin r) :
    blockBoundarySelector dim a ∈ commutingBoundaryAlgebra (blockSum O) := by
  rw [mem_commutingBoundaryAlgebra_iff]
  intro i j
  let e : ((b : Fin r) × Fin (dim b)) ≃ Fin (∑ b : Fin r, dim b) :=
    finSigmaFinEquiv
  let E := Matrix.sigmaBlockInclusion (fun b ↦ Fin (dim b)) a
  let B := fun b ↦ O b i j
  change Matrix.reindexLinearEquiv ℂ ℂ e e (E * Eᴴ) *
      Matrix.reindexLinearEquiv ℂ ℂ e e (Matrix.blockDiagonal' B) =
    Matrix.reindexLinearEquiv ℂ ℂ e e (Matrix.blockDiagonal' B) *
      Matrix.reindexLinearEquiv ℂ ℂ e e (E * Eᴴ)
  simp only [Matrix.reindexLinearEquiv_mul]
  exact congrArg (Matrix.reindex e e)
    (Matrix.blockDiagonal'_commute_sigmaBlockInclusion_rangeProjection B a).symm

/-- Closing an unweighted finite MPO direct sum with a summand selector
recovers the periodic operator of that summand, including at length zero. -/
@[simp] theorem mpoWithBoundary_blockSum_blockBoundarySelector
    (O : (a : Fin r) → MPOTensor d (dim a)) (a : Fin r) (N : ℕ) :
    mpoWithBoundary (blockSum O) (blockBoundarySelector dim a) N = mpo (O a) N := by
  ext σ τ
  change Matrix.trace (blockBoundarySelector dim a *
      evalWord (blockSum O) (List.ofFn σ) (List.ofFn τ)) =
    Matrix.trace (evalWord (O a) (List.ofFn σ) (List.ofFn τ))
  rw [evalWord_blockSum]
  let e : ((b : Fin r) × Fin (dim b)) ≃ Fin (∑ b : Fin r, dim b) :=
    finSigmaFinEquiv
  let E := Matrix.sigmaBlockInclusion (fun b ↦ Fin (dim b)) a
  let B := fun b ↦ evalWord (O b) (List.ofFn σ) (List.ofFn τ)
  change Matrix.trace (Matrix.reindexLinearEquiv ℂ ℂ e e (E * Eᴴ) *
      Matrix.reindexLinearEquiv ℂ ℂ e e (Matrix.blockDiagonal' B)) = Matrix.trace (B a)
  rw [Matrix.reindexLinearEquiv_mul ℂ ℂ e e e]
  simp only [Matrix.coe_reindexLinearEquiv, Matrix.trace_reindex]
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.sigmaBlockInclusion_compression]

end MPOTensor
