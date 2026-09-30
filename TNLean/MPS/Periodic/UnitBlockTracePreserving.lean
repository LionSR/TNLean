/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.SharedInfra.BlockAssembly
import TNLean.MPS.Periodic.Defs
import TNLean.MPS.SharedInfra.Scaling

/-!
# Trace preservation of a literal unit-weight block tensor

The direct sum of trace-preserving periodic blocks with unit coefficients is
trace preserving. This is the normalization used in the corrected forward
statement of arXiv:1708.00029, Theorem 4.1.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-- A unit-weight direct sum of trace-preserving tensors is trace preserving.
Source: arXiv:1708.00029, irreducible form II, lines 313--332, and Theorem
4.1, lines 735--743. -/
theorem leftCanonical_toTensorFromBlocks_one
    {d r : ℕ} {dim : Fin r → ℕ}
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsLeftCanonical (A k)) :
    IsLeftCanonical (toTensorFromBlocks (μ := fun _ => 1) A) := by
  classical
  let e : ((k : Fin r) × Fin (dim k)) ≃ Fin (∑ k : Fin r, dim k) := finSigmaFinEquiv
  let F : Matrix ((k : Fin r) × Fin (dim k)) ((k : Fin r) × Fin (dim k)) ℂ →
      Matrix (Fin (∑ k : Fin r, dim k)) (Fin (∑ k : Fin r, dim k)) ℂ :=
    Matrix.reindex e e
  unfold IsLeftCanonical Kraus.IsTP
  simp only [toTensorFromBlocks, one_smul]
  change ∑ i : Fin d,
    (F (Matrix.blockDiagonal' (fun k => A k i)))ᴴ *
      F (Matrix.blockDiagonal' (fun k => A k i)) = 1
  simp only [F, Matrix.conjTranspose_reindex]
  change ∑ i : Fin d,
    F ((Matrix.blockDiagonal' (fun k => A k i))ᴴ) *
      F (Matrix.blockDiagonal' (fun k => A k i)) = 1
  change ∑ i : Fin d,
    Matrix.reindexLinearEquiv ℂ ℂ e e
      ((Matrix.blockDiagonal' (fun k => A k i))ᴴ) *
      Matrix.reindexLinearEquiv ℂ ℂ e e
        (Matrix.blockDiagonal' (fun k => A k i)) = 1
  simp_rw [Matrix.reindexLinearEquiv_mul ℂ ℂ e e e]
  change ∑ i : Fin d,
    (Matrix.reindexAlgEquiv ℂ ℂ e)
      ((Matrix.blockDiagonal' (fun k => A k i))ᴴ *
        Matrix.blockDiagonal' (fun k => A k i)) = 1
  rw [← map_sum]
  simp only [Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul]
  change (Matrix.reindexAlgEquiv ℂ ℂ e)
    (∑ i : Fin d, (Matrix.blockDiagonal'RingHom (fun k : Fin r => Fin (dim k)) ℂ)
      (fun k => (A k i)ᴴ * A k i)) = 1
  rw [← map_sum]
  have hFam : (∑ i : Fin d, fun k : Fin r => (A k i)ᴴ * A k i) =
      fun k : Fin r => (1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ) := by
    funext k
    simpa [IsLeftCanonical, Kraus.IsTP] using hA k
  rw [hFam]
  change Matrix.reindex e e
    (Matrix.blockDiagonal' (1 : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) = 1
  rw [Matrix.blockDiagonal'_one]
  exact map_one (Matrix.reindexRingEquiv ℂ e)

/-- Unit-modulus copy coefficients preserve trace preservation of a direct
sum of normalized blocks. Source: arXiv:1708.00029, Theorem 4.1,
lines 752--765. -/
theorem leftCanonical_toTensorFromBlocks_of_weight_norm_one
    {d r : ℕ} {dim : Fin r → ℕ}
    (A : (k : Fin r) → MPSTensor d (dim k)) (μ : Fin r → ℂ)
    (hA : ∀ k, IsLeftCanonical (A k)) (hμ : ∀ k, ‖μ k‖ = 1) :
    IsLeftCanonical (toTensorFromBlocks (μ := μ) A) := by
  have h := leftCanonical_toTensorFromBlocks_one
    (fun k => μ k • A k)
    (fun k => leftCanonical_smul_of_norm_one (μ k) (hμ k) (A k) (hA k))
  have heq : toTensorFromBlocks (μ := fun _ => 1) (fun k => μ k • A k) =
      toTensorFromBlocks (μ := μ) A := by
    funext i
    simp only [toTensorFromBlocks, one_smul, Pi.smul_apply]
  rw [heq] at h
  exact h

end MPSTensor
