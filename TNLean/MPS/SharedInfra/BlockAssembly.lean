/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Core.MultiBlock

/-!
# Shared block-assembly infrastructure for MPS tensors

This file factors out the lightweight block-diagonal tensor constructor
`toTensorFromBlocks` and its MPV expansion formula so shared infrastructure can
depend on block assembly without importing the multi-block Fundamental Theorem.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

/-- Build a block-diagonal tensor from raw block data. -/
noncomputable def toTensorFromBlocks {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k)) :
    MPSTensor d (∑ k : Fin r, dim k) := fun i =>
  (Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv)
    (Matrix.blockDiagonal' fun k => (μ k) • (A k i))

/-- MPV of `toTensorFromBlocks` expands as a sum over blocks. -/
theorem mpv_toTensorFromBlocks_eq_sum
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k)) {N : ℕ} (σ : Fin N → Fin d) :
    mpv (toTensorFromBlocks (d := d) (μ := μ) A) σ =
      ∑ k : Fin r, (μ k) ^ N • mpv (A k) σ := by
  classical
  set w := List.ofFn σ with hw
  have hwlen : w.length = N := by simp [w]
  simp only [MPSTensor.mpv, MPSTensor.coeff, hw.symm, smul_eq_mul]
  let α := (k : Fin r) × Fin (dim k)
  let e : α ≃ Fin (∑ k, dim k) := finSigmaFinEquiv
  let BD : Fin d → Matrix α α ℂ := fun i => Matrix.blockDiagonal' (fun k => μ k • A k i)
  have hEval : MPSTensor.evalWord (toTensorFromBlocks (d := d) (μ := μ) A) w =
      (Matrix.reindex e e) (_root_.evalWord BD w) := by
    simpa [toTensorFromBlocks, BD, e, show (fun i : Fin d => toTensorFromBlocks (d := d) (μ := μ)
      A i) = fun i => (Matrix.reindex e e) (BD i) from by funext i; rfl]
      using evalWord_reindex (d := d) (e := e) (A := BD) w
  rw [hEval, Matrix.trace_reindex]
  rw [show _root_.evalWord BD w = Matrix.blockDiagonal'
      (fun k => (μ k) ^ w.length • _root_.evalWord (A k) w) from by
    simpa [BD] using evalWord_blockDiagonal'_smul (μ := μ) (A := A) w]
  rw [Matrix.trace_blockDiagonal']
  exact Finset.sum_congr rfl fun k _ => by simp [Matrix.trace_smul, hwlen]

end MPSTensor
