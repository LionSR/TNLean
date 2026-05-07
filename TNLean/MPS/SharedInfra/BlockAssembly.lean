/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Core.MultiBlock

/-!
# Shared direct-sum tensor infrastructure for MPS tensors

This file factors out the lightweight block-diagonal tensor constructor
`toTensorFromBlocks`, its word-evaluation expansion, and its MPV expansion
formula so shared infrastructure can depend on direct-sum tensor formulas
without importing gauge-equivalence theorems.
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

/-- Word evaluation of `toTensorFromBlocks` is the reindexed block diagonal of
the component word evaluations, with the scalar weight `μ k` contributing the
factor `(μ k) ^ w.length` on block `k`. -/
theorem evalWord_toTensorFromBlocks_eq_reindex_blockDiagonal
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k)) (w : List (Fin d)) :
    evalWord (toTensorFromBlocks (d := d) (μ := μ) A) w =
      (Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv)
        (Matrix.blockDiagonal' fun k => (μ k) ^ w.length • evalWord (A k) w) := by
  classical
  let α := (k : Fin r) × Fin (dim k)
  let e : α ≃ Fin (∑ k, dim k) := finSigmaFinEquiv
  let BD : Fin d → Matrix α α ℂ := fun i => Matrix.blockDiagonal' (fun k => μ k • A k i)
  have hfun : (fun i : Fin d => toTensorFromBlocks (d := d) (μ := μ) A i) =
      fun i => (Matrix.reindex e e) (BD i) := by
    funext i
    rfl
  calc
    evalWord (toTensorFromBlocks (d := d) (μ := μ) A) w =
        (Matrix.reindex e e) (_root_.evalWord BD w) := by
      simpa [toTensorFromBlocks, BD, e, hfun] using
        evalWord_reindex (d := d) (e := e) (A := BD) w
    _ = (Matrix.reindex e e)
        (Matrix.blockDiagonal' fun k => (μ k) ^ w.length • evalWord (A k) w) := by
      congr 1
      simpa [BD] using evalWord_blockDiagonal'_smul (μ := μ) (A := A) w

/-- MPV of `toTensorFromBlocks` expands as a sum over blocks. -/
theorem mpv_toTensorFromBlocks_eq_sum
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    {N : ℕ} (σ : Fin N → Fin d) :
    mpv (toTensorFromBlocks (d := d) (μ := μ) A) σ =
      ∑ k : Fin r, (μ k) ^ N • mpv (A k) σ := by
  classical
  set w := List.ofFn σ with hw
  have hwlen : w.length = N := by simp [w]
  simp only [MPSTensor.mpv, MPSTensor.coeff, hw.symm, smul_eq_mul]
  rw [evalWord_toTensorFromBlocks_eq_reindex_blockDiagonal μ A w, Matrix.trace_reindex]
  rw [Matrix.trace_blockDiagonal']
  exact Finset.sum_congr rfl fun k _ => by simp [Matrix.trace_smul, hwlen]

end MPSTensor
