/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Chain.Defs

import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Cyclic block averaging for a fixed MPS chain

This file formalizes the cyclic off-diagonal block construction in the proof of
PGVWC07, Theorem 3 (arXiv:quant-ph/0608197, lines 620--649). For a fixed
positive chain length `N`, it turns a square site-dependent chain into one
site-independent tensor of bond dimension `N * D`. At length `N`, the new
coefficient is the normalized average of the coefficients of all cyclic
rotations of the chain.

The tensor constructed here depends on `N`; the result concerns only its
length-`N` coefficient.
-/

namespace MPSChainTensor

variable {d D N : ℕ}

/-- The rotation of a chain by `k` sites. -/
def cyclicRotation (A : MPSChainTensor d D N) (k : Fin N) : MPSChainTensor d D N :=
  fun j => A (finCycle k j)

/-- A cyclic rotation evaluates the chain at the shifted site. -/
@[simp] theorem cyclicRotation_apply (A : MPSChainTensor d D N) (k j : Fin N) :
    cyclicRotation A k j = A (j + k) := rfl

/-- Rotating by `k` sites is the `k`-fold iterate of the one-site cyclic shift. -/
theorem cyclicRotation_eq_iterate_cyclicShift (A : MPSChainTensor d D N) (k : Fin N) :
    cyclicRotation A k = (cyclicShift^[k.val]) A := by
  have hiterate : ∀ (m : ℕ) (B : MPSChainTensor d D N) (j : Fin N),
      (cyclicShift^[m]) B j = B ((finRotate N)^[m] j) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        intro B j
        rw [Function.iterate_succ_apply, ih, cyclicShift, cyclicSucc,
          Function.iterate_succ_apply']
  ext j i a b
  rw [hiterate, ← finCycle_eq_finRotate_iterate]
  rfl

/-- The permutation of block coordinates induced by cyclic successor. -/
def cyclicBlockPerm : Equiv.Perm (Fin D × Fin N) :=
  Equiv.prodCongr (Equiv.refl (Fin D)) (finRotate N)

/-- The cyclic permutation matrix on the `N` blocks of size `D`. -/
def cyclicBlockPermMatrix : Matrix (Fin D × Fin N) (Fin D × Fin N) ℂ :=
  (cyclicBlockPerm (D := D) (N := N)).permMatrix ℂ

/-- Flatten block coordinates in the order `Fin N × Fin D` to `Fin (N * D)`. -/
def cyclicBlockFinEquiv : Fin D × Fin N ≃ Fin (N * D) :=
  (Equiv.prodComm (Fin D) (Fin N)).trans finProdFinEquiv

/-- The unnormalized cyclic off-diagonal block matrix for one physical index. -/
def cyclicBlockMatrix (A : MPSChainTensor d D N) (i : Fin d) :
    Matrix (Fin D × Fin N) (Fin D × Fin N) ℂ :=
  Matrix.blockDiagonal (fun k => A k i) * cyclicBlockPermMatrix

/-- The scalar `N ^ (-1 / N)` whose `N`th power is `N⁻¹`. -/
noncomputable def cyclicBlockNormalization (N : ℕ) : ℂ :=
  ((N : ℂ)⁻¹) ^ ((N : ℂ)⁻¹)

/-- The fixed-length site-independent tensor obtained from cyclic off-diagonal blocks.

This is the block matrix in PGVWC07, Theorem 3 (arXiv:quant-ph/0608197,
lines 635--647), reindexed to bond coordinates `Fin (N * D)` and multiplied by
`N ^ (-1 / N)`. -/
noncomputable def cyclicBlockTensor (A : MPSChainTensor d D N) : MPSTensor d (N * D) :=
  fun i => cyclicBlockNormalization N •
    Matrix.reindex (cyclicBlockFinEquiv (D := D) (N := N))
      (cyclicBlockFinEquiv (D := D) (N := N)) (cyclicBlockMatrix A i)

private def pathEval (A : MPSChainTensor d D N) (k : Fin N) :
    List (Fin d) → Matrix (Fin D) (Fin D) ℂ
  | [] => 1
  | i :: w => A k i * pathEval A (finRotate N k) w

private theorem cyclicBlockPermMatrix_mul_blockDiagonal
    (M : Fin N → Matrix (Fin D) (Fin D) ℂ) :
    cyclicBlockPermMatrix (D := D) (N := N) * Matrix.blockDiagonal M =
      Matrix.blockDiagonal (M ∘ finRotate N) * cyclicBlockPermMatrix := by
  rw [cyclicBlockPermMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv]
  ext ⟨a, k⟩ ⟨b, l⟩
  change Matrix.blockDiagonal M (a, finRotate N k) (b, l) =
    Matrix.blockDiagonal (M ∘ finRotate N) (a, k) (b, (finRotate N).symm l)
  simp only [Matrix.blockDiagonal_apply, Function.comp_apply]
  rw [if_congr ((finRotate N).eq_symm_apply) rfl rfl]

private def blockEvalWord
    (A : Fin d → Matrix (Fin D × Fin N) (Fin D × Fin N) ℂ) :
    List (Fin d) → Matrix (Fin D × Fin N) (Fin D × Fin N) ℂ
  | [] => 1
  | i :: w => A i * blockEvalWord A w

private theorem blockEvalWord_cyclicBlockMatrix
    (A : MPSChainTensor d D N) (w : List (Fin d)) :
    blockEvalWord (cyclicBlockMatrix A) w =
      Matrix.blockDiagonal (fun k => pathEval A k w) *
        cyclicBlockPermMatrix (D := D) (N := N) ^ w.length := by
  induction w with
  | nil =>
      simp only [blockEvalWord, pathEval, List.length_nil, pow_zero, Matrix.mul_one]
      exact Matrix.blockDiagonal_one.symm
  | cons i w ih =>
      simp only [blockEvalWord, List.length_cons, pathEval]
      rw [ih, cyclicBlockMatrix, Matrix.mul_assoc,
        ← Matrix.mul_assoc (cyclicBlockPermMatrix (D := D) (N := N)),
        cyclicBlockPermMatrix_mul_blockDiagonal]
      calc
        (Matrix.blockDiagonal fun k => A k i) *
              ((Matrix.blockDiagonal ((fun k => pathEval A k w) ∘ finRotate N) *
                cyclicBlockPermMatrix) * cyclicBlockPermMatrix ^ w.length) =
            ((Matrix.blockDiagonal fun k => A k i) *
              Matrix.blockDiagonal ((fun k => pathEval A k w) ∘ finRotate N)) *
                (cyclicBlockPermMatrix * cyclicBlockPermMatrix ^ w.length) := by
          noncomm_ring
        _ = (Matrix.blockDiagonal fun k => A k i * pathEval A (finRotate N k) w) *
              (cyclicBlockPermMatrix * cyclicBlockPermMatrix ^ w.length) := by
          rw [← Matrix.blockDiagonal_mul]
          rfl
        _ = (Matrix.blockDiagonal fun k => A k i * pathEval A (finRotate N k) w) *
              cyclicBlockPermMatrix ^ (w.length + 1) := by rw [← pow_succ']

private theorem pathEval_ofFn (A : MPSChainTensor d D N) (σ : Fin N → Fin d)
    (k : Fin N) :
    pathEval A k (List.ofFn σ) = eval (cyclicRotation A k) σ := by
  have haux : ∀ (m : ℕ) (τ : Fin m → Fin d) (l : Fin N),
      pathEval A l (List.ofFn τ) =
        Fin.prod fun j => A ((finRotate N)^[j.val] l) (τ j) := by
    intro m
    induction m with
    | zero => simp [pathEval]
    | succ m ih =>
        intro τ l
        rw [List.ofFn_succ, pathEval, Fin.prod_succ, ih]
        congr 1
  rw [haux]
  unfold eval
  congr 1
  funext j
  rw [← finCycle_eq_finRotate_iterate]
  simp [cyclicRotation, finCycle_apply, add_comm]

private theorem cyclicBlockPermMatrix_pow_length [NeZero N] :
    cyclicBlockPermMatrix (D := D) (N := N) ^ N = 1 := by
  have hrotate (k : Fin N) : (finRotate N)^[N] k = k := by
    cases N with
    | zero => exact k.elim0
    | succ n =>
        apply Fin.ext
        have h : ∀ m : ℕ, (((finRotate (n + 1))^[m]) k).val =
            (k.val + m) % (n + 1) := by
          intro m
          induction m with
          | zero => simp [Nat.mod_eq_of_lt k.isLt]
          | succ m ih =>
              rw [Function.iterate_succ_apply', finRotate_apply, Fin.val_add, ih,
                Nat.mod_add_mod, Fin.val_one', Nat.add_mod_mod]
              apply congrArg (fun x : ℕ => x % (n + 1))
              omega
        rw [h]
        simp [Nat.mod_eq_of_lt k.isLt]
  have hmatrix (p : Equiv.Perm (Fin D × Fin N)) : ∀ m : ℕ,
      p.permMatrix ℂ ^ m = (p ^ m).permMatrix ℂ := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ', ih, ← Matrix.permMatrix_mul, ← pow_succ]
  have hperm : cyclicBlockPerm (D := D) (N := N) ^ N = 1 := by
    apply Equiv.ext
    rintro ⟨a, k⟩
    rw [Equiv.Perm.coe_pow]
    have hblock : ∀ m : ℕ,
        ((cyclicBlockPerm (D := D) (N := N) : Fin D × Fin N → Fin D × Fin N)^[m])
            (a, k) = (a, (finRotate N)^[m] k) := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih =>
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
          rfl
    rw [hblock, hrotate]
    rfl
  rw [cyclicBlockPermMatrix, hmatrix, hperm, Matrix.permMatrix_one]

private theorem trace_reindex_cyclicBlockFinEquiv
    (M : Matrix (Fin D × Fin N) (Fin D × Fin N) ℂ) :
    Matrix.trace
      (Matrix.reindex (cyclicBlockFinEquiv (D := D) (N := N))
        (cyclicBlockFinEquiv (D := D) (N := N)) M) = Matrix.trace M := by
  simpa [Matrix.trace, Matrix.diag, Matrix.reindex_apply] using
    Equiv.sum_comp (cyclicBlockFinEquiv (D := D) (N := N)).symm (fun i => M i i)

private theorem evalWord_reindex_cyclicBlockFinEquiv
    (A : Fin d → Matrix (Fin D × Fin N) (Fin D × Fin N) ℂ) (w : List (Fin d)) :
    Kraus.evalWord
        (fun i => Matrix.reindex (cyclicBlockFinEquiv (D := D) (N := N))
          (cyclicBlockFinEquiv (D := D) (N := N)) (A i)) w =
      Matrix.reindex (cyclicBlockFinEquiv (D := D) (N := N))
        (cyclicBlockFinEquiv (D := D) (N := N)) (blockEvalWord A w) := by
  induction w with
  | nil =>
      simp only [Kraus.evalWord_nil, blockEvalWord]
      exact (Matrix.reindexLinearEquiv_one ℂ ℂ
        (cyclicBlockFinEquiv (D := D) (N := N))).symm
  | cons i w ih =>
      simp only [Kraus.evalWord_cons, blockEvalWord]
      rw [ih]
      exact Matrix.reindexLinearEquiv_mul ℂ ℂ
        (cyclicBlockFinEquiv (D := D) (N := N))
        (cyclicBlockFinEquiv (D := D) (N := N))
        (cyclicBlockFinEquiv (D := D) (N := N)) (A i) (blockEvalWord A w)

/-- At the fixed positive length `N`, the cyclic block tensor coefficient is
exactly the normalized average of the coefficients of all cyclic rotations of
`A`.

This is the general algebraic averaging identity underlying PGVWC07,
Theorem 3 (arXiv:quant-ph/0608197, lines 643--648). It makes no translation
invariance, injectivity, purity, or canonical-form assumption, and asserts no
equality at lengths other than `N`. -/
theorem mpv_cyclicBlockTensor_eq_average [NeZero N]
    (A : MPSChainTensor d D N) (σ : Fin N → Fin d) :
    MPSTensor.mpv (cyclicBlockTensor A) σ =
      (N : ℂ)⁻¹ * ∑ k : Fin N, coeff (cyclicRotation A k) σ := by
  change Matrix.trace
      (Kraus.evalWord
        (fun i => cyclicBlockNormalization N •
          Matrix.reindex (cyclicBlockFinEquiv (D := D) (N := N))
            (cyclicBlockFinEquiv (D := D) (N := N)) (cyclicBlockMatrix A i))
        (List.ofFn σ)) = _
  rw [Kraus.evalWord_smul, List.length_ofFn, Matrix.trace_smul]
  simp only [smul_eq_mul]
  rw [evalWord_reindex_cyclicBlockFinEquiv, blockEvalWord_cyclicBlockMatrix,
    List.length_ofFn, cyclicBlockPermMatrix_pow_length, Matrix.mul_one,
    trace_reindex_cyclicBlockFinEquiv, Matrix.trace_blockDiagonal]
  simp_rw [pathEval_ofFn, coeff]
  rw [show cyclicBlockNormalization N ^ N = (N : ℂ)⁻¹ by
    exact Complex.cpow_nat_inv_pow ((N : ℂ)⁻¹) (NeZero.ne N)]

end MPSChainTensor
