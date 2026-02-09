import MPSLean.MPS.CanonicalForm

import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Reindex

open scoped Matrix BigOperators

/-- Word evaluation for a family of square matrices indexed by `Fin d`.

This is the same recursion as `MPSTensor.evalWord`, but it works for matrices indexed by an
arbitrary finite type (in particular, the `Σ`-type indices produced by `Matrix.blockDiagonal'`). -/
def evalWord {d : ℕ} {n : Type*} [Fintype n] [DecidableEq n]
    (A : Fin d → Matrix n n ℂ) : List (Fin d) → Matrix n n ℂ
  | [] => 1
  | i :: w => A i * evalWord A w

namespace Matrix

/-- Trace is invariant under reindexing of the basis. -/
lemma trace_reindex {m n : Type*} [Fintype m] [Fintype n]
    (e : m ≃ n) (M : Matrix m m ℂ) :
    Matrix.trace ((Matrix.reindex e e) M) = Matrix.trace M := by
  classical
  -- Expand `trace` as a sum over diagonal entries and change variables along `e.symm`.
  simpa [Matrix.trace, Matrix.reindex_apply] using
    (Fintype.sum_equiv e.symm (fun j : n => M (e.symm j) (e.symm j)) (fun i : m => M i i)
      (by intro j; simp))

end Matrix

section BlockDiagonal

variable {d : ℕ} {r : ℕ} {dim : Fin r → ℕ}

/-- `evalWord` of a block-diagonal tensor is the block-diagonal of the blockwise `evalWord`s.

This lemma lives on the `Σ`-type indices of `Matrix.blockDiagonal'`. -/
lemma evalWord_blockDiagonal'
    (blocks : (k : Fin r) → (Fin d → Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) :
    ∀ w : List (Fin d),
      evalWord (fun i => Matrix.blockDiagonal' (fun k => blocks k i)) w =
        Matrix.blockDiagonal' (fun k => evalWord (blocks k) w) := by
  classical
  intro w
  induction w with
  | nil =>
      -- `evalWord` is `1` and `blockDiagonal'` of identity blocks is again `1`.
      simp only [evalWord]
      change (1 : Matrix ((k : Fin r) × Fin (dim k)) ((k : Fin r) × Fin (dim k)) ℂ) =
        Matrix.blockDiagonal' (1 : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ)
      simp
  | cons i w ih =>
      simp [evalWord, ih]

/-- Variant of `evalWord_blockDiagonal'` with a per-block scalar factor `μ k`.

Each block picks up a factor `(μ k) ^ w.length`. -/
lemma evalWord_blockDiagonal'_smul
    (μ : Fin r → ℂ) (A : (k : Fin r) → (Fin d → Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) :
    ∀ w : List (Fin d),
      evalWord (fun i => Matrix.blockDiagonal' (fun k => μ k • A k i)) w =
        Matrix.blockDiagonal' (fun k => (μ k) ^ w.length • evalWord (A k) w) := by
  classical
  intro w
  induction w with
  | nil =>
      -- `evalWord` is `1` and `blockDiagonal'` of identity blocks is again `1`.
      simp only [List.length_nil, pow_zero, one_smul]
      change (1 : Matrix ((k : Fin r) × Fin (dim k)) ((k : Fin r) × Fin (dim k)) ℂ) =
        Matrix.blockDiagonal' (1 : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ)
      simp
  | cons i w ih =>
      -- Expand one step of the recursion and insert the induction hypothesis.
      simp only [List.length_cons, pow_succ']
      -- Use `blockDiagonal'_mul` to multiply blockwise.
      have hmul :
          Matrix.blockDiagonal' (fun k => μ k • A k i) *
              Matrix.blockDiagonal' (fun k => (μ k) ^ w.length • evalWord (A k) w) =
            Matrix.blockDiagonal'
              (fun k => (μ k • A k i) * ((μ k) ^ w.length • evalWord (A k) w)) := by
        simpa using
          (Matrix.blockDiagonal'_mul (M := fun k => μ k • A k i)
            (N := fun k => (μ k) ^ w.length • evalWord (A k) w)).symm
      -- Rewrite the blockwise product into a single scalar power.
      -- Key identity: `(μ • M₁) * (μ^n • M₂) = μ^(n+1) • (M₁ * M₂)`.
      -- Then fold back the recursive definition of `evalWord`.
      simp only [evalWord, ih, hmul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
        smul_smul, Matrix.blockDiagonal'_inj]
      funext k; simp only [mul_comm]

end BlockDiagonal

namespace MPSTensor

open CanonicalForm

/-- On `Fin D` indices, the auxiliary `evalWord` from `MultiBlock.lean` agrees with
`MPSTensor.evalWord`. -/
@[simp] lemma evalWord_aux_eq {d D : ℕ} (A : MPSTensor d D) (w : List (Fin d)) :
    _root_.evalWord A w = MPSTensor.evalWord A w := by
  induction w with
  | nil =>
      simp [MPSTensor.evalWord, _root_.evalWord]
  | cons i w ih =>
      simp [MPSTensor.evalWord, _root_.evalWord, ih]

/-- `MPSTensor.evalWord` commutes with reindexing along an equivalence. -/
lemma evalWord_reindex {d D : ℕ} {m : Type*} [Fintype m] [DecidableEq m]
    (e : m ≃ Fin D) (A : Fin d → Matrix m m ℂ) :
    ∀ w : List (Fin d),
      MPSTensor.evalWord (fun i => (Matrix.reindex e e) (A i)) w =
        (Matrix.reindex e e) (_root_.evalWord A w) := by
  classical
  intro w; induction w with
  | nil => simp [MPSTensor.evalWord, _root_.evalWord]
  | cons i w ih =>
      simp only [MPSTensor.evalWord, _root_.evalWord, ih]
      -- reindex preserves multiplication (via reindexAlgEquiv)
      simp

/-- MPV of a canonical-form tensor expands as a sum over blocks. -/
theorem mpv_toTensor_eq_sum (C : CanonicalForm d) {N : ℕ} (σ : Fin N → Fin d) :
    mpv (C.toTensor) σ = ∑ k : Fin C.numBlocks, (C.μ k) ^ N • mpv (C.blockTensor k) σ := by
  classical
  set w : List (Fin d) := List.ofFn σ with hw
  have hwlen : w.length = N := by simp [w]
  simp only [MPSTensor.mpv, MPSTensor.coeff, hw.symm, smul_eq_mul]
  let α := (k : Fin C.numBlocks) × Fin (C.blockDim k)
  let e : α ≃ Fin C.totalDim := finSigmaFinEquiv
  let BD : Fin d → Matrix α α ℂ := fun i =>
    Matrix.blockDiagonal' (fun k => (C.μ k) • (C.blockTensor k i))
  have hEval : MPSTensor.evalWord (C.toTensor) w = (Matrix.reindex e e) (_root_.evalWord BD w) := by
    have hTensor : (fun i : Fin d => C.toTensor i) =
        fun i => (Matrix.reindex e e) (BD i) := by
      funext i; simp [CanonicalForm.toTensor, CanonicalForm.totalDim, BD, e]; rfl
    simpa [hTensor] using (evalWord_reindex (d := d) (D := C.totalDim) (e := e) (A := BD) w)
  rw [hEval, Matrix.trace_reindex]
  have hBD : _root_.evalWord BD w = Matrix.blockDiagonal'
      (fun k => (C.μ k) ^ w.length • _root_.evalWord (C.blockTensor k) w) := by
    simpa [BD] using (evalWord_blockDiagonal'_smul (μ := C.μ) (A := C.blockTensor) w)
  rw [hBD, Matrix.trace_blockDiagonal']
  exact Finset.sum_congr rfl fun k _ => by simp [Matrix.trace_smul, hwlen]

/-- Gauge equivalence up to a phase implies proportional MPVs. -/
theorem GaugePhaseEquiv.proportionalMPV₂_right {d D : ℕ} {A B : MPSTensor d D} :
    GaugePhaseEquiv A B → ProportionalMPV₂ B A := by
  rintro ⟨X, ζ, hX⟩ N
  refine ⟨ζ ^ N, fun σ => ?_⟩
  simp only [MPSTensor.mpv, MPSTensor.coeff]
  set w : List (Fin d) := List.ofFn σ
  have hwlen : w.length = N := by simp [w]
  have hEval : MPSTensor.evalWord B w =
      (ζ ^ w.length) • ((X : Matrix (Fin D) (Fin D) ℂ) * MPSTensor.evalWord A w *
        ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) := by
    classical
    induction w with
    | nil => simp [MPSTensor.evalWord]
    | cons i w ih =>
        simp [MPSTensor.evalWord, hX, ih, Matrix.mul_assoc, pow_succ', smul_smul]
        simp [mul_comm]
  simp only [hEval, Matrix.trace_smul, trace_conj_eq (D := D) X, hwlen, smul_eq_mul]

end MPSTensor
