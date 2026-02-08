import MPSLean.MPS.CanonicalForm
import MPSLean.MPS.GaugeInvariance

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
      simp [evalWord]
      change (1 : Matrix ((k : Fin r) × Fin (dim k)) ((k : Fin r) × Fin (dim k)) ℂ) =
        Matrix.blockDiagonal' (1 : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ)
      simpa using
        (Matrix.blockDiagonal'_one (o := Fin r) (m' := fun k => Fin (dim k)) (α := ℂ)).symm
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
      simp [evalWord]
      change (1 : Matrix ((k : Fin r) × Fin (dim k)) ((k : Fin r) × Fin (dim k)) ℂ) =
        Matrix.blockDiagonal' (1 : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ)
      simpa using
        (Matrix.blockDiagonal'_one (o := Fin r) (m' := fun k => Fin (dim k)) (α := ℂ)).symm
  | cons i w ih =>
      -- Expand one step of the recursion and insert the induction hypothesis.
      simp [evalWord, ih, List.length_cons]
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
      simp [hmul, evalWord, Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_succ'] <;>
        (funext k; simp [mul_comm, mul_left_comm, mul_assoc])

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

/-- `MPSTensor.evalWord` commutes with reindexing along an equivalence.

This is the bridge between the `Fin`-indexed tensor `C.toTensor` and its `Σ`-indexed
block-diagonal form. -/
lemma evalWord_reindex {d D : ℕ} {m : Type*} [Fintype m] [DecidableEq m]
    (e : m ≃ Fin D) (A : Fin d → Matrix m m ℂ) :
    ∀ w : List (Fin d),
      MPSTensor.evalWord (fun i => (Matrix.reindex e e) (A i)) w =
        (Matrix.reindex e e) (_root_.evalWord A w) := by
  classical
  intro w
  induction w with
  | nil =>
      -- `reindex` is an algebra equivalence, so it preserves `1`.
      have h1 : (Matrix.reindex e e) (1 : Matrix m m ℂ) = (1 : Matrix (Fin D) (Fin D) ℂ) := by
        simpa [Matrix.reindexAlgEquiv_apply] using (Matrix.reindexAlgEquiv ℂ ℂ e).map_one
      simpa [MPSTensor.evalWord, _root_.evalWord, h1]
  | cons i w ih =>
      -- One step of the recursion, then use multiplicativity of `reindex`.
      -- `reindexAlgEquiv` is an algebra equivalence, so it preserves multiplication.
      have hmul :
          (Matrix.reindex e e) (A i) * (Matrix.reindex e e) (_root_.evalWord A w) =
            (Matrix.reindex e e) (A i * _root_.evalWord A w) := by
        -- Start from the corresponding statement for `reindexAlgEquiv`.
        have :=
          (Matrix.reindexAlgEquiv_mul (R := ℂ) (A := ℂ) e (A i) (_root_.evalWord A w))
        -- Convert `reindexAlgEquiv` to `reindex`.
        simpa [Matrix.reindexAlgEquiv_apply] using this.symm
      -- Finish by unfolding `evalWord` on both sides, but without unfolding `Matrix.reindex`.
      simp only [MPSTensor.evalWord, _root_.evalWord, ih]
      exact hmul

/-- MPV of a canonical-form tensor expands as a sum over blocks.

This is the key computational lemma for the multi-block Fundamental Theorem. -/
theorem mpv_toTensor_eq_sum (C : CanonicalForm d) {N : ℕ} (σ : Fin N → Fin d) :
    mpv (C.toTensor) σ = ∑ k : Fin C.numBlocks, (C.μ k) ^ N • mpv (C.blockTensor k) σ := by
  classical
  -- Let `w` be the word corresponding to `σ`.
  let w : List (Fin d) := List.ofFn σ
  have hwlen : w.length = N := by
    simpa [w] using (List.length_ofFn σ)
  -- Unfold the MPV coefficient into a trace of a word evaluation.
  simp [MPSTensor.mpv, MPSTensor.coeff, w]
  -- Unfold `toTensor` and pull `reindex` out of the word evaluation.
  -- The inner tensor lives on the `Σ`-type indices of `blockDiagonal'`.
  classical
  -- Set up the `Σ`-indexed block-diagonal tensor and the reindexing equivalence.
  let α := (k : Fin C.numBlocks) × Fin (C.blockDim k)
  let e : α ≃ Fin C.totalDim := (finSigmaFinEquiv (m := C.numBlocks) (n := C.blockDim))
  let BD : Fin d → Matrix α α ℂ := fun i : Fin d =>
    Matrix.blockDiagonal' (fun k => (C.μ k) • (C.blockTensor k i))
  -- Replace `evalWord (C.toTensor)` by a reindexing of the `Σ`-indexed evaluation.
  have hEval :
      MPSTensor.evalWord (C.toTensor) w = (Matrix.reindex e e) (_root_.evalWord BD w) := by
    -- Unfold `toTensor` and use `evalWord_reindex`.
    -- (We keep the proof term-level to avoid `simp` getting stuck on the nested `let`s.)
    -- First, show the tensors agree pointwise.
    have hTensor :
        (fun i : Fin d => C.toTensor i) = fun i : Fin d => (Matrix.reindex e e) (BD i) := by
      funext i
      -- Unfold `toTensor` and `BD`.
      simp [CanonicalForm.toTensor, CanonicalForm.totalDim, BD, e]
      rfl
    -- Now use `hTensor` to rewrite and apply the general reindex lemma.
    --
    -- `simp [hTensor]` would unfold too aggressively, so we do it in two steps.
    --
    -- Note: `MPSTensor.evalWord` is definitional, so rewriting the tensor suffices.
    simpa [hTensor] using (evalWord_reindex (d := d) (D := C.totalDim) (e := e) (A := BD) w)
  -- Use trace invariance to remove the outer reindex.
  -- (Trace is computed on the `Σ`-indexed matrix.)
  --
  -- We also rewrite `w.length` to `N` using `hwlen`.
  --
  -- Finally we use `trace_blockDiagonal'` to turn the trace into a sum.
  --
  -- At the end, each summand is exactly `(μ k)^N • mpv (blockTensor k) σ`.
  --
  -- Start by substituting `hEval`.
  rw [hEval]
  -- Remove the outer reindex inside the trace.
  rw [Matrix.trace_reindex (e := e) (_root_.evalWord BD w)]
  -- Compute `_root_.evalWord BD w` blockwise.
  have hBD :
      _root_.evalWord BD w =
        Matrix.blockDiagonal'
          (fun k => (C.μ k) ^ w.length • _root_.evalWord (C.blockTensor k) w) := by
    simpa [BD] using (evalWord_blockDiagonal'_smul (μ := C.μ) (A := C.blockTensor) w)
  -- Turn the trace of a block diagonal into a sum of traces, then pull out the scalars.
  calc
    Matrix.trace (_root_.evalWord BD w)
        = Matrix.trace
            (Matrix.blockDiagonal'
              (fun k => (C.μ k) ^ w.length • _root_.evalWord (C.blockTensor k) w)) := by
            simpa [hBD]
    _ = ∑ k : Fin C.numBlocks,
          Matrix.trace ((C.μ k) ^ w.length • _root_.evalWord (C.blockTensor k) w) := by
          simpa using (Matrix.trace_blockDiagonal'
            (M := fun k => (C.μ k) ^ w.length • _root_.evalWord (C.blockTensor k) w))
    _ = ∑ k : Fin C.numBlocks,
          (C.μ k) ^ w.length • Matrix.trace (_root_.evalWord (C.blockTensor k) w) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          simpa using
            (Matrix.trace_smul ((C.μ k) ^ w.length) (_root_.evalWord (C.blockTensor k) w))
    _ = ∑ k : Fin C.numBlocks,
          (C.μ k) ^ N • Matrix.trace (MPSTensor.evalWord (C.blockTensor k) w) := by
          -- Replace `w.length` by `N` and convert `_root_.evalWord` on each block.
          simp [hwlen]

/-- Gauge equivalence up to a phase implies proportional MPVs.

Note: with our definition of `GaugePhaseEquiv`, the proportionality is naturally
`V_N(B) = (ζ^N) V_N(A)`. -/
theorem GaugePhaseEquiv.proportionalMPV₂_right {d D : ℕ} {A B : MPSTensor d D} :
    GaugePhaseEquiv A B → ProportionalMPV₂ B A := by
  rintro ⟨X, ζ, hX⟩
  intro N
  refine ⟨ζ ^ N, ?_⟩
  intro σ
  -- Unfold MPVs into traces.
  simp only [MPSTensor.mpv, MPSTensor.coeff]
  -- Let `w` be the corresponding word.
  set w : List (Fin d) := List.ofFn σ
  -- We show `evalWord B w = (ζ^N) • (X * evalWord A w * X⁻¹)`.
  have hEval :
      MPSTensor.evalWord B w =
        (ζ ^ w.length) •
          ((X : Matrix (Fin D) (Fin D) ℂ) * MPSTensor.evalWord A w *
            ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) := by
    -- Induction on the word.
    classical
    induction w with
    | nil =>
        simp [MPSTensor.evalWord]
    | cons i w ih =>
        -- One step: insert the gauge+phase relation and use associativity.
        simp [MPSTensor.evalWord, hX, ih, Matrix.mul_assoc, pow_succ',
          Matrix.smul_mul, Matrix.mul_smul, smul_smul] <;>
          simpa [mul_comm, mul_left_comm, mul_assoc]
  -- Take traces: trace of conjugation is invariant, and trace is linear in scalar factors.
  -- Also `w.length = N`.
  have hwlen : w.length = N := by
    simpa [w] using (List.length_ofFn σ)
  -- Use `hEval` and simplify.
  -- First pull out the scalar factor, then remove the conjugation.
  --
  -- The goal is `trace (evalWord B w) = (ζ^N) * trace (evalWord A w)`.
  --
  -- Then rewrite back to `mpv`.
  calc
    Matrix.trace (MPSTensor.evalWord B (List.ofFn σ))
        = Matrix.trace (MPSTensor.evalWord B w) := by simp [w]
    _ = Matrix.trace
          ((ζ ^ w.length) •
            ((X : Matrix (Fin D) (Fin D) ℂ) * MPSTensor.evalWord A w *
              ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))) := by
          simp [hEval]
    _ = (ζ ^ w.length) •
          Matrix.trace
            ((X : Matrix (Fin D) (Fin D) ℂ) * MPSTensor.evalWord A w *
              ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) := by
          simpa using (Matrix.trace_smul (ζ ^ w.length)
            ((X : Matrix (Fin D) (Fin D) ℂ) * MPSTensor.evalWord A w *
              ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)))
    _ = (ζ ^ w.length) • Matrix.trace (MPSTensor.evalWord A w) := by
          -- Remove the conjugation via cyclicity of trace.
          -- We reuse the lemma from `GaugeInvariance`.
          -- Scale the equality from `trace_conj_eq`.
          simpa using
            congrArg (fun t : ℂ => (ζ ^ w.length) • t)
              (trace_conj_eq (D := D) X (MPSTensor.evalWord A w))
    _ = (ζ ^ N) • Matrix.trace (MPSTensor.evalWord A w) := by
          simpa [hwlen]

end MPSTensor
