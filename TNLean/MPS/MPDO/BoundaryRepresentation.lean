/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BoundaryTransport
import TNLean.MPS.SharedInfra.BoundaryDecomposition
import TNLean.MPS.SharedInfra.WordTupleGauge
import Mathlib.Algebra.Algebra.NonUnitalHom

/-!
# The representation determined by arbitrary-boundary transport

The bilinear trace dual of a length-independent boundary map carries each
simultaneous tuple of target word matrices to the corresponding source word
matrix. If the target tuples span their product matrix algebra at one positive
length, comparison at that length and twice that length makes the trace dual
multiplicative. Its image of the identity is the support idempotent; it need
not be the identity of the ambient matrix algebra.

This proves the representation-theoretic step in GLM23 Appendix A without
assuming a star structure or a decomposition into fusion tensors. A later
matrix-unit decomposition of this representation is still needed to obtain
the biorthogonal fusion or action matrices.

## References

* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, Appendix A,
  `decompopen` and `eq:ortho`, lines 2305--2455.
-/

open scoped Matrix BigOperators

noncomputable section

namespace Matrix

variable {r D : ℕ} {dim : Fin r → ℕ}

/-- The trace dual of a boundary map taking an ambient matrix to one boundary
for each target block. Source: GLM23, Appendix A, `decompopen`. -/
def familyTraceAdjoint
    (b : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ]
      ((c : Fin r) → Matrix (Fin (dim c)) (Fin (dim c)) ℂ)) :
    ((c : Fin r) → Matrix (Fin (dim c)) (Fin (dim c)) ℂ) →ₗ[ℂ]
      Matrix (Fin D) (Fin D) ℂ :=
  ∑ c : Fin r,
    (traceAdjointMap ((LinearMap.proj c).comp b)).comp (LinearMap.proj c)

/-- The defining trace identity of the family trace dual. No adjoints or
positivity hypotheses occur. Source: GLM23, Appendix A, `decompopen`. -/
theorem trace_familyTraceAdjoint_mul
    (b : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ]
      ((c : Fin r) → Matrix (Fin (dim c)) (Fin (dim c)) ℂ))
    (M : (c : Fin r) → Matrix (Fin (dim c)) (Fin (dim c)) ℂ)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    trace (familyTraceAdjoint b M * X) =
      ∑ c : Fin r, trace (M c * b X c) := by
  simp only [familyTraceAdjoint, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, Matrix.sum_mul, Matrix.trace_sum,
    trace_traceAdjointMap_mul]

/-- Extract all diagonal blocks of a matrix on a flattened direct sum.
Source: GLM23, Appendix A, the block projectors preceding `decompopen`. -/
def finSigmaDiagonalBlocks :
    Matrix (Fin (∑ c : Fin r, dim c)) (Fin (∑ c : Fin r, dim c)) ℂ →ₗ[ℂ]
      ((c : Fin r) → Matrix (Fin (dim c)) (Fin (dim c)) ℂ) where
  toFun X c := finSigmaDiagonalBlock X c
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Matrix

namespace MPSTensor

variable {d D r : ℕ} {dim : Fin r → ℕ}

/-- Arbitrary-boundary transport determines every nonempty word matrix by
trace duality. This is the exact open-chain identity of GLM23 Appendix A,
`decompopen`; equality only for periodic traces would not suffice. -/
theorem familyTraceAdjoint_wordTuple
    (B : MPSTensor d D) (A : (c : Fin r) → MPSTensor d (dim c))
    (b : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ]
      ((c : Fin r) → Matrix (Fin (dim c)) (Fin (dim c)) ℂ))
    (hb : ∀ (L : ℕ), 0 < L → ∀ X : Matrix (Fin D) (Fin D) ℂ,
      ∀ w : Fin L → Fin d,
        mpvWithBoundary B X w = ∑ c : Fin r, mpvWithBoundary (A c) (b X c) w)
    {L : ℕ} (hL : 0 < L) (w : Fin L → Fin d) :
    Matrix.familyTraceAdjoint b (wordTuple A L w) =
      Kraus.evalWord B (List.ofFn w) := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro X
  rw [Matrix.trace_familyTraceAdjoint_mul]
  calc
    (∑ c : Fin r, Matrix.trace (wordTuple A L w c * b X c)) =
        ∑ c : Fin r, mpvWithBoundary (A c) (b X c) w := by
      apply Finset.sum_congr rfl
      intro c _
      exact Matrix.trace_mul_comm _ _
    _ = Matrix.trace (X * Kraus.evalWord B (List.ofFn w)) := (hb L hL X w).symm
    _ = Matrix.trace (Kraus.evalWord B (List.ofFn w) * X) := Matrix.trace_mul_comm _ _

/-- A length-independent boundary map has a multiplicative trace dual when
simultaneous target words span at some positive length. Compare lengths
`L` and `2 * L`; one-site simultaneous injectivity is not required.

Source: GLM23, Appendix A, the comparison following `decompopen` and before
`eq:ortho`, lines 2360--2453. This statement derives multiplicativity and
does not assume biorthogonal fusion or action tensors. -/
theorem familyTraceAdjoint_map_mul
    (B : MPSTensor d D) (A : (c : Fin r) → MPSTensor d (dim c))
    (b : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ]
      ((c : Fin r) → Matrix (Fin (dim c)) (Fin (dim c)) ℂ))
    (hb : ∀ (n : ℕ), 0 < n → ∀ X : Matrix (Fin D) (Fin D) ℂ,
      ∀ w : Fin n → Fin d,
        mpvWithBoundary B X w = ∑ c : Fin r, mpvWithBoundary (A c) (b X c) w)
    {L : ℕ} (hL : 0 < L) (hSpan : WordTupleSpanTop A L)
    (M N : (c : Fin r) → Matrix (Fin (dim c)) (Fin (dim c)) ℂ) :
    Matrix.familyTraceAdjoint b (M * N) =
      Matrix.familyTraceAdjoint b M * Matrix.familyTraceAdjoint b N := by
  have hM : M ∈ Submodule.span ℂ (Set.range (wordTuple A L)) := by
    rw [hSpan]; exact Submodule.mem_top
  have hN : N ∈ Submodule.span ℂ (Set.range (wordTuple A L)) := by
    rw [hSpan]; exact Submodule.mem_top
  induction hM, hN using Submodule.span_induction₂ with
  | mem_mem M N hM hN =>
    obtain ⟨u, rfl⟩ := hM
    obtain ⟨v, rfl⟩ := hN
    have happ : wordTuple A L u * wordTuple A L v =
        wordTuple A (L + L) (Fin.append u v) := by
      funext c
      simp [wordTuple, List.ofFn_fin_append, Kraus.evalWord_append]
    rw [happ, familyTraceAdjoint_wordTuple B A b hb (by omega),
      familyTraceAdjoint_wordTuple B A b hb hL,
      familyTraceAdjoint_wordTuple B A b hb hL,
      List.ofFn_fin_append, Kraus.evalWord_append]
  | zero_left N hN => simp
  | zero_right M hM => simp
  | add_left M N P hM hN hP hMP hNP =>
    simp only [add_mul, map_add, hMP, hNP]
  | add_right M N P hM hN hP hMN hMP =>
    simp only [mul_add, map_add, hMN, hMP]
  | smul_left z M N hM hN hMN =>
    simp only [smul_mul_assoc, map_smul, hMN]
  | smul_right z M N hM hN hMN =>
    simp only [mul_smul_comm, map_smul, hMN]

/-- A length-independent boundary transport and simultaneous spanning
produce a representation of the product of the target matrix algebras.
The representation is not required to preserve the ambient identity.
Source: GLM23, Appendix A, `decompopen` and `eq:ortho`. -/
def boundaryRepresentation
    (B : MPSTensor d D) (A : (c : Fin r) → MPSTensor d (dim c))
    (b : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ]
      ((c : Fin r) → Matrix (Fin (dim c)) (Fin (dim c)) ℂ))
    (hb : ∀ (n : ℕ), 0 < n → ∀ X : Matrix (Fin D) (Fin D) ℂ,
      ∀ w : Fin n → Fin d,
        mpvWithBoundary B X w = ∑ c : Fin r, mpvWithBoundary (A c) (b X c) w)
    {L : ℕ} (hL : 0 < L) (hSpan : WordTupleSpanTop A L) :
    ((c : Fin r) → Matrix (Fin (dim c)) (Fin (dim c)) ℂ) →ₙₐ[ℂ]
      Matrix (Fin D) (Fin D) ℂ where
  toFun := Matrix.familyTraceAdjoint b
  map_zero' := map_zero _
  map_add' := map_add _
  map_smul' := map_smul _
  map_mul' := familyTraceAdjoint_map_mul B A b hb hL hSpan

/-- The boundary representation maps the tuple of local target letters to
the source letter, with no remainder. Source: GLM23, `fusiontensors`,
`fusiontensors2`, and Appendix A at length one. -/
theorem boundaryRepresentation_letter
    (B : MPSTensor d D) (A : (c : Fin r) → MPSTensor d (dim c))
    (b : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ]
      ((c : Fin r) → Matrix (Fin (dim c)) (Fin (dim c)) ℂ))
    (hb : ∀ (n : ℕ), 0 < n → ∀ X : Matrix (Fin D) (Fin D) ℂ,
      ∀ w : Fin n → Fin d,
        mpvWithBoundary B X w = ∑ c : Fin r, mpvWithBoundary (A c) (b X c) w)
    {L : ℕ} (hL : 0 < L) (hSpan : WordTupleSpanTop A L) (i : Fin d) :
    boundaryRepresentation B A b hb hL hSpan (fun c ↦ A c i) = B i := by
  change Matrix.familyTraceAdjoint b (fun c ↦ A c i) = B i
  have h := familyTraceAdjoint_wordTuple B A b hb (by omega : 0 < 1) (fun _ ↦ i)
  have ht : wordTuple A 1 (fun _ ↦ i) = (fun c ↦ A c i) := by
    funext c
    simp [wordTuple, List.ofFn_succ]
  simpa only [ht, List.ofFn_succ, List.ofFn_zero, Kraus.evalWord_cons,
    Kraus.evalWord_nil, mul_one] using h

/-- Arbitrary boundaries of an unweighted direct sum split into diagonal
block boundaries. Source: GLM23, Appendix A, the block-projector expansion
preceding `decompopen`. -/
theorem mpvWithBoundary_toTensorFromBlocks_one
    (A : (c : Fin r) → MPSTensor d (dim c))
    (X : Matrix (Fin (∑ c : Fin r, dim c)) (Fin (∑ c : Fin r, dim c)) ℂ)
    {L : ℕ} (w : Fin L → Fin d) :
    mpvWithBoundary (toTensorFromBlocks (fun _ ↦ 1) A) X w =
      ∑ c : Fin r, mpvWithBoundary (A c) (Matrix.finSigmaDiagonalBlocks X c) w := by
  rw [mpvWithBoundary, Matrix.trace_mul_comm, trace_evalWord_toTensorFromBlocks_mul]
  apply Finset.sum_congr rfl
  intro c _
  simp only [one_pow, one_smul, mpvWithBoundary]
  exact Matrix.trace_mul_comm _ _

end MPSTensor
