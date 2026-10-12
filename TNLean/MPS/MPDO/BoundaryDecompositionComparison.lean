/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BoundaryBiorthogonal

/-!
# Comparing exact decompositions with repeated target blocks

Two exact biorthogonal decompositions of one tensor over the same separated
target family give the same linear representation of the target matrix
algebra. In particular their support idempotents agree, even if their
coordinate spaces or repetitions of target labels differ.

This is the support comparison needed before defining a multiplicity
L-matrix from the two decompositions of a double action. The module does not
construct the double-action trees or assert the mixed pentagon.

## References

* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, `rawrels`,
  `eq:F_symbol2`, and `1Fsymbol`, lines 491--552.
-/

open scoped Matrix BigOperators

namespace MPSTensor.IsBiorthogonalDecomposition

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  {d DB r : ℕ} {dim : Fin r → ℕ}
  {B : MPSTensor d DB} {A : ∀ c, MPSTensor d (dim c)}
  {f : ι → Fin r} {g : κ → Fin r}
  {V : ∀ i, Matrix (Fin (dim (f i))) (Fin DB) ℂ}
  {W : ∀ i, Matrix (Fin DB) (Fin (dim (f i))) ℂ}
  {V' : ∀ j, Matrix (Fin (dim (g j))) (Fin DB) ℂ}
  {W' : ∀ j, Matrix (Fin DB) (Fin (dim (g j))) ℂ}

/-- Simultaneous word spanning identifies the entire reconstructed linear
map, even for differently indexed repetitions of the target blocks.
Source: GLM23 `rawrels`, using Appendix A at a common positive word length. -/
theorem sum_sandwich_eq_of_wordTupleSpanTop
    (h : IsBiorthogonalDecomposition B (fun i ↦ A (f i)) V W)
    (h' : IsBiorthogonalDecomposition B (fun j ↦ A (g j)) V' W')
    {L : ℕ} (hL : 0 < L) (hSpan : WordTupleSpanTop A L)
    (M : ∀ c, Matrix (Fin (dim c)) (Fin (dim c)) ℂ) :
    (∑ i, W i * M (f i) * V i) = ∑ j, W' j * M (g j) * V' j := by
  have hM : M ∈ Submodule.span ℂ (Set.range (wordTuple A L)) := by
    rw [hSpan]
    exact Submodule.mem_top
  induction hM using Submodule.span_induction with
  | mem M hM =>
    obtain ⟨w, rfl⟩ := hM
    have hw : List.ofFn w ≠ [] := by rw [Ne, List.ofFn_eq_nil_iff]; omega
    exact (h.evalWord (List.ofFn w) hw).symm.trans (h'.evalWord (List.ofFn w) hw)
  | zero => simp
  | add M N _ _ hM hN =>
    simp only [Pi.add_apply, Matrix.mul_add, Matrix.add_mul,
      Finset.sum_add_distrib, hM, hN]
  | smul z M _ hM =>
    simpa only [Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul, ← Finset.smul_sum]
      using congrArg (fun X ↦ z • X) hM

/-- The support idempotent is determined by the incoming tensor and its
separated target blocks, not by a choice of exact multiplicity coordinates.
Source: GLM23 `rawrels` and `1Fsymbol`. -/
theorem support_eq_of_wordTupleSpanTop
    (h : IsBiorthogonalDecomposition B (fun i ↦ A (f i)) V W)
    (h' : IsBiorthogonalDecomposition B (fun j ↦ A (g j)) V' W')
    {L : ℕ} (hL : 0 < L) (hSpan : WordTupleSpanTop A L) :
    (∑ i, W i * V i) = ∑ j, W' j * V' j := by
  simpa using h.sum_sandwich_eq_of_wordTupleSpanTop h' hL hSpan 1

end MPSTensor.IsBiorthogonalDecomposition

namespace Matrix

/-- Coordinate changes between two left-invertible factorizations of the
same support are inverse and carry each synthesis to the other. No adjoints
or completeness on the ambient space are needed. Source: GLM23 `1Fsymbol`. -/
theorem comparison_of_common_support
    {R m n k : Type*} [Semiring R] [Fintype m] [Fintype n] [Fintype k]
    [DecidableEq n] [DecidableEq k]
    (S : Matrix m n R) (H : Matrix n m R)
    (S' : Matrix m k R) (H' : Matrix k m R)
    (hHS : H * S = 1) (hHS' : H' * S' = 1) (hSupport : S * H = S' * H') :
    (H' * S) * (H * S') = 1 ∧ (H * S') * (H' * S) = 1 ∧
      S' * (H' * S) = S ∧ S * (H * S') = S' := by
  have hforward : S' * (H' * S) = S := by
    rw [← Matrix.mul_assoc, ← hSupport, Matrix.mul_assoc, hHS, Matrix.mul_one]
  have hbackward : S * (H * S') = S' := by
    rw [← Matrix.mul_assoc, hSupport, Matrix.mul_assoc, hHS', Matrix.mul_one]
  refine ⟨?_, ?_, hforward, hbackward⟩
  · rw [Matrix.mul_assoc, hbackward, hHS']
  · rw [Matrix.mul_assoc, hforward, hHS]

end Matrix
