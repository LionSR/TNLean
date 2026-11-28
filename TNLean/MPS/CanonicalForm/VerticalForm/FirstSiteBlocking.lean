/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.Physical.Blocking
import TNLean.MPS.CanonicalForm.VerticalForm.VerticalCF

/-!
# First-site actions under physical blocking

This file gives auxiliary blocking statements for combining the
block-injectivity argument of arXiv:1606.00608, lines 318--345, with the
first-site identity in Appendix C.3, Lemma L, lines 1835--1858.  On a block
of length `L + 1`, the induced matrix acts on the first letter and fixes the
remaining `L` letters.  Its insertion into the blocked tensor is the original
insertion followed by the word carried by those remaining letters.

If the length-`L` words span the full matrix algebra, equality of two such
blocked insertions implies equality before blocking.

## Main definitions

* `firstSiteActionOnBlock`: the physical matrix induced on a block by an
  action on its first letter.

## Main statements

* `firstSiteActionAgree_iff_trace`: the trace-pairing form of the all-length
  first-site identity.
* `FirstSiteActionAgree.trace_evalWord`: its consequence for an arbitrary
  finite word.
* `insertedTensor_firstSiteActionOnBlock_block`: the induced insertion
  factors as the original insertion followed by the remaining word.
* `FirstSiteActionAgree.block`: first-site agreement is preserved by
  physical blocking.
* `insertedTensor_eq_of_firstSiteActionOnBlock_block_eq`: block
  injectivity recovers equality before blocking.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  lines 318--345 and Appendix C.3, Lemma L, lines 1835--1858.
-/

open MPTensor

open scoped Matrix BigOperators

namespace MPSTensor

variable {α : Type*} [Fintype α] [DecidableEq α] {D : ℕ}

/-- The physical matrix induced on a block of length `L + 1` by a matrix on
its first letter.  On block words it is `Y ⊗ 1`.

This auxiliary construction is used to relate the block-injectivity argument
of arXiv:1606.00608, lines 318--345, to Appendix C.3, Lemma L,
lines 1835--1858. -/
noncomputable def firstSiteActionOnBlock (L : ℕ) (Y : Matrix α α ℂ) :
    Matrix (Fin (L + 1) → α) (Fin (L + 1) → α) ℂ :=
  fun I J =>
    Y (I 0) (J 0) *
      if (fun k : Fin L => I k.succ) = (fun k : Fin L => J k.succ) then 1 else 0

omit [DecidableEq α] in
/-- The all-length first-site identity is equivalent to equality of the trace
pairings obtained by inserting the two physical matrices before an arbitrary
word.

Source: arXiv:1606.00608, Appendix C.3, Lemma L, lines 1835--1847. -/
theorem firstSiteActionAgree_iff_trace (A : MPTensor α (Fin D))
    (Y Z : Matrix α α ℂ) :
    FirstSiteActionAgree A Y Z ↔
      ∀ (L : ℕ) (s : α) (w : Fin L → α),
        Matrix.trace (insertedTensor Y A s * Kraus.evalWord A (List.ofFn w)) =
          Matrix.trace (insertedTensor Z A s * Kraus.evalWord A (List.ofFn w)) := by
  constructor
  · intro h L s w
    have h' := h L (Fin.cons s w)
    simpa [FirstSiteActionAgree, mpv, coeff, List.ofFn_succ, Fin.cons_zero,
      Fin.cons_succ, insertedTensor, Finset.sum_mul, Matrix.trace_sum,
      Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul] using h'
  · intro h L σ
    have h' := h L (σ 0) (σ ∘ Fin.succ)
    simpa [FirstSiteActionAgree, mpv, coeff, List.ofFn_succ, Fin.cons_zero,
      Fin.cons_succ, insertedTensor, Finset.sum_mul, Matrix.trace_sum,
      Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Function.comp_def] using h'

omit [DecidableEq α] in
/-- The trace-pairing form of a first-site identity for an arbitrary finite
word. -/
theorem FirstSiteActionAgree.trace_evalWord {A : MPTensor α (Fin D)}
    {Y Z : Matrix α α ℂ} (h : FirstSiteActionAgree A Y Z)
    (s : α) (w : List α) :
    Matrix.trace (insertedTensor Y A s * Kraus.evalWord A w) =
      Matrix.trace (insertedTensor Z A s * Kraus.evalWord A w) := by
  simpa using (firstSiteActionAgree_iff_trace A Y Z).mp h w.length s w.get

/-- Inserting the induced first-site action into a blocked tensor inserts the
original matrix before the word carried by the remaining letters of the
block.

This auxiliary identity is used to relate the block-injectivity argument of
arXiv:1606.00608, lines 318--345, to Appendix C.3, Lemma L,
lines 1835--1858. -/
theorem insertedTensor_firstSiteActionOnBlock_block
    (A : MPTensor α (Fin D)) (L : ℕ) (Y : Matrix α α ℂ) (I : Fin (L + 1) → α) :
    insertedTensor (firstSiteActionOnBlock L Y) (Kraus.block A (L + 1)) I =
      insertedTensor Y A (I 0) *
        Kraus.evalWord A (List.ofFn fun k : Fin L => I k.succ) := by
  classical
  rw [insertedTensor]
  rw [← (Fin.consEquiv (fun _ : Fin (L + 1) => α)).sum_comp]
  rw [Fintype.sum_prod_type]
  rw [insertedTensor, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Fintype.sum_eq_single (fun k : Fin L => I k.succ)]
  · simp [firstSiteActionOnBlock, List.ofFn_succ, Kraus.evalWord_cons]
  · intro w hw
    simp only [Fin.consEquiv_apply, firstSiteActionOnBlock, Fin.cons_zero, Fin.cons_succ]
    rw [ite_eq_right]
    · simp
    · exact fun h => hw h.symm

/-- A first-site action identity remains valid after physical blocking when
the action on each block is induced from its first letter.

This auxiliary transport is used to relate the block-injectivity argument of
arXiv:1606.00608, lines 318--345, to Appendix C.3, Lemma L,
lines 1835--1858. -/
theorem FirstSiteActionAgree.block {A : MPTensor α (Fin D)}
    {Y Z : Matrix α α ℂ} (h : FirstSiteActionAgree A Y Z) (L : ℕ) :
    FirstSiteActionAgree (Kraus.block A (L + 1))
      (firstSiteActionOnBlock L Y) (firstSiteActionOnBlock L Z) := by
  rw [firstSiteActionAgree_iff_trace]
  intro N I w
  rw [insertedTensor_firstSiteActionOnBlock_block,
    insertedTensor_firstSiteActionOnBlock_block]
  simp only [Kraus.evalWord_block, Matrix.mul_assoc, ← Kraus.evalWord_append]
  exact h.trace_evalWord (I 0)
    (List.ofFn (fun k : Fin L => I k.succ) ++ (List.ofFn w).flatMap List.ofFn)

/-- Equality of the induced insertions on a block of length `L + 1` implies
equality of the original insertions when the remaining length-`L` words span
the full matrix algebra.

This supporting statement combines the block-injectivity result of
arXiv:1606.00608, lines 318--345, with the insertion in Lemma L.  It uses no
normalization or positivity hypothesis.

Source context: arXiv:1606.00608, lines 318--345 and Appendix C.3,
Lemma L, lines 1848--1858. -/
theorem insertedTensor_eq_of_firstSiteActionOnBlock_block_eq
    (A : MPTensor α (Fin D)) (L : ℕ) (hInj : Kraus.IsNBlkInjective A L)
    {Y Z : Matrix α α ℂ}
    (hEq :
      insertedTensor (firstSiteActionOnBlock L Y) (Kraus.block A (L + 1)) =
        insertedTensor (firstSiteActionOnBlock L Z) (Kraus.block A (L + 1))) :
    insertedTensor Y A = insertedTensor Z A := by
  funext s
  apply sub_eq_zero.mp
  let Δ := insertedTensor Y A s - insertedTensor Z A s
  change Δ = 0
  have hzero : ∀ w : Fin L → α, Δ * Kraus.evalWord A (List.ofFn w) = 0 := by
    intro w
    have hI := congrFun hEq (Fin.cons s w)
    rw [insertedTensor_firstSiteActionOnBlock_block,
      insertedTensor_firstSiteActionOnBlock_block] at hI
    simp only [Fin.cons_zero, Fin.cons_succ] at hI
    dsimp [Δ]
    rw [Matrix.sub_mul, hI, sub_self]
  have hzero_span : ∀ M ∈ Submodule.span ℂ
      (Set.range fun w : Fin L → α => Kraus.evalWord A (List.ofFn w)), Δ * M = 0 := by
    apply Submodule.span_induction
    · intro M hM
      obtain ⟨w, rfl⟩ := hM
      exact hzero w
    · simp
    · intro M N _ _ hM hN
      simp [Matrix.mul_add, hM, hN]
    · intro c M _ hM
      simp [hM]
  have hspan : Submodule.span ℂ
      (Set.range fun w : Fin L → α => Kraus.evalWord A (List.ofFn w)) = ⊤ := by
    exact hInj.span_eq_top
  have hOne : Δ * (1 : Matrix (Fin D) (Fin D) ℂ) = 0 :=
    hzero_span 1 (hspan.symm ▸ Submodule.mem_top)
  simpa using hOne

end MPSTensor
