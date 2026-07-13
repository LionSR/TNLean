/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.Blocking
import TNLean.MPS.MPDO.VerticalCF

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
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- The physical matrix induced on a block of length `L + 1` by a matrix on
its first letter.  In decoded coordinates it is `Y ⊗ 1`.

This auxiliary construction is used to relate the block-injectivity argument
of arXiv:1606.00608, lines 318--345, to Appendix C.3, Lemma L,
lines 1835--1858. -/
noncomputable def firstSiteActionOnBlock (L : ℕ)
    (Y : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin (blockPhysDim d (L + 1))) (Fin (blockPhysDim d (L + 1))) ℂ :=
  fun I J =>
    Y (decodeBlock d (L + 1) I 0) (decodeBlock d (L + 1) J 0) *
      if (fun k : Fin L => decodeBlock d (L + 1) I k.succ) =
          (fun k : Fin L => decodeBlock d (L + 1) J k.succ) then 1 else 0

/-- The all-length first-site identity is equivalent to equality of the trace
pairings obtained by inserting the two physical matrices before an arbitrary
word.

Source: arXiv:1606.00608, Appendix C.3, Lemma L, lines 1835--1847. -/
theorem firstSiteActionAgree_iff_trace (A : MPSTensor d D)
    (Y Z : Matrix (Fin d) (Fin d) ℂ) :
    FirstSiteActionAgree A Y Z ↔
      ∀ (L : ℕ) (s : Fin d) (w : Fin L → Fin d),
        Matrix.trace (insertedTensor Y A s * evalWord A (List.ofFn w)) =
          Matrix.trace (insertedTensor Z A s * evalWord A (List.ofFn w)) := by
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

/-- The trace-pairing form of a first-site identity for an arbitrary finite
word. -/
theorem FirstSiteActionAgree.trace_evalWord {A : MPSTensor d D}
    {Y Z : Matrix (Fin d) (Fin d) ℂ} (h : FirstSiteActionAgree A Y Z)
    (s : Fin d) (w : List (Fin d)) :
    Matrix.trace (insertedTensor Y A s * evalWord A w) =
      Matrix.trace (insertedTensor Z A s * evalWord A w) := by
  simpa using (firstSiteActionAgree_iff_trace A Y Z).mp h w.length s w.get

/-- Inserting the induced first-site action into a blocked tensor inserts the
original matrix before the word carried by the remaining letters of the
block.

This auxiliary identity is used to relate the block-injectivity argument of
arXiv:1606.00608, lines 318--345, to Appendix C.3, Lemma L,
lines 1835--1858. -/
theorem insertedTensor_firstSiteActionOnBlock_blockTensor
    (A : MPSTensor d D) (L : ℕ) (Y : Matrix (Fin d) (Fin d) ℂ)
    (I : Fin (blockPhysDim d (L + 1))) :
    insertedTensor (firstSiteActionOnBlock L Y) (blockTensor A (L + 1)) I =
      insertedTensor Y A (decodeBlock d (L + 1) I 0) *
        evalWord A
          (List.ofFn fun k : Fin L => decodeBlock d (L + 1) I k.succ) := by
  classical
  rw [insertedTensor]
  rw [← Equiv.sum_comp (decodeBlockEquiv d (L + 1)).symm
    (fun J : Fin (blockPhysDim d (L + 1)) =>
      firstSiteActionOnBlock L Y I J • blockTensor A (L + 1) J)]
  rw [← (Fin.consEquiv (fun _ : Fin (L + 1) => Fin d)).sum_comp]
  rw [Fintype.sum_prod_type]
  rw [insertedTensor, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Fintype.sum_eq_single
    (fun k : Fin L => decodeBlock d (L + 1) I k.succ)]
  · simp [firstSiteActionOnBlock, blockTensor, wordOfBlock, List.ofFn_succ,
      evalWord_cons]
  · intro w hw
    simp only [Fin.consEquiv_apply, firstSiteActionOnBlock,
      decodeBlock_decodeBlockEquiv_symm, Fin.cons_zero, Fin.cons_succ]
    rw [if_neg]
    · simp
    · exact fun h => hw h.symm

/-- A first-site action identity remains valid after physical blocking when
the action on each block is induced from its first letter.

This auxiliary transport is used to relate the block-injectivity argument of
arXiv:1606.00608, lines 318--345, to Appendix C.3, Lemma L,
lines 1835--1858. -/
theorem FirstSiteActionAgree.blockTensor {A : MPSTensor d D}
    {Y Z : Matrix (Fin d) (Fin d) ℂ} (h : FirstSiteActionAgree A Y Z)
    (L : ℕ) :
    FirstSiteActionAgree (blockTensor A (L + 1))
      (firstSiteActionOnBlock L Y) (firstSiteActionOnBlock L Z) := by
  rw [firstSiteActionAgree_iff_trace]
  intro N I w
  rw [insertedTensor_firstSiteActionOnBlock_blockTensor,
    insertedTensor_firstSiteActionOnBlock_blockTensor]
  simp only [evalWord_blockTensor, Matrix.mul_assoc, ← evalWord_append]
  exact h.trace_evalWord (decodeBlock d (L + 1) I 0)
    (List.ofFn (fun k : Fin L => decodeBlock d (L + 1) I k.succ) ++
      flattenBlockedWord d (L + 1) (List.ofFn w))

/-- Equality of the induced insertions on a block of length `L + 1` implies
equality of the original insertions when the remaining length-`L` words span
the full matrix algebra.

This supporting statement combines the block-injectivity result of
arXiv:1606.00608, lines 318--345, with the insertion in Lemma L.  It uses no
normalization or positivity hypothesis.

Source context: arXiv:1606.00608, lines 318--345 and Appendix C.3,
Lemma L, lines 1848--1858. -/
theorem insertedTensor_eq_of_firstSiteActionOnBlock_blockTensor_eq
    (A : MPSTensor d D) (L : ℕ) (hInj : IsNBlkInjective A L)
    {Y Z : Matrix (Fin d) (Fin d) ℂ}
    (hEq :
      insertedTensor (firstSiteActionOnBlock L Y) (blockTensor A (L + 1)) =
        insertedTensor (firstSiteActionOnBlock L Z) (blockTensor A (L + 1))) :
    insertedTensor Y A = insertedTensor Z A := by
  funext s
  apply sub_eq_zero.mp
  let Δ := insertedTensor Y A s - insertedTensor Z A s
  change Δ = 0
  have hzero : ∀ w : Fin L → Fin d, Δ * evalWord A (List.ofFn w) = 0 := by
    intro w
    let I : Fin (blockPhysDim d (L + 1)) :=
      (decodeBlockEquiv d (L + 1)).symm (Fin.cons s w)
    have hI := congrFun hEq I
    rw [insertedTensor_firstSiteActionOnBlock_blockTensor,
      insertedTensor_firstSiteActionOnBlock_blockTensor] at hI
    have hdecode : decodeBlock d (L + 1) I = Fin.cons s w := by
      exact decodeBlock_decodeBlockEquiv_symm d (L + 1) (Fin.cons s w)
    have hfirst : decodeBlock d (L + 1) I 0 = s := by
      rw [hdecode]
      simp
    have htail : (fun k : Fin L => decodeBlock d (L + 1) I k.succ) = w := by
      funext k
      rw [hdecode]
      simp
    rw [hfirst, htail] at hI
    dsimp [Δ]
    rw [Matrix.sub_mul, hI, sub_self]
  have hzero_span : ∀ M ∈ Submodule.span ℂ
      (Set.range fun w : Fin L → Fin d => evalWord A (List.ofFn w)), Δ * M = 0 := by
    apply Submodule.span_induction
    · intro M hM
      obtain ⟨w, rfl⟩ := hM
      exact hzero w
    · simp
    · intro M N _ _ hM hN
      simp [Matrix.mul_add, hM, hN]
    · intro c M _ hM
      simp [hM]
  have hOne : Δ * (1 : Matrix (Fin D) (Fin D) ℂ) = 0 :=
    hzero_span 1 (hInj.symm ▸ Submodule.mem_top)
  simpa using hOne

end MPSTensor
