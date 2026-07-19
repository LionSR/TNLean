/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BiCFDerivation.Selectors
import TNLean.MPS.RFP.ResidualIsometry

/-!
# One-site spans from residual isometries

This file connects the residual-isometry equations for a finite family of
matrix product tensors to the simultaneous one-site matrix span of that family.

The residual equations are the statement that the scalar one-site entry
vectors, indexed by the block label and the two virtual indices, have identity
Gram matrix. Consequently these vectors are linearly independent, and the
one-site word tuples span the product of the block matrix algebras.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ}

private theorem IsResidualIsometryFamily.wordEntryFamily_one_gram
    {U : (j : Fin r) → MPSTensor d (dim j)}
    (hU : IsResidualIsometryFamily U) (x y : BlockEntryIndex dim) :
    ∑ w : Fin 1 → Fin d,
      wordEntryFamily U 1 x w * star (wordEntryFamily U 1 y w) =
        if x = y then 1 else 0 := by
  classical
  rcases x with ⟨j, α, β⟩
  rcases y with ⟨j', α', β'⟩
  rw [← Equiv.sum_comp (Equiv.funUnique (Fin 1) (Fin d)).symm
    (fun w : Fin 1 → Fin d ↦
      wordEntryFamily U 1 ⟨j, (α, β)⟩ w *
        star (wordEntryFamily U 1 ⟨j', (α', β')⟩ w))]
  simp only [wordEntryFamily, blockEntryValue, wordTuple,
    Equiv.funUnique_symm_apply, List.ofFn_succ, List.ofFn_zero,
    evalWord_cons, evalWord_nil, mul_one, uniqueElim_const]
  by_cases hj : j = j'
  · subst j'
    rw [hU.1]
    simp
  · rw [hU.2 j j' hj α β α' β']
    simp [hj]

/-- The one-site scalar entry vectors of a residual-isometry family are
linearly independent. Their Gram matrix is the identity by the residual
equations in arXiv:1606.00608, eq:III_isometry (line 551). -/
theorem IsResidualIsometryFamily.wordEntryFamily_linearIndependent
    {U : (j : Fin r) → MPSTensor d (dim j)}
    (hU : IsResidualIsometryFamily U) :
    LinearIndependent ℂ (wordEntryFamily U 1) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc x
  have hcoeff (w : Fin 1 → Fin d) :
      ∑ y : BlockEntryIndex dim, c y * wordEntryFamily U 1 y w = 0 := by
    simpa [Finset.sum_apply, Pi.smul_apply] using congrFun hc w
  calc
    c x = ∑ y : BlockEntryIndex dim, c y * (if y = x then 1 else 0) := by
      simp
    _ = ∑ y : BlockEntryIndex dim, c y *
        (∑ w : Fin 1 → Fin d,
          wordEntryFamily U 1 y w * star (wordEntryFamily U 1 x w)) := by
      apply Finset.sum_congr rfl
      intro y _
      rw [hU.wordEntryFamily_one_gram y x]
    _ = 0 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro w _
      simp_rw [← mul_assoc]
      rw [← Finset.sum_mul, hcoeff w, zero_mul]

/-- A residual-isometry family spans the product of its block matrix algebras
with one-site word tuples. This is the simultaneous one-site span consequence
of arXiv:1606.00608, eq:III_isometry (line 551). -/
theorem IsResidualIsometryFamily.wordTupleSpanTop_one
    {U : (j : Fin r) → MPSTensor d (dim j)}
    (hU : IsResidualIsometryFamily U) :
    WordTupleSpanTop U 1 :=
  wordTupleSpanTop_of_wordEntryFamily_linearIndependent U
    hU.wordEntryFamily_linearIndependent

/-- Simultaneous one-site word spanning is preserved by invertible left and
right multiplication in each block. -/
theorem wordTupleSpanTop_one_of_blockwise_mul
    (A B : (j : Fin r) → MPSTensor d (dim j))
    (L R : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hL : ∀ j, (L j).det ≠ 0) (hR : ∀ j, (R j).det ≠ 0)
    (hB : ∀ j i, B j i = L j * A j i * R j)
    (hSpan : WordTupleSpanTop A 1) :
    WordTupleSpanTop B 1 := by
  classical
  unfold WordTupleSpanTop at hSpan ⊢
  apply top_unique
  intro M _
  let N : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ :=
    fun j ↦ (L j)⁻¹ * M j * (R j)⁻¹
  have hN : N ∈ Submodule.span ℂ (Set.range (wordTuple A 1)) := by
    rw [hSpan]
    exact Submodule.mem_top
  have hTN : (fun j ↦ L j * N j * R j) ∈
      Submodule.span ℂ (Set.range (wordTuple B 1)) := by
    refine Submodule.span_induction
      (p := fun Z _ ↦ (fun j ↦ L j * Z j * R j) ∈
        Submodule.span ℂ (Set.range (wordTuple B 1))) ?_ ?_ ?_ ?_ hN
    · rintro Z ⟨w, rfl⟩
      apply Submodule.subset_span
      refine ⟨w, ?_⟩
      funext j
      simp [wordTuple, hB]
    · convert
        (Submodule.zero_mem (Submodule.span ℂ (Set.range (wordTuple B 1)))) using 1
      funext j
      simp
    · intro X Y _ _ hX hY
      convert
        Submodule.add_mem (Submodule.span ℂ (Set.range (wordTuple B 1))) hX hY using 1
      funext j
      simp [mul_add, add_mul]
    · intro a X _ hX
      convert
        Submodule.smul_mem (Submodule.span ℂ (Set.range (wordTuple B 1))) a hX using 1
      funext j
      simp
  convert hTN using 1
  funext j
  simp only [N]
  symm
  calc
    L j * ((L j)⁻¹ * M j * (R j)⁻¹) * R j =
        (L j * (L j)⁻¹) * M j * ((R j)⁻¹ * R j) := by
      noncomm_ring
    _ = M j := by
      rw [Matrix.mul_nonsing_inv (L j) (Ne.isUnit (hL j)),
        Matrix.nonsing_inv_mul (R j) (Ne.isUnit (hR j))]
      simp

/-- Under the whole-direct-sum renormalization-fixed-point hypotheses, the
one-site word tuples of the normal-tensor blocks span the product of their
matrix algebras. This is the span consequence of the residual isometry
condition in arXiv:1606.00608, eq:III_isometry (line 551) and Corollary
III.cor3 (line 584).

**Scope restriction (whole-tensor canonical form):** the hypotheses expose
normality, irreducibility, left canonical form, and gauge-phase distinctness
block by block. The passage from the paper's single canonical-form predicate
to these hypotheses is recorded in
docs/paper-gaps/cpsv16_rfp_isometry_scope.tex. -/
theorem wordTupleSpanTop_one_of_isTransferIdempotent_directSum
    [∀ k, NeZero (dim k)]
    (B : (k : Fin r) → MPSTensor d (dim k))
    (hnormal : ∀ k, IsNormal (B k))
    (hirr : ∀ k, IsIrreducibleTensor (B k))
    (hleft : ∀ k, ∑ i : Fin d, (B k i)ᴴ * B k i = 1)
    (hdist : ∀ j k : Fin r, j ≠ k → ∀ h : dim j = dim k,
      ¬ GaugePhaseEquiv (cast (congrArg (MPSTensor d) h) (B j)) (B k))
    (hRFP : IsTransferIdempotent (directSumTensor B)) :
    WordTupleSpanTop B 1 := by
  classical
  obtain ⟨X, Λ, U, hXdet, hΛpos, _, hdecomp, hU⟩ :=
    exists_residualIsometryFamily_of_isTransferIdempotent_directSum B
      hnormal hirr hleft hdist hRFP
  let D : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ :=
    fun j ↦ Matrix.diagonal (fun k ↦ (Real.sqrt (Λ j k) : ℂ))
  have hDdet : ∀ j, (D j).det ≠ 0 := by
    intro j
    rw [show D j = Matrix.diagonal
      (fun k ↦ (Real.sqrt (Λ j k) : ℂ)) from rfl,
      Matrix.det_diagonal, Finset.prod_ne_zero_iff]
    intro k _
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hΛpos j k)).ne'
  apply wordTupleSpanTop_one_of_blockwise_mul U B
    (fun j ↦ X j * D j) (fun j ↦ (X j)⁻¹)
  · intro j
    rw [Matrix.det_mul]
    exact mul_ne_zero (hXdet j) (hDdet j)
  · intro j
    exact (Matrix.isUnit_nonsing_inv_det (X j) (Ne.isUnit (hXdet j))).ne_zero
  · intro j i
    simpa only [D, Matrix.mul_assoc] using hdecomp j i
  · exact hU.wordTupleSpanTop_one

end MPSTensor
