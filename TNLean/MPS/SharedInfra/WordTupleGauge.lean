/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Gauge transport for simultaneous MPS word spans

This module defines the fixed-length tuple of word evaluations for a block family and proves
that spanning the product of the block matrix algebras is invariant under an independent
invertible virtual gauge in every block.  The gauges need not be unitary.

The nonunitary form is needed in the normalization route for the block-separation argument of
Pérez-García--Verstraete--Wolf--Cirac: one may establish the BNT separation certificate after
gauging each block to a left-canonical prepared representative, then transport that certificate
back to the source unital gauge carrying its positive dual fixed point.  This transport is only
one ingredient of that route; it does not by itself remove the remaining normalization
hypotheses from the parent-Hamiltonian theorem.

## Main declarations

* `wordTuple` — simultaneous length-`L` word evaluation in every block.
* `WordTupleSpanTop` — the tuples span the full product matrix algebra.
* `wordTupleSpanTop_iff_of_family_gaugeEquiv` — invariance under blockwise invertible gauges.

## References

* Pérez-García, Verstraete, Wolf, Cirac, quant-ph/0608197, lines 742--763 and 1424--1456.
* Cirac, Pérez-García, Schuch, Verstraete, arXiv:1606.00608, lines 317--345.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ} {r : ℕ} {dim : Fin r → ℕ}

/-- The tuple of length-`L` word evaluations across all blocks. -/
def wordTuple
    (A : (k : Fin r) → MPSTensor d (dim k))
    (L : ℕ) (w : Fin L → Fin d) :
    (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ :=
  fun k => evalWord (A k) (List.ofFn w)

/-- Finite-length span condition on the product algebra of block matrices. -/
def WordTupleSpanTop
    (A : (k : Fin r) → MPSTensor d (dim k))
    (L : ℕ) : Prop :=
  Submodule.span ℂ (Set.range (wordTuple A L)) = ⊤

/-- Reindexing the common physical alphabet by an equivalence preserves the
simultaneous word-tuple span.

This is the index transport used in the simultaneous BNT blocking of
arXiv:1606.00608, lines 317--345. -/
theorem wordTupleSpanTop_reindexPhysical_equiv {d' : ℕ}
    (e : Fin d' ≃ Fin d) (A : (k : Fin r) → MPSTensor d (dim k)) (L : ℕ) :
    WordTupleSpanTop (fun k ↦ reindexPhysical e (A k)) L ↔
      WordTupleSpanTop A L := by
  unfold WordTupleSpanTop
  have hRange :
      Set.range (wordTuple (fun k ↦ reindexPhysical e (A k)) L) =
        Set.range (wordTuple A L) := by
    ext X
    constructor
    · rintro ⟨w, rfl⟩
      refine ⟨fun i ↦ e (w i), ?_⟩
      funext k
      simp [wordTuple, evalWord_reindexPhysical, List.map_ofFn,
        Function.comp_def]
    · rintro ⟨w, rfl⟩
      refine ⟨fun i ↦ e.symm (w i), ?_⟩
      funext k
      simp [wordTuple, evalWord_reindexPhysical, List.map_ofFn,
        Function.comp_def]
  rw [hRange]

/-- A full simultaneous word-tuple span is preserved by independent invertible
virtual gauges in the blocks; no gauge is assumed unitary.

This is the forward transport used to pass a BNT separation certificate from one
normalization to another while preserving the block-family indices and bond dimensions.
In the PGVWC07 normalization route it transports the certificate from a left-canonical
prepared family back to the source unital/dual-fixed-point gauge. -/
theorem wordTupleSpanTop_of_family_gaugeEquiv
    {A B : (j : Fin r) → MPSTensor d (dim j)} {L : ℕ}
    (hSpan : WordTupleSpanTop A L)
    (hGauge : ∀ j, GaugeEquiv (A j) (B j)) :
    WordTupleSpanTop B L := by
  classical
  choose X hX using hGauge
  unfold WordTupleSpanTop at hSpan ⊢
  apply top_unique
  intro M _
  let M' : (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ := fun j =>
    (↑((X j)⁻¹) : Matrix _ _ ℂ) * M j * (X j : Matrix _ _ ℂ)
  have hM' : M' ∈ Submodule.span ℂ (Set.range (wordTuple A L)) := by
    rw [hSpan]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hM'
  apply (Submodule.mem_span_range_iff_exists_fun ℂ).2
  refine ⟨c, ?_⟩
  funext j
  have hcj : (∑ w, c w • evalWord (A j) (List.ofFn w)) = M' j := by
    simpa [wordTuple, Fintype.linearCombination_apply] using congrFun hc j
  have hGoal : (∑ w, c w • evalWord (B j) (List.ofFn w)) = M j := by
    calc
      (∑ w, c w • evalWord (B j) (List.ofFn w)) =
          ∑ w, c w • ((X j : Matrix _ _ ℂ) *
            evalWord (A j) (List.ofFn w) *
            (↑((X j)⁻¹) : Matrix _ _ ℂ)) := by
        apply Finset.sum_congr rfl
        intro w _
        rw [evalWord_gauge (X j) (hX j)]
      _ = (X j : Matrix _ _ ℂ) *
          (∑ w, c w • evalWord (A j) (List.ofFn w)) *
          (↑((X j)⁻¹) : Matrix _ _ ℂ) := by
        rw [Matrix.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro w _
        simp
      _ = (X j : Matrix _ _ ℂ) * M' j *
          (↑((X j)⁻¹) : Matrix _ _ ℂ) := by rw [hcj]
      _ = M j := by simp [M', Matrix.mul_assoc]
  simpa [wordTuple] using hGoal

/-- A full simultaneous word-tuple span can be transported against a given
blockwise invertible gauge relation.

This is the directional form used when the certificate is known in the target gauge and is
needed in the source gauge carrying the PGVWC07 positive dual fixed point. -/
theorem wordTupleSpanTop_of_family_gaugeEquiv_symm
    {A B : (j : Fin r) → MPSTensor d (dim j)} {L : ℕ}
    (hSpan : WordTupleSpanTop B L)
    (hGauge : ∀ j, GaugeEquiv (A j) (B j)) :
    WordTupleSpanTop A L :=
  wordTupleSpanTop_of_family_gaugeEquiv hSpan (fun j ↦ (hGauge j).symm)

/-- Simultaneous fixed-length word tuples span the product matrix algebra before a
blockwise invertible gauge change if and only if they span it afterwards.

The equivalence is nonunitary and preserves the original block-family indexing and every
block bond dimension.  It supports transport between a left-canonical prepared gauge and
the source unital/dual-fixed-point gauge in the PGVWC07 separation argument; further
normalization-dependent parent-Hamiltonian steps remain separate. -/
theorem wordTupleSpanTop_iff_of_family_gaugeEquiv
    {A B : (j : Fin r) → MPSTensor d (dim j)} {L : ℕ}
    (hGauge : ∀ j, GaugeEquiv (A j) (B j)) :
    WordTupleSpanTop A L ↔ WordTupleSpanTop B L :=
  ⟨fun hSpan ↦ wordTupleSpanTop_of_family_gaugeEquiv hSpan hGauge,
    fun hSpan ↦ wordTupleSpanTop_of_family_gaugeEquiv_symm hSpan hGauge⟩

end MPSTensor
