/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Finite simultaneous MPS word spans and gauge transport

This module defines the fixed-length tuple of word evaluations for a block family and proves
that spanning the product of the block matrix algebras is invariant under an independent
invertible virtual gauge in every block.  The gauges need not be unitary.

The nonunitary form is needed in the normalization route for the block-separation argument of
Pérez-García--Verstraete--Wolf--Cirac: one may establish the BNT separation certificate after
gauging each block to a left-canonical prepared representative, then transport that certificate
back to the source unital gauge carrying its positive dual fixed point.  This transport is only
one ingredient of that route; it does not by itself remove the remaining normalization
hypotheses from the parent-Hamiltonian theorem.

## Main definitions

* `wordTuple` — simultaneous length-`L` word evaluation in every block.
* `WordTupleSpanTop` — the tuples span the full product matrix algebra.

## Main results

* `wordTupleSpanTop_eventually_of_wordTupleSpanTop_period_window` — a finite residue
  window and a positive full-span period give eventual full spans.
* `block_matrices_eq_zero_of_wordTupleSpanTop_trace` — trace separation from a full
  simultaneous span.
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

/-- The tuple-valued span of word evaluations is closed under pointwise matrix
multiplication, at the cost of adding word lengths. -/
theorem pointwise_mul_mem_span_wordTuple_add
    (A : (k : Fin r) → MPSTensor d (dim k))
    {L S : ℕ}
    {M N : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ}
    (hM : M ∈ Submodule.span ℂ (Set.range (wordTuple A L)))
    (hN : N ∈ Submodule.span ℂ (Set.range (wordTuple A S))) :
    (fun k : Fin r => M k * N k) ∈
      Submodule.span ℂ (Set.range (wordTuple A (L + S))) := by
  classical
  let spanLS : Submodule ℂ ((k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ) :=
    Submodule.span ℂ (Set.range (wordTuple A (L + S)))
  have hleft_gen : ∀ u : Fin L → Fin d,
      (fun k : Fin r => wordTuple A L u k * N k) ∈ spanLS := by
    intro u
    induction hN using Submodule.span_induction with
    | mem N hNmem =>
        rcases hNmem with ⟨v, rfl⟩
        have hEq : (fun k : Fin r => wordTuple A L u k * wordTuple A S v k) =
            wordTuple A (L + S) (Fin.append u v) := by
          funext k
          simp [wordTuple, List.ofFn_fin_append, evalWord_append]
        rw [hEq]
        exact Submodule.subset_span ⟨Fin.append u v, rfl⟩
    | zero =>
        have hzero : (fun k : Fin r =>
            wordTuple A L u k *
              (0 : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ) k) = 0 := by
          funext k
          simp
        rw [hzero]
        exact Submodule.zero_mem _
    | add N₁ N₂ _ _ hN₁ hN₂ =>
        have hEq : (fun k : Fin r => wordTuple A L u k * (N₁ + N₂) k) =
            (fun k : Fin r => wordTuple A L u k * N₁ k) +
              (fun k : Fin r => wordTuple A L u k * N₂ k) := by
          funext k
          simp [Matrix.mul_add]
        rw [hEq]
        exact Submodule.add_mem _ hN₁ hN₂
    | smul a N _ hN =>
        have hEq : (fun k : Fin r => wordTuple A L u k * (a • N) k) =
            a • (fun k : Fin r => wordTuple A L u k * N k) := by
          funext k
          simp
        rw [hEq]
        exact Submodule.smul_mem _ a hN
  induction hM using Submodule.span_induction with
  | mem M hMmem =>
      rcases hMmem with ⟨u, rfl⟩
      exact hleft_gen u
  | zero =>
      have hzero : (fun k : Fin r =>
          (0 : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ) k * N k) = 0 := by
        funext k
        simp
      rw [hzero]
      exact Submodule.zero_mem _
  | add M₁ M₂ _ _ hM₁ hM₂ =>
      have hEq : (fun k : Fin r => (M₁ + M₂) k * N k) =
          (fun k : Fin r => M₁ k * N k) +
            (fun k : Fin r => M₂ k * N k) := by
        funext k
        simp [Matrix.add_mul]
      rw [hEq]
      exact Submodule.add_mem _ hM₁ hM₂
  | smul a M _ hM =>
      have hEq : (fun k : Fin r => (a • M) k * N k) =
          a • (fun k : Fin r => M k * N k) := by
        funext k
        simp
      rw [hEq]
      exact Submodule.smul_mem _ a hM

/-- Homogeneous identity padding preserves the full word-tuple span.

If the length-\(L\) simultaneous word tuples span the full product algebra, and
the simultaneous identity tuple lies in the length-\(S\) word-tuple span, then
the length-\(L+S\) simultaneous word tuples also span the full product algebra.
-/
theorem wordTupleSpanTop_add_of_identity_mem_span_wordTuple
    (A : (k : Fin r) → MPSTensor d (dim k))
    {L S : ℕ}
    (hSpan : WordTupleSpanTop A L)
    (hId : (fun k : Fin r => (1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) ∈
      Submodule.span ℂ (Set.range (wordTuple A S))) :
    WordTupleSpanTop A (L + S) := by
  classical
  unfold WordTupleSpanTop at hSpan ⊢
  apply eq_top_iff.mpr
  intro M _
  have hM : M ∈ Submodule.span ℂ (Set.range (wordTuple A L)) := by
    rw [hSpan]
    exact Submodule.mem_top
  have hmul := pointwise_mul_mem_span_wordTuple_add A hM hId
  have hprod :
      (fun k : Fin r =>
        M k * (fun k : Fin r => (1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) k) = M := by
    funext k
    simp
  simpa [hprod] using hmul

/-- Two homogeneous full word-tuple spans compose by concatenating words. -/
theorem wordTupleSpanTop_add_of_wordTupleSpanTop
    (A : (k : Fin r) → MPSTensor d (dim k))
    {L S : ℕ}
    (hSpanL : WordTupleSpanTop A L)
    (hSpanS : WordTupleSpanTop A S) :
    WordTupleSpanTop A (L + S) := by
  apply wordTupleSpanTop_add_of_identity_mem_span_wordTuple A hSpanL
  unfold WordTupleSpanTop at hSpanS
  rw [hSpanS]
  exact Submodule.mem_top

/-- A full homogeneous word-tuple span at one period extends any full base
length along the arithmetic progression obtained by adding that period. -/
theorem wordTupleSpanTop_add_mul_of_wordTupleSpanTop
    (A : (k : Fin r) → MPSTensor d (dim k))
    {base period : ℕ}
    (hbase : WordTupleSpanTop A base)
    (hperiod : WordTupleSpanTop A period) :
    ∀ q : ℕ, WordTupleSpanTop A (base + q * period)
  | 0 => by
      simpa using hbase
  | q + 1 => by
      have hq : WordTupleSpanTop A (base + q * period) :=
        wordTupleSpanTop_add_mul_of_wordTupleSpanTop A hbase hperiod q
      have hstep := wordTupleSpanTop_add_of_wordTupleSpanTop A hq hperiod
      simpa [Nat.succ_mul, Nat.add_assoc] using hstep

/-- A finite residue window of full homogeneous word-tuple spans, together with
one positive period, gives full homogeneous word-tuple spans at every
sufficiently large length. -/
theorem wordTupleSpanTop_eventually_of_wordTupleSpanTop_period_window
    (A : (k : Fin r) → MPSTensor d (dim k))
    {start period : ℕ} (hperiod_pos : 0 < period)
    (hperiod : WordTupleSpanTop A period)
    (hwindow : ∀ residue : ℕ, residue < period → WordTupleSpanTop A (start + residue)) :
    ∃ L : ℕ, ∀ n : ℕ, n ≥ L → WordTupleSpanTop A n := by
  refine ⟨start, ?_⟩
  intro n hn
  let residue := (n - start) % period
  let quotient := (n - start) / period
  have hresidue : residue < period := by
    exact Nat.mod_lt _ hperiod_pos
  have hbase : WordTupleSpanTop A (start + residue) :=
    hwindow residue hresidue
  have hpad : WordTupleSpanTop A (start + residue + quotient * period) :=
    wordTupleSpanTop_add_mul_of_wordTupleSpanTop A hbase hperiod quotient
  have hlen : start + residue + quotient * period = n := by
    dsimp [residue, quotient]
    rw [Nat.add_assoc]
    rw [Nat.mul_comm ((n - start) / period) period]
    rw [Nat.mod_add_div]
    exact Nat.add_sub_of_le hn
  rw [← hlen]
  exact hpad

/-- If simultaneous word evaluations span the product algebra, then a block
matrix family whose trace pairing vanishes on those word evaluations is zero. -/
theorem block_matrices_eq_zero_of_wordTupleSpanTop_trace
    (A : (k : Fin r) → MPSTensor d (dim k))
    {L : ℕ} (hSpan : WordTupleSpanTop A L)
    (Δ : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ)
    (hΔ : ∀ w : Fin L → Fin d,
      (∑ k : Fin r, Matrix.trace (Δ k * evalWord (A k) (List.ofFn w))) = 0) :
    ∀ k, Δ k = 0 := by
  classical
  have hZeroOnSpan :
      ∀ M : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ,
        M ∈ Submodule.span ℂ (Set.range (wordTuple A L)) →
        (∑ k : Fin r, Matrix.trace (Δ k * M k)) = 0 := by
    intro M hM
    exact Submodule.span_induction (p := fun x _ =>
        (∑ k : Fin r, Matrix.trace (Δ k * x k)) = 0)
      (fun x hx => by
        rcases hx with ⟨w, rfl⟩
        simpa [wordTuple] using hΔ w)
      (by simp)
      (fun x y hx hy hxzero hyzero => by
        simp [Matrix.mul_add, Matrix.trace_add, hxzero, hyzero, Finset.sum_add_distrib])
      (fun a x hx hxzero => by
        simpa [Pi.smul_apply, Matrix.mul_smul, Matrix.trace_smul, Finset.mul_sum] using
          congrArg (fun z : ℂ => a * z) hxzero)
      hM
  intro k
  apply (Matrix.ext_iff_trace_mul_right (A := Δ k) (B := 0)).2
  intro N
  have hsum := hZeroOnSpan (Function.update 0 k N) (by
    rw [hSpan]
    exact Submodule.mem_top)
  rw [Finset.sum_eq_single k
      (fun j _ hj => by
        rw [Function.update_of_ne hj, Pi.zero_apply, mul_zero, Matrix.trace_zero])
      (fun hk => absurd (Finset.mem_univ k) hk),
    Function.update_self] at hsum
  simpa using hsum

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
