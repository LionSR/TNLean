/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.TwoMarkerScalarRecovery
import TNLean.Algebra.TwoMarkerMiddleFactors
import QICLean.Algebra.LowFrequencyWordPartition
import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sum

/-!
# Common scalar recovery of a two-window polynomial

Low-frequency selectors assign each original ordered-word coefficient to
one pair of crossing positions and frequencies. A common monomial box then
gives scalar samples and weights before the operator family and every
polynomial of degree at most the supplied cutoff are chosen.

The finite index records both selected positions and their frequencies.
The recovery theorem keeps the distinguished operators unweighted and
preserves the order of all noncommuting factors. The cutoff may be zero;
the existence theorem requires a positive window half-width.

**Local fix (interpolation):** The recovery uses a spanning family of
evaluations and imposes no independence on coefficient operators. The
source distinction is recorded at:
https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf

This module contains supporting algebra for AKLV, arXiv:1301.1162v1,
Lemma l:agsp, lines 604–644, and ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1324–1333. No spatial, matrix product, rank,
sharp bond-dimension, or computational estimate is asserted.
-/

open scoped BigOperators

noncomputable section

namespace TNLean.MPS.AreaLaw

/-- The two selected crossing positions and two frequencies at most
`k / (2 * ell)`, as used in ALVV, arXiv:1602.08828v2, Proposition 5.7,
lines 1324–1333. -/
abbrev crossingFrequencyIndex (ell k : ℕ) :=
  Fin (2 * ell) × Fin (2 * ell) × Fin (k / (2 * ell) + 1) × Fin (k / (2 * ell) + 1)

open Classical in
/-- A bin selected by two labels and their frequencies is a weighted full-frequency slice.
The weight restricts the two chosen labels, while the slice fixes their frequencies.
ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
theorem frequency_bin_eq_weighted_slice
    {I M : Type*} [AddCommMonoid M] [Module ℂ M]
    (E : Finset (I → ℕ)) (left right : (I → ℕ) → I)
    (u v : I) (i j : ℕ) (coefficient : (I → ℕ) → M) :
    (∑ α ∈ E with ((left α, α (left α)), (right α, α (right α))) =
        ((u, i), (v, j)), coefficient α) =
      ∑ α ∈ E with α u = i ∧ α v = j,
        (if left α = u ∧ right α = v then (1 : ℂ) else 0) • coefficient α := by
  classical
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro α _
  by_cases hl : left α = u <;> by_cases hr : right α = v <;>
    simp [hl, hr, Prod.mk.injEq]

open Classical in
/-- The common degree cutoff and the selected-label mask give one partition
for every polynomial through degree `k`. The selectors precede the operator
family and all degrees; multiplication of operator factors is unchanged.
This combines the existing cutoff partition and frequency-bin identity from
ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333.
No MPO, source-sharp bond or running-time claim is included. -/
private theorem exists_common_two_window_polynomial_partition
    {ι A : Type*} [Fintype ι] [Semiring A] [Module ℂ A]
    (L R : Finset ι) (hL : L.Nonempty) (hR : R.Nonempty) :
    ∃ (pickL : (↥L → ℕ) → ↥L) (pickR : (↥R → ℕ) → ↥R),
      (∀ (a : ι → ℕ) (n : ℕ), (∑ x, a x) ≤ n →
        a (pickL (fun u : ↥L ↦ a u)) ≤ n / L.card ∧
        a (pickR (fun v : ↥R ↦ a v)) ≤ n / R.card) ∧
      ∀ (H : ι → A) (k : ℕ) (c : Fin (k + 1) → ℂ),
        let E := fun r : ℕ ↦ Finset.piAntidiag (Finset.univ : Finset ι) r
        let B := (L.product (Finset.range (k / L.card + 1))).product
          (R.product (Finset.range (k / R.card + 1)))
        let left := fun a : ι → ℕ ↦ pickL (fun u : ↥L ↦ a u)
        let right := fun a : ι → ℕ ↦ pickR (fun v : ↥R ↦ a v)
        let coefficient := fun (r : ℕ) (a : ι → ℕ) ↦
          ∑ w ∈ (Finset.univ : Finset (Fin r → ι)).filter
              (fun w ↦ (WordMultiplicity.countsFinsupp w : ι → ℕ) = a),
            (List.ofFn (fun t ↦ H (w t))).prod
        let slice := fun (t : (ι × ℕ) × (ι × ℕ)) (r : ℕ) ↦
          ∑ a ∈ E r with a t.1.1 = t.1.2 ∧ a t.2.1 = t.2.2,
            (if (left a : ι) = t.1.1 ∧ (right a : ι) = t.2.1
              then (1 : ℂ) else 0) • coefficient r a
        (∑ r : Fin (k + 1), c r • (∑ x, H x) ^ r.val) =
          ∑ t ∈ B, ∑ r : Fin (k + 1), c r • slice t r.val := by
  classical
  obtain ⟨pickL, pickR, hpick, hpartition⟩ :=
    Fintype.exists_two_window_word_coefficient_partition_of_le (𝓡 := A) L R hL hR
  refine ⟨pickL, pickR, hpick, ?_⟩
  intro H k c E B left right coefficient slice
  have hpower (r : Fin (k + 1)) : (∑ x, H x) ^ r.val = ∑ t ∈ B, slice t r.val := by
    have hpart := hpartition H k r.val (Nat.le_of_lt_succ r.isLt)
    change (∑ x, H x) ^ r.val = ∑ t ∈ B,
      ∑ a ∈ E r.val with
        (((left a : ι), a (left a)), ((right a : ι), a (right a))) = t,
          coefficient r.val a at hpart
    apply hpart.trans
    apply Finset.sum_congr rfl
    intro t _ht
    exact frequency_bin_eq_weighted_slice (E r.val)
      (fun a ↦ (left a : ι)) (fun a ↦ (right a : ι))
      t.1.1 t.2.1 t.1.2 t.2.2 (coefficient r.val)
  calc
    (∑ r : Fin (k + 1), c r • (∑ x, H x) ^ r.val) =
      ∑ r : Fin (k + 1), c r • (∑ t ∈ B, slice t r.val) := by
      apply Finset.sum_congr rfl
      intro r _hr
      exact congrArg (fun a : A ↦ c r • a) (hpower r)
    _ = _ := by
      simp_rw [Finset.smul_sum]
      exact Finset.sum_comm

/-- The raw two-window labels are precisely the finite crossing/frequency
indices used for the common operator family. Only finite sums are rearranged.
Supporting ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem sum_two_window_labels_eq_crossing_indices
    {M : Type*} [AddCommMonoid M] (ell k : ℕ)
    (f : ((Fin (2 * ell) ⊕ Fin (2 * ell)) ⊕ Fin 3) →
      ((Fin (2 * ell) ⊕ Fin (2 * ell)) ⊕ Fin 3) → ℕ → ℕ → M) :
    let eL : Fin (2 * ell) ↪ ((Fin (2 * ell) ⊕ Fin (2 * ell)) ⊕ Fin 3) :=
      ⟨fun p ↦ Sum.inl (Sum.inl p), fun _ _ h ↦ Sum.inl.inj (Sum.inl.inj h)⟩
    let eR : Fin (2 * ell) ↪ ((Fin (2 * ell) ⊕ Fin (2 * ell)) ⊕ Fin 3) :=
      ⟨fun s ↦ Sum.inl (Sum.inr s), fun _ _ h ↦ Sum.inr.inj (Sum.inl.inj h)⟩
    let Lwin := (Finset.univ : Finset (Fin (2 * ell))).map eL
    let Rwin := (Finset.univ : Finset (Fin (2 * ell))).map eR
    let m := k / (2 * ell) + 1
    (∑ t ∈ (Lwin.product (Finset.range m)).product (Rwin.product (Finset.range m)),
      f t.1.1 t.2.1 t.1.2 t.2.2) =
        ∑ v : Fin (2 * ell) × Fin (2 * ell) × Fin m × Fin m,
          f (eL v.1) (eR v.2.1) v.2.2.1.val v.2.2.2.val := by
  classical
  intro eL eR Lwin Rwin m
  simp only [Lwin, Rwin, Finset.product_eq_sprod, Finset.sum_product,
    Finset.sum_map, Finset.sum_range, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro p _hp
  exact Finset.sum_comm

open Classical in
/-- The common polynomial partition with named ordered-word coefficients and
caller-controlled equality on the label type. This is a proof interface for
the same partition, without a new word expansion. Supporting ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1324–1333. -/
private theorem exists_common_two_window_namedCoefficient_partition
    {I A : Type*} [Fintype I] [DecidableEq I] [Semiring A] [Module ℂ A]
    (L R : Finset I) (hL : L.Nonempty) (hR : R.Nonempty) :
    ∃ (pickL : (↥L → ℕ) → ↥L) (pickR : (↥R → ℕ) → ↥R),
      (∀ (a : I → ℕ) (n : ℕ), (∑ x, a x) ≤ n →
        a (pickL (fun u : ↥L ↦ a u)) ≤ n / L.card ∧
        a (pickR (fun v : ↥R ↦ a v)) ≤ n / R.card) ∧
      ∀ (H : I → A) (k : ℕ) (c : Fin (k + 1) → ℂ),
        let E := fun r : ℕ ↦ Finset.piAntidiag (Finset.univ : Finset I) r
        let B := (L.product (Finset.range (k / L.card + 1))).product
          (R.product (Finset.range (k / R.card + 1)))
        let left := fun a : I → ℕ ↦ pickL (fun u : ↥L ↦ a u)
        let right := fun a : I → ℕ ↦ pickR (fun v : ↥R ↦ a v)
        let slice := fun (t : (I × ℕ) × (I × ℕ)) (r : ℕ) ↦
          ∑ a ∈ E r with a t.1.1 = t.1.2 ∧ a t.2.1 = t.2.2,
            (if (left a : I) = t.1.1 ∧ (right a : I) = t.2.1
              then (1 : ℂ) else 0) • WordMultiplicity.wordCoefficient H r a
        (∑ r : Fin (k + 1), c r • (∑ x, H x) ^ r.val) =
          ∑ t ∈ B, ∑ r : Fin (k + 1), c r • slice t r.val := by
  classical
  cases Subsingleton.elim (inferInstance : DecidableEq I) (Classical.decEq I)
  obtain ⟨pickL, pickR, hpick, hpartition⟩ :=
    exists_common_two_window_polynomial_partition (A := A) L R hL hR
  refine ⟨pickL, pickR, hpick, ?_⟩
  intro H k c E B left right slice
  simpa only [E, B, left, right, slice, WordMultiplicity.wordCoefficient] using hpartition H k c

open Classical in
/-- Shared selector masks and common scalar samples recover the full
polynomial as a finite sum of the actual two-marker coefficients. All sample
points and recovery weights precede the operator family and every polynomial
coefficient. This combines the existing word partition, mask identity and
counted-word recovery for ALVV, arXiv:1602.08828v2, Proposition 5.7,
lines 1324–1333. The distinguished operators remain unweighted; no MPO,
source-sharp bond or running-time estimate is asserted here. -/
theorem exists_global_two_window_polynomial_recovery
    {R : Type*} [Ring R] [Algebra ℂ R] (ell k : ℕ) (hell : 1 ≤ ell) :
    ∃ z : crossingFrequencyIndex ell k → Fin ((k + 1) ^ (4 * ell + 1)) →
        (((Fin (2 * ell) ⊕ Fin (2 * ell)) ⊕ Fin 3) → ℂ),
      ∃ gamma : crossingFrequencyIndex ell k → Fin ((k + 1) ^ (4 * ell + 1)) → ℂ,
        ∀ (H : ((Fin (2 * ell) ⊕ Fin (2 * ell)) ⊕ Fin 3) → R)
          (c : Fin (k + 1) → ℂ),
          let O : crossingFrequencyIndex ell k →
              Finset ((Fin (2 * ell) ⊕ Fin (2 * ell)) ⊕ Fin 3) := fun v ↦
            (Finset.univ.erase (Sum.inl (Sum.inl v.1))).erase
              (Sum.inl (Sum.inr v.2.1))
          let D := fun (v : crossingFrequencyIndex ell k)
              (t : Fin ((k + 1) ^ (4 * ell + 1))) ↦ ∑ a ∈ O v, z v t a • H a
          (∑ r : Fin (k + 1), c r • (∑ a, H a) ^ r.val) =
            ∑ v : crossingFrequencyIndex ell k, ∑ t : Fin ((k + 1) ^ (4 * ell + 1)),
              ∑ r : Fin (k + 1), (c r * gamma v t) •
                twoMarkerCoefficient (D v t) (H (Sum.inl (Sum.inl v.1)))
                  (H (Sum.inl (Sum.inr v.2.1))) r.val v.2.2.1.val v.2.2.2.val := by
  classical
  let I := (Fin (2 * ell) ⊕ Fin (2 * ell)) ⊕ Fin 3
  let : DecidableEq I :=
    inferInstanceAs (DecidableEq ((Fin (2 * ell) ⊕ Fin (2 * ell)) ⊕ Fin 3))
  let eL : Fin (2 * ell) ↪ I :=
    ⟨fun p ↦ Sum.inl (Sum.inl p), fun _ _ h ↦ Sum.inl.inj (Sum.inl.inj h)⟩
  let eR : Fin (2 * ell) ↪ I :=
    ⟨fun s ↦ Sum.inl (Sum.inr s), fun _ _ h ↦ Sum.inr.inj (Sum.inl.inj h)⟩
  have hLapply (p : Fin (2 * ell)) : eL p = Sum.inl (Sum.inl p) := rfl
  have hRapply (s : Fin (2 * ell)) : eR s = Sum.inl (Sum.inr s) := rfl
  let Lwin := (Finset.univ : Finset (Fin (2 * ell))).map eL
  let Rwin := (Finset.univ : Finset (Fin (2 * ell))).map eR
  have hLcard : Lwin.card = 2 * ell := by
    simp only [Lwin, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hRcard : Rwin.card = 2 * ell := by
    simp only [Rwin, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  let p0 : Fin (2 * ell) := ⟨0, by omega⟩
  have hLn : Lwin.Nonempty :=
    ⟨eL p0, Finset.mem_map.mpr ⟨p0, Finset.mem_univ _, rfl⟩⟩
  have hRn : Rwin.Nonempty :=
    ⟨eR p0, Finset.mem_map.mpr ⟨p0, Finset.mem_univ _, rfl⟩⟩
  obtain ⟨pickL, pickR, _hpick, hpartition⟩ :=
    exists_common_two_window_namedCoefficient_partition (A := R) Lwin Rwin hLn hRn
  let left := fun a : I → ℕ ↦ pickL (fun u : Lwin ↦ a u)
  let right := fun a : I → ℕ ↦ pickR (fun v : Rwin ↦ a v)
  let μ := fun (v : crossingFrequencyIndex ell k) (a : I → ℕ) ↦
    if (left a : I) = eL v.1 ∧ (right a : I) = eR v.2.1 then (1 : ℂ) else 0
  have hsamples (v : crossingFrequencyIndex ell k) :=
    Polynomial.exists_twoWindow_wordCoefficient_recovery (R := R) v.1 v.2.1 k
  choose z hz using hsamples
  have hweights (v : crossingFrequencyIndex ell k) :=
    hz v v.2.2.1.val v.2.2.2.val (μ v)
  choose gamma hgamma using hweights
  refine ⟨z, gamma, ?_⟩
  intro H c O D
  let E := fun r : ℕ ↦ Finset.piAntidiag (Finset.univ : Finset I) r
  let B := (Lwin.product (Finset.range (k / (2 * ell) + 1))).product
    (Rwin.product (Finset.range (k / (2 * ell) + 1)))
  let f := fun (u v : I) (i j : ℕ) ↦ ∑ r : Fin (k + 1), c r •
    (∑ a ∈ E r.val with a u = i ∧ a v = j,
      (if (left a : I) = u ∧ (right a : I) = v then (1 : ℂ) else 0) •
        WordMultiplicity.wordCoefficient H r.val a)
  have hpart : (∑ r : Fin (k + 1), c r • (∑ a, H a) ^ r.val) =
      ∑ t ∈ B, f t.1.1 t.2.1 t.1.2 t.2.2 := by
    have hp := hpartition H k c
    dsimp only at hp
    rw [hLcard, hRcard] at hp
    exact hp
  have hindex : (∑ t ∈ B, f t.1.1 t.2.1 t.1.2 t.2.2) =
      ∑ v : crossingFrequencyIndex ell k, f (eL v.1) (eR v.2.1)
        v.2.2.1.val v.2.2.2.val :=
    sum_two_window_labels_eq_crossing_indices ell k f
  have hrec (v : crossingFrequencyIndex ell k) (r : Fin (k + 1)) :
      (∑ a ∈ E r.val with a (eL v.1) = v.2.2.1.val ∧ a (eR v.2.1) = v.2.2.2.val,
        μ v a • WordMultiplicity.wordCoefficient H r.val a) =
        ∑ t : Fin ((k + 1) ^ (4 * ell + 1)), gamma v t •
          twoMarkerCoefficient (D v t) (H (eL v.1)) (H (eR v.2.1))
            r.val v.2.2.1.val v.2.2.2.val := by
    simpa only [E, hLapply, hRapply,
      MvPolynomial.twoMarkerOrdinaryLabels, O, D, twoMarkerCoefficient] using
      hgamma v H r.val (Nat.le_of_lt_succ r.isLt)
  calc
    (∑ r : Fin (k + 1), c r • (∑ a, H a) ^ r.val) =
      ∑ v : crossingFrequencyIndex ell k, ∑ r : Fin (k + 1), c r •
        (∑ a ∈ E r.val with a (eL v.1) = v.2.2.1.val ∧ a (eR v.2.1) = v.2.2.2.val,
          μ v a • WordMultiplicity.wordCoefficient H r.val a) := hpart.trans hindex
    _ = ∑ v : crossingFrequencyIndex ell k, ∑ r : Fin (k + 1), c r •
        (∑ t : Fin ((k + 1) ^ (4 * ell + 1)), gamma v t •
          twoMarkerCoefficient (D v t) (H (eL v.1)) (H (eR v.2.1))
            r.val v.2.2.1.val v.2.2.2.val) := by
      apply Finset.sum_congr rfl
      intro v _hv
      apply Finset.sum_congr rfl
      intro r _hr
      exact congrArg (fun a : R ↦ c r • a) (hrec v r)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v _hv
      simp_rw [Finset.smul_sum, smul_smul]
      exact Finset.sum_comm

end TNLean.MPS.AreaLaw

end
