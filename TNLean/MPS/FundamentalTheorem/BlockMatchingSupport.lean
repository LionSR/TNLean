/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.BNT.Construction
import TNLean.Algebra.ScalarPowerSumIdentity

/-!
# BNT block matching and power sums

This module contains the witness type used for BNT block matching and the
Newton--Girard power-sum lemmas needed for the multiplicity-recovery argument
in arXiv:1606.00608.

It deliberately contains no equal- or proportional-MPV Fundamental Theorem
formulation: statements with common block structure or explicit coefficient
arrays as hypotheses are stricter than arXiv:1606.00608, Theorem II.1 and
Corollary II.2.

## Main results

### Block matching witness

`BlockPermutationGaugeWitness` records the block-count, permutation,
bond-dimension, and gauge-phase data produced by the heterogeneous equal-MPV
block-matching theorem.

### Power-sum multiset equality

If two same-cardinality sequences of complex numbers have equal power sums for all positive
exponents, their multisets are equal.  For different cardinalities, the positive-power
theorem needs nonzero entries; otherwise positive powers determine only the multiset after
zero entries are deleted.  See `TNLean.Algebra.ScalarPowerSumIdentity`.

## References

- Pérez-García, Verstraete, Wolf, Cirac, *Matrix Product State Representations*,
  Quantum Inf. Comput. 7 (2007), arXiv:quant-ph/0608197.
- Cirac, Pérez-García, Schuch, Verstraete, *Matrix product states and projected entangled pair
  states: Concepts, symmetries, theorems*, Rev. Mod. Phys. 93 (2021), arXiv:2011.12127.

-/
open scoped Matrix BigOperators

namespace MPSTensor

/-- Conclusion type for BNT block-matching statements.

Source: arXiv:1606.00608, Theorem II.1, lines 349--352 and 1165--1192.  This is
the permutation, dimension-equality, and gauge-phase part of the conclusion; it
does not assert the hypotheses from which that conclusion follows. -/
abbrev BlockPermutationGaugeWitness
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k)) : Prop :=
  ∃ _h : rA = rB,
    ∃ perm : Fin rA ≃ Fin rB,
      ∀ j : Fin rA,
        ∃ hdim : dimA j = dimB (perm j),
          GaugePhaseEquiv (d := d)
            (cast (congr_arg (MPSTensor d) hdim) (A j))
            (B (perm j))

/-! ## Power-sum multiset equality

This provides the power-sum lemmas from `ScalarPowerSumIdentity.lean`.
The bounded same-cardinality version is the common Newton--Girard input.
The nonzero-entry version below compares possibly unequal cardinalities using
positive powers only; without a nonzero-entry hypothesis, positive powers do not
count zero entries.
-/

/-- **Bounded equal power sums imply equal multisets** (same-cardinality part of
the power-sum argument in arXiv:1606.00608, lines 1155--1163).

If two sequences of complex numbers `α : Fin n → ℂ` and `β : Fin n → ℂ` satisfy
`∑ i, (α i)^k = ∑ i, (β i)^k` for `1 ≤ k ≤ n`, then `α` and `β` have the same
multiset of values counted with multiplicity. -/
theorem power_sum_eq_implies_multiset_eq_of_le_card (n : ℕ)
    (α β : Fin n → ℂ)
    (h : ∀ k : ℕ, 0 < k → k ≤ n →
      ∑ i : Fin n, (α i) ^ k = ∑ i : Fin n, (β i) ^ k) :
    Finset.univ.val.map α = Finset.univ.val.map β := by
  apply Matrix.sum_pow_eq_implies_multiset_eq_of_le_card
  intro k hk hkcard
  exact h k hk (by simpa using hkcard)

/-- **Bounded unequal-cardinality power sums imply equal cardinality and equal
multisets** under a nonzero-entry hypothesis.

If two nonzero finite sequences `α : Fin m → ℂ` and `β : Fin n → ℂ` satisfy
`∑ i, (α i)^k = ∑ i, (β i)^k` for `1 ≤ k ≤ max m n`, then `m = n` and the two
sequences have the same multiset of values counted with multiplicity.

The nonzero-entry hypothesis is mathematically necessary for this positive-power
statement: zero entries have no effect on the sums for `k > 0`. -/
theorem power_sum_eq_implies_card_eq_and_multiset_eq_of_le_max_card
    (m n : ℕ) (α : Fin m → ℂ) (β : Fin n → ℂ)
    (hα : ∀ i, α i ≠ 0) (hβ : ∀ i, β i ≠ 0)
    (h : ∀ k : ℕ, 0 < k → k ≤ max m n →
      ∑ i : Fin m, (α i) ^ k = ∑ i : Fin n, (β i) ^ k) :
    m = n ∧ Finset.univ.val.map α = Finset.univ.val.map β :=
  Matrix.sum_pow_eq_implies_card_eq_and_multiset_eq_of_le_max_card m n α β hα hβ h

end MPSTensor
