/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.BNT.Construction
import TNLean.Algebra.ScalarPowerSumIdentity
import TNLean.MPS.FundamentalTheorem.SectorDecomposition

/-!
# Equal and Proportional MPV Fundamental Theorems

This module collects the **equal-case** and **proportional-case** fundamental theorems for
matrix product states in canonical form with basis-of-normal-tensors (BNT) separation,
together with supporting corollaries.

## Main results

### Theorem 1: Equal-MPV Fundamental Theorem for `IsCanonicalFormBNT`
(`fundamentalTheorem_equalMPV_CFBNT`)

**Corollary II_cor2 (equal case)**: If two families of tensors in canonical form with
basis-of-normal-tensors (BNT) separation share the same `μ`-weights, same block count `r`, and
same block dimensions, and
generate *equal* MPVs for all system sizes, then per-block gauge equivalence holds together
with a global gauge equivalence of the block-diagonal tensors.

### Proportional-MPV Fundamental Theorem (Theorem 4.4)

The proportional case is not restated here as a Lean theorem.  The former
one-shot proportional-decomposition theorem used coefficient hypotheses that do
not by themselves imply the full block matching conclusion.  The retained
formal theorem in this file is the equal-MPV route below, whose hypotheses
produce nondecaying block overlaps directly.

### Theorem 3: Equal MPVs imply proportional MPVs
(`sameMPV₂_implies_proportionalMPV₂`)

Trivial but useful: `SameMPV₂ A B → ProportionalMPV₂ A B` (take `c_N = 1`).

### Theorem 4: Power-sum multiset equality (Lem:app_simple support lemma)

If two same-cardinality sequences of complex numbers have equal power sums for all positive
exponents, their multisets are equal.  For different cardinalities, the positive-power
theorem needs nonzero entries; otherwise positive powers determine only the multiset after
zero entries are deleted.  See `TNLean.Algebra.ScalarPowerSumIdentity`.

## References

- Pérez-García, Verstraete, Wolf, Cirac, *Matrix Product State Representations*,
  Quantum Inf. Comput. 7 (2007), arXiv:quant-ph/0608197.
- Cirac, Pérez-García, Schuch, Verstraete, *Matrix product states and projected entangled pair
  states: Concepts, symmetries, theorems*, Rev. Mod. Phys. 93 (2021), arXiv:2011.12127.

## Design notes

The **coefficient packaging**: the proportional-case theorem takes the per-`N`
coefficient arrays `aCoeff`, `bCoeff` and proportionality scalar `c` as explicit
data, together with the source-faithful dominant-block normalization
(`‖aCoeff N 0‖ = ‖bCoeff N 0‖ = 1` and `‖aCoeff N j‖, ‖bCoeff N k‖ ≤ 1`) and a
per-`N` nonzero condition `c N ≠ 0`. The earlier convergence-to-nonzero-limit
formulation deviated from arXiv:1606.00608; the deviation is recorded in
`docs/paper-gaps/cpsv16_cf_normalization_and_proportional_comparison.tex`.
-/
open scoped Matrix BigOperators
open Filter

namespace MPSTensor

variable {d : ℕ}

/-! ## Theorem 1: Equal-MPV Fundamental Theorem for `IsCanonicalFormBNT`

This is the content of Corollary II_cor2 from arXiv:2011.12127 / arXiv:1606.00608,
specialized to the case where both families share the same block structure (same `r`,
same `dim`, same `μ`).
-/

/-- **Equal-MPV Fundamental Theorem for CF-BNT (Corollary II_cor2, same structure).**

If two families of tensors in canonical form with BNT separation share the same
block weights `μ`, the same number of blocks `r`, and the same block dimensions
`dim`, and generate equal MPV families for all system sizes, then:

(i)  per-block gauge equivalence: `GaugeEquiv (A k) (B k)` for all `k`;
(ii) global gauge equivalence of the block-diagonal tensors.

**Scope restriction (one-copy-per-sector)**: Both families must share the same block
structure `(r, dim, μ)`.  This is the multiplicity-free special case of Cor II.2; the
paper's general theorem does not assume identical block structures as a hypothesis —
it derives them.  The multiplicity recovery (`Lem:app_simple` on `∑_q μ_{j,q}^N`) is
absent.  See `docs/paper-gaps/ft_one_copy_scope_restriction.tex`. -/
-- SCOPE(one-copy-per-sector): requires same (r, dim, μ); paper derives this from BNT.
theorem fundamentalTheorem_equalMPV_CFBNT
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    {μ : Fin r → ℂ}
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : IsCanonicalFormBNT μ A)
    (hB : IsCanonicalFormBNT μ B)
    (hSame : SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks μ B)) :
    (∀ k, GaugeEquiv (A k) (B k)) ∧
    GaugeEquiv (toTensorFromBlocks μ A) (toTensorFromBlocks μ B) :=
  fundamentalTheorem_canonicalForm μ A B hA.toIsCanonicalForm hA.mu_strict_anti
    hB.block_injective hB.leftCanonical hSame

/-- **Equal-MPV FT for CF-BNT with explicit gauge matrices.**

**Scope restriction (one-copy-per-sector)**: same-structure restriction as
`fundamentalTheorem_equalMPV_CFBNT`; see that theorem's note. -/
-- SCOPE(one-copy-per-sector): same-structure restriction.
theorem fundamentalTheorem_equalMPV_CFBNT_explicit
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    {μ : Fin r → ℂ}
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : IsCanonicalFormBNT μ A)
    (hB : IsCanonicalFormBNT μ B)
    (hSame : SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks μ B)) :
    ∃ (X : ∀ k, GL (Fin (dim k)) ℂ),
    ∀ k i, B k i = (X k : Matrix _ _ ℂ) * A k i *
      (((X k)⁻¹ : GL _ ℂ) : Matrix _ _ ℂ) :=
  fundamentalTheorem_canonicalForm_explicit μ A B hA.toIsCanonicalForm hA.mu_strict_anti
    hB.block_injective hB.leftCanonical hSame

/-! ## Theorem 2: Proportional-MPV Fundamental Theorem (Theorem 4.4)

This is the content of Theorem 4.4 from arXiv:1606.00608 (primitive branch).
The theorem takes convergent coefficient data as explicit hypotheses.
-/

/-- Conclusion type for the BNT proportional-MPV comparison theorems. -/
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

/-! ## Theorem 3: Equal MPVs imply proportional MPVs -/

/-- **Equal MPVs imply proportional MPVs** (trivially, with proportionality constant `1`).

This is useful for reducing Corollary II_cor2 to the proportional case of Theorem 4.4. -/
theorem sameMPV₂_implies_proportionalMPV₂
    {D₁ D₂ : ℕ} (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (h : SameMPV₂ A B) :
    ProportionalMPV₂ A B := by
  intro N
  exact ⟨1, fun σ => by simpa using h N σ⟩

/-! ## Theorem 4: Power-sum multiset equality (Lem:app_simple support lemma)

This provides the power-sum lemmas from `ScalarPowerSumIdentity.lean`.
The bounded same-cardinality version is the common Newton--Girard input.
The nonzero-entry version below compares possibly unequal cardinalities using
positive powers only; without a nonzero-entry hypothesis, positive powers do not
count zero entries.
-/

/-- **Equal power sums imply equal multisets** (same-cardinality support lemma for
`Lem:app_simple` of arXiv:1606.00608).

If two sequences of complex numbers `α : Fin n → ℂ` and `β : Fin n → ℂ` satisfy
`∑ i, (α i)^k = ∑ i, (β i)^k` for all positive `k`, then `α` and `β` have the same
multiset of values (counted with multiplicity).

This is a corollary of Newton's identities via
`Matrix.sum_pow_eq_implies_multiset_eq` from `ScalarPowerSumIdentity.lean`.
The unequal-cardinality Appendix use requires the nonzero-entry version below. -/
theorem power_sum_eq_implies_multiset_eq (n : ℕ)
    (α β : Fin n → ℂ)
    (h : ∀ k : ℕ, 0 < k → ∑ i : Fin n, (α i) ^ k = ∑ i : Fin n, (β i) ^ k) :
    Finset.univ.val.map α = Finset.univ.val.map β :=
  Matrix.sum_pow_eq_implies_multiset_eq α β h

/-- **Bounded equal power sums imply equal multisets** (same-cardinality part of
Lemma `Lem:app_simple`).

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

/-! ## Combined corollaries -/

section Corollaries

/-- **Per-block SameMPV from CF-BNT equal MPVs.**

Extracts the per-block `SameMPV` conclusion from the equal-MPV theorem. -/
theorem perBlock_sameMPV_of_equalMPV_CFBNT
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    {μ : Fin r → ℂ}
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : IsCanonicalFormBNT μ A)
    (hB : IsCanonicalFormBNT μ B)
    (hSame : SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks μ B)) :
    ∀ k, SameMPV (A k) (B k) :=
  fun k => GaugeEquiv.sameMPV ((fundamentalTheorem_equalMPV_CFBNT A B hA hB hSame).1 k)

end Corollaries

end MPSTensor
