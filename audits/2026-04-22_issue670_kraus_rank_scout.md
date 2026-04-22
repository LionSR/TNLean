# Issue #670 scout — Kraus-rank feasibility for Thm. 4.1 reverse

Date: 2026-04-22
Branch: `chore/670-kraus-rank-scout`
Scope: report-only update against current `main`

## Problem statement

The exact reverse-side gap is

```lean
def PRefinementInverseCanonicalization (d D p : ℕ) : Prop :=
  ∀ {B : MPSTensor d D}, IsIrreducibleForm B →
    IsPDivisibleChannel (transferMap B) p →
    ∃ A : MPSTensor d D, transferMap B = transferMap (blockTensor A p)
```

So the needed step is: from a CPTP root `E'` of `transferMap B`, produce a root Kraus family indexed by
`Fin d`. In practice, `≤ d` Kraus operators would already suffice, since a smaller family can be padded by
zeros before blocking.

## Mathlib API inventory

Repo grep over `.lake/packages/mathlib/Mathlib` finds **no quantum-channel surface** for Kraus, Choi, or
Stinespring minimality. The closest reusable Mathlib ingredients are purely linear-algebraic:

- `Mathlib/Analysis/InnerProductSpace/Positive.lean`
  - `ContinuousLinearMap.isPositive_iff_eq_sum_rankOne`
  - `Matrix.posSemidef_iff_eq_sum_vecMulVec`
- `Mathlib/LinearAlgebra/Matrix/Rank.lean`
  - `Matrix.rank_mul_le_left`, `Matrix.rank_mul_le_right`
  - `Matrix.rank_conjTranspose_mul_self`, `Matrix.rank_self_mul_conjTranspose`
  - `Matrix.rank_vecMulVec_le`

What is **missing** upstream:

1. a public theorem indexing a PSD decomposition by `Fin M.rank` (or even giving an explicit summand bound by
   `M.rank`);
2. any Choi-rank / minimal-Kraus API;
3. any root/composition theorem controlling Kraus rank under `E = F ^ p`.

## Repo API inventory

Current TNLean surface is strong once a root Kraus family is already available:

- `TNLean/Channel/Basic.lean`
  - `IsCPMap`, `IsChannel`: root channels are existential over an arbitrary `Fin r` Kraus family.
- `TNLean/Channel/ChoiJamiolkowski.lean`
  - `cp_iff_choi_posSemidef`
  - `exists_cpMap_of_choi_posSemidef`
  Both use `Matrix.posSemidef_iff_eq_sum_vecMulVec`, so they produce **some finite Kraus family**, but no
  minimality/cardinality theorem.
- `TNLean/Channel/KrausRepresentation.lean`
  - `kraus_same_map_of_isometry_combination`
- `TNLean/Channel/KrausFreedom.lean`
  - `kraus_rectangular_freedom'`
  - internal zero-padding helper `sum_pad_zeros`
- `TNLean/Channel/KrausUnitaryFreedom.lean`
  - `kraus_isometry_freedom_iff`, `kraus_unitary_freedom_iff`
- `TNLean/Channel/FixedPoint/CanonicalGauge.lean`
  - `gauged_unital`, `gauged_leftCanonical`
  These change gauge but **do not reduce Kraus index cardinality**.
- `TNLean/MPS/Periodic/Symmetry.lean`
  - `thm_4_1_p_refinement_reverse` is already complete once `PRefinementInverseCanonicalization` supplies a
    `d`-indexed root tensor.

## Precise obstruction

The sharp paper-level gap is now clear from `Papers/1708.00029/main.tex:812–818`:

- the definition of `p`-divisible only gives a root channel `E'`;
- the proof immediately strengthens this to “there exists an `A` such that `E_B = E_A^p`”.

That strengthening is exactly what Lean has isolated as `PRefinementInverseCanonicalization`.
Wolf Thm. 2.18 is **not** the blocker anymore: it only compares two already-chosen Kraus families of the same
CP map up to isometry. It does not show that a root channel admits a Kraus family with `≤ d` operators.

I found no theorem, either in Mathlib or TNLean, that derives

```lean
∃ (r : ℕ) (_ : r ≤ d) (A : MPSTensor r D),
  transferMap B = transferMap (blockTensor A p)
```

from `IsIrreducibleForm B` and `IsPDivisibleChannel (transferMap B) p`.
Moreover, `IsIrreducibleForm` currently contains periodic-block data and positive weights, but no minimal-Kraus
or linear-independence field that would force such a bound.

## Feasibility verdict

**Verdict for the exact current target: 🔴**.

This is not a `≤100 LOC` or even straightforward `200–500 LOC` local theorem. Even after adding a
Choi-rank/minimal-Kraus bridge, one would still need a new local result showing that **some** `p`-th root of
`transferMap B` has Kraus rank `≤ d`. No route to that bound is exposed by the paper or current API.

## Recommended next steps

1. **Schedule-friendly follow-up issue (recommended):**
   `feat(MPS/Periodic): witness-based reverse notion for Thm. 4.1`

   Suggested surface:

   ```lean
   def IsPDivisibleByTensor (d D : ℕ)
       (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) (p : ℕ) : Prop :=
     ∃ A : MPSTensor d D, E = transferMap (blockTensor A p)
   ```

   or a bounded-cardinality variant with `∃ r ≤ d` plus zero-padding.
   This should be a small standalone PR (~150–300 LOC).

2. **Longer-term upstream/local theory:** add a PSD/Choi-rank minimality bridge.
   The plausible upstreamable piece is a Mathlib theorem giving a `rank`-indexed PSD decomposition
   (`~300–500 LOC`). A TNLean Choi/Kraus wrapper would then be another `~150–250 LOC`. That still would not,
   by itself, solve the root-rank bound above.
