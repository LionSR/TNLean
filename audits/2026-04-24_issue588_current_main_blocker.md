# Issue #588 audit update — current `main` is still missing two ingredients for the final bridge

Date: 2026-04-24
Branch: `wave12-B-588`
Target theorem: `MPSTensor.chainGroundSpace_le_mpvSubmodule_of_normal_range_reduction`

## Scope of this pass

I re-read:

- issue #588 and its full comment history;
- `Papers/2011.12127/TN-Review-main.tex` §IV.C, especially lines 2049–2094;
- the current `UniqueGroundState.lean` target around the single remaining `sorry`;
- the already-landed block-injective infrastructure in
  `ExtendRight.lean`, `SuffixWindow.lean`, `BlockStrip.lean`, and
  `WrappingWindow.lean`.

I also inspected two non-main artifacts that are directly relevant to this theorem:

- commit `c40e4578` (`feat(ParentHamiltonian): formalize open-chain normal-range reduction (#588)`), which contains the reverted open-chain proof skeleton;
- the unmerged transport-API branch
  `origin/claude/issue-869-formalizationmpsparenthamiltonian-add-contiguoustail-restriction-transport`
  (commit `ac3269f9` / `2957d7ea`), which introduces `RestrictTransport.lean`.

## Finding 1 — the open-chain reduction is still not available on current `main`

The reverted `c40e4578` proof skeleton is still the right mathematical route for

```lean
chainGroundSpace A (L₀ + 1) N ≤ groundSpace A N,
```

namely:

1. shrink cyclic windows from length `L` down to `L₀ + 1`;
2. identify non-wrapping cyclic windows with contiguous windows;
3. iterate `groundSpace_extend_right_of_isNBlkInjective` to regrow the open chain.

However, current `main` still does **not** contain the arithmetic-transport API
needed to make that induction compile robustly.  The exact missing reusable
helpers are now sitting on the unmerged transport branch as

- `MPSTensor.reindexSites`,
- `MPSTensor.tailRestrictₗ_snoc`,
- `MPSTensor.tailRestrictₗ_reindex_prefix`,
- `MPSTensor.tailRestrictₗ_reindex_tail`,
- `MPSTensor.contiguousRestrictₗ_reindex_window`,
- `MPSTensor.contiguousRestrictₗ_reindex_total`.

Without those transport lemmas (or an equivalent local recreation of them inside
`UniqueGroundState.lean`), the reverted open-chain proof still runs into the same
non-definitional equalities of dependent lengths such as

- `K + 1 + L₀` vs. `K + (L₀ + 1)`, and
- `N - (L₀ + 1) + (L₀ + 1)` vs. `N`.

So current `main` still lacks an honest, compilable proof of the open-chain half
inside the requested single-file/single-sorry scope.

## Finding 2 — the periodic closure still lacks a same-witness comparison theorem

Even if I grant the open-chain half, the current wrapped-window API is still one
step short of the final periodic closure.

Current `WrappingWindow.lean` exports exactly the two one-sided block-injective
extractions

- `MPSTensor.wrapping_window_compatibility_of_isNBlkInjective`, and
- `MPSTensor.wrapping_window_mirror_compatibility_of_isNBlkInjective`.

These are valuable, but they are **not yet** the same-witness theorem needed to
feed

```lean
MPSTensor.boundary_matrix_commutes_of_isNBlkInjective_of_long_word_commutes.
```

Concretely, the two exported lemmas quantify over independent witness families
and over different complement slices.  What the final argument still needs is a
comparison result of the schematic form

```lean
∀ ω, ∃ Yω,
  (∀ j, Cω * A j * X = Yω * A j) ∧
  (∀ j, X * A j * Cω = A j * Yω),
```

for a **common** complement word `Cω` and a **common** matrix `Yω`.

I do not see such a theorem on current `main`, nor a witness-comparison lemma
showing that the matrices extracted from the two extreme wrapped positions agree
in the sense needed to synthesize long-word commutation

```lean
∀ ω, X * evalWord A (List.ofFn ω) = evalWord A (List.ofFn ω) * X.
```

So the periodic side is still missing a final comparison layer.

## Honest status

I am therefore stopping without editing Lean source files.

- `TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean` is unchanged.
- The single `sorry` at line 365 remains.
- No new `sorry` or `axiom` were introduced.

## Suggested next unblockers

### A. Land the transport API first

Either merge the existing `RestrictTransport.lean` branch or recreate its small
API locally.  Then the reverted `c40e4578` open-chain regrowth proof can be
re-landed cleanly.

### B. Add one final wrapped-window comparison theorem

After the transport layer is available, the remaining periodic target is a
public theorem in `WrappingWindow.lean` giving either

1. a same-witness pair for a common complement word, or
2. an explicit witness-comparison theorem between the two wrapped positions.

Once that exists, the rest of #588 should reduce to straightforward assembly:
open-chain reduction + long-word commutation + center/scalar argument.
