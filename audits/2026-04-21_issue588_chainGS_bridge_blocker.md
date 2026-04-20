# Issue #588 blocker audit — `chainGroundSpace_le_mpvSubmodule_of_normal_range_reduction`

Date: 2026-04-21
Branch: `feat/588-chainGroundSpace-bridge`
Scope: discharge the single remaining `sorry` in
`TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean`
without adding new `sorry`/`axiom` and without touching forbidden files.

## Files / context re-read

- `CLAUDE.md`, `docs/PROOF_INTEGRITY.md`, `docs/style.md`
- issue #588 full thread / prior blocker comments
- `TNLean/MPS/ParentHamiltonian/{UniqueGroundState,IntersectionProperty,CyclicWindow,WrappingWindow}.lean`
- `TNLean/MPS/Defs.lean`, `TNLean/MPS/BNT/Construction.lean`
- `TNLean/MPS/Irreducible/*`
- `TNLean/Wielandt/*` with focus on `SpanGrowth/CumulativeToWordSpan.lean`,
  `RectangularSpan/Basic.lean`, `QuantumWielandt.lean`, `PaperResults/WielandtInequality.lean`
- `Papers/2011.12127/TN-Review-main.tex` §IV.C, lines 2049–2094

## Main updated finding

The previously-reported **periodic-closure obstruction is not the true blocker**.

More precisely, the second exact-span step in
`WrappingWindow.boundary_matrix_commutes` can be repaired for the normal setting.
If a matrix `Z` annihilates every exact word product of some length `k`, and if
`wordSpan A n = ⊤` for any `n ≥ k`, then `Z = 0`: every length-`n` word factors
as `(length k prefix) ++ (length (n-k) suffix)`, so `Z` annihilates all generators
of `wordSpan A n`, hence annihilates `⊤`. I verified this in a scratch Lean file
(`/tmp/issue588_test.lean`) by compiling a local lemma

```lean
eq_zero_of_mul_evalWord_eq_zero_of_wordSpan_eq_top
```

using only existing repo API.

Thus, once one has an open-chain representation
`ψ = groundSpaceMap A N X`, the wrapping step for the reduced range `L₀ + 1`
can be finished: the complement length `N - (L₀ + 1)` need not itself have
full exact word span; it is enough to pad to a positive multiple of `L₀` using
`wordSpan_top_of_mul` from `Wielandt/RectangularSpan/Basic.lean`.

## The real blocker

The genuine missing piece is now the **open-chain range-reduction / blocked
intersection** step.

The paper proof at lines 2049–2078 is an **open-boundary** argument:
- invert the blocked middle region `B` of length `L₀`,
- grow `B` back onto the neighboring single-site tensors `A` and `C`,
- then invert the enlarged regions `A∘B` and `B∘C`.

Current TNLean `ParentHamiltonian` infrastructure is built around the **traced**
map

```lean
groundSpaceMap A L : Matrix -> NSiteSpace d L
```

and the injective theorem

```lean
groundSpace_intersection
```

which relies on:
1. `groundSpaceMap_injective` for a single tensor family indexed by one physical site,
2. `decompositionMap hA 1` for the single-site family `A : Fin d -> Matrix`,
3. the compatibility identity `A j * Y i = Z j * A i`, resolved by expanding the
   identity as a linear combination of the **single-site** Kraus operators `A j`.

For the normal case, the paper’s blocked middle region is injective only as an
**open-boundary region map**, not as the existing traced `groundSpaceMap`, and
its inverse is not expressible with the current single-site `decompositionMap`.
The missing API is therefore not “more exact wordSpan propagation”; it is a
region-level open-boundary injectivity package.

## Missing bridge APIs (precise)

At least one of the following is needed.

### Option A: open-boundary region API

1. A realization map for an `L`-site region with **separate left/right virtual
   boundaries** (the 1D analogue of the paper’s `Γ_L` before tracing).
2. A theorem that `IsNBlkInjective A L₀` gives a left inverse for the middle
   blocked region `B` on `L₀` sites in that open-boundary sense.
3. A “grow-back preserves injectivity” theorem for the enlarged regions
   `A∘B` and `B∘C` used at lines 2061–2069 of the paper.
4. From (1)–(3), a normal analogue of
   `IntersectionProperty.groundSpace_intersection`.

### Option B: an equivalent asymmetric extension theorem

A theorem of the form:

```lean
if ψ on (m+1) sites has
  - its first m sites in groundSpace A m, and
  - its last (L₀+1) sites in groundSpace A (L₀+1),
then ψ ∈ groundSpace A (m+1)
```

proved directly from `IsNBlkInjective A L₀`.

But proving this still requires the same open-boundary “invert B / grow back”
content, just packaged asymmetrically.

## Why I am stopping here

I do not see a sound route to close the theorem using only the existing traced
`groundSpaceMap` / `decompositionMap` API. The paper’s core step is about
open-boundary region inverses, and that API is absent on current `main`.

So the theorem is still honestly blocked, but for a **different reason** than
in the April 19–20 scouting comments:
- the **wrapping** side is salvageable with the padding lemma above;
- the missing infrastructure is the **open-chain blocked intersection** side.

## Recommended next PR target

A focused infrastructure PR should add either:
- an open-boundary region realization / left-inverse API for blocked regions, or
- an asymmetric extend-by-one-site theorem equivalent to the paper’s blocked
  intersection step.

Once that exists, the remaining periodic closure can be finished inside
`UniqueGroundState.lean` without any new axioms or sorrys.
