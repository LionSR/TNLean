# Issue #730 audit — block-injective wrapped-window extraction

Date: 2026-04-22
Branch attempted: `feat/730-wrapping-window-block-injective`
Scope: replace the one-site stripping step in `WrappingWindow.wrapping_window_matEq`
by a block-injective argument producing the long-word commutation family needed for
`boundary_matrix_commutes_of_isNBlkInjective`.

## Context re-read

- issue #730 body
- `audits/2026-04-21_issue704_block_strip_followup.md`
- `audits/2026-04-22_issue704_periodic_reintegration_blocker.md`
- `TNLean/MPS/ParentHamiltonian/{WrappingWindow,BlockStrip,CyclicWindow,SuffixWindow,ExtendRight}.lean`
- `Papers/2011.12127/TN-Review-main.tex`, §IV.C, lines 2049–2078

## Main new finding

The issue body's advertised local replacement

```lean
apply groundSpaceMap_injective_of_isNBlkInjective hInj
```

for the one-site appeal inside `wrapping_window_matEq` is **not by itself enough**
on the current Lean API.

More precisely, for the wrapped window at position `N - 1`, replacing the length-`1`
injectivity step by length-`L₀` block injectivity cleanly yields only the one-sided
compatibility family

```lean
C_τ * A_j * X = Y_τ * A_j,
```

where `C_τ` is the complement word of length `N - L₀ - 1` and `Y_τ` is the
boundary matrix witnessing membership of the wrapped `(L₀ + 1)`-window in
`groundSpace A (L₀ + 1)`.

That extraction is real: it comes from viewing the wrapped trace identity as a
length-`L₀` `groundSpaceMap` equality in the tail word.

However, the companion relation

```lean
X * A_j * C_τ = A_j * Y_τ
```

is **not obtainable from the same factorization by the same substitution**.  In the
current `WrappingWindow` proof skeleton, the wrapped physical word at position
`N - 1` has the form

$$
\omega \cdot C_\tau \cdot A_j,
$$

with the boundary matrix `X` inserted after the full physical word.  Cyclically
rotating the trace can place `X` either before the tail block `\omega` or after the
single letter `A_j`, but not in the position needed to rewrite the left restriction as

$$
\operatorname{tr}(A^\omega \cdot (X A_j C_\tau)).
$$

So the current issue description understates the remaining gap: the line-244
replacement gives only one of the two one-sided wrapped compatibilities.

## Important positive update

The old numerical obstruction from the April 22 #704 audit is **no longer the real
blocker once PR #728 is available**.

If one could produce commutation on words of any positive fixed length `m₀`, then
one automatically gets commutation on all words of length `k * m₀` by chunking a
length-`k * m₀` word into `k` consecutive length-`m₀` blocks.  Choosing `k` so that
`k * m₀ ≥ L₀` would then feed directly into

```lean
MPSTensor.boundary_matrix_commutes_of_isNBlkInjective_of_long_word_commutes.
```

Therefore the remaining difficulty is **not** the old bound `m₀ < L₀` by itself.
The true residual bottleneck is sharper:

> we still need a theorem that supplies the missing second one-sided wrapped-window
> extraction (or an equivalent comparison theorem giving a common middle matrix).

Once that exists, the length issue can be repaired by multiplication/chunking.

## Precise blocker on current API

At present I do not see a sound route from the existing wrapped-window witness

```lean
∀ σ_w, Matrix.trace (evalWord A (List.ofFn (cyclicCfg ... σ_w τ)) * X)
  = Matrix.trace (evalWord A (List.ofFn σ_w) * Y_τ)
```

to a same-witness pair of identities

```lean
C_τ * A_j * X = Y_τ * A_j
X * A_j * C_τ = A_j * Y_τ.
```

The first identity is accessible; the second is the missing step.

I can see two honest ways to unblock it:

1. **Mirror wrapped-window factorization at the same wrapped position**
   producing `X * A_j * C_τ = A_j * Y_τ` from the same `Y_τ`; or
2. **Witness-comparison infrastructure across the opposite wrapped position(s)**
   showing that the matrices extracted from the two extreme wrapped windows agree in
   the sense needed to recover a common middle matrix.

Without one of these, the requested theorem

```lean
boundary_matrix_commutes_of_isNBlkInjective
```

would still rely on an unproved compatibility comparison.

## Honest stop point

I am therefore stopping without editing the Lean source files.

The correct next target is no longer “just replace the line-244 injectivity call”;
it is to first prove one additional wrapped-window lemma supplying the missing
second compatibility / common-middle-matrix step.  After that, the rest of the
argument should assemble from the existing `BlockStrip` bridge plus the chunking
observation above.
