# Issue #704 follow-up after landing the block-word stripping family

Date: 2026-04-21
Branch: `feat/704-block-word-strip`

## What this branch adds

This branch lands the algebraic block-word stripping family identified by the
wave-1 audit:

- `MPSTensor.groundSpaceMap_injective_of_wordSpan_eq_top`
- `MPSTensor.groundSpaceMap_injective_of_isNBlkInjective`
- `MPSTensor.exists_right_factor_of_block_word_compatibility`
- `MPSTensor.commutes_block_words_of_commutes_long_words_of_isNBlkInjective`
- `MPSTensor.commutes_all_of_commutes_long_words_of_isNBlkInjective`
- the WrappingWindow corollary
  `MPSTensor.boundary_matrix_commutes_of_isNBlkInjective_of_long_word_commutes`

These theorems prove the exact algebraic reduction

$$
\text{(commutation on all words of length }m \ge L_0) \implies
\text{(commutation on all generators)}.
$$

So the old one-site stripping step has now been replaced by a genuine
length-$L_0$ stripping theorem family.

## Remaining blocker for the full wrapping theorem

The full target

- `WrappingWindow.boundary_matrix_commutes_of_isNBlkInjective`

is still not landed on this branch.

After the new theorem family, the remaining missing input is sharper than in PR
#718:

> we still need a wrapped-window comparison theorem that extracts **long-word
> commutation** from the cyclic ground-space hypothesis.

Concretely, the new theorems finish the argument **once** one has a statement of
the form

```lean
∀ ω : Fin m → Fin d,
  X * evalWord A (List.ofFn ω) = evalWord A (List.ofFn ω) * X
```

for some `m ≥ L₀`.

What is still missing in `WrappingWindow.lean` is a block-injective replacement
for the injective trace-stripping step inside `wrapping_window_matEq` which
produces that long-word commutation family from the wrapped cyclic-window
hypothesis.

In other words, this branch removes the algebraic roadblock identified in the
wave-1 audit, but the periodic-side extraction step still needs one more theorem
in the wrapping-window analysis itself.

## Practical consequence

This branch is therefore a **real infrastructure PR**, not an issue-closing PR:

- it resolves the abstract block-word stripping gap from audit #718;
- it narrows the remaining #704 work to a single periodic-side extraction step;
- it still does **not** close #704 / #588 by itself.
