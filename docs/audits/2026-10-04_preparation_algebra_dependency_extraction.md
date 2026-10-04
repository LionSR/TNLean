# Preparation algebra dependency extraction

Partial work on [#8637](https://github.com/LionSR/TNLean/issues/8637), under the
proof-debt tracker [#4529](https://github.com/LionSR/TNLean/issues/4529).
Baseline: `b9b093adafcdbe4d0eaa5c6517fe8313c80da34f`; Lean/Mathlib
`v4.35.0-rc3`; QICLean `af43b1c6f147a4a717583c9e6f4049a1306ea34e`.
The pins and package Lean options are unchanged.

## Change and ownership

- Move the four existing `Matrix` contraction identities from
  `ApproximatingState` to their principal domain consumer, `BlockIsometryState`:
  `sum_star_mul_prod_eq_sum_conjTranspose_mul`, `sum_star_mul_prod_of_support`,
  `IsIsometry.sum_star_mul_prod`, and `IsIsometry.sum_star_mul_tensorPower`.
- Move the concrete fixed-point tensor, cyclic pair states and their algebraic
  identities to `FixedPointPairState`. `FixedPointPairs` imports it and retains
  the two spectral convergence theorems.
- Move generic block-circuit assembly to `BlockStatePreparation`.
  `DepthUpperBound` imports it and retains the uniform approximating-state bridge.
- Narrow `PairLayer` to the concrete pair-state module. Regenerate the directory
  aggregator.

There is no new general-purpose matrix API or `Algebra` module. The existing
finite-configuration identities stay in the Preparation domain, immediately
beside their block-state consumers, with their existing names. This retains the
current ownership boundary rather than creating a competing local matrix library.
An upstream migration remains a separate library decision.

All 54 moved declarations are existing code: four matrix identities, 22 pair-state
items (including two private helpers), and 28 block-circuit items. The three
implementation blocks are token-identical after removing comments and whitespace;
no mathematical statement or proof was changed. The original owner modules still
export the moved public names through imports. No forwarding theorem, deprecation
alias, new hypothesis, or new axiom was added. The net Lean change is +70 lines,
from module headers and context; the gain is dependency separation, not a proof
line-count reduction.

## Structural result

Source-import closures were traversed with comments removed, excluding Mathlib
and counting TNLean, pinned QICLean and Gametheory modules. Both traversals use
the same pins and source root. No import cycle was found.

| Interface | Before | After | Whole-Mathlib path after |
| --- | ---: | ---: | --- |
| `BlockIsometryState` | 319 = 97 TNLean + 219 QICLean + 3 Gametheory | 90 = 22 TNLean + 68 QICLean | None |
| `FixedPointPairState` | New import boundary | 32 = 6 TNLean + 26 QICLean | None |
| `BlockStatePreparation` | New import boundary | 113 = 45 TNLean + 68 QICLean | None |
| `PartialIsometryPreparation` | 357 | 359 | Still present |

The first interface no longer reaches `NormalTensorGauge`, `Gametheory.Brouwer`,
`Gametheory.Brouwer_product`, or `Gametheory.Scarf`. The latter three import the
whole Mathlib library. The generic circuit interface has the same separation.

## Preserved and deferred scope

`InhomogeneousPreparation` is unchanged, including its `DepthUpperBound` import.
Consequently `PartialIsometryPreparation` still reaches the high-level convergence
route. Its count increases by the two new re-exported modules; this PR does not
claim to have narrowed that consumer. The existing gap-note link to
`DepthUpperBound` remains valid because that module still exports the declarations.

The full consumer migration and the controlled before/after capstone benchmarks
requested by #8637 remain open. In particular, the historical cold-build times
are not used as a speedup benchmark. No result from another in-flight preparation
branch is incorporated here.

## Verification

At candidate `83d4837a0d398479fc46138c7979655e5cb60e26`:

- The pair-state and block-isometry modules passed isolated-output Lean compilation
  with all four package Lean/linter options and no diagnostics.
- A second exact-tree check passed all nine modules needed by `BlockStatePreparation`,
  including the changed `PairLayer`. Source-identical cached dependencies were
  checked against their actual Lake build-trace hashes; dependencies affected by
  a rebuilt module were rebuilt rather than reused.
- Observed single-thread elapsed times in that check were about 3.1 seconds for
  `FixedPointPairState`, 3.5 seconds for `BlockIsometryState`, and 3.7 seconds for
  `BlockStatePreparation`. These are post-change observations only, not a controlled
  before/after comparison.
- Generated imports, integrity, numbered-file, oversized-file, committed prose and
  whitespace checks passed. All declaration names and existing Blueprint tags are
  retained. Previously untagged moved helpers are linked to the existing
  block-circuit proof, with their coordinate identities made explicit.
- All 46 open PR changed-file lists were checked before editing; none touched the
  changed handwritten Lean source files.

The prebuilt Mathlib cache was verified; Mathlib was not rebuilt from source.
Full-root and compiled declaration verification are required on the published
commit; the PR checks record that result.
