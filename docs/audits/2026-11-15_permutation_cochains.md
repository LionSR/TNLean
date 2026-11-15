# Permutation-coefficient foundation for #8320

This is an independent first part of [#8320](https://github.com/LionSR/TNLean/issues/8320),
based on `cbf482955f46f36c71c95ab1547b3cc86b6d58c2`. It does not close the issue.
No scalar three-cochain work (#8319), legacy-definition deletion, or consumer migration
(#8321) is included.

## Source and Mathlib comparison

`Papers/2502.20257/main.tex:1915–1923` gives `eq:Lsymbgauge` and `eq:omega_and_Ls`.
Lines 5914–5921 give the block coboundaries, with the last group index corrected as
documented in `fbc25_two_cochain_coboundary_index_typo.tex`.

At the pinned Mathlib revision `625d8914199bc567cca9b91f90e8e5afafa5ae51`,
`GroupTheory/GroupAction/DomAct/Basic.lean` explains why a permutation action on a
function space must not be a global instance: it conflicts with pointwise actions.
The new scoped instance uses inverse pullback, `(g • f)(x) = f(g⁻¹ • x)`.
The representation is an abbreviation for `Rep.ofMulDistribMulAction`; the
differentials are literally `groupCohomology.d₁₂` and `groupCohomology.d₂₃`.
There is no new cocycle predicate or cochain-complex definition.

The necessary coordinate changes are

```text
cγ(g)(x)   = γ(g, g⁻¹ • x)
cL(g,h)(x) = L((gh)⁻¹ • x, g, h).
```

Both are invertible. Evaluating their differentials at `gh • x` and `ghk • x`
gives the source's coboundaries. The compatibility theorem states that `d₂₃ cL`
equals the constant-function image of the scalar three-cochain exactly when
the source compatibility identity holds. It requires neither finite groups,
transitive actions, nonempty block sets, nor a cocycle hypothesis on that scalar cochain.
The coefficient group is any commutative group, including complex units and `Circle`.

No existing declaration is removed or weakened. In particular, `LSymbol`,
`GeneralizedCocycle`, scalar cohomology, their consumers, and dependency pins are untouched.
The old overlap PRs #8284 and #8275 are both closed; no open PR was found by searching
for #8320 before implementation.

## Validation and remaining blocker

- Generated import aggregation and whitespace checks pass.
- The reader-facing prose check passes.
- Source-level blueprint synchronization finds every new declaration and no duplicate
  tag. Its full-tree report contains 563 missing references; the Mathlib and QICLean
  checkouts are absent, and none of the reported missing names belongs to this module.
- Independent exact rational computations on the noncommutative permutation action
  of `S₃` on three points checked 108 degree-one and 648 degree-two evaluations.
  These computations check the coordinate convention, not Lean elaboration.
- `lake build TNLean.Algebra.PermutationCochains` cannot start: `lake` is not installed.
  There is no `.lake` directory. The selected environment reports an enforced disabled
  network policy, and toolchain-download and dependency-clone requests return HTTP 403.
  No Mathlib source build or cache mutation was attempted.

Lean elaboration, linter-bearing targeted build, and compiled blueprint declaration
checks remain required before review readiness. On a configured Linux environment,
fetch the pinned prebuilt artifacts with `lake exe cache get`, verify
`.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean`, then run
`lake build TNLean.Algebra.PermutationCochains`. Do not rebuild Mathlib from source.

Prepared with OpenAI Codex; the exact model identifier is not exposed in this session.
