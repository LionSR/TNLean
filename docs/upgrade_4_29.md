# Lean/Mathlib 4.29 Upgrade Notes

This document records the TNLean-specific lessons from the upgrade to Lean 4.29.0 and Mathlib
v4.29.0.

The official Lean release notes are here:

- <https://lean-lang.org/doc/reference/latest/releases/v4.29.0/#release-v4___29___0>

The main purpose of this note is not to repeat the upstream changelog, but to explain which changes
actually mattered for this repository and how they should shape future code.

## Main upstream change affecting TNLean

The main breaking change for TNLean is the Lean 4.29 section
"Changes to Instance and Reducibility Handling".

In Lean 4.28 and earlier, implicit argument comparison inside `isDefEq` would often unfold
semireducible definitions more aggressively. Lean 4.29 stops doing that by default. The release
notes describe this as surfacing "definitional abuse" in downstream libraries.

For TNLean, this showed up exactly where we rely on type synonyms, transported instances, and
restricted-scalars structure:

- `Matrix n n ℂ` viewed as an `ℝ`-normed space
- `MatrixCLM n := Matrix n n ℂ →L[ℂ] Matrix n n ℂ`
- transport between `Matrix` and `CStarMatrix`
- finite-dimensional / complete-space instances for matrix endomorphism spaces
- `CompatibleSMul`, `IsScalarTower`, `ContinuousSMul`, and related bridges

In practice, many proofs that previously elaborated "for free" stopped elaborating until the
relevant structure was made explicit.

## Other upstream changes that mattered

The same Lean 4.29 notes also record two related changes that affected migration work:

- `inferInstanceAs` now behaves more strictly and is intended for transport between source and
  target instance types. If no transport is needed, prefer `inferInstance` with an explicit
  expected type.
- `simp` and `dsimp` no longer process typeclass instances in the old way. Code that relied on
  instance simplification happening implicitly may now need a more explicit rewrite or instance path.

These changes were not usually the root cause by themselves, but they made old elaboration tricks
less effective.

## What changed in TNLean

The upgrade revealed that TNLean already had repeated local scaffolding for the same matrix and
operator-space structures. Lean 4.29 did not create this duplication, but it made the duplication
fail visibly.

The main cleanup during the migration was to centralize that repeated infrastructure:

- [MatrixFunctionalCalculus.lean](../TNLean/Algebra/MatrixFunctionalCalculus.lean) now holds the
  shared matrix CFC setup.
- [MatrixOperatorSpace.lean](../TNLean/Algebra/MatrixOperatorSpace.lean) now holds the shared
  matrix / CLM operator-space setup.

This is the intended direction. We should prefer one shared low-level module over repeating local
instance bundles in semigroup, channel, or MPS files.

## Typical 4.29 failure modes in this repository

During the upgrade, the most common failures were:

- missing `CompatibleSMul` instances after restricting scalars from `ℂ` to `ℝ`
- missing `IsScalarTower` or `ContinuousSMul` evidence for matrix spaces
- `CompleteSpace` / `FiniteDimensional` synthesis failures for `MatrixCLM`
- direct reuse of matrix CFC lemmas failing until the `CStarMatrix` transport was made explicit
- proofs depending on definitional equality between a local alias and the underlying matrix-CLM type
- deprecated Mathlib interfaces, such as `push_neg`-style usage or older cyclic-group lemmas

These should now be viewed as structural signals, not as invitations to copy-paste another local
instance block.

## Migration policy for TNLean

When adapting existing code or writing new code on top of Lean/Mathlib 4.29, prefer the following
rules.

### 1. Do not use the global compatibility switch

Lean 4.29 allows projects to recover older behavior with:

```toml
backward.isDefEq.respectTransparency = false
```

The official release notes describe this as a migration aid. TNLean should not use it project-wide.
If a declaration truly needs it temporarily, localize it to the smallest possible declaration and
treat it as migration debt to remove.

### 2. Prefer shared infrastructure over local instance blocks

If a file needs matrix / CLM restricted-scalars infrastructure, first check:

- [MatrixOperatorSpace.lean](../TNLean/Algebra/MatrixOperatorSpace.lean)
- [MatrixFunctionalCalculus.lean](../TNLean/Algebra/MatrixFunctionalCalculus.lean)

Do not duplicate:

- `MatrixCLM` aliases
- local `PosSMulMono ℝ ℂ`
- repeated `NormedSpace ℝ`, `Module ℝ`, `IsScalarTower`, `ContinuousSMul` bundles
- ad hoc matrix CFC instances

If a genuinely new shared bridge is needed, add it once to the relevant helper module.

### 3. Prefer explicit expected types

When instance search becomes fragile, first try:

- `haveI : ... := inferInstance`
- explicit type annotations
- explicit `show ...` / `change ...` steps

Only use `inferInstanceAs` when transporting from one instance type to another is actually the
point.

### 4. Treat local aliases with caution

Type aliases that are "obviously the same" mathematically may no longer be definitionally
interchangeable enough for elaboration. If the alias does not add mathematical meaning, prefer the
shared canonical name.

For this repository, `MatrixCLM (Fin D)` is usually preferable to a file-local `CLM D`.

### 5. Bias toward Mathlib-native rewrites

When a proof breaks, do not stop at a mechanical patch if a newer Mathlib-native lemma or API gives
the cleaner statement. The 4.29 upgrade is a good opportunity to remove brittle local proof shape.

## Why the upgrade seemed to add boilerplate

The upgrade did not mostly add new mathematics. It forced TNLean to write down mathematical
structure that older elaboration had been recovering implicitly.

So the apparent boilerplate came from two sources:

- real upstream tightening of transparency and instance behavior in Lean 4.29
- pre-existing local duplication in TNLean that the upgrade made impossible to ignore

The correct long-term response is not to preserve every old proof shape verbatim, but to keep
compressing repeated compatibility scaffolding into shared, Mathlib-native infrastructure.

## References

- Lean 4.29.0 release notes:
  <https://lean-lang.org/doc/reference/latest/releases/v4.29.0/#release-v4___29___0>
- In particular, see the subsection "Changes to Instance and Reducibility Handling".
