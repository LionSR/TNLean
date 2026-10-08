# Labelled torus flat-connection audit

## Mathematical scope

`TNLean/PEPS/TorusBondFlatConnection.lean` proves the group-valued seam
reduction required in SCP10, Theorem 5.5 and `eq:2d:move-strings`, for the
native labelled horizontal and vertical bonds. It does not assert the
remaining tensor-network spanning or local-inverse steps of that theorem.

The labels are the existing `TorusBondLabels width height G`, a pair of
vertex-indexed functions. Horizontal labels transform by
`H'(v) = q(v + (1, 0)) H(v) q(v)⁻¹`; vertical labels transform by
`V'(v) = q(v) V(v) q(v + (0, 1))⁻¹`. The plaquette condition is
`V(v + (1, 0)) H(v + (0, 1)) = H(v) V(v)`.

For arbitrary groups and all positive periods, every flat assignment has a
vertex gauge giving the standard horizontal seam `h` and vertical seam `g`,
with `g h = h g`. Conversely, every vertex-gauge transform of a commuting
closure is flat. Neither finiteness of the group nor periods at least three
are required. In particular, no parallel bonds of the two-by-two torus are
identified.

## Reuse and orientation check

The proof reuses the existing group-valued `IsTorusFlat` tree-gauge lemmas,
which already apply at all positive periods. Those lemmas are declared
before the graph-specific section of `TorusFlatConnectionGauge.lean`.
No theorem from its graph-specific section is used. The conversion is
horizontal transport `H`, vertical transport `V⁻¹`, and the inverse of the
existing rooted-tree gauge. This explains the opposite native vertical
convention without treating the group as abelian.

The finite-sum identity `sum_torusBondGauge` uses Mathlib's `Equiv.mulRight`
and `Equiv.sum_comp`; it establishes gauge invariance of averaging any
function on the actual bond assignments.

## Validation

Both the new source and `TNLeanTest/TorusBondFlatConnection.lean` elaborate
with Lean v4.35.0-rc3 and the package's pinned dependencies under:

```text
-j1 -DautoImplicit=false -DrelaxedAutoImplicit=false
-Dlinter.mathlibStandardSet=true -DwarningAsError=true
```

The tests check:

- The classifier at period two over any group, without additional instances.
- All four explicit rooted-gauge values at period two.
- Horizontal holonomy `H(1,0) H(0,0)` and vertical holonomy
  `V(0,0) V(0,1)`, with their commutation consequence.
- Flatness of relative vertex labels.
- Separate labels on parallel horizontal bonds.
- The classifier at the positive degenerate period one.
- A noncommuting pair in the permutation group on three elements fails
  closure flatness, while an equal pair satisfies it.

The classifier, orbit characterization, explicit tree-gauge theorem, and
averaging theorem use only `propext`, `Classical.choice`, and `Quot.sound`.
No unproved declarations or additional axioms are introduced. Source and
test files pass the forbidden-proof-token scan and `git diff --check`.
The repository tactic-pattern scanner was run; this change does not add a
new repeated proof pattern requiring promotion. Mathlib was not rebuilt:
validation used the exact existing dependency cache through a private
symlink overlay.

Full-repository build, generated import-router updates, and blueprint
integration are deliberately left to the integrating task.
