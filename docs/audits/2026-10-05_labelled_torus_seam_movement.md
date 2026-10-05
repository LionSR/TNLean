# Native labelled-torus seam movement

## Statement and source

`TNLean/PEPS/TorusBondClosureSeamMovement.lean` proves the group-valued
seam deformation used in Schuch, Cirac, and Pérez-García,
arXiv:1001.3807, Theorem 5.5 and equation `eq:2d:move-strings`.

For commuting elements `g, h`, a horizontal seam at column `c` and a downward
vertical seam at row `r` are obtained from the standard zero seams by the
explicit vertex gauge

`q(x,y) = torusSeamGauge (g⁻¹) r y * torusSeamGauge h c x`.

The proof first moves the horizontal seam and then the vertical seam. In each
step, commutation preserves the transverse insertion. The native vertical bond
convention is retained, so its seam gauge uses the inverse vertical label.

## Scope

- An arbitrary group and arbitrary positive horizontal and vertical periods.
- No finite-group assumption for the explicit gauge identity.
- No representation, matrix coordinate type, physical dimension, injectivity,
  semi-regularity, or unitarity assumption.
- Horizontal and vertical edges are indexed separately by their initial vertex;
  period-two parallel edges and period-one self bonds are never merged.
- For a finite group, `sum_torusBondGauge_closureAt` identifies the all-vertex-gauge
  sums of any function into any additive commutative monoid. Applying a common
  normalization factor gives the corresponding normalized averaging statement.

This is the dimension-independent group step needed before evaluating labels
in independently dimensioned bond representations. It does not itself assert
the dependent-dimensional cut-space theorem or a general blocking theorem.
The imported `TorusMatchedCutClosureMembership` supplies only its pure
`torusSeamGauge` functions and identities; its matrix-valued closure theorem is
not used.

## Declarations

- `torusBondClosureLabelsAt`
- `torusBondClosureLabelsAt_zero`
- `torusBondClosureSeamGauge`
- `torusBondGauge_horizontalClosureAt`
- `torusBondGauge_verticalClosureAt`
- `torusBondGauge_closureSeamGauge`
- `exists_torusBondGauge_eq_closureAt`
- `sum_torusBondGauge_closureAt`

## Validation

Both the source module and
`TNLeanTest/PEPS/TorusBondClosureSeamMovement.lean` were compiled with:

```
-j1 -DautoImplicit=false -DrelaxedAutoImplicit=false
-Dlinter.mathlibStandardSet=true -DmaxSynthPendingDepth=3
-DwarningAsError=true
```

Validation used a private output overlay on the supplied exact pinned Lean and
prebuilt dependency cache. Mathlib was not rebuilt. The regressions cover
arbitrary groups, additive-monoid-valued averaging, unequal periods 2 by 3,
period-one self bonds, the actual period-two edge support, and a nonabelian
ambient permutation group with commuting labels. Guarded axiom checks for the
explicit seam identity and the averaging theorem report only `propext`,
`Classical.choice`, and `Quot.sound`.

The repository tactic-pattern scanner and whitespace check were run. The two
transverse conjugation cancellations reuse Mathlib's `Commute.mul_inv_cancel`;
no new custom tactic or copied cancellation proof is introduced. Shared import
routers, the shared tactic ledger, and blueprint files are left to the
integration owner under the assigned new-files-only scope.
