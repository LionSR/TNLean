# Independently matched torus projector contractions

The subsequent common-alphabet reverse closure inclusion is recorded in
[the reconstruction audit](2026-10-05_scp10_four_cut_closure_reconstruction.md).

## New mathematical results

`TorusMatchedProjectorExpansion.lean` generalizes the actual native contraction
identity to separate matrices on all four incident legs. Its projector expansion
uses independently chosen horizontal and vertical bond representations `Uh v`
and `Uv v`, with the same bond's representation evaluated at its head and tail.
The horizontal operator becomes
`Uh v (q (v.x + 1, v.y)) * Oh v * Uh v ((q v)⁻¹)`;
the downward vertical operator becomes
`Uv v (q v) * Ov v * Uv v ((q (v.x, v.y + 1))⁻¹)`.
There is one vertex group label per site and the normalization is
`|G|⁻|vertices|`. This is an equality of the actual bond-network coefficients,
not a definition of a surrogate averaged contraction.

The same four-leg identity proves invariance under arbitrary vertex-dependent
group gauges for site-dependent invariant tensors. No unitarity,
semi-regularity, local injectivity, or region Gram premise occurs in this step.

`TorusMatchedCutClosureMembership.lean` applies this invariance to move the two
seams independently. The elementary group-valued cyclic seam identities are
public. The resulting boundary witness is the product of the representations
on the actual crossed bonds. Consequently the matched commuting closure span
is contained in every cut space, hence in the intersection of the four
native two-by-two cut spaces.

## Source scope

Source: Schuch, Cirac, Pérez-García, arXiv:1001.3807, Definition 5.1,
Theorem 5.5, Definition 5.6, equation `eq:2d:move-strings`, and the projector
contraction in the proof of Theorem 5.9.

- Site tensors and oriented bond representations are independently varying.
- Both endpoints use the same representation for their particular bond.
- Period-two parallel bonds and period-one self bonds are retained. No
  `SimpleGraph` contraction or minimum circumference of three is used.
- A common finite coordinate alphabet remains imposed on all bonds. Different
  bond dimensions are not covered by this change.
- The cut-space result is the forward inclusion only. This module does not
  assert the reverse inclusion or the full source theorem.

## Verification

All of the following passed with Lean's standard Mathlib linter set and
warnings treated as errors:

- `TNLean.PEPS.TorusMatchedProjectorExpansion`
- `TNLean.PEPS.TorusMatchedCutClosureMembership`
- `TNLeanTest.PEPS.MatchedTorusProjectors`

The regression file checks the exact opposite-bond indexing on a two-by-two
torus, independently varying representation families in the four-cut
inclusion, the explicit matched boundary witness, and the actual one-by-one
torus contraction expansion. Its six axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. No proof placeholders, added axioms, or
kernel-bypassing tactics were introduced.

Validation used the existing precompiled dependencies and a private symlink
overlay, with `-j1 -DautoImplicit=false -DrelaxedAutoImplicit=false
-Dlinter.mathlibStandardSet=true -DwarningAsError=true`. No Mathlib rebuild
was performed. Root import routers and blueprint integration are left to the
coordinating change; the checks above are focused module checks, not a full
repository or blueprint build.

## Library and repetition review

The proof uses Mathlib's Kronecker multiplication, matrix entry expansion,
`Fintype.prod_sum`, and `Fintype.sum_equiv`. The gauge proof is the
four-independent-leg generalization of the existing two-operator proof. The
cyclic group arithmetic currently appears twice because the original seam
helpers are private. Both pairs can subsequently be deduplicated by moving
the general identity into a lower dependency layer and making the uniform
API a specialization; this patch does not modify established modules.
The repository tactic-pattern scanner was run on `TNLean/PEPS`; no new custom
tactic was needed.
