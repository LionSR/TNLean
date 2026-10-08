# Native nonuniform torus closure independence

## Mathematical scope

`TNLean.PEPS.NativeTorus` contracts the actual ordered edges of
`torusGraph width height`, with both periods at least three. Its virtual
alphabet `D e` may differ on every edge, and `Phys v` may differ at every
vertex. Every bond has its own semi-regular representation, and each physical
site has its own G-injective tensor. No common tensor, bond dimension,
physical dimension, isometry, unitarity, blocking map, spanning assumption,
or independence assumption is introduced.

The closure definition uses the native `graphEdgeTail` and `graphEdgeHead`
with `torusClosureEdgeAssignment`. In particular, an ordered horizontal seam
carries the inverse horizontal element, whereas an ordered vertical seam
carries the vertical element. The regression test checks both conventions.

## Argument and source

SCP10 (arXiv:1001.3807), Definition 5.8 and the independence argument of
Theorem 5.9, are formalized by the following sequence:

1. `closureLabels_eq_iff`: equality of two gauged native closure assignments
   forces equality of vertex gauges across all nonseam bonds. The existing
   native right/up transport lemmas handle the ordered-edge orientations.
   Nonseam connectivity forces a single constant gauge, which simultaneously
   conjugates both seam elements.
2. `bondCoefficientExtraction_closure`: genuine trace-dual pairings for all
   independently represented edges count simultaneous conjugations. This
   uses the canonical network's coherent sum over all vertex gauges.
3. `bondCoefficientExtraction_closure_self`: the exact diagonal scalar is
   `(card G)⁻¹ ^ card (TorusVertex width height)` times the cardinality of the
   common centralizer. It is nonzero because the centralizer contains identity.
4. `linearIndependent_closureClass`: one product of genuine G-injective
   local inverses sends the actual physical closures to canonical closures,
   so the trace-dual separation proves independence of the original vectors.
5. `finrank_commutingClosureSpan`: restriction to commuting classes and
   Mathlib's `finrank_span_eq_card` give exactly one dimension per simultaneous
   conjugacy class of commuting pairs.

Independence for all pair classes is an auxiliary algebraic extension. The
source comparison uses its commuting restriction. Identification of this span
with the microscopic plaquette parent kernel is a separate parent theorem.

## Reuse and validation

Reused existing native transport, nonseam connectivity, dependent product-map,
canonical averaging, and semi-regular trace-dual APIs. Reused Mathlib quotient,
linear independence, and finite-dimensional span results instead of creating
parallel structures.

Strict compilation passed for:

- `TNLean/PEPS/NativeTorusClosures.lean`
- `TNLean/PEPS/NativeTorusClosureIndependence.lean`
- `TNLean/PEPS/NativeTorusClosureDimension.lean`
- `TNLeanTest/PEPS/NativeTorusClosureDimension.lean`

All were checked with automatic implicits disabled, maximum synthesis pending
depth three, the standard Mathlib linter set, and warnings treated as errors.
A separate validation check prints axioms for native gauge separation, the exact scalar,
commuting closure independence, and exact dimension. They use only
`propext`, `Classical.choice`, and `Quot.sound`.
