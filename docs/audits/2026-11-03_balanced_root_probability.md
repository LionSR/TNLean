# Guarded failures in one actual balanced hierarchy

Every member of the actual midpoint merge list determines a valid finite
endpoint coordinate. The coordinate is constructed only for a listed
interval inside a valid root; neither endpoint is clamped or assigned an
out-of-range default. It reduces to that interval's original endpoint pair.

`intervalSamplingMeasure_guarded_failure_union_le` bounds the union of the
actual listed guarded failures by `max(r-p-1,0)*beta`, using the fixed
independent interval Haar law. Its premises are exactly measurability of
each listed guarded event and a bound `beta` on every true section formed
by updating that interval's own coordinate in a whole seed. The proof uses
the existing finite-list section theorem on the list of occurrences, then
the existing merge count. Repeated entries would not invalidate the bound.
No leaf invariant is needed for this primary union estimate.

`intervalSamplingMeasure_root_failure_le` is an active corollary. Its only
recursive invariant is that the full local space satisfies the property at
valid short leaves. Existing deterministic failure ancestry includes root
failure in the same guarded union. The primary bound is also available for
other failure events shown to lie in that union.

These are explicitly conditional measure-theoretic auxiliaries supporting
ALVV, arXiv:1602.08828v2, Figure `fig:algo1` and lines 1777–1817. They do not
assert physical section bounds or assume success of the actual long-node
operation. Establishing those section bounds for a particular sampled
operation is a separate mathematical step.

The final actual-name strict check passed in 4.941 seconds against immutable
TNLean `435cbe7fe53e5d3a04c1b8eb2382753749f21a64` and its own QICLean
`b2ea12a0139820758e161514968ed9ead661c5a7` package, with the frozen geometry,
ancestry, interval law and finite-list probability results supplied as
explicit source/object overrides. All 43 selected dependency pairs and the
build inputs were guarded. A three-name imported foundation inspection
passed in 4.819 seconds with only `propext`, `Classical.choice`, and
`Quot.sound`; its temporary source was deleted. Default options were used.
The earlier root-only checkpoint is retained under the private
`superseded-root-only` directory and is superseded by this shared-union proof.

Generated imports, source/blueprint synchronization, reader prose, proof
integrity, whitespace and pattern checks passed. The mathematical entry
was rendered and inspected. Ordinary combined compilation and compiled
blueprint declarations remain integration checks. No provider source,
artifact, cache, pin, or Mathlib source was changed or built.
