# Geometry of the actual balanced merge list

Every member `[a,b)` of the existing midpoint merge list descended from
`[p,r)` satisfies `p ≤ a ≤ b ≤ r` and has length greater than the positive
leaf width. The proof follows the actual list recursion by strong induction
on root length; it uses no second tree representation. The public theorem
name and signature of the proposed membership bounds are unchanged.

This supports ALVV, arXiv:1602.08828v2, Figure `fig:algo1` and lines 1777–1817.
In particular it supplies valid finite endpoint coordinates for every listed
internal interval when `r ≤ L`, without clamping invalid endpoints.

The actual-name strict check passed in 4.050 seconds against immutable
TNLean `435cbe7fe53e5d3a04c1b8eb2382753749f21a64` and its own QICLean
`b2ea12a0139820758e161514968ed9ead661c5a7` package, guarding three selected
source/object pairs and the build inputs. An imported foundation inspection
passed in 4.042 seconds with only `propext`, `Classical.choice`, and
`Quot.sound`; its temporary source was deleted. Default options were retained.
Generated imports, source/blueprint synchronization, reader prose, proof
integrity and whitespace checks passed. Ordinary combined compilation and
compiled blueprint declarations remain integration checks. No shared source,
cache, artifact, pin, or Mathlib source was changed or built.
