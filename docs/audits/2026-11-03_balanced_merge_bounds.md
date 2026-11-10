# Geometry of the actual balanced merge list

Every member `[a,b)` of the existing midpoint merge list descended from
`[p,r)` satisfies `p ≤ a ≤ b ≤ r` and has length greater than the positive
leaf width. The proof follows the actual list recursion by strong induction
on root length; it uses no second tree representation. The public theorem
name and signature of the proposed membership bounds are unchanged.

This supports ALVV, arXiv:1602.08828v2, Figure `fig:algo1` and lines 1777–1817.
In particular it supplies valid finite endpoint coordinates for every listed
internal interval when `r ≤ L`, without clamping invalid endpoints.

Default options were retained. Ordinary combined compilation and compiled
blueprint declarations remain integration checks. No shared source, cache,
artifact, pin, or Mathlib source was changed or built.
