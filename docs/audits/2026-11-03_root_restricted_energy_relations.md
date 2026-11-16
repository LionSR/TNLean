# Energy relations on the actual balanced root subdivision

The new generic lemma accepts an actual relation on long intervals and a
local energy-preserving node certificate only when the interval belongs to
the specified root's balanced merge list. The original attained-minimum
certificate is explicit for every valid interval, as in the existing global
scalar-assignment lemma. No filtering, sampling, center or global successful
energy assignment is assumed.

The relation is extended outside the listed subdivision by exact original
minima. This extension preserves the energy error width independently of
the two child estimates. One call to the existing global recursion then
returns the root and listed-node estimates, exact minima at their short
children, and the specified relation at those same assigned child values.
Neither a new recursion nor a parallel realization predicate is introduced.
Variable collars and the corrected terminal untrimmed image may be included
in the supplied actual relation.

The existing word-family root theorem is now an active specialization of
this generic lemma. Its public header is byte-identical. All other old
public headers and unchanged proofs are byte-identical, including the
private recursion and the existing global relation theorem. The conditional
source scope remains explicit; there is no success premise on all overlapping
intervals outside the actual root subdivision.

Temporary commands were removed. Partial proof diagnostics, including an
unnecessary simplification in the old specialization, are preserved; no
resource limit was changed.

The shared root-restriction pattern is recorded in the tactic ledger. Combined
ordinary gates remain required. No provider, dependency pin, cache or Mathlib
source was changed.

Application to the actual terminal-image relation on one successful original-
target history event remains a separate physical composition. No runtime,
measurable scalar selection or complete physical energy theorem is claimed.
