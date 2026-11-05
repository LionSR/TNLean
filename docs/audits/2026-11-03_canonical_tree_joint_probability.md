# Conditional joint probability for the actual canonical hierarchy

The theorem `intervalSamplingMeasure_canonical_tree_joint_failure_le` uses
the actual canonical sampled operation, the original interval Haar product
law, and the existing balanced root merge list. Its conclusion bounds true
failure of simultaneous viability at the root and every actual listed
internal descendant by `max(r-p-1,0)*beta`. The same original global target
and its whole regional exterior are retained at every interval.

Its analytic premise is explicit: for every valid long parent and every
fixed whole seed, if the two actual baseline children are viable, the true
failure measure of their same canonical sampled parent is at most `beta`.
The improving families and their parameters precede the whole seed.
No measurability, independence, coordinate-freshness, short-leaf, or dimension
hypothesis is supplied separately. The proof derives listed guarded-event
measurability from the actual Borel tree, obtains their true section bounds
from the frozen guarded-section theorem, and uses the shared actual-list
union bound. Nonnegative viability error gives viability of every full
short leaf through the existing top-space theorem. Joint ancestry includes
failure anywhere in the actual root hierarchy in this same guarded union.
There is no extra union over unrelated overlapping intervals.

This is a conditional analytic auxiliary supporting ALVV,
arXiv:1602.08828v2, Figure `fig:algo1` and lines 1777–1817. It does not assert
the analytic parent estimate for an arbitrary family. A physical application
must establish that estimate using the same families and actual child spaces.

Default options were used. The mathematical entry was rendered and inspected.
Ordinary combined compilation and compiled blueprint declarations remain
integration checks. No provider source, artifact, cache, pin, or Mathlib
source was changed or built.
