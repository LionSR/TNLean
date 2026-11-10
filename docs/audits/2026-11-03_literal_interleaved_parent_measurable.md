# Borel projections of the literal sampled interleaved parent

The existing interval family-and-trim step and every finite iterate now
have Borel actual orthogonal projections when the initial actual projection
is Borel. Each successor applies the fixed family to the preceding current
space and performs that round's actual collective trim. The implementation
and its public signatures are unchanged.

Basis invariance identifies the trim computed from the existing chosen
orthonormal basis with the canonical range trim of that same projection. The
basis is transported across an equality of its actual range using Mathlib's
isometric equivalence of equal subspaces. This avoids a measurable-basis
assumption. Induction follows the existing iterator, including zero rounds,
empty families and zero spaces.

The canonicalSampledIntervalInterleavedTrim parent has the exact native
interval space as its candidate domain. For configuration space C, its
random argument belongs to the fixed finite product of U(j), for
0 ≤ j ≤ card C. It relabels the actual candidate projection through the
fixed equivalence Fin(card C) ≃ C, uses the existing canonical range-basis
sample at the actual-rank unitary coordinate, transports the sample back
to the interval, and calls the existing intervalFamilyTrimIterate for
Nat.clog D (D² s) rounds. Its actual projection is jointly Borel in the
candidate history and unitary product. The original viability event is
Borel for every real error and fixed global target, retaining the whole
parent exterior. No comparison target or chosen varying measurable hull
is assumed.

These are auxiliaries for ALVV, arXiv:1602.08828v2, Lemma l:rs,
lines 530–558, and Figure fig:merge-prime, lines 1668–1670. The corrected
current-space assignment and larger integer round count remain explicit
in the existing approximation-parameter note. Native-coordinate uniform
sampling bounds and whole-tree probability are separate contributions.
This checkpoint proves neither a joint adaptive success probability nor
a runtime estimate.

All selected source, object, root-input, prebuilt-Mathlib and changed-importer
guards passed. Its temporary source was deleted.

Explicit local-space, exterior and history types fixed the elaboration without
increasing any proof budget.

The area-law tactic scan was recorded; its repeated patterns lie in unchanged
files, and the new proof shares the generic image-projection and
canonical-trim lemmas. No provider or cache was modified, no compiled artifact
was copied and no Mathlib source was built. Canonical builds and compiled-book
checks remain coordinated integration gates.
