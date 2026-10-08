# Physical template boundary slice (#8754)

The seven new declarations in `Geometry/TemplateCutBoundary.lean` prove:

- physical crossing-edge endpoints belong to the source set Z;
- a cut restricted to U avoiding Z maps injectively into the actual unordered
  ambient boundary of U, giving the cardinality comparison;
- actual `Template.IsSeparated` implies every dilation through radius s₀
  avoids Z when D₀≥1;
- physical template dilation/core boundaries have at most 4n edges and shells
  have at most 8n edges, for Ctpl≥24 and j≤s₀.

The final signatures assume separation, not endpoint avoidance. Missing lattice
edges are never counted as physical edges. Empty cuts, empty intersections,
zero radius, maximal radius, negative coordinates, and disconnected domains are
allowed by these statements. No entropy or repaired-family claim is made.

The immutable source is openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a,
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/08-scanner.tex`,
Definition 9.3 and Lemma 9.4 (especially lines 671–678). The source fixes
D₀>2R+10 in `02-initial.tex:225`; interaction range R is nonnegative, so the
sufficient condition D₀≥1 adds no restriction to the source theorem. The
blueprint records only these geometric subresults, not the full Lemma 9.4.
These are original proofs from the mathematical manuscript, with no upstream
Lean proof text reused. The private test fixture is reused from TNLean #8826.

Regressions include the complete thin-real-polygon Template, zero/maximal
radii, negative coordinates, empty/full cuts, unordered orientation, and
missing lattice neighbors. A concrete disconnected physical domain has a
proved nonempty remote cut boundary, proved separation, and a proved nonempty
local template boundary; the final core and shell bounds are instantiated
without additional hypotheses.
