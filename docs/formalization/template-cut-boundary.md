# Physical template boundary slice (#8754)

Draft #8832 is stacked on #8826 at acb16ed1, with #8788 6b053b8b and
#8790 cf6736f4 ancestry. The actual model sources are unchanged, and
`Geometry.boundaryEndpoints` is imported from `CellCounting` without duplication.
The combined-tree generated import aggregators remove inherited conflict markers.

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

The production module built in 1.7 seconds at 38a082f4 in PR CI run
37638741577. All seven axiom outputs contained only propext, Classical.choice,
and Quot.sound. One full-cut regression simplification required correction;
its fix, expanded edge cases, and exact axiom guards await the next run.

Full validation is pending normal PR CI: the toolchain download in this fresh Linux
workspace returned HTTP 403. No Mathlib source build was attempted. The workflow
builds the new module and elaborates the regression/axiom file with strict
options before the full library build. Blueprint completion tags and verified
provenance evidence will be added only after successful checks.

OpenAI Codex assisted the implementation and source comparison. Merges remain
centralized with the parent; this branch has not been merged.
