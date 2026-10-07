# Physical template boundary slice (#8754)

Draft #8832 is stacked on #8826 at ad9db077e1a7acb105a4d00e0d9c1bccba3e4c1d, with #8788 162fa69a88d407d97c5ce2682c95d2f87542cf10 and
#8790 cf6736f4 ancestry. The actual model sources are unchanged, and
`Geometry.boundaryEndpoints` is imported from `CellCounting` without duplication.
The model owner withdrew 6b053b8b because its generated imports contained
conflict markers; 162fa69a8 supersedes it. Our combined-tree aggregators were
regenerated and checked, and the corrected model head is now in ancestry.
No validation claim is made for the withdrawn model head.

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

The production module built in 1.3 seconds at
`addfd463ce7ac29b03ca00b5fe4d452cd8fe35cd` in
[PR CI run 37641625254, build job 112863109726](https://github.com/LionSR/TNLean/actions/runs/37641625254/job/112863109726).
Every build-job step through `Complete job` reports success, including the full
12,510-job library build, lint target, strict actual-model regressions, exact
axiom guards, explicit axiom audit, all repository regressions, style,
compilation times, and compiled blueprint/paper-gap declarations. The aggregate
job status lagged behind its completed steps when this evidence was captured;
no claim is made that the entire workflow is green.

All seven captured axiom records contain only `propext`, `Classical.choice`,
and `Quot.sound`. The build and explicit axiom output are preserved in
[the build evidence](../provenance/evidence/8754-cut-build.log) and
[the axiom evidence](../provenance/evidence/8754-cut-axioms.log), with hashes in
the seven verified provenance entries. Timestamp/ANSI removal and whitespace
normalization are stated in the evidence. All 199 combined provenance records
validate with the immutable upstream checkout. Source-level blueprint sync
passes with the pinned QICLean checkout present.

Regressions include the complete thin-real-polygon Template, zero/maximal
radii, negative coordinates, empty/full cuts, unordered orientation, and
missing lattice neighbors. A concrete disconnected physical domain has a
proved nonempty remote cut boundary, proved separation, and a proved nonempty
local template boundary; the final core and shell bounds are instantiated
without additional hypotheses.

Remaining validation: the separate blueprint-render job 112863110027 reported
failure without any step records; its log download returned `BlobNotFound`.
The job-retry API and two PR-comment attempts returned connector internal
errors. This is not a diagnosed LaTeX/source error. The evidence update triggers
fresh final-head CI; the rendering result must be checked before merge.
Local toolchain retrieval returned HTTP 403, so no local Mathlib proof-source
build was attempted. The blueprint completion marks refer only to these seven
compiled, source-faithful geometric results, not the full Lemma 9.4.

OpenAI Codex assisted the implementation and source comparison. Merges remain
centralized with the parent; this branch has not been merged.
