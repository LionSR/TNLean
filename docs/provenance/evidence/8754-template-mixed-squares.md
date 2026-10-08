# Actual-template mixed dyadic-square estimates

This contribution concerns `scanner:mixed-piece` and its use in the covering
argument, `08-scanner.tex` lines 622–649, following actual Definition 9.3
geometry. Source pin: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
No upstream Lean source or proof text is reused.

## Ownership and prerequisites

Fresh #8754/#8758/#8837 comments and the open mixed-dyadic PR search were
inspected before implementation. No mixed-square counting owner was found.
Scope was announced in #8754 comment 6051372294, #8758 comment 6051373435,
and #8837 comment 6051374207. The initial-star and sector proofs remain with
the #8758 group. #8798/#8826/#8832/#8840 retain their separate authors.
Parent controls all merges.

The new branch is separate from the frozen #8863 checkpoint
`e020b1ab1de9b99f71e0fd1cb5350b8a0d8820cf`. That exact partition head passed
all jobs in [CI run 37716612542](https://github.com/LionSR/TNLean/actions/runs/37716612542),
including full Lean, strict regressions and imported dependency audits,
compiled declarations, complete blueprint rendering and timing. The result
was recorded on #8863 in comment 6051345245. It is prerequisite evidence,
not evidence for this new contribution.

The row prerequisite is #8798's verified immutable head
`85f0c6e1b01a6297d32839eb5a4b118f7480f484`. Its four production proof files
are byte-identical to latest owner head
`684844a83337abdc0d68092cbb29ec2807506e4e`. Merge `9d7bf11ab` retains both
contributions and resolves only additive import, chapter-input and glossary
conflicts. Toolchain and all dependency pins are unchanged; this avoids an
unrelated dependency refresh. All 247 inherited provenance records and their
historical evidence are preserved.

## Exact candidate scope

For `u = 2^k`, the candidate conclusions are:

- Coordinate bounds for the existing dyadic cells and mixedness/count
  subadditivity for arbitrary finite unions and differences.
- Actual sampled points and integer-dilated points can move to any occupied
  row with horizontal displacement at most the row displacement. The proof
  derives this from the existing integer supporting strips and row interval
  theorems; no regularity field is supplied.
- For each actual template piece at every radius `j`,
  `u * #mixed((sample i)_j) ≤ 24 * (s₀ + j + u)`.
- The finite union has bound `24 * N₀ * (s₀ + j + u)`. For `Ctpl ≥ 24`
  and `j ≤ s₀`, the core, dilated template and shell have respective scaled
  bounds `n + 24*N₀*u`, `2*n + 24*N₀*u`, and `3*n + 48*N₀*u`.
- At every selected scale strictly below the cap, with `u ≤ s₀`, the actual
  shell partition satisfies `u * #selected ≤ 14*n`.

The one-piece proof separates the first and last occupied dyadic row blocks
from the interior blocks. At most ten columns arise in each interior block;
the two extreme blocks are controlled by the actual diameter enclosure.
This gives the numerical factor 24. Integer quotients preserve negative
coordinates. Empty samples, thin polygons, overlapping pieces and disconnected
unions require no additional hypotheses. Dilation is the existing finite
ambient integer operation, not sampling of a continuous dilation.

This does not establish safe-box clearance, subadditivity for shell entropy,
the final dyadic entropy sum, complete Lemma 9.4 or a headline theorem.

## Validation status

All 14 new original-proof records remain planned with pending verification;
the new blueprint entries have no completion tags. No successful elaboration,
regression run or imported dependency audit is yet claimed for these sources.

Normal CI builds the new production target before unrelated library work.
After the full build it runs strict regressions and the exact 14-name imported
audit with package options and warnings as errors. Actual output must also
pass the unchanged allowed-dependency validator for every ledger declaration.

Regressions reuse the actual thin-polygon Template fixture from the row
contribution and cover exact mixed indices, maximal source radius, selected
scales, ambient dilation, negative coordinates, empty samples, disconnected
unions, holes and overlapping/duplicate constituents. Expected finite fixture
counts were independently computed, but only their eventual Lean checks count
as proof verification.

Local prebuilt Mathlib artifacts remain absent. A renewed cache preflight on
October 8, 2026, returned proxy HTTP 403. No Mathlib proof-source rebuild was
started. Full pinned-source provenance validation, blueprint synchronization,
formatting and source policies are checked separately from Lean verification.
