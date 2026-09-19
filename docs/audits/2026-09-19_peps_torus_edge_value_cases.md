# PEPS torus edge-coordinate pinning and the per-vertex scalar argument

This audit records two duplication removals inside PEPS proof bodies, together
with the removal of an unused pair of declarations that carried a third copy of
one of them, and the promotion of the case split they all shared to a tactic. Three
declarations and one tactic are added.

## Torus edge-coordinate pinning

The crossing-edge theorems of `TNLean/PEPS/TorusEdgeBlockingCrossing.lean` and
`TNLean/PEPS/TorusWindowRegion.lean` each opened with the same two steps: the
ordered-endpoint convention of an edge rewritten in coordinate-value form, and
the adjacency of the edge unfolded into a horizontal or vertical cyclic step and
then, by five sub-cases, into coordinate arithmetic through the single-step
lemmas. The horizontal blocks of the two files were byte-identical, and so were
the vertical ones; only the coordinates being pinned differed.

Both steps are now stated once, beside the single-step lemmas they assemble:

| New declaration | Content |
|---|---|
| `TNLean.PEPS.torusEdge_val_lt` | the ordered endpoints of a torus edge in coordinate-value form |
| `TNLean.PEPS.torusEdge_val_cases` | the eight arithmetic alternatives of a cyclic step: shared row with the columns differing by one or wrapping the seam in either orientation, and the transposed statement |

`torusEdge_val_cases` is the disjunctive assembly of `torus_horizontal_step_val`,
`torus_horizontal_step_val_wrap`, `torus_vertical_step_val`,
`torus_vertical_step_val_wrap`, `torus_eq_fst_val` and `torus_eq_snd_val` over
`torusGraph_adj`; all six are retained, and are now used exactly there. The
pinning proof of `isCrossingEdge_torusHorizontalEdge`,
`isCrossingEdge_torusVerticalEdge` and `isCrossingEdge_horizontalStaircase` is
one case split on the alternatives followed by the block-membership split that
already closed every branch. Statements, hypotheses and consumers are unchanged:
`TNLean/PEPS/TorusRectangleReferenceData.lean` and
`TNLean/PEPS/TorusWindowExtraction.lean` call the same theorems with the same
arguments.

The lemmas were placed in `TNLean/PEPS/TorusEdgeBlockingCrossing.lean`, next to
the single-step lemmas they are assembled from, rather than beside
`torusGraph_adj` in `TNLean/PEPS/TorusLatticeGraph.lean`: hosting them there
would either move the six single-step lemmas as well or duplicate their content,
and would rebuild the whole torus development for a fact used in two files.

## Removal of the vertical staircase end pair

`isCrossingEdge_verticalStaircase` and its feeder `verticalStaircaseEdge_val`
(`TNLean/PEPS/TorusWindowRegion.lean`) had no consumer: no module, no
`\lean{...}` tag and no paper-gap note names them, and they had none since they
were written. The overlapping-window chain around an edge runs through the
horizontal end pair. Under the repository-local style rule
(`docs/project_conventions.md` §Style) they are removed rather than retained
under deprecation, so the third copy of the pinning case analysis goes with
them.

| Removed declaration | Replacement |
|---|---|
| `verticalStaircaseEdge_val` | none needed — zero consumers; the horizontal end pair `horizontalStaircaseEdge_val` carries the window-chain geometry |
| `isCrossingEdge_verticalStaircase` | none needed — zero consumers; the chain around an edge is run through `isCrossingEdge_horizontalStaircase` |

The transposed statement is recoverable from the horizontal one by the same
argument, now three lines rather than forty given `torusEdge_val_cases`, should
the vertical route ever need it. The description of the pair as live development
in `docs/audits/2026-08-26_peps_vertical_staircase_mirror_deletion.md` was about
the coordinate convention it uses, not about a consumer; the vertical bond
transport results named there are untouched.

## The block-membership split

What every one of those pinning proofs ends with, and what the window-bound step at the
head of each of them also does, is the same split: each of the two boundary-membership
hypotheses says that one endpoint of the edge lies in the block and the other does not, and
all four assignments of the endpoints to the red and the blue block are decided by the
coordinate ranges. Five sites remained after the pinning cleanup, three of them textually
identical, so the split is promoted to the tactic `crossing_blocks`, defined beside the
crossing arguments whose hypothesis shapes it is written for; the form
`crossing_blocks hRed hBlue ⊢` also normalizes a goal that is itself a conjunction of
coordinate bounds. The ledger entry in `docs/tactic_patterns.md` is marked promoted and
records the net delta.

## The per-vertex scalar product argument

`prod_perVertexScalar_eq_one` (`TNLean/PEPS/FundamentalTheorem.lean`) and
`prod_perVertexScalar_eq_one_of_regionInjective`
(`TNLean/PEPS/RegionScalarCondition.lean`) had byte-identical bodies apart from
the line producing a nonvanishing state coefficient. That argument — substituting
the per-vertex relation into the state contraction, factoring out the scalar
product, and cancelling against the gauge-invariant coefficient — uses neither
injectivity hypothesis, only the existence of a nonzero state coefficient, which
is the source's standing assumption that the state is not the zero vector.

It is now stated once as
`TNLean.PEPS.prod_perVertexScalar_eq_one_of_exists_stateCoeff_ne_zero`, with
hypothesis `∃ σ, stateCoeff A σ ≠ 0` in place of the injectivity and positivity
hypotheses. Both named theorems are retained with their present signatures and
become one-line corollaries, supplying the coefficient by
`exists_stateCoeff_ne_zero` and `exists_stateCoeff_ne_zero_of_regionInjective`
respectively. The names are load-bearing: `prod_perVertexScalar_eq_one` is cited
in `docs/paper-gaps/peps_gaugeConsistency_connectivity_gap.tex` and
`docs/paper-gaps/peps_normal_ft_section3_route.tex`, and the region form is
called from `TNLean/PEPS/NormalGeneralFundamentalTheorem.lean` and
`TNLean/PEPS/TorusFundamentalTheorem.lean`. No hypothesis is added anywhere; the
new generic statement is weaker than both.

## What was checked

* No `\lean{...}` tag under `blueprint/src/` names any declaration touched here.
  The tagged wrapper at
  `blueprint/src/chapter/ch24_peps_ft_torus_single_bond_peeling.tex` names
  `isCrossingEdge_horizontalStaircaseEndWindows`, whose statement and proof are
  untouched.
* The consumers of the three rewritten crossing theorems and of the two
  per-vertex scalar theorems call them with unchanged argument lists.
* `TNLean/PEPS/RegionScalarCondition.lean` already imported
  `TNLean/PEPS/FundamentalTheorem.lean` transitively, so hosting the generic
  statement there adds no import and closes no cycle.
* After the removal, no file, tag, paper-gap note or audit other than this one
  and `docs/audits/2026-08-26_peps_vertical_staircase_mirror_deletion.md` names
  the two removed declarations.

## Deferred

* Relocation of the region-injective corollary next to
  `exists_stateCoeff_ne_zero_of_regionInjective` and removal of the resulting
  one-declaration file.
* The two occurrences of a related but differently shaped split in
  `TNLean/PEPS/NormalEdgeSingleCrossing.lean`, whose open-lattice memberships need no
  negation normalization; they are left as they are and noted in the ledger entry.
