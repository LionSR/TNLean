# PEPS endpoint forwarder retirement and region-scalar relocation

Two small continuations of earlier PEPS passes are applied together. Neither
changes any mathematical content: one removes a pair of theorems whose bodies
were an existing theorem applied at one vertex, the other moves a one-line
corollary next to the lemma that supplies its hypothesis and removes the
one-declaration file it was alone in.

## The endpoint forwarder pair

`TNLean/PEPS/InsertionRealization.lean` carried both
`edgeLeftLocalVirtualOpOfPhysicalOp_eq_iff_projected_realization_eq` and
`edgeRightLocalVirtualOpOfPhysicalOp_eq_iff_projected_realization_eq`, each
assuming vertex injectivity of the whole tensor, beside the twins
`edgeLeftLocalVirtualOpOfPhysicalOp_eq_iff_projected_realization_eqAt` and
`edgeRightLocalVirtualOpOfPhysicalOp_eq_iff_projected_realization_eqAt`, which
assume only linear independence of the family of local physical vectors at the
one endpoint. The body of each removed theorem was its twin's statement applied
at that endpoint, so it carried no content of its own. This is the shape the
2026-09-19 pass retired eleven times one layer down
(`docs/audits/2026-09-19_peps_virtual_insertion_forwarder_retirement.md`), which
recorded this pair as the natural continuation.

| Removed declaration | Existing replacement |
|---|---|
| `edgeLeftLocalVirtualOpOfPhysicalOp_eq_iff_projected_realization_eq` | `edgeLeftLocalVirtualOpOfPhysicalOp_eq_iff_projected_realization_eqAt A e (hA e.1.1)` |
| `edgeRightLocalVirtualOpOfPhysicalOp_eq_iff_projected_realization_eq` | `edgeRightLocalVirtualOpOfPhysicalOp_eq_iff_projected_realization_eqAt A e (hA e.1.2)` |

Both had a single consumer, the two branches of
`edgeEndpointLocalVirtualOpOfPhysicalOp_eq_of_projected_realization_eq` in the
same file; each branch now names the per-endpoint twin with `(hA e.1.1)` or
`(hA e.1.2)` in place of `hA`. The statement of that consumer is unchanged: it
is spelled with the vertex-injective pullback, projector and realization, which
unfold to their per-vertex forms, so the twin closes the goal directly. No other
non-`Archive` Lean file mentioned either removed name.

The two docstrings of the surviving twins described themselves by reference to
the removed names; they now carry the mathematical description the removed
theorems had, namely that the left endpoint represents the inserted matrix by
its transpose on the distinguished incident edge while the right endpoint acts
by the matrix itself, together with the endpoint specialization of the local
recovery step of Lemma `inj_isomorph` of arXiv:1804.04964, Section 3.

### Blueprint retagging

The two theorem nodes
`thm:peps_edgeLeftLocalVirtualOpOfPhysicalOp_eq_iff_projected_realization_eq`
and
`thm:peps_edgeRightLocalVirtualOpOfPhysicalOp_eq_iff_projected_realization_eq`
of
`blueprint/src/chapter/ch24_peps_ft_edge_kernel_gauges_kernel_descent_recovery.tex`
now cite the per-endpoint declarations. Following the retagging of the same
family in `ch24_peps_ft_foundations.tex`, each statement names linear
independence of the family of local physical vectors at the endpoint in place of
vertex injectivity of the tensor. That hypothesis is weaker and the conclusion
is unchanged, so both nodes state a theorem at least as strong as before and
keep `\leanok`. The labels are unchanged, so the `\uses` list of
`thm:peps_edgeEndpointLocalVirtualOpOfPhysicalOp_eq_of_projected_realization_eq`
needs no edit.

## The region-injective per-vertex scalar corollary

After the 2026-09-19 pass stated the per-vertex scalar-product argument once
(`docs/audits/2026-09-19_peps_torus_edge_value_cases.md`),
`prod_perVertexScalar_eq_one_of_regionInjective` was the only declaration left in
`TNLean/PEPS/RegionScalarCondition.lean`. It supplies the nonvanishing closed
state coefficient by `exists_stateCoeff_ne_zero_of_regionInjective` and feeds it
to `prod_perVertexScalar_eq_one_of_exists_stateCoeff_ne_zero`.

The corollary now lives at the end of
`TNLean/PEPS/RegionBlock/BlockRangeCoincidence.lean`, immediately after the
existence lemma it consumes, under its own section heading; its statement,
docstring and proof are carried over unchanged. `TNLean/PEPS/RegionScalarCondition.lean`
is removed, and `TNLean/PEPS.lean` was regenerated. No declaration is removed
and no name changes, so no `\lean{...}` tag and no citation of the declaration
in `docs/paper-gaps/peps_normal_ft_section3_route.tex` is affected.

The two Lean consumers are handled as follows.
`TNLean/PEPS/TorusFundamentalTheorem.lean` imports
`TNLean.PEPS.RegionBlock.BlockRangeCoincidence` in place of the removed module,
which leaves its import closure unchanged because the removed module imported
nothing else. `TNLean/PEPS/NormalGeneralFundamentalTheorem.lean` simply drops
the line: each of its three remaining imports already reaches
`TNLean.PEPS.RegionBlock.BlockRangeCoincidence`, so an explicit import would add
nothing to its exclusive cone, the criterion used in
`docs/audits/2026-08-27_unused_import_lines.md`. The prose pointer in the
docstring of `prod_perVertexScalar_eq_one_of_exists_stateCoeff_ne_zero`
(`TNLean/PEPS/FundamentalTheorem.lean`) and the file overview of
`TNLean/PEPS/RegionBlock/BlockRangeCoincidence.lean` name the new location.

## Checked

* The `TNLean.PEPS` aggregator, which imports every module that imports the
  edited files, builds clean; it is also the target that proves the removed
  module is gone from the build.
* No non-`Archive` Lean file, blueprint tag, paper-gap note or `docs/` file
  outside this note and the two earlier audits mentions either removed
  declaration name or the removed module path.
* Every `\lean{...}` tag edited here points at a declaration that exists, by
  `python3 scripts/blueprint_lean_sync.py --ci`.
* `python3 scripts/generate_import_aggregators.py --check` and
  `python3 scripts/check_numbered_lean_files.py` are clean after the removal.

## Retained

The vertex-injective definitions `localVirtualOpOfPhysicalOp`, `localProjector`
and `physRealizeLocalOp` remain: the statement of
`edgeEndpointLocalVirtualOpOfPhysicalOp_eq_of_projected_realization_eq` and its
downstream consumers are spelled in them, and the earlier pass already recorded
them as untagged conveniences. Only the theorem layer above them is affected
here.

## Deferred

The remaining items of the 2026-09-19 torus note stand: the two occurrences of a
differently shaped crossing split in `TNLean/PEPS/NormalEdgeSingleCrossing.lean`
are untouched.
