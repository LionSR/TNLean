# PEPS local virtual insertion forwarder retirement

`TNLean/PEPS/VirtualInsertion.lean` carried two parallel theorem families about
the local virtual operations at a vertex. The `…At` family assumes only that
the family of local physical vectors at the one vertex `v` is linearly
independent; the other family assumes `IsVertexInjective A`, which is that same
linear independence at every vertex, and each of its eleven theorems had a body
that was the corresponding `…At` theorem applied at `v`. The eleven theorems
carried no mathematical content of their own.

The 2026-07-30 pass-through wave
(`docs/audits/2026-07-30_peps_zero_reference_pass_through_audit.md`) already
retired three siblings of exactly this shape from the same file
(`physRealizeLocalOp_comp`, `localProjector_idempotent`,
`localVirtualOpOfPhysicalOp_eq_of_projected_action_eq`). The eleven survivors
were the ones a Blueprint `\lean{...}` tag still cited, which the removal
policy in `docs/project_conventions.md` blocks. This pass redirects those tags
first and then removes the layer. It is a step in the PEPS insertion-machinery
consolidation tracked as ledger entry D6
(`docs/proof_debt_ledger.md`, issue #4522).

## Removed declarations

All removals are from `TNLean/PEPS/VirtualInsertion.lean`. In each row `hA` is
the vertex-injectivity hypothesis of the removed statement and `v` is the
vertex it was applied at.

| Removed declaration | Existing replacement |
|---|---|
| `physRealizeLocalOp_spec` | `physRealizeLocalOpAt_spec A (hA v)` |
| `localIncidentMatrixOp_physicalRealization` | `localIncidentMatrixOp_physicalRealizationAt A (hA v)` |
| `physRealizeLocalOp_injective` | `physRealizeLocalOpAt_injective A (hA v)` |
| `localVirtualOpOfPhysicalOp_spec` | `localVirtualOpOfPhysicalOpAt_spec A (hA v)` |
| `localVirtualOpOfPhysicalOp_realizes_of_projector` | `localVirtualOpOfPhysicalOpAt_realizes_of_projector A (hA v)` |
| `localVirtualOpOfPhysicalOp_eq_of_realizes` | `localVirtualOpOfPhysicalOpAt_eq_of_realizes A (hA v)` |
| `localVirtualOpOfPhysicalOp_eq_iff_projected_action_eq` | `localVirtualOpOfPhysicalOpAt_eq_iff_projected_action_eq A (hA v)` |
| `localVirtualOpOfPhysicalOp_physRealizeLocalOp` | `localVirtualOpOfPhysicalOpAt_physRealizeLocalOpAt A (hA v)` |
| `physRealizeLocalOp_localVirtualOpOfPhysicalOp` | `physRealizeLocalOpAt_localVirtualOpOfPhysicalOpAt A (hA v)` |
| `localVirtualOpOfPhysicalOp_eq_of_projected_realization_eq` | `localVirtualOpOfPhysicalOpAt_eq_of_projected_realization_eq A (hA v)` |
| `localVirtualOpOfPhysicalOp_eq_iff_projected_realization_eq` | `localVirtualOpOfPhysicalOpAt_eq_iff_projected_realization_eq A (hA v)` |

Eight of the eleven had no consumer outside the defining file. The three with
consumers were migrated in place at eight call sites:
`TNLean/PEPS/InsertionRealization.lean` (six sites) and
`TNLean/PEPS/InsertionCoefficientRealization.lean` (two sites). Six of the
eight migrations are the mechanical
substitution of `(hA v)` for `hA`. The two sites in
`edgePhysicalToVirtualInsertion_of_projected_realization_eq` rewrite a
hypothesis against the non-per-vertex spelling of the virtual pullback, so
there the per-vertex theorem is introduced through a type ascription that names
the spelling the rewrite expects; the two spellings agree by unfolding.

## Blueprint retagging

Fifteen nodes of `blueprint/src/chapter/ch24_peps_ft_foundations.tex` were
redirected to the per-vertex declarations. The eleven theorem nodes are the
labels `thm:peps_physRealizeLocalOp_spec`,
`thm:peps_physRealizeLocalOp_injective`,
`thm:peps_localVirtualOpOfPhysicalOp_spec`,
`thm:peps_localVirtualOpOfPhysicalOp_realizes_of_projector`,
`thm:peps_localVirtualOpOfPhysicalOp_eq_of_realizes`,
`thm:peps_localVirtualOpOfPhysicalOp_eq_of_projected_action_eq`,
`thm:peps_localVirtualOpOfPhysicalOp_physRealizeLocalOp`,
`thm:peps_physRealizeLocalOp_localVirtualOpOfPhysicalOp`,
`thm:peps_localVirtualOpOfPhysicalOp_eq_of_projected_realization_eq`,
`thm:peps_localVirtualOpOfPhysicalOp_eq_iff_projected_realization_eq` and
`thm:peps_localIncidentMatrixOp_physicalRealization`. The four definition nodes
are `def:peps_localLeftInverse`, `def:peps_physRealizeLocalOp`,
`def:peps_localProjector` and `def:peps_localVirtualOpOfPhysicalOp`; they were
redirected with the theorems so that the definition and theorem nodes of the
subsection share one carrier. All labels keep their names, so the five
references from
`blueprint/src/chapter/ch24_peps_ft_edge_kernel_gauges_kernel_descent_recovery.tex`
are unaffected.

Five node statements named vertex injectivity as their hypothesis; they now
name linear independence of the family of local physical vectors at the one
vertex. That hypothesis is implied by vertex injectivity and the conclusions
are unchanged, so every redirected node states a theorem at least as strong as
before, and no `\leanok` was demoted. The source, Section 3 of
arXiv:1804.04964, is not narrowed: it uses local injectivity one vertex at a
time.

## Retained

The three definitions `physRealizeLocalOp`, `localProjector` and
`localVirtualOpOfPhysicalOp`, and the definition `localLeftInverse`, remain in
Lean as untagged conveniences: `TNLean/PEPS/InsertionRealization.lean` and
`TNLean/PEPS/LocalGauge.lean` state results in those spellings.

The simp lemma `localProjector_apply_localTensorMap` also remains. It is a
pass-through of the same shape, but it was restored deliberately because the
bare `simp` calls in `TNLean/PEPS/LocalGauge.lean` fire on it; see
`docs/audits/2026-08-27_peps_cycle_edge_simp_retirement.md`.

## Checked

Every tag redirected here points at a declaration that exists, by
`python3 scripts/blueprint_lean_sync.py --ci`. No `\lean{...}` tag and no
non-`Archive` Lean file mentions a removed name. The PEPS aggregator, which
imports every module that imports the three edited files, builds clean.

The eleven statements were restored on 2026-09-19 as a merge artefact of an
unrelated branch and retired again on 2026-09-23; the re-retirement and its
checks are recorded in
`docs/audits/2026-09-23_peps_restored_layer_retirement.md` and re-establish
the clearance above.

## Deferred

`TNLean/PEPS/InsertionRealization.lean` repeats the same shape one level up:
`edgeLeftLocalVirtualOpOfPhysicalOp_eq_iff_projected_realization_eq` and its
right-hand twin forward to the `…eqAt` statements below them and are tagged in
`blueprint/src/chapter/ch24_peps_ft_edge_kernel_gauges_kernel_descent_recovery.tex`.
Retiring that pair is the natural continuation and is left to a follow-up.
