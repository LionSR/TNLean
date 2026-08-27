# Deleting the superseded overlap bridge and dissolving the transport waypoint

Three cleanup decisions in the `PEPS/RegionBlock` overlapping-union chain,
audited at the head of 2026-08-27: delete the superseded non-fiber bridge
capstone together with the private helper restored solely for its proof; remove
the separate fiber carrier restatement; and dissolve the transport waypoint
module parked between the bridge and the closure.

## Direct deletion

| Declaration | Disposition |
|---|---|
| `TNLean.PEPS.overlap_bridge_rightCoupling_eq_zero` (`TNLean/PEPS/RegionBlock/UnionInjectivityOverlap3b.lean`) | deleted; live code uses `TNLean.PEPS.overlapFiber_bridge_rightCoupling_eq_zero` (`TNLean/PEPS/RegionBlock/UnionInjectivityOverlap6.lean`) |
| `TNLean.PEPS.overlapLeft_firstStrip_weightCombination_eq_zero_rightGeometry` (private, same file) | deleted with its sole consumer |
| `TNLean.PEPS.overlapLeft_firstStrip_fiber_weightCombination_eq_zero_rightGeometry` (private, `TNLean/PEPS/RegionBlock/UnionInjectivityOverlap6.lean`) | removed in favor of `TNLean.PEPS.overlapLeft_firstStrip_fiber_weightCombination_eq_zero`, applied at the call site through `smul_eq_zero_of_right` |

The non-fiber bridge is superseded for the live proof route. A bridge row indexed
by the `R₂` boundary alone cannot separate the `P₀`-outer host indices, which is
obligation 1 of `docs/paper-gaps/peps_normal_ft_section3_route.tex`; the live
closure restricts the coefficient family to each `P₀`-outer fiber first, and the
fiber bridge is what the rebuild step consumes.

Both private restatements were convert-plus-`rfl` carrier translations of their
base lemmas with `R₂ \ R₁` spelled as
`(overlapRightGeometry R₁ R₂).complement`. The non-fiber helper disappears with
its sole consumer, while the surviving live fiber call site accepts the base
lemma directly.

No blueprint `\lean{...}` tag cites the deleted theorem. No compatibility
declaration is retained under the maintainer's explicit confirmation that TNLean
does not promise public API compatibility.

## The transport waypoint

`TNLean/PEPS/RegionBlock/UnionInjectivityOverlap5.lean` held four generic
results with nothing to do with the overlapping-union argument that surrounded
it, yet sat eleven files deep in that chain, so every importer of the waypoint
dragged the whole chain into its compile cone. The declarations moved to the
modules that own their subject matter, with statements and proofs unchanged:

| Declaration | From | To |
|---|---|---|
| `TNLean.PEPS.regionPhysicalConfigCongr` | `UnionInjectivityOverlap5.lean` | `TNLean/PEPS/RegionBlock/Basic.lean` |
| `TNLean.PEPS.regionPhysicalConfigCongr_apply` | `UnionInjectivityOverlap5.lean` | `TNLean/PEPS/RegionBlock/Basic.lean` |
| `TNLean.PEPS.regionBlockedWeight_congr` | `UnionInjectivityOverlap5.lean` | `TNLean/PEPS/RegionBlock/Basic.lean` |
| `TNLean.PEPS.isRegionBoundaryEdge_congr` | `UnionInjectivityOverlap3.lean` | `TNLean/PEPS/RegionBlock/Basic.lean` |
| `TNLean.PEPS.regionBoundaryConfigCongr` | `UnionInjectivityOverlap3.lean` | `TNLean/PEPS/RegionBlock/Basic.lean` |
| `TNLean.PEPS.regionBoundaryConfigCongr_apply` | `UnionInjectivityOverlap3.lean` | `TNLean/PEPS/RegionBlock/Basic.lean` |
| `TNLean.PEPS.ThreeBlockGeometry.complPhysical_surjective` | `UnionInjectivityOverlap5.lean` | `TNLean/PEPS/RegionBlock/UnionInjectivityGeneral.lean` |

The three boundary-transport results moved as well because the weight transport
is stated in terms of them, and `Basic.lean` is upstream of the file that held
them. The blocked-weight transport belongs beside `regionBlockedWeight` itself;
the fused-leg surjectivity belongs beside `ThreeBlockGeometry.complPhysical`,
whose block-disjointness and covering fields are its whole proof.

`UnionInjectivityOverlap5.lean` then held nothing and was deleted, together with
its row in the numbered-file allowlist of
`scripts/check_numbered_lean_files.py`, which the checker treats as a ratchet.
The `PEPS/RegionBlock` import aggregator was regenerated.

## Imports

Two files imported the waypoint: `TNLean/PEPS/RegionTransportInsertion.lean` and
`TNLean/PEPS/RegionBlock/CoarseThreeSite11.lean`. `CoarseThreeSite11` reaches
both new homes through its remaining imports and lost the line outright.

`RegionTransportInsertion` did not. The 2026-08-27 cycle-and-edge audit
(`docs/audits/2026-08-27_peps_cycle_edge_simp_retirement.md` §Imports) had
dropped that file's `TNLean.PEPS.RegionBlock.Insertion` line on the ground that
the waypoint still reached it; with the waypoint gone the line was restored, and
it now names the module that supplies `regionInsertedCoeff`. The same audit had
dropped `TNLean.PEPS.RegionBlock.Algebra` from
`TNLean/PEPS/RegionTransferCovariance.lean` on the same ground, and the root
build caught the consequence: `regionInsertedCoeff_injective` became unknown
there. That line was restored too. Both restorations name a module the file
genuinely uses; both files now reach a far smaller cone than the waypoint gave
them.

## Prose repairs

The module docstring of `UnionInjectivityOverlap3b.lean` emphasizes the bridge
host-coefficient identity used by the live route; the superseded capstone has
been deleted. The chain summary in
`UnionInjectivityOverlap6.lean` described the same file's contribution and named
the waypoint as a supplier; both sentences were rewritten to the surviving
modules. The docstring of `overlapFiber_bridge_rightCoupling_eq_zero` states the rebuild
hypothesis it discharges directly rather than relying on the deleted theorem
as its primary description.

In `docs/paper-gaps/peps_normal_ft_section3_route.tex`, the paragraph reciting
the abandoned unrestricted route no longer cites the deleted capstone: the
paragraph records why that route does not close. The surviving reference to
`TNLean.PEPS.overlapBridgeRow` and the
citation of `TNLean.PEPS.overlapFiber_bridge_rightCoupling_eq_zero` elsewhere in
the same document are untouched.

## Ledger

Ledger entry S7 (issue #4567) plans further deletions in this chain and cites a
line range inside the deleted waypoint that no longer existed at the audited
head. `UnionInjectivityOverlap4.lean` was already absent before this PR. That
entry's remaining targets are only the dead spans in files 1, 2, 3, and 6;
they are unaffected by this slice.
