# PEPS cycle and edge slice: zero-consumer projection lemma retirement

This audit records the repository-local pass-through exception of
`docs/project_conventions.md` §Style for the PEPS cycle, edge, and coherent-frame
modules. Two cleanups are covered: one obsolete transport definition together
with its three projection lemmas, and a batch of projection and application
lemmas that no proof in the repository consumed.

The batch was grep-proposed and build-decided. Every candidate was first checked
to have exactly one occurrence of its name repository-wide — its own declaration
— which rules out named consumers but says nothing about a bare `simp`, `simpa`,
or `aesop` that closes a goal by picking the lemma out of the default simp set.
The compiler settled those: each lemma below marked *restored* was put back
because a root build named the proof it had been silently carrying.

## Decidable-equality transport of a one-edge blocking datum

| Removed | Replacement |
|---|---|
| `TNLean.PEPS.transportBlockingData` (`TNLean/PEPS/CoherentFrameInstance2.lean`) | none — the transport is obsolete apparatus, not an unused seam |
| `TNLean.PEPS.transportBlockingData_red` (same file) | none |
| `TNLean.PEPS.transportBlockingData_blue` (same file) | none |
| `TNLean.PEPS.transportBlockingData_complement` (same file) | none |

The transport moved a one-edge blocking datum between two decidable-equality
instances on the vertex set, on the grounds that a square-lattice geometry layer
builds its blocking data over the canonical product decidable equality while the
gauge interface synthesizes one from the ambient linear order. That mismatch no
longer exists. Both lattice order instances now pin the decidable-equality field
to `instDecidableEqProd` rather than letting `LinearOrder.lift'` synthesize a
comparison-derived one, a design recorded at
`TNLean/PEPS/SquareLatticeGraph.lean` lines 25–37 ("pinning the field makes the
two definitionally equal, so an interior blocking datum feeds the gauge
interface with no subsingleton transport") and again at
`TNLean/PEPS/TorusLatticeGraph.lean` lines 95–99. With the two instances
definitionally equal, the transport is the identity dressed as a subsingleton
elimination, and nothing referenced it.

`TNLean.PEPS.transportBlockingDataAlong` and its lemmas in
`TNLean/PEPS/RegionTransportData.lean` and `TNLean/PEPS/TorusBlockingData.lean`
are a different declaration — transport along a graph isomorphism, with many
live consumers — and were not touched.

## Zero-consumer projection and application lemmas

| Removed | File |
|---|---|
| `TNLean.PEPS.mem_edgeRightVertices` | `TNLean/PEPS/Blocking.lean` |
| `TNLean.PEPS.notMem_edgeMiddleVertices_left` | `TNLean/PEPS/Blocking.lean` |
| `TNLean.PEPS.notMem_edgeMiddleVertices_right` | `TNLean/PEPS/Blocking.lean` |
| `TNLean.PEPS.edgeLeftVertices_card` | `TNLean/PEPS/Blocking.lean` |
| `TNLean.PEPS.edgeRightVertices_card` | `TNLean/PEPS/Blocking.lean` |
| `TNLean.PEPS.edgeBoundaryToInsertedBoundaryConfig_leftEdgeIndex` | `TNLean/PEPS/Blocking.lean` |
| `TNLean.PEPS.edgeBoundaryToInsertedBoundaryConfig_rightEdgeIndex` | `TNLean/PEPS/Blocking.lean` |
| `TNLean.PEPS.edgeBoundaryToInsertedBoundaryConfig_leftResidual` | `TNLean/PEPS/Blocking.lean` |
| `TNLean.PEPS.edgeBoundaryToInsertedBoundaryConfig_rightResidual` | `TNLean/PEPS/Blocking.lean` |
| `TNLean.PEPS.edgeMiddleConfigToOpenMiddleConfig_apply` | `TNLean/PEPS/Blocking.lean` |
| `TNLean.PEPS.edgeOpenMiddleConfigToMiddleConfig_edge` | `TNLean/PEPS/Blocking.lean` |
| `TNLean.PEPS.edgeComplementValue_edgeMiddleConfigToOpenMiddleConfig` | `TNLean/PEPS/Blocking.lean` |
| `TNLean.PEPS.legPair0_apply_fst` | `TNLean/PEPS/CoherentFrameInstance.lean` |
| `TNLean.PEPS.legPair0_apply_snd` | `TNLean/PEPS/CoherentFrameInstance.lean` |
| `TNLean.PEPS.legPair1_apply_fst` | `TNLean/PEPS/CoherentFrameInstance.lean` |
| `TNLean.PEPS.legPair1_apply_snd` | `TNLean/PEPS/CoherentFrameInstance.lean` |
| `TNLean.PEPS.legPair2_apply_fst` | `TNLean/PEPS/CoherentFrameInstance.lean` |
| `TNLean.PEPS.legPair2_apply_snd` | `TNLean/PEPS/CoherentFrameInstance.lean` |
| `TNLean.PEPS.coarseFrameOfRegions_red` | `TNLean/PEPS/CoherentFrameInstance.lean` |
| `TNLean.PEPS.coarseFrameOfRegions_blue` | `TNLean/PEPS/CoherentFrameInstance.lean` |
| `TNLean.PEPS.coarseFrameOfRegions_complement` | `TNLean/PEPS/CoherentFrameInstance.lean` |
| `TNLean.PEPS.coarseFrameOfRegions_coarseBondDim` | `TNLean/PEPS/CoherentFrameInstance.lean` |
| `TNLean.PEPS.coherentFrameOfRegions_frame` | `TNLean/PEPS/CoherentFrameInstance.lean` |
| `TNLean.PEPS.coherentFrameOfRegions_red` | `TNLean/PEPS/CoherentFrameInstance.lean` |
| `TNLean.PEPS.coherentFrameOfRegions_blue` | `TNLean/PEPS/CoherentFrameInstance.lean` |
| `TNLean.PEPS.coherentFrameOfRegions_complement` | `TNLean/PEPS/CoherentFrameInstance.lean` |
| `TNLean.PEPS.cycleNormalPEPSBlockingHypotheses_red` | `TNLean/PEPS/CycleBlockingData.lean` |
| `TNLean.PEPS.cycleNormalPEPSBlockingHypotheses_blue` | `TNLean/PEPS/CycleBlockingData.lean` |
| `TNLean.PEPS.cycleEdgeEquiv_apply` | `TNLean/PEPS/CycleMPSTensor.lean` |
| `TNLean.PEPS.cycleLeftIncident_fst` | `TNLean/PEPS/CycleMPSTensor.lean` |
| `TNLean.PEPS.cycleRightIncident_fst` | `TNLean/PEPS/CycleMPSTensor.lean` |
| `TNLean.PEPS.cycleTensorOfMPS_bondDim` | `TNLean/PEPS/CycleMPSTensor.lean` |
| `TNLean.PEPS.Edge.ofAdj_fst_snd` | `TNLean/PEPS/Defs.lean` |
| `TNLean.PEPS.edgeMiddleLeftInverse_comp_edgeMiddleTensorMap` | `TNLean/PEPS/InsertionRealization.lean` |
| `TNLean.PEPS.edgeMiddleLeftInverse_apply_edgeMiddleTensorMap` | `TNLean/PEPS/InsertionRealization.lean` |
| `TNLean.PEPS.Edge.equiv_symm_apply` | `TNLean/PEPS/IsoTransport.lean` |
| `TNLean.PEPS.IncidentEdge.equiv_coe` | `TNLean/PEPS/IsoTransport.lean` |
| `TNLean.PEPS.castLocalVirtualConfig_symm_apply` | `TNLean/PEPS/LocalGauge.lean` |
| `TNLean.PEPS.squareLatticeCoordinateSwapEquiv_apply` | `TNLean/PEPS/SquareLatticeCoordinateSwap.lean` |
| `TNLean.PEPS.localLeftInverse_comp_localTensorMap` | `TNLean/PEPS/VirtualInsertion.lean` |
| `TNLean.PEPS.localIncidentMatrixOp_one` | `TNLean/PEPS/VirtualInsertion.lean` |
| `TNLean.PEPS.localProjectorAt_apply_component` | `TNLean/PEPS/VirtualInsertion.lean` |
| `TNLean.PEPS.localProjector_apply_component` | `TNLean/PEPS/VirtualInsertion.lean` |

The replacement in every row is none: each lemma projected a field out of a
structure literal or unfolded an equivalence by `rfl`, and the goals that need
that step reach it definitionally or through the surviving lemma next to it.
`edgeMiddleLeftInverse_apply_edgeMiddleTensorMap` and
`localProjector_apply_component` each had one reference, from a sibling in the
same batch, so the two pairs were removed together.

## Restored by the build

Eleven candidates turned out to be load-bearing for a proof that never names
them. Each was put back where it stood, with a one-line source comment naming
the call site that needs it.

| Restored | Call site that needs it |
|---|---|
| `TNLean.PEPS.edgeInsertedLeftLocalConfig_edgeBoundaryToInsertedBoundaryConfig` | `edgeInsertedCoeff_identity_diagonal_summand`, `TNLean/PEPS/Blocking.lean` |
| `TNLean.PEPS.edgeInsertedRightLocalConfig_edgeBoundaryToInsertedBoundaryConfig` | `edgeInsertedCoeff_identity_diagonal_summand`, `TNLean/PEPS/Blocking.lean` |
| `TNLean.PEPS.edgeInsertedLeftLocalConfig_edgeBoundary_rightIndex` | `TNLean/PEPS/InsertionCoefficientRealization.lean` |
| `TNLean.PEPS.edgeInsertedRightLocalConfig_edgeBoundary_leftIndex` | `TNLean/PEPS/InsertionCoefficientRealization.lean` |
| `TNLean.PEPS.Edge.equiv_apply` | `IncidentEdge.equiv`, `TNLean/PEPS/IsoTransport.lean` |
| `TNLean.PEPS.localVirtualConfigSplitAt_apply_fst` | `localIncidentMatrixOp_single`, `TNLean/PEPS/VirtualInsertion.lean` |
| `TNLean.PEPS.localLeftInverse_apply_localTensorMap` | `TNLean/PEPS/LocalGauge.lean` |
| `TNLean.PEPS.localProjector_apply_localTensorMap` | `TNLean/PEPS/LocalGauge.lean` |
| `TNLean.PEPS.coherentFrameOfBlockingData_red`, `_blue`, `_complement` | `exists_regionEdgeGauge_of_blockingData`, `TNLean/PEPS/CoherentFrameInstance2.lean` |

`castLocalVirtualConfig_symm_apply` was restored once on a wrong diagnosis and
then removed again after a root build confirmed the two `LocalGauge.lean`
failures came from the two `localTensorMap` lemmas instead; its removal stands.

## Deferred

`TNLean.PEPS.coherentFrameOfRegions_isPartition` is in the same zero-consumer
condition but carries an active `@[deprecated ... (since := "2026-07-30")]`
attribute. It is held until its six-month window closes on 2027-01-30 and is
not part of this batch.

## Transition declarations

Every removed name had exactly one occurrence repository-wide before removal,
none is cited by a blueprint `\lean{...}` tag or a `\leanid{...}` reference, and
none appears under `blueprint/src`, `docs/glossary.md`, or `docs/paper-gaps/`.
No deprecation alias is warranted under the pass-through exception.

## Imports

Twenty import lines in the same slice supplied nothing their file used. They
split into two classes, and the two classes were verified differently.

Seventeen are transitively implied by a sibling import of the same file, so the
module they name stays in the compile cone and removal cannot change the
elaboration environment at all — not the instances in scope, not the notation,
not the default simp set. Each was confirmed by walking the transitive import
closure of the file's remaining imports and finding the named module inside it:

| File | Import dropped | Still reached via |
|---|---|---|
| `TNLean/PEPS/CoherentFrameInstance.lean` | `TNLean.PEPS.NormalEdgeBlockingData` | `TNLean.PEPS.RegionBlock.CoarseThreeSite11` |
| `TNLean/PEPS/CoherentFrameInstance.lean` | `TNLean.PEPS.RegionBlock.UnionClosure` | `TNLean.PEPS.RegionBlock.CoarseThreeSite11` |
| `TNLean/PEPS/CycleBlockingData.lean` | `TNLean.PEPS.NormalBlocking` | `TNLean.PEPS.RegionBlock.CoarseThreeSite2` |
| `TNLean/PEPS/CycleMPSFundamentalTheorem.lean` | `TNLean.PEPS.TorusAbsorbedCovariance` | `TNLean.PEPS.CycleFundamentalTheorem` |
| `TNLean/PEPS/CycleMPSOverlapCapstone.lean` | `TNLean.PEPS.NormalEdgeGaugeFamily` | `TNLean.PEPS.TorusGaugeUniqueness` |
| `TNLean/PEPS/CycleMPSTensor.lean` | `TNLean.MPS.Defs` | `TNLean.MPS.Core.CyclicTrace` |
| `TNLean/PEPS/CycleMPSWordTransport.lean` | `TNLean.Wielandt.SpanGrowth.CumulativeSpan` | `TNLean.MPS.ParentHamiltonian.IntersectionProperty` |
| `TNLean/PEPS/EdgeGaugeFamily.lean` | `TNLean.PEPS.Blocking` | `TNLean.PEPS.InsertionAlgebra` |
| `TNLean/PEPS/EdgeGaugeFamily.lean` | `TNLean.PEPS.EdgeMiddlePhysical` | `TNLean.PEPS.InsertionAlgebra` |
| `TNLean/PEPS/RegionComplementComparison.lean` | `TNLean.PEPS.NormalEdgeGauge` | `TNLean.PEPS.RegionBlock.Insertion` |
| `TNLean/PEPS/RegionTransferCovariance.lean` | `TNLean.PEPS.RegionBlock.Algebra` | `TNLean.PEPS.RegionTransportInsertion` |
| `TNLean/PEPS/RegionTransportData.lean` | `TNLean.PEPS.NormalEdgeBlockingData` | `TNLean.PEPS.RegionBlock.CoarseThreeSite2` |
| `TNLean/PEPS/RegionTransportData.lean` | `TNLean.PEPS.RegionBlock.UnionClosure` | `TNLean.PEPS.RegionBlock.CoarseThreeSite2` |
| `TNLean/PEPS/RegionTransportInsertion.lean` | `TNLean.PEPS.RegionBlock.Insertion` | `TNLean.PEPS.RegionBlock.UnionInjectivityOverlap5` |
| `TNLean/PEPS/SquareLatticeCoordinateSwap.lean` | `TNLean.PEPS.SquareLatticeGraph` | `TNLean.PEPS.NormalEdgeBlockingTranslated` |
| `TNLean/PEPS/Blocking.lean` | `Mathlib.Data.Matrix.Basic` | `TNLean.PEPS.VirtualInsertion` |
| `TNLean/PEPS/IdentityInsertion.lean` | `Mathlib.Data.Matrix.Basic` | `TNLean.PEPS.Blocking` |

The two `Mathlib.Data.Matrix.Basic` lines each sat in their own import group;
the orphaned blank separator went with them.

Three genuinely trim the compile cone, and each was applied on its own and
followed by a full root build before the next was attempted:
`TNLean.PEPS.RegionComplementComparison` from
`TNLean/PEPS/RegionScalarCondition.lean`, and `TNLean.Algebra.TracePairing` from
both `TNLean/PEPS/CycleMPSChainArc.lean` and
`TNLean/PEPS/CycleMPSInjectivity.lean`. All three builds were green; none was
restored.

`TNLean/PEPS/NormalEdgeGauge.lean` keeps its own unused
`TNLean.PEPS.NormalBlocking` import, justified at
`docs/audits/2026-08-26_peps_normal_cycle_zero_reference_deletion.md` §Imports.
Dropping the `RegionComplementComparison` line above leaves `NormalEdgeGauge`
with one direct importer, `TNLean/PEPS/RegionBlock/Insertion.lean`, and that
note's rationale is unaffected.

## Ledger

This slice belongs to ledger entry S2 (zero-reference declarations, issue
#4564), as the sibling 2026-08-26 PEPS notes do.
