# Nonzero bond-dimension convention: parent Hamiltonians and normal PEPS

This audit continues `docs/audits/2026-10-13_peps_injective_tensor_convention.md`.
That note put the convention that every virtual bond space is nonzero into
`TNLean.PEPS.Tensor.IsInjective` and migrated the injective Fundamental Theorem
of arXiv:1804.04964, Section 3. This note records the second pass over the
parent-Hamiltonian results and the general normal theorem: the signatures that
changed, the renames, the theorems that keep explicit positivity and why, and
the decision on the two counterexample modules. No compatibility alias is
provided.

## Parent-Hamiltonian theorems

Each theorem below paired `IsVertexInjective A` with positivity of the same
tensor. It now takes `A.IsInjective` in place of the pair.

In `TNLean/PEPS/ParentHamiltonian/InjectiveRegionSupport.lean`:

- `openRegionMap_injective_of_isInjective` (renamed);
- `range_regionReducedDensity_eq_regionGroundSpace_of_isInjective` (renamed);
- `rank_regionReducedDensity_of_isInjective` (renamed).

In `TNLean/PEPS/ParentHamiltonian/InjectiveCoveringParentGroundSpace.lean`:

- `finrank_regionParentGroundSpace_eq_one_of_isInjective_of_cover` (renamed).

In `TNLean/PEPS/ParentHamiltonian/InjectiveNearestNeighborParent.lean`:

- `finrank_regionParentGroundSpace_edgePairs_eq_one`;
- `finrank_regionParentGroundSpace_edgeAndIsolated_eq_one`;
- `finrank_ker_regionParentHamiltonian_edgePairs_eq_one`;
- `finrank_ker_regionParentHamiltonian_edgeAndIsolated_eq_one`.

The four nearest-neighbor names do not name the hypothesis and are unchanged.
The span and kernel theorems
`regionParentGroundSpace_eq_span_of_isVertexInjective_of_cover`,
`ker_regionParentHamiltonian_eq_span_of_isVertexInjective_of_cover` and their
nearest-neighbor specializations keep `IsVertexInjective` alone: they hold with
zero-dimensional bonds, where the span is zero, and take no positivity.

The module marker of `InjectiveRegionSupport.lean` is kept as a self-contained
`**Local fix (nonzero virtual spaces):**` marker citing the paper-gap note, and
the other parent-Hamiltonian modules that use `Tensor.IsInjective` carry the
same marker: each affected module stays independently marked.

## Renames

All in namespace `TNLean.PEPS`; the old name is followed by the new one.

- `openRegionMap_injective_of_isVertexInjective` →
  `openRegionMap_injective_of_isInjective`;
- `range_regionReducedDensity_eq_regionGroundSpace_of_isVertexInjective` →
  `range_regionReducedDensity_eq_regionGroundSpace_of_isInjective`;
- `rank_regionReducedDensity_of_isVertexInjective` →
  `rank_regionReducedDensity_of_isInjective`;
- `finrank_regionParentGroundSpace_eq_one_of_isVertexInjective_of_cover` →
  `finrank_regionParentGroundSpace_eq_one_of_isInjective_of_cover`.

In each case the hypothesis is now `Tensor.IsInjective`, and the old name
named a hypothesis the theorem no longer takes.

## The general normal theorem

The general normal theorem (arXiv:1804.04964, Section 3, theorem labelled
`normal`, `Papers/1804.04964/paper_normal.tex:1576--1583`) is stated for two
normal PEPS. Its explicit positivity hypotheses `hposA` and `hposB` were about
the two tensors, and the nonzero bond spaces are the same Section 3 convention.
`NormalPEPSBlockingHypotheses` carries the blocking regions as data and is
indexed by a region-injectivity assignment, not by the tensors, so the
convention cannot be added to it. The new structure

```lean
structure NormalPEPSPairHypotheses (A B : Tensor G d) extends
    NormalPEPSBlockingHypotheses
      (regionInjectivityDataPair (regionInjectivityDataOf (G := G) A)
        (regionInjectivityDataOf (G := G) B)) G where
  bondDim_pos_left : ∀ e : Edge G, 0 < A.bondDim e
  bondDim_pos_right : ∀ e : Edge G, 0 < B.bondDim e
```

in `TNLean/PEPS/NormalBondDimension.lean` is the hypothesis "two normal PEPS"
of the source theorem: the shared blockings, which encode normality as defined
at line 1318, together with the nonzero bond spaces. It carries one
`**Local fix (nonzero virtual spaces):**` marker citing
`docs/paper-gaps/peps_injective_ft_section3_route.tex`. It adds no hypothesis
absent from the source: it replaces the blocking hypothesis and the two
positivity hypotheses.

## Per-theorem decisions in the normal and blocking chain

Interface (`NormalPEPSPairHypotheses A B` in place of explicit positivity):

- `fundamentalTheorem_normalPEPS` (`NormalGeneralFundamentalTheorem.lean`):
  `hposA` and `hposB` removed.
- `fundamentalTheorem_normalPEPS_gauge_unique`
  (`NormalGeneralFundamentalTheorem.lean`): `hposA` removed. The second
  positivity field follows from `hbond` and the first, so it adds no content.
- `bondDim_eq_of_normalBlocking` (`NormalBondDimension.lean`): `hposA` and
  `hposB` removed.

Explicit positivity kept, because the hypotheses are region, blocking or chain
data:

- `bondDim_apply_eq_of_blockingData` and `bondDim_apply_eq_of_coherentFrames`
  (`NormalBondDimension.lean`). They see the tensors only through one blocking
  datum or one pair of coherent frames, and the torus and square-lattice
  theorems apply them to their own blockings.
- `absorbedGauge_unique_scalar_of_region`
  (`NormalGeneralFundamentalTheorem.lean`). Its hypotheses are injectivity of
  one region and its complement.
- `exists_absorbingGauge_of_pairBlockingDatum` and
  `exists_normalAbsorbedGaugeFamily` (`NormalAbsorbedFamily.lean`). Internal
  assembly steps over blocking data, with no blueprint entry; the theorem
  passes them the projections of the new structure.
- `exists_normalPerVertexScalar` (`NormalComparisonScalar.lean`). Internal
  assembly step over blocking data, using positivity of the first tensor only.
- `coherentFrameOfBlockingData`, `coherentFrameOfBlockingData_isPartition` and
  `exists_regionEdgeGauge_of_blockingData` (`BlockingDataEdgeGauge.lean`). One
  blocking datum; also used by the torus, square-lattice and
  region-reconciliation routes.
- `physical_to_virtual_insertion` (`InsertionRealization.lean`). Its
  injectivity hypothesis is chain data, `EdgeBlockedThreeSiteInjective A e`,
  and it sees its tensors only through that chain. Its caller, through
  `isEdgeBlockedInsertionAlgebraIsomorphism` and `exists_edgeGaugeFamily`,
  takes positivity from `Tensor.IsInjective`.
- `isEdgeBlockedInsertionAlgebraIsomorphism` (`InsertionAlgebra.lean`). Chain
  data as well; its caller `exists_edgeGaugeFamily` takes positivity from
  `Tensor.IsInjective`. Its scope-restriction marker no longer proposes
  deriving positivity from injectivity, which is false.

`NormalAbsorbedFamily.lean`, `NormalComparisonScalar.lean`,
`BlockingDataEdgeGauge.lean` and `InsertionRealization.lean` are unchanged.

The cycle corollaries `fundamentalTheorem_normalMPS_cycle` and
`fundamentalTheorem_normalMPS_cycle_gauge_unique` in
`CycleFundamentalTheorem.lean` keep their explicit `hposA` and `hposB` and build
the new structure from them. The other source-facing normal theorems with
explicit tensor positivity are on fixed lattices:
`fundamentalTheorem_normalSquarePEPS_unconditional`,
`bondDim_eq_of_normalTorusRectangle`,
`fundamentalTheorem_normalTorusPEPS_unconditional` and
`bondDim_eq_of_normalArcWindows_sameState`. Carrying the convention through
tensor interfaces for these, as `IsNormalTorusArcWindowPEPS` already does for
the torus window corollary, is the remaining work.

## Counterexample modules

This pass deletes one counterexample module, keeps the other, and adds no new
refutation.

- `TNLean/PEPS/PositivityCounterexamples.lean` is deleted. It refuted the
  injective Fundamental Theorem stated with vertex injectivity alone. No
  library theorem has that hypothesis set any more: the injective theorems take
  `Tensor.IsInjective`, the general normal theorem and
  `bondDim_eq_of_normalBlocking` take `NormalPEPSPairHypotheses`, and the
  fixed-lattice corollaries listed above state tensor positivity explicitly.
  None of these admits the zero-bond triangle witness, so the convention is in
  every hypothesis set the witness could reach. Removed declarations, all in
  the namespace `TNLean.PEPS.FundamentalTheoremCounterexample`:
  - the statement `FundamentalTheoremPEPSStatement` and its refutation
    `fundamentalTheoremPEPSStatement_false`;
  - the witness data `V3`, `adj3`, `G3`, `e3`, `f3`, `g3`, `bdA`, `bdB`, `A3`,
    `B3`, `e3_at0`, `e3_at1`, `g3_at2` and the instances on their
    configuration spaces;
  - the helper facts `f3_ne_e3`, `f3_ne_g3`, `bdA_e3`, `bdA_g3`, `bdB_e3`,
    `bdB_g3`, `bdA_f3`, `bdB_f3`, `A3_bondDim`, `B3_bondDim`, `stateCoeff_A3`,
    `stateCoeff_B3`, `A3_vertexInjective`, `B3_vertexInjective`,
    `A3_B3_sameState` and `not_gaugeEquiv`.
- The one-edge step `bondDim_apply_eq_of_blockingData` keeps explicit
  positivity of the original tensors. It is an internal step that cites no
  source statement as its hypothesis set, and every caller supplies the
  positivity from `NormalPEPSPairHypotheses` or from the fixed-lattice
  corollaries, so it needs no counterexample.
- `TNLean/PEPS/PhysicalToVirtualCounterexample.lean` is kept. It refutes
  `physical_to_virtual_insertion` without positivity. That theorem keeps
  `hpos` explicit because its hypothesis is chain data, and the witness
  satisfies `EdgeBlockedThreeSiteInjective`.
