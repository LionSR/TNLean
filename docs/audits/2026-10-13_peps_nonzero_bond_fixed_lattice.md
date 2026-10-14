# Nonzero bond-dimension convention: fixed-lattice normal corollaries

This audit continues `docs/audits/2026-10-13_peps_nonzero_bond_parent_and_normal.md`.
That note carried the convention that every virtual bond space is nonzero
through the general normal Fundamental Theorem of arXiv:1804.04964 and listed
the fixed-lattice corollaries that still stated tensor positivity explicitly.
This note records the third pass over those corollaries: the new tensor
hypotheses, the changed signatures, the theorems that keep explicit positivity
and why, and what remains. No compatibility alias is provided and no theorem is
renamed.

## New tensor hypotheses

Each region-family structure below is indexed by a region-injectivity
assignment, not by a tensor, so it cannot carry the convention. Following
`IsNormalTorusArcWindowPEPS`, each gets a tensor-level `Prop` structure that
extends it at `regionInjectivityDataOf A` and adds the field
`bondDim_pos : ∀ e, 0 < A.bondDim e`.

- `IsNormalCycleArcMPS L A` in `TNLean/PEPS/CycleFundamentalTheorem.lean`,
  extending `NormalCycleArcInjectivityHypotheses`. Source: the closed-chain
  corollary, `Papers/1804.04964/paper_normal.tex:1597-1622` ("two normal MPS
  on `n ≥ 3L` sites with the property that blocking any `L` consecutive sites
  results in an injective tensor"). The helper
  `IsNormalCycleArcMPS.pairHypotheses` builds `NormalPEPSPairHypotheses` on the
  cycle from two such tensors.
- `IsNormalTorusRectanglePEPS A` in
  `TNLean/PEPS/TorusUnconditionalFundamentalTheorem.lean`, extending
  `NormalTorusRectangleInjectivityHypotheses`. Source: Theorem 3,
  `Papers/1804.04964/paper_normal.tex:1453-1471` ("two normal 2D PEPS tensors
  such that every `2 × 3` and `3 × 2` region is injective"). The helper
  `IsNormalTorusRectanglePEPS.unionClosure` gives union closure of injective
  regions.
- `IsNormalSquareLatticeRectanglePEPS A` in
  `TNLean/PEPS/NormalSquareUnconditionalFundamentalTheorem.lean`, extending
  `NormalSquareLatticeRectangleInjectivityHypotheses`. Source: the same
  Theorem 3, read on the open square lattice.

Each structure replaces a region hypothesis and a positivity hypothesis of the
same tensor, so it adds no hypothesis absent from the source. Each module
carries one `**Local fix (nonzero virtual spaces):**` marker citing
`docs/paper-gaps/peps_injective_ft_section3_route.tex`.

## Signature changes

- `fundamentalTheorem_normalMPS_cycle`: `harcA`, `harcB`, `hposA` and `hposB`
  are replaced by `hA hB : IsNormalCycleArcMPS L _`.
- `fundamentalTheorem_normalMPS_cycle_gauge_unique`: the same replacement;
  `hbond` is kept.
- `fundamentalTheorem_normalSquarePEPS_unconditional`: `hAr`, `hBr`, `hposA`
  and `hposB` are replaced by
  `hA hB : IsNormalSquareLatticeRectanglePEPS _`; `hbond` is kept.
- `bondDim_eq_of_normalTorusRectangle`: `hAr`, `hBr`, `hUA`, `hUB`, `hposA` and
  `hposB` are replaced by `hAn hBn : IsNormalTorusRectanglePEPS _`. The union
  closure hypotheses `hUA` and `hUB` are dropped as well: they follow from the
  nonzero bonds through `regionInjectivityUnionClosure_of_overlap`, and the
  source proves them as its Lemma `injective_union` rather than assuming them.
- `fundamentalTheorem_normalTorusPEPS_unconditional`: `hAr`, `hBr`, `hposA` and
  `hposB` are replaced by `hAn hBn : IsNormalTorusRectanglePEPS _`.
- `bondDim_eq_of_normalArcWindows_sameState`: the region hypotheses and
  `hposA`, `hposB` are replaced by `hAn hBn : IsNormalTorusArcWindowPEPS L K _`.
  Its callers `exists_translationCovariantGauge_of_normalArcWindows_sameState`
  and `staircaseCrossTensorVirtualOperation_coeff` pass the structure.

## Explicit positivity kept

These steps take their tensors through region data and keep explicit
positivity; every caller supplies it from a tensor hypothesis above.

- `bondDim_apply_eq_of_normalSquareInteriorEdge`,
  `exists_normalSquareInteriorAbsorbedGaugeFamily` and
  `exists_windowScalar_of_interiorAbsorbed` on the open square lattice.
- `component_eq_gaugeVertex_of_cornerProportional` on the torus.
- The staircase steps of `TorusWindowCrossTensorTransfer.lean`, which carries
  its own marker for them.
- The one-edge and coherent-frame steps listed in the previous note, and
  `physical_to_virtual_insertion` with its chain hypothesis.

## Counterexample module

`TNLean/PEPS/PhysicalToVirtualCounterexample.lean` is kept. It refutes
`physical_to_virtual_insertion` without positivity, and that lemma's hypothesis
is still the edge-blocked three-site chain, which its witness satisfies. Its
positivity is therefore not derivable from its hypotheses, and its callers take
positivity from `Tensor.IsInjective`.

## Remaining source-facing statements with explicit positivity

The uniqueness clauses of the torus results still pair a region hypothesis with
explicit positivity:

- `torusAbsorbedGauge_unique_scalar`,
  `torusCovariantAbsorbedGauge_unique_classScalar` and
  `torusGauge_unique_scalar_of_perVertex` in
  `TNLean/PEPS/TorusGaugeUniqueness.lean` (Theorem 3, "X and Y are unique up to
  a multiplicative constant");
- `torusGauge_unique_scalar_of_normalArcWindows` in
  `TNLean/PEPS/TorusWindowGaugeUniqueness.lean` (the window corollary's
  uniqueness clause).

They can take `IsNormalTorusRectanglePEPS` and `IsNormalTorusArcWindowPEPS`.
`TorusGaugeUniqueness.lean` is imported by the module that now defines
`IsNormalTorusRectanglePEPS`, so that structure first has to move to an earlier
module.
