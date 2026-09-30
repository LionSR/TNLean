# Bundling the vertical-sector hypotheses in the transported-sector theorems

This audit records a signature pass over the Appendix C.4 vertical-sector
chapter of the MPDO development. The structure
`MPOTensor.VerticalSectorHypotheses` already bundled the full Appendix C.4
hypothesis telescope, but four later theorems still spelled that telescope out
field by field, and one of them rebuilt the structure from those fields in the
first lines of its own proof. The pass restates the four theorems over the
structure, deletes the rebuild, and adds one builder so that the consumers
outside the chapter assemble the hypotheses once.

No declaration was removed or renamed. Every hypothesis, and every conclusion,
is the one the theorem carried before; only the shape of the binders changed.

## Restated theorems

Each of the following now takes a single argument
`(h : MPOTensor.VerticalSectorHypotheses (g₁ := g₁) (g₂ := g₂) (d := d)
(D := D))` in place of the twenty-eight separate arguments that were exactly
the fields of that structure, and refers to the data by projection.

| Theorem | File | Arguments kept outside the structure |
|---|---|---|
| `MPOTensor.transportedVerticalSector_exists_unitaryBlockEquiv` | `TNLean/MPS/MPDO/VerticalSectorRelabeling.lean` | none |
| `MPOTensor.transportedVerticalSector_exists_unitaryBlockEquiv_coefficient_eq` | `TNLean/MPS/MPDO/VerticalSectorCoefficientComparison.lean` | none |
| `MPOTensor.transportedVerticalSector_exists_blockedOperatorRepresentations` | `TNLean/MPS/MPDO/VerticalBlockedOperatorRepresentations.lean` | `{L} (hL : 0 < L)` |
| `MPOTensor.transportedVerticalSector_exists_positiveFusionDecomposition` | `TNLean/MPS/MPDO/VerticalProductFusionDecomposition.lean` | `hHorizontal`, `hM` |

The field list each of them carried matches
`MPOTensor.VerticalSectorFixedGeneratorHypotheses`
(`TNLean/MPS/MPDO/VerticalSectorCoordinates.lean`) extended by the five
normal-tensor, coisometry, and channel fields of
`MPOTensor.VerticalSectorHypotheses`
(`TNLean/MPS/MPDO/VerticalSectorGeneration.lean`), so the restatement neither
adds nor drops a hypothesis. The two conclusions of
`transportedVerticalSector_exists_unitaryBlockEquiv` that were introduced by
`let` bindings for the transported refinement and coarse-graining maps are now
written `h.Tbar` and `h.Sbar`, which are the definitions those bindings
unfolded to.

The anchor of the chapter,
`MPOTensor.transportedVerticalSector_composites_eq_id`, already took the
bundled hypotheses, so the four theorems now agree with the statement the
blueprint nodes quote when they say "under the hypotheses of" that theorem.

## Deleted repack

`transportedVerticalSector_exists_unitaryBlockEquiv` opened its proof by
rebuilding `VerticalSectorHypotheses` from its own arguments, field by field,
and then argued entirely through that value. The rebuild is gone; the proof
now uses the argument directly and is otherwise unchanged.

## Added builder

`MPOTensor.VerticalSectorHypotheses.ofDecompositions`
(`TNLean/MPS/MPDO/RFPPositiveFusionDecomposition.lean`) assembles the
hypotheses from a one-site and a two-site `MPOTensor.CPSVVerticalDecomposition`
of the same tensor together with the two trace-preserving completely positive
maps of the renormalization fixed-point condition and their intertwining
identities. It is placed beside `CPSVVerticalDecomposition`, the first point
in the import order where both structures are available.

Three call sites outside the vertical-sector chapter had been passing the
twenty-eight projections of those two decompositions positionally. Each now
builds one value:

- `MPOTensor.exists_positiveFusionDecomposition_of_isRFPViaTS`
  (`TNLean/MPS/MPDO/RFPPositiveFusionDecomposition.lean`)
- `MPOTensor.HasBNTFusionTensorClause.of_isRFPViaTS_of_horizontalCF`
  (`TNLean/MPS/MPDO/BNTFusionTensorClauseFromRFP.lean`)
- `MPOTensor.HasBNTFusionTensorClause.of_isRFPViaTS`
  (`TNLean/MPS/MPDO/CPSVBNTFusionTensorClauseFromRFP.lean`)

The internal chain calls inside the four restated theorems pass `h`.

## What is retained and why

`MPOTensor.exists_positiveFusionDecomposition_of_unitaryBlockEquiv` and its
twin `MPOTensor.exists_positiveFusionDecomposition_of_unitaryBlockEquiv_of_cpsvCanonicalForm`
keep their explicit argument lists. They carry a strict subset of the
structure's fields — they omit the one-site basis-of-normal-tensors
hypothesis, both channels, their complete positivity and trace preservation,
both forward identities, and both physical intertwining identities — and take
the transport witness as input instead. Restating them over
`VerticalSectorHypotheses` would add nine hypotheses to a statement whose
literal-canonical-form twin carries a blueprint tag, which the faithfulness
rule of `CLAUDE.md` forbids; introducing a third, narrower bundle for them
alone would create a parallel structure family, which the same file forbids.

## Deferred

The eight-field cyclic-sector core repeated across
`TNLean/MPS/Periodic/Overlap/NoSectorMatch.lean` and
`TNLean/MPS/Periodic/Overlap/SectorMatch/Propagation.lean` is the other half
of the same record and is not touched here. That area carries live proof work,
and three of its names are blueprint-tagged; it is scheduled separately.

## Verification

- `lake build TNLean.MPS.MPDO` completes with the package lean options and no
  new error or linter warning. That target covers every edited module and
  every module in the repository that imports one of them.
- `python3 scripts/check_forbidden_lean_tokens.py` clean against the working
  tree before the commit.
- `python3 scripts/check_reader_facing_prose.py --root . --diff-base
  origin/main --ci` clean on the committed branch.
- No declaration was renamed or removed, so every `\lean{...}` tag in
  `blueprint/src/chapter/ch21_mpdo_rfp_blocked_rfp_fusion_decomposition.tex`
  still names an existing declaration. Declaration existence was checked with
  `python3 scripts/blueprint_lean_sync.py --ci`; the full `checkdecls` run is
  left to continuous integration.
