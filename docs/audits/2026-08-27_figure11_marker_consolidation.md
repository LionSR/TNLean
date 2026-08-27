# Figure-11 marker consolidation in the vertical-product modules

This audit records a hygiene pass over the vertical-product MPDO modules. It
covers two kinds of change: the consolidation of duplicated Figure-11
paper-gap markers to one marker per module, as required by `CLAUDE.md`
§"Degenerate readings are conventions, not gaps", and two declaration
removals under the pass-through exception of
`docs/project_conventions.md` §Style, each named below with its replacement.

## Marker consolidation

Six declaration-level Figure-11 markers restated the same restriction inside
one module. Per the one-marker-per-(restriction, module) rule they were
folded into the module docstring, with the module marker naming the
declarations it covers so that it claims no more than it carries.

In `TNLean/MPS/MPDO/VerticalProductFusionDecomposition.lean`, the fixed-pair
support marker and the fusion-coisometry marker were each stated three times,
on `MPOTensor.RetainedProductSpectralFamily.OriginalCornerFamily.toBNTFusionCoisometryFamily`,
`MPOTensor.RetainedProductSpectralFamily.exists_bntFusionCoisometryFamily`,
and `MPOTensor.transportedVerticalSector_exists_positiveFusionDecomposition`.
Both now appear once in the module docstring, naming those three
declarations.

In `TNLean/MPS/MPDO/VerticalProductCornerComparison.lean`, the fixed-pair
support marker was stated on
`MPOTensor.RetainedProductSpectralFamily.exists_flatBlockedBNTComparison` and
on `MPOTensor.RetainedProductSpectralFamily.exists_originalCornerFamily`. The
module marker now states both readings and names both declarations.

In `TNLean/MPS/MPDO/VerticalProductSpectralFamily.lean`, the fixed-pair
support marker was stated on
`MPOTensor.RetainedProductSpectralFamily.exists_blockedBNT_gaugePhase_of_flatBlock`,
on `MPOTensor.RetainedProductSpectralFamily.FlatBlockedBNTComparison`, and on
`MPOTensor.RetainedProductSpectralFamily.OriginalCornerFamily`. The module
marker now states the reading once and names the three declarations. The
surrounding prose that already stated the coverage-only restriction and the
non-surjectivity of `label` was left in place; it is mathematical content,
not a marker.

Each surviving marker remains self-contained: it names the deviation and
cites `docs/paper-gaps/cpsv16_figure11_per_pair_support.tex` or
`docs/paper-gaps/cpsv16_figure11_fusion_coisometry.tex` by path.

Two further Figure-11 markers were reviewed and **left alone**, because each
is already the single marker of its module:
`TNLean/MPS/MPDO/VerticalProductRetainedBlocks.lean` and
`TNLean/MPS/MPDO/CPSVVerticalProductFusionDecomposition.lean`. No
zero-sector-complement, blocked-coefficient-exponent, or `Scope restriction`
marker was touched.

## Removed declarations and their replacements

| Removed | Replacement |
|---|---|
| `MPOTensor.pi_list_prod_apply` (private, `TNLean/MPS/MPDO/VerticalSectorDensityBlocks.lean`) | Mathlib's `Pi.list_prod_apply` |
| `MPOTensor.verticalSectorFinEquiv_copy` (`TNLean/MPS/MPDO/VerticalSectorCoordinates.lean`) | `MPOTensor.verticalSectorFinEquiv_outer_symm` together with `Equiv.symm_apply_apply` |

`pi_list_prod_apply` restated Mathlib's `Pi.list_prod_apply` verbatim for a
family of monoids. Its single call site now rewrites with the Mathlib lemma,
which is already in the module's import closure and is used with the same
rewrite pair in `TNLean/MPS/MPDO/VerticalSectorGeneration.lean`.

`verticalSectorFinEquiv_copy` was a `@[simp]` lemma with no reference
anywhere in the repository and no blueprint tag. It could not fire in a bare
`simp`: its left-hand side strictly contains the left-hand side of the
`@[simp]` lemma `verticalSectorFinEquiv_outer_symm`, which simp's bottom-up
traversal applies first, after which `Equiv.symm_apply_apply` closes the
remainder. No compatibility alias is provided; neither name encoded banned
terminology, and both removals fall under the pass-through exception.

## Unused imports

Five import lines were removed from
`TNLean/MPS/MPDO/VerticalProductReconstruction.lean`:
`TNLean.MPS.CanonicalForm.BNTCharacterization`, the then-current
`TNLean.MPS.CanonicalForm.NormalCommutant`,
`TNLean.MPS.MPDO.FigureEightPairwise`, `TNLean.MPS.MPDO.VerticalBNT`, and
`TNLean.MPS.MPDO.VerticalSpectral`. At that checkpoint each remained reachable
through the four surviving imports, so the import closure of this module and of
every module downstream of it was unchanged and the deletion could not alter
elaboration anywhere. The generic normal-commutant API subsequently moved to
`QICLean.Kraus.NormalCommutant`.

Three further imports of the same module —
`TNLean.MPS.MPDO.VerticalCoisometry`,
`TNLean.MPS.MPDO.HorizontalBlocking`, and
`TNLean.MPS.CanonicalForm.BNTTransport` — were also unused by name inside the
file, but deleting them does shrink the closure, and this module is the only
route by which they reach their downstream consumers. Removing
`HorizontalBlocking` broke three proofs in
`TNLean/MPS/MPDO/VerticalProductRetainedBlocks.lean`, which reaches
`MPOTensor.IsHorizontalCF.blockTwo` only through this pass-through. All three
were restored. An import that is unused by name in its own file is still
load-bearing when it is the sole path to a name used downstream; the honest
repair is an explicit import at the consumer, which is out of scope for a
hygiene pass.

Twenty-one further candidate import deletions in sixteen sibling modules were
examined and rejected: they are closure-neutral, so they buy no compilation
time, and most delete an import whose declarations the file uses directly.

## Verification

- Root `lake build` completes successfully with the package lean options; no
  new error or linter warning on any touched file.
- `python3 scripts/check_forbidden_lean_tokens.py` clean against the working
  tree before the commit.
- `python3 scripts/check_reader_facing_prose.py --root . --diff-base
  origin/main --ci` clean on the committed branch.
- `leanblueprint checkdecls` unaffected: no declaration was renamed, and the
  blueprint `\lean{...}` tags in
  `ch21_mpdo_rfp_blocked_rfp_fusion_decomposition.tex` and
  `ch21_mpdo_rfp_blocked_rfp_retained_vertical_coordinates.tex` cite no
  removed name.
