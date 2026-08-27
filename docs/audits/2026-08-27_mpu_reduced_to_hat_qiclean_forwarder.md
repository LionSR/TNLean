# The QICLean reduced-projection forwarder in the MPU transport module

This audit records the removal of one zero-content forwarder from
`TNLean/MPS/MPU/ReducedToHatTransport.lean`. It is the audit note required by
`docs/project_conventions.md` §Style for a removal under the pass-through
exception: the removed declaration is named below together with the surviving
declaration that supersedes it, and the blueprint tag that cited the old name
was removed in the same change, so no `@[deprecated] alias` is retained.

## Removed

| Removed | Replacement |
| --- | --- |
| `MPOTensor.exists_units_for_hat_reducedProjection` (`TNLean/MPS/MPU/ReducedToHatTransport.lean`) | `Matrix.exists_units_supportInvExtension_reducedProjection_rightFactor` (`QICLean/Analysis/MatrixReducedProjection.lean`) |

## What was checked

The two statements are identical up to the `Matrix.` qualifier on the reduced
projection. Both take two positive semidefinite matrices and produce three
invertible matrices $X$, $Z$, $Y$ with
$$
  XL=\operatorname{supp}(L),\qquad R Z=\operatorname{supp}(R),\qquad
  \operatorname{supp}(L)\operatorname{supp}(R)Y
    =\widetilde P\bigl(\operatorname{supp}(L),\operatorname{supp}(R)\bigr),
$$
with the same implicit dimension binder and the same hypothesis names. The
TNLean body was a bare `exact` of the QICLean theorem applied to the two
hypotheses in order, so the forwarder carried no mathematical content beyond
re-exporting a name into the `MPOTensor` namespace.

The forwarder had no Lean consumer: a name search across `TNLean/` (excluding
`Archive/`) found only its own definition, and a root `lake build` after the
deletion named no importer.

The module keeps both of its imports. `QICLean.Analysis.MatrixReducedProjection`
is still required, because `Matrix.reducedProjection` and
`Matrix.reducedProjection_mul_second` appear in the three surviving theorems of
the file. The module docstring's supplied-fixed-pair scope-restriction marker is
unchanged: it describes the surviving theorems, whose outer-factor identities
and letterwise support absorptions remain explicit hypotheses.

## Blueprint handling

The `\lean{...}` payload of `thm:mpu_reduced_to_hat_source_ranks` in
`blueprint/src/chapter/ch28_mpu.tex` was **shortened**, not redirected. The
survivor already carries a `\leanok` tag at the preceding node
`thm:reduced_projection_invertible_factor`, which the source-rank node already
lists among its `\uses`, so naming it again here would tag one declaration at two
nodes. This follows the precedent set in
`docs/audits/2026-08-26_mpu_duplicate_and_dead_surface.md`, where a removed name
whose content was already tagged elsewhere was dropped from the payload rather
than replaced. The node keeps its `\leanok`, its prose, its scope-restriction
comments, and its `\uses` list.

The paper-gap note
`docs/paper-gaps/mpu_reduced_representative_supplied_fixed_pair.tex` referenced
the removed name in the paragraph describing the supplier of the invertible
outer factors. That paragraph now names the matrix-level theorem directly; its
mathematical content — that this supplier assumes only positive semidefiniteness
and assumes no fixed-point identity, trace normalization, or support absorption —
is unchanged, and the elimination plan and its tracking references are untouched.

## Net delta

−17 Lean lines, −1 blueprint line, −2 paper-gap lines.

## Verification

- Root `lake build` completes successfully with the package lean options.
- `python3 scripts/check_forbidden_lean_tokens.py` is clean.
- `python3 scripts/check_reader_facing_prose.py --root . --diff-base origin/main --ci`
  is clean.
- `python3 scripts/blueprint_lean_sync.py --root . --update-lean-decls` followed by
  `lake exe checkdecls blueprint/lean_decls` resolves every tag.
