# RFP canonical-form pass-through restatement retirement

This audit records the repository-local pass-through exception of
`docs/project_conventions.md` §Style. Both declarations below restated an
existing result under an extra hypothesis their own blueprint prose described
as unused: one applied a single-block equivalence to a chosen block of a
canonical-form family, the other projected a defining field of the
canonical-form predicate.

| Removed | Replacement |
|---|---|
| `MPSTensor.rfp_iff_zcl` (`TNLean/MPS/RFP/Assembly.lean`, file deleted) | `MPSTensor.zcl_iff_idempotent_transfer` applied to the chosen block and symmetrized: `(MPSTensor.zcl_iff_idempotent_transfer (A k)).symm` (`TNLean/MPS/RFP/ZeroCorrelationLength.lean`), which is exactly what the removed proof body was |
| `MPSTensor.rfp_cf_structural` (`TNLean/MPS/RFP/StructuralForm.lean`) | `MPSTensor.IsCanonicalForm.block_injective` (`TNLean/PiAlgebra/CanonicalFormSepAux.lean`), the structure field the removed proof body already returned |

## What was checked

Neither name had a non-`Archive` Lean consumer, so no call site needed
migration. The canonical-form family hypothesis of the first declaration was
already bound as `_hCF`, and the block-family hypothesis of the second was used
only to supply the projected field.

`TNLean/MPS/RFP/Assembly.lean` contained that one declaration and nothing else,
so the file was deleted. Its only importer was the generated aggregator
`TNLean/MPS/RFP.lean`; the import line was removed by re-running
`scripts/generate_import_aggregators.py`, whose only output change was that one
line. `TNLean.lean` is unchanged.

An attempt to also drop the now-unused direct import of the canonical-form
auxiliary module from `TNLean/MPS/RFP/StructuralForm.lean` was reverted: that
module is the only route by which the file reaches the unitary
diagonal-fixed-point existence theorem it still uses, and the root build fails
without it.

## Blueprint

Both numbered entries were deleted rather than redirected, and nothing
referenced either label outside its own `\label{...}`, so no `\uses` or `\ref`
was broken.

The first entry's content survives verbatim in the per-block transfer
equivalence theorem of the same chapter file
(`blueprint/src/chapter/ch26_mps_rfp_renormalization_flow_correlations.tex`,
label `thm:zcl_iff_idempotent_transfer`), which is already `\leanok`.

The second entry's content survives as clause (1) of the canonical-form
definition (`blueprint/src/chapter/ch26_mps_rfp_normal_isometry_canonical_forms.tex`,
label `def:is_canonical_form`), which is already `\leanok`. Its `\lean{}` tag
was not repointed at the structure field: per `docs/blueprint_style_guide.md`
§display hierarchy rule 3, a structure-field projection gets no separate
numbered entry and its tag belongs on the parent, which that definition already
carries.

## What is retained

The prose bullet naming the second declaration was removed from the
`## Main results` list of `TNLean/MPS/RFP/StructuralForm.lean`; the other four
bullets and the `## Proof strategy` section are untouched. The dated scouting
and inventory records under `docs/audits/` that mention the two old names as
historical entries were deliberately left alone.
