# Simplification of TNLean/MPS/MPU

Date: 2026-10-22; documentation corrected 2026-10-23. PR: #9934.
Addresses #9881 (zero-reference declarations); part of the simplification in #9923.

The simplification preserves the mathematical hypotheses and conclusions of all
surviving theorems. The two common-blocking theorems now explicitly bind the
natural-number dimensions previously inferred as implicit parameters.

## Removed declarations and replacements

The six removed declarations are listed below. Private declarations are identified
by their source spelling and file, rather than by Lean's generated private names.
No deprecated aliases are retained, in accordance with `docs/project_conventions.md`.

| Removed declaration | File under `TNLean/MPS/MPU/` | Retained replacement or derivation |
|---|---|---|
| `threeTupleEquiv_apply` (private) | `AnchoredThreeBlockOperator.lean` | Unused coordinate identity; the retained `threeTupleEquiv` definition gives the same identity by `funext t; fin_cases t <;> rfl`. |
| `MPOTensor.shiftSourceScale_cancel_rev` | `Examples/ShiftSourceFactors.lean` | The retained private `sourceSqrt_inv_mul_nat_mul_inv d`, by `simpa [sourceSqrt, mul_assoc]`. The public `shiftSourceScale_cancel d` also gives the reflected identity by commutativity. |
| `MPOTensor.siteProduct_conjTranspose` | `FundamentalTheoremGates.lean` | Unused entrywise identity; derive it from the retained `siteProduct` definition by `ext a b; simp [siteProduct, Matrix.conjTranspose_apply, star_prod]`. |
| `sourceSVD₁_V_vecMul_injective` (private) | `SourceFactors.lean` | `MPOTensor.vecMul_injective_of_isCoisometry (sourceSVD₁ U).V_coisometry`; the consumer `sourceGram₁_posDef` now uses this general lemma. |
| `vecMul_injective_of_isCoisometry` (private) | `SourceFactorChoice.lean` | The shared public `MPOTensor.vecMul_injective_of_isCoisometry` in `SourceFactors.lean`; the consumer uses it with `S₁.V_coisometry`. |
| `MPOTensor.isMPUSimple_virtualSandwich_gl_iff` | `VirtualSandwichBlocking.lean` | `MPOTensor.isMPUSimple_virtualSandwich_iff _ _ (Units.inv_mul X)`, which specializes the retained equivalence to an invertible matrix and its inverse. |

## Preservation of source statements and references

No theorem from the cited paper is removed without a retained derivation.
In particular, the equivalence expressing invariance of simplicity under bond
similarity remains available in the more general form
`MPOTensor.isMPUSimple_virtualSandwich_iff`. The scalar cancellation and coordinate
identities are auxiliary calculations, not independent statements from the paper.

At the reviewed head, a search of all tracked files found the five removed names
that are no longer declared only in this audit. No blueprint `\lean{...}` tag
cites them. The sixth name, `vecMul_injective_of_isCoisometry`, remains as the
shared public declaration and at its two consumers in `SourceFactors.lean` and
`SourceFactorChoice.lean`; the private duplicate has been removed.

## Verification

- [PR CI run 39831189997](https://github.com/LionSR/TNLean/actions/runs/39831189997)
  passed on reviewed commit `1ed78a724df25a504b038928f03ff35415ff2481`:
  full project build, strict changed-file checks, text-based style lint,
  compilation-time checks, module policies, and blueprint and paper-gap
  declaration checks. Blueprint web/PDF rendering was skipped.
- The subsequent documentation-only correction was checked by inspecting the
  full diff, matching the six removed declarations to their retained replacements
  or derivations, searching tracked files for remaining references, and running
  `git diff --check`. No local Lean build was run for this correction.
