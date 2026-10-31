# Trace-form duality reuse — 2026-10-29

Issue: #7850. Baseline: TNLean `152f3c81984a0d25599471bf700ecc967e13777f`;
pinned QICLean `acda92aa70e69b37507e422bceb5414036859fe6`.

## Existing upstream authority

`QICLean/Algebra/TraceFormDuality.lean` already supplies the nondegenerate
finite-family and product trace forms, their full-span criteria, and both
zero-pairing criteria. Mathlib's `LinearMap.BilinForm.toDual` supplies the
single-functional representation. No dependency bump or parallel bilinear
form is needed.

## Removed declarations and replacements

| Removed local declaration | Surviving authority |
|---|---|
| `Matrix.exists_trace_representation` | Inverse of `(Matrix.traceBilinForm _).toDual Matrix.traceBilinForm_nondegenerate` |
| `Matrix.exists_family_trace_representation` | `Matrix.piTraceForm_nondegenerate` and `LinearMap.BilinForm.toDual` |
| `Matrix.family_submodule_eq_top_of_trace_separating` | `Matrix.eq_top_of_pi_trace_separating` |
| private `exists_pair_trace_repr` | `Matrix.prodTraceForm_nondegenerate` |
| private `pair_matrix_span_top_of_pair_trace_separating` | `Matrix.eq_top_of_prod_trace_separating` |
| private `pair_trace_zero_on_span` | `Submodule.span_le` into `LinearMap.ker (Matrix.prodTraceForm _ _ _)` |
| private `eq_zero_and_eq_zero_of_pair_trace_eq_zero` | `Matrix.eq_zero_of_forall_trace_mul_add_eq_zero` |

The now-unused `TNLean/MPS/SharedInfra/MatrixFamilyTracePairing.lean` is deleted.
Its callers import QICLean's existing module. The public MPS, MPDO and
parent-Hamiltonian theorem statements retain their names and hypotheses.
The word-tuple converse uses `Matrix.eq_zero_of_forall_sum_trace_mul_eq_zero`
instead of re-expanding matrix units. The Blueprint's matrix-family duality
node points directly at the upstream form and dual equivalence.

No compatibility aliases are retained. TNLean's local convention permits
removing these superseded declarations after migrating all non-Archive uses
and Blueprint references; this note records the replacement for each.

## Validation boundary

This change was written without local Lean builds or elaboration at the user's
explicit request. Source searches, a public-signature comparison, regenerated
import manifests, the import generator's deterministic check, LaTeX formatting
and `git diff --check` are the available checks. Compilation and declaration
validation remain required before integration. No persistent Lean test fixture,
new axiom or proof placeholder is added.
