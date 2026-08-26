# Duplicate and dead surface in the MPU development

This audit records the removals made when the `TNLean/MPS/MPU/` development was
swept for duplicated helper lemmas, local reimplementations of Mathlib facts,
and zero-reference declarations. It is the audit note required by
`docs/project_conventions.md` §Style for removals under the pass-through
exception: every removed declaration is named below together with the surviving
declaration that supersedes it. No compatibility alias is provided; every
removed name was `private` or had no consumer at all.

Each removal was checked by name across `TNLean/` (excluding `Archive/`),
`blueprint/src/`, and `docs/`, and confirmed by a full `lake build`. None of the
removed names carries a blueprint `\lean{...}` tag, so no blueprint entry was
redirected.

## Duplicated helper lemmas

### The letter decomposition into diagonal and residual

The identity splitting an MPO letter into its normalized-diagonal term and the
residual slice against the dual matrix unit was proved three times: once in
general form and once specialized to the double layer, in files that import one
another. The general statement now lives once, publicly, beside the definition
of the residual slice.

| Removed | Replacement |
| --- | --- |
| `MPOTensor.doubleLayer_entry_eq_diagonal_add_residual` (private, `TNLean/MPS/MPU/ThreeFormSpan.lean`) | `MPOTensor.entry_eq_diagonal_add_residual` applied to `doubleLayerTensor U` |
| `MPOTensor.entry_eq_diagonal_add_residual` (private, `TNLean/MPS/MPU/SimpleBlocking.lean`) | `MPOTensor.entry_eq_diagonal_add_residual` (`TNLean/MPS/MPU/DoubleLayerContraction.lean`) |

The surviving lemma is the specialized one with its double-layer hypothesis
dropped: it needs no nonempty-physical-dimension assumption, so it is strictly
more general than either copy.

### The rank-one sandwich and list-product identities

Four statements about a rank-one insertion between matrix factors were retyped
verbatim in `SimpleBlocking.lean` from `Simple.lean`, which it transitively
imports. They mention no tensor-network notion at all, so the surviving copies
were moved out of the tensor namespace into `Matrix` and made public.

| Removed | Replacement |
| --- | --- |
| `MPOTensor.IsMPUSimple.sandwich_mul_rankOne_mul` (private) | `Matrix.sandwich_mul_rankOne_mul` |
| `MPOTensor.IsMPUSimple.sandwich_listProd` (private) | `Matrix.sandwich_listProd` |
| `MPOTensor.IsMPUSimple.trace_mul_rankOne_mul` (private) | `Matrix.trace_mul_rankOne_mul` |
| `MPOTensor.IsMPUSimple.trace_listProd` (private) | `Matrix.trace_listProd` |
| `MPOTensor.sandwich_mul_rankOne_mul_local` (private) | `Matrix.sandwich_mul_rankOne_mul` |
| `MPOTensor.sandwich_listProd_local` (private) | `Matrix.sandwich_listProd` |
| `MPOTensor.trace_mul_rankOne_mul_local` (private) | `Matrix.trace_mul_rankOne_mul` |
| `MPOTensor.trace_listProd_local` (private) | `Matrix.trace_listProd` |

`MPOTensor.listProd_mul_eq_listProd_mul_rankOne_mul` was checked and retained:
it has no counterpart in `Simple.lean` and is genuinely not duplicated.

## Local reimplementation of a Mathlib fact

Two copies of the induction showing that a positive power of an idempotent is
that idempotent shadow a lemma the library already provides.

| Removed | Replacement |
| --- | --- |
| `MPOTensor.pow_eq_self_of_pos` (private, `TNLean/MPS/MPU/ThreeFormSpan.lean`) | `IsIdempotentElem.pow_eq` (Mathlib, `Mathlib/Algebra/Group/Idempotent.lean`) |
| `MPOTensor.pow_eq_self_of_pos_local` (private, `TNLean/MPS/MPU/SimpleBlocking.lean`) | `IsIdempotentElem.pow_eq` |

All four call sites were migrated in the same commit; the positivity hypothesis
becomes a nonvanishing hypothesis through `Nat.pos_iff_ne_zero`, supplied at the
call sites as `.ne'`. No import was added: the Mathlib module is already in the
transitive import closure.

## Zero-reference declarations

The bridge carrying the stronger normal-block canonical-form data to the weaker
MPU canonical-form predicate had no consumer. Downstream code, in
`TNLean/MPS/MPU/Equivalence.lean`, uses the target predicate
`MPSTensor.IsMPUCanonicalForm` directly, so the bridge has no replacement.

| Removed | Replacement |
| --- | --- |
| `MPSTensor.CPSVCanonicalFormData.toMPUCanonicalFormData` | none — `MPSTensor.MPUCanonicalFormData` is constructed directly where needed |
| `MPSTensor.IsCPSVCanonicalForm.toIsMPUCanonicalForm` | none — `MPSTensor.IsMPUCanonicalForm` is used directly |
| `MPOTensor.physicalSlice_tensorPhysicalId` | none — the identity had no consumer |

The three predicates retained in `MPUCanonicalForm.lean`
(`MPSTensor.IsMPUCanonicalBlock`, `MPSTensor.MPUCanonicalFormData`,
`MPSTensor.IsMPUCanonicalForm`) are the ones the blueprint cites; all three are
untouched.

## Records

This slice is evidence for the open ledger entry S2 (zero-reference
declarations), recorded there rather than as a new entry. The line-number
citations in `docs/tactic_patterns.md` for the diagonal normalized-ancilla sum
collapse were shifted to follow the deletion in
`TNLean/MPS/MPU/PhysicalAncilla.lean`.
