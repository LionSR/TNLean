# Wielandt and Spectral named-step forward audit (2026-08-27)

Two named proof steps whose bodies were a single application of an upstream
lemma have been retired in favour of the upstream statement. The project
pass-through exception at `docs/project_conventions.md` §Style applies: every
non-`Archive` consumer is migrated and no Blueprint `\lean{...}` tag names
either declaration.

| Removed declaration | Replacement |
| --- | --- |
| `MPSTensor.irreducibleMap_of_irreducibleTensor` (private, `TNLean/Spectral/TransferOperatorGapNT.lean`) | `Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily` (`QICLean/Kraus/InvariantProjection.lean`); eight call sites migrated inside the defining file |
| `MPSTensor.not_posSemidef_of_hermitian_ne_zero_trace_eq_zero` (`TNLean/Wielandt/Primitivity/ImpliesStronglyIrreducibleAux.lean`) | `Matrix.PosSemidef.trace_eq_zero_iff` (Mathlib); the sole call site now writes the one-line proof inline, and the Hermitian hypothesis the wrapper carried was already unused (`_hH`) |

No `@[deprecated] alias` is warranted for either name. The first was `private`
and so had no surface outside its own module; the second had no consumer outside
its own module and no Blueprint tag. Neither name encodes misleading
terminology, so the mathematical-language rename clause does not apply.

The step headers in `ImpliesStronglyIrreducibleAux.lean` track the proof outline
of Sanz, Pérez-García, Wolf and Cirac, arXiv:0909.5347, Proposition 3, not the
file's declaration ordering. The header for the step that is now inline was
removed with its declaration; the remaining headers keep their numbering.
