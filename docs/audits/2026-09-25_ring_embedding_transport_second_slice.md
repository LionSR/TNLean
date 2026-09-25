# Ring-embedding transport, second slice: the golden and Eisenstein rings

Date: 2026-09-25. Issue #7846, ledger item D16 of `docs/proof_debt_ledger.md`; PR #8098.
Follows `docs/audits/2026-09-19_ring_embedding_transport.md`, which converted the integer and
`ℤ√2` examples and deferred the rings `ℤ[σ]` and `ℤ[ω]`.

## What became generic

In `TNLean/Algebra/ComplexOfRing.lean`, for a commutative ring `R` and `f : R →+* ℂ`:
`complexOfRing_sub`, `complexOfRing_transpose`,
`complexOfRing_blockDiagonal'`, `complexOfRing_injective` and `complexOfRing_ne_zero` (for
injective `f`), and `complexOfRing_mul_eq_one`, which sends `G * H = 1` over `R` to the same
identity between the images.

In `TNLean/MPS/FundamentalTheorem/Reduction/RingEmbedding.lean`: the word evaluation
`evalWordR` with `evalWord_complexOfRing`, and the matrix-unit certificates
`isNBlkInjective_of_complexOfRing_smul_single` and `isNormal_of_complexOfRing_smul_single`.
The earlier audit kept the golden and Eisenstein certificates apart from the integer one, since
that one carries a complex prefactor outside the ring. The golden and Eisenstein certificates
keep their scalar inside the ring, and they are the same statement with the ring swapped (the
golden one at the scalar one). They are therefore merged here. The integer certificate is not
touched.

## Removed declarations and replacements

| Removed | Replacement |
|---|---|
| `actGoldenTensor`, `actTensor_complexOfGolden` | `actTensorR`, `actTensor_complexOfRing` |
| `evalWordEisenstein`, `evalWord_complexOfEisenstein` | `evalWordR`, `evalWord_complexOfRing` |
| `mulEisensteinTensor`, `mulTensor_complexOfEisenstein` | `mulTensorR`, `mulTensor_complexOfRing` |
| `complexOfEisenstein_mul_eq_one`, `fibGaugeComplex_mul_inv`, `fibGaugeComplex_inv_mul` | `complexOfRing_mul_eq_one` |
| `complexOfEisenstein_sum`, `complexOfEisenstein_injective` | `complexOfRing_sum`, `complexOfRing_injective` |
| `complexOfGolden_add`, `complexOfEisenstein_add` | none (unused) |
| `fibGauge`, `fibStack_conj_golden`, `fibStack_conjMatrix`, `fibTauMPS_eq_complexOfGolden`, `fibOneMPS_eq_complexOfGolden` | none (unused: the only consumer of the first two was the third, which had none) |

A search of `TNLean/`, `blueprint/src` and `docs/` found every reference to these names, and
all of them are migrated. None of them is tagged in the blueprint.

## Kept, with unchanged statements

`complexOfGolden` and `complexOfEisenstein` are now same-name `abbrev`s of `complexOfRing`.
`evalWordGolden` and `mulGoldenTensor` are `abbrev`s of `evalWordR` and `mulTensorR`. The
blueprint-tagged golden declarations of `ch25_asymmetric_examples_fibonacci.tex` keep their
names and statements, and their proofs are one-line instances: `complexOfGolden`,
`evalWordGolden`, `mulGoldenTensor`, `complexOfGolden_mul`, `evalWord_complexOfGolden` and
`mulTensor_complexOfGolden`. The ring-specific rewrite lemmas are also kept as one-line
instances. A forward `rw` with a general lemma does not match a goal headed by the
abbreviation, so those lemmas are still needed for rewriting. About thirty hand-written
gauge-inverse rewrites `rw [← complexOfX_mul, h, complexOfX_one]` became
`complexOfRing_mul_eq_one _ h`. The general definitions have the same recursion as the ones
they replace, so kernel `decide` targets are unaffected.

## What is still deferred

- The three datum constructors (`ofGolden`, `ofEisenstein`, `ofConjInt`), for the reason the
  earlier audit gives.
- The Kramers–Wannier call sites.

Net change of PR #8098: Lean −69 lines, whole diff −25 lines before this note.
