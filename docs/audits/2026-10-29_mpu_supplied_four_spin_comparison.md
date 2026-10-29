# Supplied four-spin/source comparison — 2026-10-29

Source: `Papers/1703.09188/paper_v2.tex`, `FundamentalMPU`, lines 624–648,
and `eq:block-twosites`, lines 1237–1252. The latter displays the literal
four-original-spin gate `(I⊗v⊗I)(u⊗u)`. Raw decomposition uniqueness is
FBC25, arXiv:2502.20257, `lem:deco`, lines 1052–1066.

## Delivered

For any existing supplied standard form `S`, compare its actual four-spin
gates `A=V23*(u⊗u)` and `B=V23` with any actual normalized source factor
record of the same tensor whose unshifted gate is unitary. The source cuts
and the actual right inverses from #10346 are transported only along their
proved rank equalities. Existing raw reciprocal-unitary uniqueness produces
two unitary gauge factors and a positive scalar. Its reciprocal pair cancels
in both gate contractions, giving `uT=(x⊗y)A` and `vT=B(y†⊗x†)` in the
canonical finite-index coordinates.

The canonical corollary takes only the actual supplied standard form and an
explicit reduced canonical-form-II presentation of the ambient tensor. It
derives simplicity from the actual source ranks and `ℓ*r=d*d`, then chooses
the existing normalized source factors internally. No extra gate, factor,
normalization, inverse, SVD or gauge-existence premise is added to that
corollary.

The same comparison now derives square intermediate dimensions for any
supplied standard form when its explicit canonical ambient tensor has
adjoint symmetry at even standard-form lengths. Actual adjunction exchanges
its source cuts, the even-family FT identifies those actual cut ranks, and
`r[W]=d*r`, `ℓ[W]=ℓ*d` give `ℓ=r`. Unitarity supplies `ℓ*r=d*d`, hence both
equal `d`. No all-length symmetry or further blocking is used.

## Scope

The ambient canonical presentation remains explicit. The minimality of all
four displayed cut factors does not imply minimality, faithful boundary or
canonicality of the ambient bond space; virtual padding is still possible.
This comparison removes chosen-half-factor dependence only. It does not
claim the unrestricted local symmetry criterion or an all-length statement.
The four-spin matrices themselves are retained, without an extra gate-level
block. The remaining presentation issue is documented in
`docs/paper-gaps/mpu_canonical_form_full_support.tex` and tracked by #7020.

The four-spin unitarity proof was extracted at its existing owner in
`SuppliedHalfFactorMinimality.lean` and its earlier adjoint-cut proof now
reuses it. The raw source-U transport reuses the existing public theorem;
the mirror source-V transport is a private elementary finite-sum lemma.
No parallel source or admissibility predicate is introduced.

## Verification

Pinned Mathlib/QIC API inspection; actual source-cut and four-spin entry
identities; reciprocal scalar cancellation; generated imports; changed
Blueprint declaration coverage; reader prose; tactic repetition; changed TeX
formatting; whitespace, source width and proof-integrity checks. New entries
are `notready` pending hosted acceptance. No local Lean build, elaboration,
compilation or cache mutation was run.
