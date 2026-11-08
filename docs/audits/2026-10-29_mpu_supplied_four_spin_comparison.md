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
This comparison removes chosen-half-factor dependence. It does not
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

## Actual supplied-gate forward certificate

`SuppliedTimeReversalCriterion.lean` now combines the actual comparison with
normalized-source necessity. For ANY supplied standard form in an explicit
ambient CFII tensor, adjoint symmetry at even standard-form lengths derives
its square intermediate ranks and the literal four-spin sign equation for
its own gates, after only the derived rank identifications. In source-rank
coordinates, write the comparison as
`A_T=(X⊗Y)A`, `B_T=B(Y†⊗X†)` and the actual normalized certificate as
`A_T=σ(z⊗z†)B_T†`. Multiplication by `X†⊗Y†` gives the supplied certificate
with the actual unitary `x=X†zY`. A private elementary matrix proof performs
this cancellation; no comparison-unitary existence premise is added to the
public theorem.

The normalized-source necessity proof is promoted at its existing owner as
`IsMPUCanonicalFormII.exists_supplied_source_adjoint_certificate` and both
its original coarse-source caller and the supplied-gate theorem reuse it.
No duplicate FT proof or compatibility alias is retained. This is the same
proof body that hosted job123583866714 accepted under strict options at
head160dc15b57cc5845495bd598f49e0a7894219afc; the new caller and transport
proofs remain source-written and uncompiled. The ambient presentation and
even-length restrictions are unchanged. Removal of the explicit ambient
presentation is not asserted by this new module.

## Actual supplied-gate converse

The same module now proves the converse and the full equivalence on this
explicit ambient CFII/even-standard-form-length scope. For a supplied local
certificate with x, inverse gate comparison gives the actual normalized
source certificate with z=X*x*Y†. The existing normalized-source even-ring
contraction theorem then proves the periodic adjoint equation. No adjoint
standard-form supplier, extra physical closure equation or comparison
witness is added as a premise. General intermediate ranks are transported
only along the derived equalities r=ℓ=d.

The two square-gate comparisons share a private source-coordinate proof.
The repeated physical-pair adjoint-certificate transport is promoted as
`Matrix.reindex_adjoint_certificate` at the existing gate-transport owner;
the original chosen-source sufficiency proof and the new supplied-source
converse both use it. This removes their duplicated coordinate proof. The
new equivalence, transport and callers remain uncompiled pending hosted CI;
the source nodes remain notready and #7020 remains open.


The shared supplied-gate dimension identity `TwoSiteStandardFormData.left_mul_right`
is reused at the three existing card-inequality proofs: four-spin unitarity,
ambient-canonical simplicity and the zero-index square-rank consequence.
Its source-only helper was coordinated with the actual output-support/index
work and added at the existing supplied-standard-form owner. It does not
strengthen the supplied record or infer ambient minimality.
