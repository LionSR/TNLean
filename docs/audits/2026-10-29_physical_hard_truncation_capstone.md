# Actual physical hard truncation with a sufficient cutoff

This is the spectral client of draft TNLean #10432 at exact
`c8ca41cdbc18e16a3df4aa74e42171f6bb56fd29`, itself a child of unaccepted
#10404 at `b7c81587051f15ad7f3e9f6acb8c02665a7632c9`. The physical residual
and disjoint regional minimum constructions are TNLean draft prerequisites,
not accepted QICLean exports. Their acceptance/integration remain gates.

## Actual physical input and output

`ALVV.exists_single_region_hard_truncation_spectral_comparison` takes only
original nearest-neighbor positive-contraction bonds, their actual supports,
positive physical dimension and cuts `l<=r<=L`. The actual three regional
sums, distinct crossing bonds, regional minimum energies `e_j` and common
unit vector are constructed by the physical producer. Empty/coincident
regions, endpoint cuts and empty chains are included. No minimum, basis,
gap, forcing estimate, decomposition or residual is supplied.

Write `S=sum_j e_j`, `A_j` for the actual three internal regional sums,
and `Y` for the actual crossing bond sum. The matrices in the theorem are

`H=sum_i h_i-S I`,

`F=energyTruncation(A_1,e_1+t)+A_0+A_2+Y-S I`.

The original physical discrepancy is unchanged by this common shift:
`H-F=A_1-energyTruncation(A_1,e_1+t)`, proved inside the producer. All stated
canonical spectral spaces and ordered eigenvalues belong to these displayed
centered matrices. No identity between separately chosen canonical bases of
shifted and unshifted matrices is asserted.

For `eta>0` and the explicit sufficient cutoff `t>=eta+7`, put
`xi=32 exp(-(t-eta)/8)>0`. The theorem retains both actual restricted errors
at the same original absolute cutoff `E+eta`, and the genuine attained
minimum certificates `0<=E,E'<=2`. It then derives:

- For every canonically ordered index with `lambda_i(F)<=E+eta`,
  `lambda_i(F)<=lambda_i(H)<=lambda_i(F)+xi`.
- `E'<=E<=E'+xi`.
- For every `delta>0`, set
  `eta'=eta+xi+2xi sqrt(ceil(eta/(2xi))/delta)`.
  The original closed spectral space up to `E+eta` is delta-close to the
  clipped space up to `E'+eta'`, and the clipped space up to `E'+eta` is
  delta-close to the original space up to `E+eta'`.

Repeated eigenvalues and arbitrary ground degeneracy are allowed. There is
no source-gap hypothesis and no additional `delta<=1` restriction. This is
an explicit finite-window conclusion, not a uniform asymptotic claim about
arbitrarily small bandwidths.

## Actual canonical minima

The physical producer supplies normalized attained eigenvectors and PSD
lower certificates. Existing
`Matrix.IsHermitian.minEigenvalue_eq_add_of_centered_ground`, with zero
additional shift, identifies the actual finite minimum with `E` or `E'`.
A private bridge proves that the last canonically ordered eigenvalue equals
`minEigenvalue`: use antitonicity, attainment of the finite minimum, and the
actual reindex equivalence. Thus the generic relative-space result receives
the actual canonical energies; no minimum/basis certificate is assumed.

The sorted upper bound is exactly
`Matrix.IsHermitian.eigenvalues₀_le_add_of_norm_domRestrict_low_le` applied
to the derived clipped low-space residual. The lower bound is ordinary
Hermitian eigenvalue monotonicity from the derived `F<=H`. The ground-shift
and both relative comparisons use
`Matrix.IsHermitian.groundEnergy_compare_and_isCloseTo_spectralSpanLE_of_norm_domRestrict_le`.
No generic window-count algebra is duplicated in TNLean.

## Coherent candidate and exact provenance

All three TNLean records (`lakefile.toml`, `lake-manifest.json`, and
`docbuild/lake-manifest.json`) pin candidate QICLean
`fc38c6bda842f5d6b5379a821de04243422aeb68`, published branch
`snapshot/alvv-physical-truncation-candidate`. It is an assembly-only
snapshot based on the parent's exact
`716753c025d95fe36e3dc8f421571c81754adaaf`.

Its only changed mathematical source bytes are:

- `QICLean/Analysis/WeylMonotonicity.lean`, exactly the reviewed blob from
  QICLean draft #1011, `c04b69cdc483bc79c2512bbf1aba33e03e111d3e`.
- New `QICLean/Analysis/RelativeLowEnergyCloseness.lean`, exactly the
  reviewed blob from QICLean draft #1013,
  `4e688e3d81704e0906aae8b75cf31bf8dd4ea32b`.

The generated import and the two new unready Blueprint entries accompany
these exact blobs. Every other original 716 Lean source, toolchain and
dependency record is unchanged. This snapshot is a coherent review
candidate, not an accepted upstream release or substitute math PR.
Acceptance/integration of QICLean #1011/#1013, the existing 716 prerequisites,
and an accepted coherent repin all remain gates.

## Source correction and remaining acceptance

Source: ALVV, arXiv:1602.08828v2, Section 4.2, Definition 4.3,
Proposition 4.4 and Lemma 4.5, `local_alg_arxiv_v2.tex`, lines 873–968.
The source normalization is `0<=h_i<=I`, not norm exactly one.
The theorem uses `t>=eta+7`; it does not claim the printed unrestricted
truncated-side bound under merely `t>eta`. The actual-chain counterexample
is separate draft TNLean #10431.

The existing companion-owned note is
https://sirui-lu.com/QICLean/paper-gaps/alvv16_hard_truncation_windows.pdf.
Its cutoff correction is pending in doc-only QICLean draft #1012 at exact
`0cf09da9f6af2b4d24ca4dfd69fc604656ec7211`, and is not yet in that published
PDF. Acceptance and note publication remain gates. No duplicate TNLean gap
note or source-paper modification is introduced.

Root and independent native mathematical/API reviews are required before
publication. No local Lean, Lake, build, elaboration or declaration check
is run. New Blueprint statement/proof links remain `notready` until exact
hosted acceptance. Keep #9844 OPEN for these acceptance/integration gates
and any remaining full leaf source obligations; this bounded client does
not erase the literal false-source record.
