# Supplied standard-form cut minimality — 2026-10-29

Source: `Papers/1703.09188/paper_v2.tex`, equations `vdagger` and
`StandardForm`, lines 532–543 and 603–617; `eq:block-twosites`, lines
1237–1244. The source says “where u is a unitary and v ... too.”

## Delivered mathematical statement

For any existing `TwoSiteStandardFormData W u v`, derive independent
columns of both actual half factors and actual left inverses. Its actual
cut factors have ranks `d*r`, `d*r`, `ℓ*d`, `ℓ*d`, respectively, and both
right factors have actual right inverses. The actual source cuts therefore
have ranks `r[W]=d*r` and `ℓ[W]=ℓ*d`.

The first kernel argument uses only the shifted gate's isometry and its
supplied half-factor contraction. The right-factor argument uses the
adjoint of the actual four-spin unitary `v23*(u⊗u)`, whose contraction was
already proved for arbitrary supplied standard forms. It does not select
normalized factors or assume the existence of missing inverses.

## Scope and remaining work

No canonical presentation, weight, normalized half factor, local symmetry,
comparison gauge, or global-to-local implication is an input or a conclusion.
Positive dimensions are already part of the existing standard-form data.
This is a necessary algebraic prerequisite for #7020, not its unrestricted
local symmetry criterion. The existing raw reciprocal-unitary decomposition
comparison can consume these minimal factorizations, but that assembly and
the unrestricted ambient-presentation comparison remain separate work.

## Source/API checks

- Reuse Mathlib linear-map kernel criteria and
  `LinearMap.exists_leftInverse_of_injective`; matrix inverse equations are
  obtained through `LinearMap.toMatrix'`.
- Reuse the existing isometry Kronecker product, staircase isometry, and
  equal-cardinality unitary theorem. Both cardinal inequalities come from
  the supplied unshifted gate, rather than an assumed rank product.
- Reuse Mathlib rank as finite-dimensional range dimension and its
  conjugate-transpose and product inequalities.
- One private kernel-contraction argument serves both original half factors
  and the adjointed four-spin cut factors. No new predicate or factor record.

Eight public declarations have one scope-matching Blueprint entry, kept
`notready` pending hosted proof acceptance. Import aggregators were
regenerated. Whitespace, declaration coverage, reader prose, proof-integrity,
source width, pinned APIs, and tactic repetition were checked; changed TeX
was formatted. No local Lean build, elaboration, compilation, or cache
mutation was run.
