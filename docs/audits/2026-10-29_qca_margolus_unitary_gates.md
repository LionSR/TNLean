# Actual QCA Margolus unitary gates

The source is Schumacher–Werner, `Papers/quant-ph_0405174/qca.tex`,
lines 980–1001, equations `bruleU` and `bruleV`. The one-dimensional
support-factor identification and both adjacent-generation equalities
are reused from GNVW, `References/0910.3675v2/QCI12.tex`, lines 1276–1318.

The new source derives prescribed full matrix input/output rules from
these actual support algebras, and implements both rules by finite
rectangular unitaries. Their dimensions use the same coherent positive
matrix-size family already constructed in `GNVWIndex`. The Kronecker
identities identify the literal ambient products of the actual embedded
factor observables; the rules are not additional factorization premises.
The unshifted gate maps the physical pair to its even/odd factors. The
shifted gate maps the odd/next-even factors to the physical pair.

The existing commuting-product owner now exposes its actual tensor
product-to-join equivalence and product-coordinate evaluation. The
existing adjacent-generation owner exposes the prescribed presentations
and their product evaluations. Center, relative-commutant and generation
arguments are reused, with no second proof of the factor construction.
The finite spatial adapter reuses the existing QICLean same-index
Skolem–Noether theorem after deriving equality of the coordinate sizes.

The current domain is a homogeneous positive-dimensional chain and an
actual nearest-neighbour star-automorphism. Gates may depend on position.
This establishes the finite spatial and local product-rule steps of
issue 7035, not its full translation-covariant generalized Margolus
partitioning theorem. Independent unitary changes of the intermediate
factor bases preserve gate unitarity and cancel in both actual product
local rules, as in source lines 1033–1041. Still remaining are an assembled
alternating-layer action on the full local algebra and its translation
compatibility against the original QCA.
No selected compact-SVD or MPU source-factor presentation is identified.

No Lean executable, elaboration or build was run, as requested. All new
Blueprint entries remain notready. Source validation includes pinned
Mathlib/QICLean API scouting, independent orientation review, generated
imports, mathematical-role checking, reader-facing prose, width,
whitespace and proof-integrity scans. Hosted compilation is pending.
