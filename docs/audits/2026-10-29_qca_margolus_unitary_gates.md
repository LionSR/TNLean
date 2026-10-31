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
The alternating rule now recovers the even factor through the preceding
shifted output rule and the odd factor through the following output rule.
A matrix-unit expansion gives the literal finite sum for every pair
matrix. Existing even-pair generation and completion density prove that
this explicit recipe has exactly one continuous global star-algebra
extension, namely the original automorphism. Actual original translation
covariance gives agreement with that QCA on every translated block.
No action, local compatibility or translation constraint is assumed as an
independent conclusion premise. Independent intermediate unitary basis
changes preserve gate unitarity and cancel in both product local rules.

The independently chosen support-factor presentations do not give
constant gates even when the original QCA is translation covariant.
Extracting constant gates in translation-transported factor coordinates,
as needed for direct conversion to one translation-invariant MPU tensor,
is a separate remaining step. This distinction does not weaken the
position-dependent alternating representation or its actual translated
block agreement.
No selected compact-SVD or MPU source-factor presentation is identified.

No Lean executable, elaboration or build was run, as requested. All new
Blueprint entries remain notready. Source validation includes pinned
Mathlib/QICLean API scouting, independent orientation review, generated
imports, mathematical-role checking, reader-facing prose, width,
whitespace and proof-integrity scans. Hosted compilation is pending.
