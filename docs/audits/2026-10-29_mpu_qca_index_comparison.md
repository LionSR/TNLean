# Actual MPU output support and the QCA index

Source: arXiv:1703.09188, StandardForm/SF, lines 603–622, and Appendix,
lines 2313–2334. Prerequisite branches construct the actual supplied-data
quasi-local automorphism and the homogeneous nearest-neighbour GNVW index.

`TwoSiteOutputSupport.lean` bundles the existing actual two-link output
observable into a star-homomorphism. The rectangular-unitary conjugation
adapter is at `Algebra/RectangularUnitaryConjugation.lean`: pinned QICLean
has the rectangular unitary predicate and its products, but no matrix
star-algebra equivalence adapter. Mathlib's analogous conjugation API is
on continuous operators; this adapter stays in the matrix coordinates
used by the actual finite family and existing support algebras.

Intermediate product inputs, recovered through the inverse supplied u,
give exactly the Kronecker product of v(I_r⊗A)v† and v(B⊗I_ell)v†.
Matrix-unit induction proves every left coefficient belongs to the first
factor. Taking B=I recovers every element of that factor as a diagonal
coefficient, proving equality with the least left support algebra. Its
explicit full-matrix presentation has size ell, derived from faithful
identity-tensor embedding and actual conjugation. No support-factor
presentation, selected singular-value decomposition, or rank equality is
assumed.

`SupportAlgebraReindex.lean` transports least left support through
independent factor-coordinate equivalences. `SupportIntersection.lean`
derives intersection of finite quasi-local supports using the existing
outside-commutant characterization. The original finite commutation
helper now delegates to `commute_map_localObservable_of_singletons`,
which pulls back a target centralizer and reuses finite single-site
algebra generation.

The supplied gate dimension product is promoted at its existing owner
as `TwoSiteStandardFormData.left_mul_right`. The companion four-spin
source change refactors all three known cardinal-inequality proofs;
the same Blueprint node and ledger entry are retained here.

The global comparison uses actual blocking of the supplied-data
automorphism by k, exactly as the source groups sites before defining
support factors. `TwoSiteMiddleOutput.lean` proves the literal four-half-
block output placement. `TwoSiteBlockedLocalAction.lean` evaluates the
completed action on the entire two-block input using an actual 8k-site
ambient chain. Actual blocking gives the precise two-cell to four-cell
matrix action. Intersecting two overlapping pair-output bounds gives
singleton radius one; finite single-site generation derives full
nearest-neighbour propagation.

`TwoSiteCanonicalPairImage.lean` identifies the canonical even-pair image
with the actual two-link image through the faithful canonical bipartite
embedding. Its least left support on {-1,0} has the derived full-matrix
presentation of size ell. Existing GNVW matrix-size uniqueness gives the
actual positive-rational index ell/d^k=d^k/r. Neither locality, an image
equality, nor a support-factor presentation is a premise. No arbitrary
regrouping independence is asserted.

Two concrete Appendix corrections are documented in
`docs/paper-gaps/mpu_qca_index_normalization.tex`: the main definition
implies MPU index = -log₂(QCA index), while line 2334 prints an extra
factor two; and actual forward transport uses v(I_r⊗M_ell)v† in the
main-text direction of v, whereas line 2333 reverses the adjoints.
The positive rational target ell/d is unchanged.

Independent source/API reviews checked the rectangular conjugation,
finite product factorization, least left-support proof, support
intersection, exact output coordinates, actual 8k completed interval
evaluation, blocking and nearest-neighbour derivation, canonical pair
image coordinates, actual image equality, full-matrix presentation and
index ratios, with no concrete mismatch found. No local Lean command is
run. All new Blueprint entries remain notready pending hosted checking.
