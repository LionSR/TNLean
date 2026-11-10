# The additive constant in frustration-free truncation

ALVV, arXiv:1602.08828v2, Theorem `thm:FF-tH`, item 2, asserts
operator Schmidt rank at most d²+2 for the regional frustration-free
truncation. An eight-qubit example gives rank seven at the middle cut.
Both the original and truncated Hamiltonians have unique ground state
|0>^8 and spectral gap exactly one. Thus the example satisfies the source's
nondegeneracy and normalization conditions. It is not an empty-region or
zero-term reading.

The complete mathematical proof is in
`docs/paper-gaps/alvv16_frustration_free_truncation_rank.tex`. All local
terms are nonzero supported projections. Four disjoint even terms already
force the unique ground state and a gap of at least one; an endpoint
excitation attains energy one. The truncated operator has an explicit
seven-product decomposition. Both factor families have nonzero minors
with determinants -4 and 4, and all seven coefficients are nonzero.
The resulting exact operator Schmidt rank is seven.

An independent calculation built the entire 256 by 256 rational matrix
directly from the singlet projector and the actual parity products. It
verified the seven-product expansion entry by entry. After realignment at
cut four, a seven by seven minor has determinant -3/16. The independent
source is `/tmp/tnlean-alvv-ff-rank-independent-review/check_full_matrix.py`,
SHA-256 `feea90ca4ab51b168deb2823fdf3e765eaa5933cb1bf0c764fcddba77973d193`;
the review and exact result are in the same directory. The original
factor-family calculation is separately preserved in
`/tmp/tnlean-alvv-ff-rank-20261029/check.py`.

The corrected universal bound is d²+3. At an interior cut the crossing
parity product contributes at most d², the other parity product at most
one, and the complementary left and right Hamiltonians together with the
constant identity contribute at most two. The narrower bound d²+2 holds
when the interval touches an endpoint. This restriction is absent from
the source's arbitrary-region theorem.

This is an independently reviewed mathematical counterexample, not a Lean
counterexample theorem. It changes the additive rank constant and leaves
the ground-space and spectral-gap conclusions intact. The current
range-projection and detectability theorems do not use the false rank
claim. The regional truncated-Hamiltonian formalization must use the
corrected constant and cite the note.

The two-page note rendered without warnings and both pages were visually
inspected. The repository-wide paper-gap check passed: 281 referenced
slugs resolve and every note has a registered source prefix. That check
also required registering the existing AKLV note under the source key
`aklv13`; no mathematical statement was changed by this registration.
No additional Lean elaboration, build, cache operation or permanent test
fixture was introduced for this calculation. Nothing was published.
