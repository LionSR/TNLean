# Actual tensors for a Hermitian operator approximation

Exchanging the physical indices and conjugating the virtual coefficients
represents the actual adjoint of a site-dependent trace-chain operator. The
closing matrix is conjugated entrywise as well. The proof uses Mathlib's
matrix coefficient homomorphism, ordered-product identity and trace identity.
It does not use the existing adjoint-tensor operation whose virtual adjoints
also produce a spatial reflection.

On a nonempty chain, diagonal blocks with coefficients one half construct
the Hermitian part at twice the virtual dimension. The original approximation
tensors therefore determine actual Hermitian approximation tensors with the
same norm error against a Hermitian target. The contraction of the Hermitian
part is supplied by the companion QICLean result. No Hermiticity of the
original approximant and no positivity of either approximation are assumed.

These are operator-algebra auxiliaries for ALVV, arXiv:1602.08828v2,
`lem:exp-approx-eff` and `prop:Cheby-AGSP-eff`, lines 1262–1268 and 1311–1333.
They do not prove the regional spectral comparisons or GEN.

The source-only contribution starts at the checked soft-MPO continuation
`9eb8dcb5ff7a82a1f6bbc91f9826c7274db52a70`, over TNLean `5fc343a57d` and
QICLean `ba017330`. The complete production module passed a fresh strict
actual-name check in 4.706 seconds. The imported audit of all three public
declarations passed in 15.300 seconds; each depends only on `propext`,
`Classical.choice` and `Quot.sound`. Selected sources, imported objects and
build inputs were guarded before and after each private check. No provider
or dependency cache was changed and no Mathlib source was rebuilt. The
worktree has no `.lake` directory.

The mathematical book entries are included. Ordinary integrated full-build
and complete-book checks remain pending. Foundation commands are confined
to a temporary audit; no test fixture is introduced. The unfinished regional
sum is not part of this contribution.
