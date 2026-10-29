# The three regional energy shifts in AKLV

`AKLV/Normalization.lean` constructs the actual three regional energy shifts in
AKLV, arXiv:1301.1162v1, Section 6.1, proves the relative ground-energy bound six,
and applies them to the actual two-exterior-block residual. No regional energy,
common ground vector, residual, spectral comparison, or global energy bound is
supplied as a hypothesis.

## The original reference sums

For \(q\ge1\), \(s\ge6\), and \(a+s+1\le L\), the three actual supported reference
sums are the internal interactions of

\[
[0,a+1),\qquad [a+3,a+s-2),\qquad [a+s,L).
\]

These are respectively the original left exterior, the central bulk after removing
three boundary interactions at each end of the window, and the original right
exterior. Their supports are pairwise disjoint. The remaining interactions start
at \(a,a+1,a+2,a+s-3,a+s-2,a+s-1\), and there are at most six.

The theorem constructs their genuine lowest energies \(e_j\), a common unit ground
vector \(x\), and positive centered regional operators. The minima are nonnegative.
It then constructs an actual unit ground vector \(z\) of
\(H=\sum_i h_i-(e_0+e_1+e_2)I\), with attained energy \(0\le E_0\le6\).
The proof uses `DisjointRegionalGround` only to obtain genuine minima and a common
unit vector on the three disjoint regions. Its clipping selector is empty; no
five-region truncation is used. Positivity and the six-bond budget give the global
bound by the actual common zero-energy trial vector.

## The two enlarged exterior sums

For the two-block partition at \(a+2,a+s-1\), write its regional sums as \(C_j\).
The checked identities are

\[
C_0=A_0+h_a,\qquad C_2=h_{a+s-1}+A_2.
\]

For any scalar shifts, the centered operators have supports \([0,a+2)\) and
\([a+s-1,L)\). These are exactly the enlarged exterior sums used in the source's
truncation \((H_L+H_1)^{\le t}\) and \((H_s+H_R)^{\le t}\).
Their genuine reference energies \(e_0,e_2\) are proved lower bounds; they are not
asserted to be attained minima of the enlarged sums. The middle reference sum is
likewise contained in the retained middle regional sum, so \(e_jI\le C_j\) for
all three regions.

The normalized residual theorem chooses \(e_j,x,z,E_0\) before the real bandwidth
\(\eta\) and clipping threshold \(t\). For \(\eta\ge0\), \(t\ge\eta+11\), and
every actual partial outer clipping \(T\), it derives

\[
\|(H-B_{\mathrm{all}})|_{G_T(E_0+\eta)}\|
\le64e^{3/4}e^{-(t-\eta)/8}.
\]

The spaces are the actual canonical low spectral subspaces of the constructed
Hamiltonians. This theorem supplies no perturbation or low-space witness as input.

## The source's middle counting error

[AKLV v1, Section 6.1](https://arxiv.org/html/1301.1162v1) proposes subtracting
\(d/(s-7)\) from each term with \(4\le i\le s-3\), where \(d\) is the lowest
energy of their sum. That inclusive range has \(s-6\) terms. For \(s=8\), the
printed rule subtracts \(2d\) in total and leaves lowest energy \(-d\), rather
than zero when \(d>0\). The correct uniform redistribution uses \(s-6\).
The production theorem subtracts the actual middle lowest energy once from the
aggregate sum; no individual redistribution is required. The local correction is
recorded in `docs/paper-gaps/aklv13_two_block_robustness.tex`.

## Verification and remaining scope

The exact production source has SHA-256
`556ccd4177519558a078b20359c724f408137ee7d834c64aff9a4077f1320327`.
Its strict separate-module check passes in 8.16 seconds. Imported manual inspection
of all five public declarations passes in 2.68 seconds; only `propext`,
`Classical.choice`, and `Quot.sound` occur. All inspection commands and objects remain
under `/tmp`. The scoped tactic scan finds no repeated blocks at its default
thresholds; the original-bond support proof reuses the existing internal-bond
containment and supported finite-sum theorems.

Checks use the read-only TNLean provider
`8153728de51a3a489c932a8f377690c764892326` with QICLean
`b66600027b2e60ccafea43d041d563cdd00cf05b`, the same source-identical mathematical
context as the two-block residual. New objects are private temporary files.
No cache, pin, other worktree, or Mathlib source is changed, and no ordinary build
is queued by this contribution. Ordinary verification and compiled blueprint
integration remain pending. Place the new chapter after
`ch35_aklv_two_block_truncation.tex`.

The actual gap-preservation and normalized ground-vector comparison of AKLV
Theorem 6.1 remain separate. No area-law theorem or ALVV five-region robustness
result is used as a replacement.
