# Verified soft residual, variable-window refinement and range projections

The mathematical revision is TNLean
`f5e011c2e551b318e6df7f7d6e5e81725dedea7a`. Its successor
`4bdda88ad1455106fd05ba6d874ecd1aca53aadb` changes only the wrapping of a
module docstring. The exact companion pin is QICLean
`4175de302e6b580d1bbb4a022f57424ab9f05e73`, the documentation successor of
mathematical revision `a81cad04c854c6816788abdd3c4bdaab414501fa`.
The preceding companion range-projection revision is `15a60a1b`.
All changes remain local.

## Physical constructions

For every prescribed interval of a positive unit nearest-neighbour chain,
the regional minima and original centered ground data are constructed
before the approximate regional energy, window width and truncation order.
Writing $G_\eta$ for the original spectral window up to ground energy
plus $\eta\ge0$, the actual equal-order-and-scale soft Hamiltonian satisfies
\[
\widetilde H_{m,m}\le H,\qquad
\bigl\|(H-\widetilde H_{m,m})|_{G_\eta}\bigr\|
 \le80\exp\bigl((17+\eta)/8-m/16\bigr).
\]
The approximate regional minimum lies within ten below the attained minimum.
The proof derives the physical exponential moment and the CFC remainder
factorization. It assumes neither a supplied moment nor a spectral gap or
ground-space rank. Empty and boundary intervals are included.
This is an auxiliary corrected residual estimate, not the false printed
first uniform energy estimate of ALVV.

For the AKLV construction, a unit input within squared distance $1/16$ of
the original ground vector is refined by an actual clipped polynomial on
every fitting window of at least six interactions. The genuine regional
minima precede the threshold; the clipped target precedes the chosen degree.
The phase-normalized polynomial image retains both
\[
 \|\psi-\phi_t\|^2\le8\Delta\|x-\phi_t\|^2,
 \qquad
 \|\psi-\Omega\|^2\le16\Delta+e^{-t/16}/50,
\]
and the sharp window-dependent operator Schmidt-rank factor. The hypothesis
that the supplied original gap is attained at the first excited energy
remains explicit. The coherent changing-target sequence, boundary treatment
and optimized MPS estimate are subsequent steps.

For positive contraction chains, replacement of each term by its actual
range projection preserves its bond support and the full zero-energy kernel,
and increases the Hamiltonian in operator order. The physical even/odd
product consequently satisfies
\[
 \|\operatorname{DL}(P)x\|^2\le\frac4{4+\gamma}\|x\|^2
 \quad(x\perp\ker H),
\]
when every nonzero spectral value of the original Hamiltonian is at least
$\gamma>0$. No upper-gap or ground-space-dimension hypothesis is imposed.
The shared CFC support identity replaces the two older duplicated diagonal
calculations in QICLean.

## Alternating sums and a rank correction

The companion library proves the energy-normalized alternating exponential
sum bound $e^{\beta\lambda}\|R_S^H(\beta)\|\le(e^\beta-1)^{|S|}$ for a
finite selected label set, Hermitian terms of norm at most one,
$H\ge\lambda I$ and $\beta\ge0$. The lower energy may be negative.
Its Duhamel identity and norm induction are proved. The spatial cluster
remainder, cut rank and MPO construction remain separate.

The printed frustration-free regional rank bound $d^2+2$ is false. An
explicit eight-qubit chain with unique ground and gap one has a truncated
operator of Schmidt rank seven at the middle cut. The corrected universal
bound is $d^2+3$. The complete exact calculation is in
`docs/paper-gaps/alvv16_frustration_free_truncation_rank.tex` and was
independently checked by full rational matrix realignment. This is a
mathematical counterexample, not a Lean counterexample theorem. It affects
the additive rank constant, not the ground-space or gap conclusions.
The two-page note and updated three-page soft-energy note rendered without
warnings and were visually inspected.

## Verification

The exact mathematical revision passed the full 15,112-job library build.
Strict checking passed for all ten changed production and aggregator files
and all five selected existing regressions. The only initial failure was an
overlong module-docstring line; after wrapping it, an incremental locked
build and the strict check of that file passed. No proof or declaration was
changed for this correction.

An imported audit covers all fifteen public declarations in the changed
mathematical modules. Only `propext`, `Classical.choice` and `Quot.sound`
occur. Source synchronization, compiled blueprint declaration checks,
reader-facing prose, proof-integrity, paper-gap registration and tactic
pattern checks passed. The shared support identity is recorded in the
reuse ledger; the squared-triangle comparisons use Mathlib's `add_sq_le`.

The required changed-module timing check used the repository's
`--changed-files-from` selector with the existing 25-second warning and
50-second failure thresholds. The variable-window refinement took 29 seconds
in the full dependent build; no changed module reached 50 seconds.
Some unchanged dependent modules exceeded 50 seconds. Their unfiltered
local diagnostic is retained separately; the CI policy applies the limit
to changed Lean files. Neither threshold was raised.

The companion shared-source batch passed a 10,354-job full build, strict
checks of four changed files and all 181 affected existing regressions,
and an imported 29-declaration audit. The subsequent analytic leaf passed a
10,355-job full build, strict checks of its two changed source and aggregator
files, and its public foundation audit. The dependency selector found no
newly affected regression for that leaf. Both companion blueprint and
integrity checks passed.

Mathlib was not rebuilt from source. The exact prebuilt artifacts and the
repository build lock were used. No modified-worktree build artifacts were
copied, and no permanent test fixture was added. The local records are
`/tmp/tnlean-soft-refinement-range-gates.json`,
`/tmp/qiclean-range-projection-gates.json` and
`/tmp/qiclean-mandatory-norm-gates.json`.

These results do not complete the three broader programmes. The remaining
work includes arbitrary-accuracy LVV construction, the coherent AKLV
approximation arguments, soft spectral-subspace comparisons, the corrected
spatial cluster/MPO estimate, and sampled low-energy and binary-tree
constructions.
