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

## Subsequent reverse-residual, projection-kernel and cluster contributions

The next coordinated mathematical revisions are TNLean
`8ace1dccea363b9ea3ee1611083fa3d73292f8a7` and QICLean
`34cb0c3a24a9cfb8073e1fe7bb1087bc409fb951`.
They add the actual soft-window reverse residual, the fixed-space
characterization of complementary projection products and physical parity
products, the arbitrary-factor tensor-sum lower-gap estimate, and the
mandatory-label cluster identity. The exponential restriction and soft
remainder estimates now reside in QICLean; their mathematical statements
and proof bodies were preserved during the move.

QICLean passed its 10,360-job build in 56.721 seconds, strict checks of eight
changed sources and four existing regressions, imported foundation audits
of 23 public declarations, source synchronization, compiled blueprint
checks, prose and integrity checks, and the changed-module timing check.
TNLean passed its 15,119-job build in 139.153 seconds, strict checks of seven
changed sources and five existing regressions, imported foundation audits
of 15 public declarations, source synchronization, compiled blueprint
checks, prose and integrity checks, the changed-module timing check,
the paper-gap registry check, and the tactic-pattern scan. Both foundation
audits found only `propext`, `Classical.choice` and `Quot.sound`.

The exact phase records and logs are
`/tmp/qiclean-reverse-kernel-padding-gates.json` and
`/tmp/tnlean-reverse-kernel-cluster-gates.json`. The five dependency-pin
entries and the private package checkout were advanced together under the
repository lock; `/tmp/tnlean-reverse-kernel-padding-pin.json` records the
unchanged Mathlib artifact hash. Neither build compiled Mathlib from source,
and no artifacts were copied from a modified worktree. No changed module
reached the 25-second build warning threshold in this batch.

The LVV arbitrary-accuracy construction, directed comparison of the two
actual spectral windows, the spatial cluster tail and MPO construction,
and the regional frustration-free truncation with corrected rank bound
remain subsequent work. The proved tensor-gap and cluster identities are
ingredients in those constructions and do not assert their completion.

## Constructive accuracy and corrected spectral and cluster estimates

The next verified mathematical revisions are TNLean
`da3ab8dcc9f9149cbbdcc56cae817ff783825f24` and QICLean
`4276de2eeb5c4122f4482ef5e4fa205be5b71bd9`.
They include arbitrary LVV accuracy obtained from one actual padded
successive construction; both directed soft-window comparisons with a
uniform logarithmic order; the corrected, energy-normalized cluster tail
on an actual interaction-label path; the actual regional frustration-free
Hamiltonian's positivity, full kernel and internal norm bound; and the
partition identity for commuting complementary products.

QICLean passed its 10,365-job build in 66.591 seconds, strict checks of seven
changed sources and three existing regressions, imported foundation audits
of 13 public declarations, source synchronization, compiled blueprint
checks, prose and integrity checks, and changed-module timing checks.
TNLean passed its 15,140-job build in 147.466 seconds, strict checks of 22
changed sources and five existing regressions in 159.879 seconds, imported
foundation audits of 61 public declarations, source synchronization,
compiled blueprint checks, prose and integrity checks, changed-module
timing checks, the paper-gap registry check and the tactic-pattern scan.
Both foundation audits found only `propext`, `Classical.choice` and
`Quot.sound`. No changed module reached the 25-second build warning
threshold; an unchanged dependent clipped-polynomial module took 27 seconds.
The earlier private strict check of the touched low-energy-family consumer
took 42.828 seconds, below the 50-second limit; its combined build took
20 seconds. These are local timings under different loads.

The exact records are `/tmp/qiclean-accuracy-window-tail-gates.json` and
`/tmp/tnlean-accuracy-window-tail-gates.json`. The pin record
`/tmp/tnlean-accuracy-window-tail-pin.json` confirms five coordinated entries,
the matching private package checkout and an unchanged Mathlib artifact.
No Mathlib module was compiled from source and no modified-worktree
artifacts were copied.

The [six-paper comparison](../formalization/classical-area-law-comparison.md)
records the mathematical scope. The LVV result gives a polynomial whose
coefficient and degree precede both length and requested accuracy; it
retains the corrected trimming and Gaussian-filter qualifications and
asserts no running time. The soft comparison covers one interval, equal
scale and order, and positive bandwidth and enlargement. The corrected
cluster tail uses interaction labels and an explicit lower-energy
normalization, and supplies no MPO representation. The regional
frustration-free spectral gap and corrected rank bound remain open.
The AKLV changing-target iteration and optimized tails, ALVV sampled tree
and low-density extension, and the remaining Hastings constructions
also require further proofs.
