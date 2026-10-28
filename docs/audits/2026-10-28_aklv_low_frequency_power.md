# AKLV low-frequency decomposition and transport to the central cut

The contribution proves the actual decomposition and the finite-sum rank estimate in
AKLV, arXiv:1301.1162v1, Lemma 4.2 (`l:agsp`, source lines 604–662), before
estimating the binomial coefficients and choosing a shorter window. It uses the frozen
fixed-frequency estimate from commit `168857149d` and the separate QICLean algebra.
No area-law theorem is used in its place.

## Statement and construction

Let \(G=H_L+\sum_{u=0}^{s-1}H_u+H_R\) be the actual window Hamiltonian, where
\(q\ge1\), \(s\ge1\), \(a+s+1\le L\), and \(H_u\) is supported on
\(\{a+u,a+u+1\}\). The exterior supports are \([0,a+1)\) and \([a+s,L)\).
Distinct interaction labels are retained even when their operators coincide.

For every natural degree \(\ell\), the construction gives actual operators
\(Q_{u,k}\), indexed by \(0\le u<s\) and
\(0\le k\le\lfloor\ell/s\rfloor\), such that

\[
G^\ell=\sum_{u=0}^{s-1}\sum_{k=0}^{\lfloor\ell/s\rfloor}Q_{u,k},
\]

and

\[
\operatorname{OSR}_{a+\lfloor s/2\rfloor}(Q_{u,k})
\le \binom{\ell-k+s}{s}\binom{\ell+k+1}{2k+1}
q^{2k+2|u+1-\lfloor s/2\rfloor|}.
\]

The module also proves the corresponding overall rank bound, obtained by summing
these explicit quantities. The number of pieces is exactly
\(s(\lfloor\ell/s\rfloor+1)\).

A selector is chosen from the occurrence counts within the middle window. Its chosen
count is at most the total degree divided by \(s\). The full ordered-word coefficients
are grouped by this actual selector and its count. For a fixed part, the weight on a
full frequency vector is one when the selector chooses the specified interaction and
zero otherwise. The full-frequency identity in QICLean identifies this weighted sum
with the actual residual coefficient family. The frozen rank estimate applies at the
distinguished cut, and the existing partition inequality transports that same operator
to the central cut.

The source interaction index is \(i=u+1\). The central cut is therefore
\(a+\lfloor s/2\rfloor\), not \(a+\lfloor s/2\rfloor+1\). The exact distance is
retained for odd \(s\); no even-window displacement estimate is silently used.

## Hypotheses and source correction

No suitable distinguished interaction, tensor presentation, coefficient-rank bound,
positivity, Hermiticity or spectral hypothesis is supplied. The tensor forms and the
crossing rank are derived from the actual supports. The left exterior support permits
the first window site, which weakens the source support hypothesis. Zero powers,
vanishing operators, and cancellations among coefficients are included.

The binomial coefficient retains the additional `+1` documented in
[the QICLean word-count note](https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf).
This is a correction to the printed exponent-tuple count, not a proof of the printed
sharper quantitative conclusions.

## Remaining AKLV steps

The arbitrary-polynomial assembly, the numerical binomial estimates, the choice of
a shorter window when needed, and the optimized bound
\((q\ell)^{O(\max\{\ell/s,\sqrt\ell\})}\) remain separate. The AKLV spectral
truncation and robustness argument, area law, and six-paper comparison programme
are not completed by this contribution.

## Verification

The final actual source modules pass the strict private module check with
`autoImplicit=false`, `relaxedAutoImplicit=false`, `maxSynthPendingDepth=3`,
Mathlib standard linters and warnings as errors:

| Module | Time | SHA-256 |
| --- | --- | --- |
| `CutTransport` | 8.27 s | `10a1c8ea72de7138ed01c2e1a4e328776710cab226bc51bef8726b5923d0a8d0` |
| `FullFrequencyRank` | 3.04 s | `675aa06349592db47f25e167262156cbe2085b9cc68ac843c34fe235d2ba5a3a` |
| `LowFrequencyPower` | 3.62 s | `7e5dbeabf1e66b1cdd050befb98ce8c17188b4ce5ad03cfbd34d5d8ca078d33f` |

An imported manual inspection covers all twelve new public declarations across the
QICLean and TNLean contributions. It passed in 3.06 seconds, with only `propext`,
`Classical.choice`, and `Quot.sound`. No permanent per-theorem fixture is added.

The full reachable TNLean/QICLean source closure contains 66 modules: 50 existing
QICLean sources and four new QICLean contribution sources. Every existing QICLean
source in this closure is unchanged between the seeded TNLean pin `c97ffd63` and
current QICLean main `164c79df`. The existing QICLean build inputs are also unchanged.
The exact new QICLean source hashes passed ordinary target builds, a full 10,334-job
library build, and compiled blueprint declaration validation in the canonically
seeded current-main QICLean worktree. Private output objects were written outside all
repository caches.

The TNLean dependency pin is unchanged; ordinary TNLean integration and compiled
blueprint declaration checks remain pending the separate QICLean contribution and
pin integration. The new chapter should follow `ch35_aklv_frequency_rank.tex`.
No Mathlib source was compiled and no other worktree or build was interrupted.
