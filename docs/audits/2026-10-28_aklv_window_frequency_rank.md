# The physical AKLV fixed-frequency estimate

The two modules prove the distinguished-cut estimate in the proof of AKLV,
arXiv:1301.1162v1, Lemma 4.2 (`l:agsp`, source lines 604–662). They derive the
required tensor factors and crossing rank from physical chain supports. No tensor
presentation or evaluated coefficient-rank bound is assumed.

## Physical statement

Consider an \(L\)-site chain of local dimension \(q\ge1\). Let
\(H_j\), \(0\le j<s\), be supported on adjacent sites
\(\{a+j,a+j+1\}\), with \(a+s+1\le L\). The exterior operators are supported
on \([0,a+1)\) and \([a+s,L)\). The left support permits the first window site,
which weakens the corresponding printed support hypothesis.

The actual alphabet consists of these \(s+2\) operators. Its sum is exactly
\(H_L+\sum_jH_j+H_R\). For \(u<s\), distinguish \(T=H_u\) and use the other
\(s+1\) terms as the ordinary alphabet. Let \(C_\alpha\) be the sum of actual
ordered words having \(k\) occurrences of \(T\), total ordinary frequency
\(t\), and individual ordinary counts \(\alpha\). Every complex weight family
satisfies

\[
\operatorname{OSR}_{a+u+1}\left(\sum_\alpha\lambda_\alpha C_\alpha\right)
\le \binom{t+s}{s}\binom{t+2k+1}{2k+1}q^{2k}.
\]

Every ordinary interaction lies entirely on one side of the cut. The corresponding
one-sided tensor forms are deduced from the supported-operator predicates. The
support of \(H_u\) meets the left block at exactly one site, giving rank at most
\(q^2\). Stars and bars computes the number of residual frequency vectors as
\(\binom{t+s}{s}\). Zero and linearly dependent coefficient operators are allowed.
No positivity, Hermiticity, spectral gap or nonzero coefficient assumption is needed.

The binomial coefficient is the corrected one in
[the QICLean word-count note](https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf).
For total degree \(\ell=t+k\), it is
\(\binom{\ell+k+1}{2k+1}\). The correction does not by itself complete the
optimized AKLV polynomial rank estimate.

## Scope and dependencies

The generic weighted-frequency algebra belongs to the separate QICLean contribution
`OneMarkerWeightedSchmidtRank.lean`, based on current QICLean main `b294d968`.
These TNLean modules require that contribution; the dependency pin is unchanged.
No QICLean source is vendored into TNLean or written into its dependency checkout.

The low-frequency partition, movement to the central cut, summation over selected
interactions, and optimized degree-dependent bound remain separate. The independent
chain area-law theorem is not used. This contribution does not finish AKLV Lemma 4.2,
the AKLV area law, or the six-paper comparison programme.

## Verification

Separate strict checks passed for the actual modules:

| Module | Time | SHA-256 |
| --- | --- | --- |
| `AKLV/OneMarkerRank` | 23.71 s | `16aa3710ff2c0cc22ae79977fa6545c226addc93e2b663d5d5bea49c1f21d0cf` |
| `AKLV/WindowFrequencyRank` | 3.46 s | `79d2770ec3b6221dc1a52c38ede8efaf4d8bb4cc45abf94e898c93c7a0a49ad0` |

The checks use `autoImplicit=false`, `relaxedAutoImplicit=false`,
`maxSynthPendingDepth=3`, Mathlib standard linters and warnings as errors. All output
objects are private temporary files. The prebuilt dependencies belong to the already
seeded worktree and its QICLean pin `c97ffd63`; all 18 existing QICLean algebra sources
in the relevant transitive import closure, and its build inputs, were compared with
`b294d968` and are identical. This remains preliminary evidence until ordinary
current-main QICLean and TNLean dependency integration checks pass.

An imported manual inspection covers all four public declarations here, all new
public QICLean declarations, and the existing two-marker consumer. It passed in
2.85 seconds. The only axioms are `propext`, `Classical.choice`, and `Quot.sound`.
The temporary inspection is not a permanent test fixture.

The chapter `ch35_aklv_frequency_rank.tex` contains the exact mathematical statements
and declaration tags. Its registration, ordinary build and compiled blueprint
validation remain pending integration. No Mathlib source was built, no other build
was interrupted, and no shared cache was changed.
