# The AKLV polynomial operator Schmidt rank estimate

The contribution proves the rank estimate in AKLV, arXiv:1301.1162v1, Lemma 4.2
(`l:agsp`, source lines 586–663), from the original physically supported interaction
family. It gives explicit universal constants and covers arbitrary complex
polynomials, shorter windows, odd window lengths, zero degree, and local dimension
one. It does not assume a coefficient-rank estimate, a suitable marker, an operator
Schmidt decomposition, an approximate ground-space projector, or an area-law theorem.

## Headline statements

Let \(G=H_L+\sum_{u=0}^{s-1}H_u+H_R\) act on an \(L\)-site chain of local dimension
\(q\ge1\), with \(s\ge1\), \(a+s+1\le L\), and each \(H_u\) supported on
\(\{a+u,a+u+1\}\). The exterior supports are \([0,a+1)\) and \([a+s,L)\).
For every complex polynomial \(P\) of degree at most \(\ell\),

\[
\operatorname{OSR}_{a+\lfloor s/2\rfloor}(P(G))
\le \bigl(q(\ell+1)\bigr)^{16(\lfloor\ell/s\rfloor+\lfloor\sqrt\ell\rfloor+1)}.
\]

For every positive degree bound \(\ell\ge1\), the source base gives

\[
\operatorname{OSR}_{a+\lfloor s/2\rfloor}(P(G))
\le(q\ell)^{96\max\{\lfloor\ell/s\rfloor,\lfloor\sqrt\ell\rfloor\}}.
\]

The constants `16` and `96` are universal: they precede the chain length, local
dimension, window, Hamiltonian, degree and polynomial. No coefficient norm bound
is imposed. The corresponding maximum-form bound with base \(q(\ell+1)\) has
constant `48`.

## Actual shorter-window construction

For every consecutive subwindow \(b\le j<b+m\), define the retained interactions by
\(H'_j=H_{b+j}\). The exterior operators are the actual sums

\[
H'_L=H_L+\sum_{j<b}H_j,\qquad
H'_R=H_R+\sum_{b+m\le j<s}H_j.
\]

Their supports are derived from those of the given interactions. Reindexing the
retained terms and partitioning the original finite alphabet proves
\(G=H'_L+\sum_jH'_j+H'_R\). This equality is applied inside the same polynomial;
no replacement Hamiltonian is supplied or assumed.

For \(\ell\ge1\), put \(n=\lfloor\sqrt\ell\rfloor\) and
\(m=\min\{s,2n\}\). If \(s\le2n\), take \(b=0\). Otherwise take
\(b=\lfloor s/2\rfloor-n\). In both cases,
\(b+m\le s\) and \(b+\lfloor m/2\rfloor=\lfloor s/2\rfloor\), so the original
central cut is unchanged, including odd \(s\). When \(\ell=0\), use \(m=1\) and
\(b=\lfloor s/2\rfloor\); this one-interaction subwindow exists because \(s\ge1\).

The scalar estimates in the separate QICLean module bound every power of degree
\(r\le\ell\) uniformly by
\((q(\ell+1))^{3m+6\lfloor\ell/m\rfloor+4}\). Expanding the arbitrary polynomial
into at most \(\ell+1\le q(\ell+1)\) powers gives one more exponent. The effective
width estimate then gives constant `16`. For positive degree, the three exponent
summands are each bounded by the displayed maximum, giving `48`. When
\(q\ell\ge2\), the comparison \(q(\ell+1)\le2q\ell\le(q\ell)^2\) gives `96`.
The exceptional positive-degree case is \(q=\ell=1\); the Hilbert space is
one-dimensional, and the operator-Schmidt realignment has rank at most one.

## Source faithfulness

The left exterior support permits the first window site. This weakens the printed
support hypothesis; it does not add one. Positivity, Hermiticity and norm hypotheses
are unnecessary for this algebraic estimate and are not introduced. Occurrence counts
are taken over labels, retaining distinct labels when operators coincide. The exact
word coefficients and their multiplicities are preserved throughout the proof.

The additional `+1` in the commuting-gap binomial coefficient is the genuine source
correction documented in
[the QICLean interpolation and word-count note](https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf).
The resulting universal-exponent conclusion retains the sharp dependence of the source
rank estimate. No generic exponential-in-degree estimate replaces it.

The earlier audit `2026-10-28_aklv_low_frequency_power.md` records the preceding
stage, at which shorter-window regrouping and arbitrary-polynomial assembly remained
open. Those particular steps are discharged here. The AKLV spectral truncation,
robustness and area-law arguments, and the six-paper programme, remain separate.

## Verification

All three actual production modules passed strict private compilation with
`autoImplicit=false`, `relaxedAutoImplicit=false`, `maxSynthPendingDepth=3`, Mathlib
standard linters and warnings as errors:

| Module | Time | SHA-256 |
| --- | --- | --- |
| `ShortWindow` | 11.81 s | `7a57ff7ccc3d6eafcf7c8d679cf7b1038ea299cae7ce796ad6a63ee0d366d1e1` |
| `WidthPolynomial` | 13.20 s | `869f9d658cb8872f0597ba8c3d311a4af7265de9cbf0a3621d894b5e228bb727` |
| `PolynomialRank` | 4.73 s | `746b2423885906625fea427595c968fa7a59116a1abcf4420de820a8d4fb5e75` |

An imported manual inspection of all nine new public declarations across the numerical
and physical contributions passed in 3.69 seconds. Their only axioms are `propext`,
`Classical.choice`, and `Quot.sound`. No permanent per-theorem fixture is added.

The complete reachable TNLean/QICLean source closure contains 121 modules, including
97 existing QICLean sources and five new contribution modules. Every existing QICLean
source in this closure, and the QICLean toolchain/configuration/manifest inputs, is
unchanged between the already seeded TNLean dependency pin `c97ffd63` and current
QICLean main `acda92aa`. The new source objects were checked in private temporary
namespaces. The earlier six QICLean mathematical modules retain their full-library
and compiled-blueprint verification at the exact `164c79df` snapshot.

Ordinary verification of the new numerical module and TNLean integration against a
combined current-main companion pin remain pending. No dependency pin, hot-main cache
or other worktree was changed, no duplicate full build was started, and no Mathlib
source was compiled. The new chapter should follow `ch35_aklv_low_frequency.tex`.
