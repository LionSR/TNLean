# AKLV physical robustness at the source polynomial threshold

`AKLV/PhysicalRobustness.lean` proves the actual two-exterior gap and ground-vector
comparison at an explicit universal constant in the source's polynomial threshold.
It retains the original positive-contraction nearest-neighbour setting and states
the remaining restriction to windows of at least six interactions.

## Exact source and contextual hypotheses

The official source is [arXiv:1301.1162v1](https://arxiv.org/src/1301.1162v1),
`1dfrustrated34.tex`, SHA-256
`65bf824cd7d4f89bef5d819f713ac751445704bb077e81b4af3eb4ce5f2e4065`.
The downloaded archive has SHA-256
`510ce26e4b7a656e29e4debe42e1a5d7134052b61a4b2dfa72ac96f7bf34e6e4`.
The relevant passages are:

- Lines 879–884 begin with original positive-contraction nearest-neighbour
  interactions, a unique unit ground vector and an actual first excited energy.
- Lines 890–899 introduce an exterior-block description; lines 901–925 explicitly
  construct its regional sums and energy shifts from the original interactions.
- Lines 938–963 define the actual two exterior clippings and state Theorem 6.1,
  with threshold proportional to \((E_0/g+1)/g\).
- Lines 1301–1312 use the norm-one constituent interactions in the exponential
  commutator estimate. This dependence must not be discarded when reading the
  earlier exterior-block description.

The source does not explicitly quantify Theorem 6.1 over arbitrary independently
supplied exterior matrices. Such an extension is not needed for the present proof
and is not claimed. In particular, an obstruction to an arbitrary-exterior
extension is not a counterexample to the contextual source theorem. The optional
abstract common-compression energy lemmas remain separate mathematics.

The production signature takes the original supported \(0\le h_i\le I\), the unit
vector \(\Omega\), its original energy \(\mu\), the positive global rank-one gap
\(g\), and spectral attainment of \(\mu+g\). These express the original unit
unique ground vector and actual first excited energy. Membership of the ground
energy in the spectrum is derived internally. Two distinct spectral values force
\(q\ge2\), and the endpoint trial-vector theorem then derives \(g\le1\).
Neither dimension at least two nor the upper gap bound is an independent hypothesis.
No perturbation estimate, residual, closeness estimate, or truncated ground vector
is supplied.

## Quantitative conclusion

The theorem constructs the three genuine regional minima and a common unit vector
attaining them, before choosing \(t\). Their normalized original energy satisfies
\(E_0+\sum_j e_j=\mu\) and \(0\le E_0\le6\). For every

\[
t\ge\frac{1024}{g}\left(\frac{E_0}{g}+1\right),
\]

the actual two-exterior truncation is proved Hermitian. It has an actual
phase-aligned unit ground eigenvector \(\phi\). Its canonical eigenvalues satisfy
\(\lambda_j\ge\lambda_{j_0}+9g/10\) for every other index, and

\[
\|\phi-\Omega\|^2\le\frac{e^{-t/16}}{100}.
\]

This is an actual spectral gap bound: the canonical basis is complete, and the
phase-aligned vector spans the selected ground eigenspace. The theorem does not
separately return the equivalent matrix projector-gap inequality.

The proof sets \(\tau=e^{-t/16}\) in the already constructed two-block comparison.
The elementary estimates \(\log(10^6\cdot64e^{3/4})\le61\),
\(-\log g\le g^{-1}-1\), and \(g^{-1}\ge1\) show that \(t\ge1024/g\)
dominates the logarithmic accuracy threshold. Nonnegativity of \(E_0\) makes the
source polynomial threshold sufficient. Multiplication by the inverse relative
phase preserves the actual norm and eigenvalue and gives the aligned output.

## Support, normalization and window size

Line 897 gives the left support as sites \(1,\ldots,m\), while the explicit sum at
line 907 includes \(h'_m\) on \(\{m,m+1\}\). The formalization follows the explicit
original-bond sum, including its boundary site. Thus the reference left support is
\([0,a+1)\), and adding the first window bond gives \([0,a+2)\).
The middle range \(4\le i\le s-3\) contains \(s-6\) terms; the source's printed
individual denominator \(s-7\) is corrected by subtracting the genuine middle
minimum once from its aggregate sum. Both local corrections are documented in
`docs/paper-gaps/aklv13_two_block_robustness.tex`.

The theorem assumes \(s\ge6\), so the six boundary labels are distinct.
The middle reference sum is empty at \(s=6\) and has genuine minimum zero.
No explicit numerical minimum for \(s\) is stated beside source Theorem 6.1.
The application at line 1023 chooses an asymptotically large window; its constant
can be increased to give width at least six, but that numerical parameter choice
has not yet been formalized. Smaller windows remain separate, and the blueprint
states this restriction explicitly.

## Verification

Production SHA-256:
`98852cae48a4f2d7c2e134095b089d73f84af3933dd79ed25ba79c7bcf7d571b`.
The strict separate-module check passes in 4.47 seconds, with strict implicit
arguments, Mathlib standard linters, warnings as errors and the default heartbeat
limit. Imported manual foundation inspection passes in 18.44 seconds; only
`propext`, `Classical.choice`, and `Quot.sound` occur. Inspection commands remain
under `/tmp`, with no permanent fixture added. The scoped tactic scan finds no repeated blocks at its default
thresholds.

Checks use the same read-only TNLean provider
`8153728de51a3a489c932a8f377690c764892326` with QICLean
`b66600027b2e60ccafea43d041d563cdd00cf05b`. All new objects are private temporary
files. No dependency pin, shared cache, other worktree, or Mathlib source is changed.
No ordinary build is queued by this contribution. Ordinary module and compiled
blueprint verification remain pending common integration. Place the new chapter
after `ch35_aklv_spectral_cluster.tex`; the existing endpoint gap theorem must be
included in the blueprint as well.
