# Gap and ground-vector comparison for the actual two exterior truncations

`AKLV/SpectralCluster.lean` now derives an actual unique truncated ground vector,
a gap at least nine tenths of the original lower bound, and a phased vector
comparison. It starts from the original positive-contraction nearest-neighbour
interactions and their actual unique gapped ground vector. No residual,
perturbation estimate, truncated ground vector, or spectral comparison is supplied.

## Quantitative statement

Let \(q\ge1\), \(s\ge6\), \(a+s+1\le L\), and let the original interactions satisfy
\(0\le h_i\le I\), with support on \(\{i,i+1\}\). Suppose the unit vector \(\Omega\)
has energy \(\mu\) for \(H'=\sum_i h_i\) and

\[
H'-\mu I\ge g(I-|\Omega\rangle\langle\Omega|),\qquad g>0.
\]

The theorem constructs the three genuine reference minima and a common unit
vector attaining them. They determine the original normalized energy \(E_0\),
with \(E_0+\sum_j e_j=\mu\) and \(0\le E_0\le6\). These choices precede the
accuracy and truncation parameters.

For \(0<\tau\le1\), define

\[
\Theta(g,\tau)=\max\left\{g+11,\,
g+8\log\frac{10^6\cdot64e^{3/4}}{\tau g}\right\}.
\]

For every \(t\ge\Theta(g,\tau)\), the operator in the conclusion is the actual
two-exterior truncation already defined in `TwoBlockTruncation.lean`, using the
constructed reference shifts and the cuts \(a+2,a+s-1\). Write its actual canonical
eigenbasis as \((v_j)\), with eigenvalues \(\lambda_j\). The theorem proves:

- The spectral subspace below \(E_0+g/20\) has dimension one and remains unchanged
  throughout the full cutoff band \([E_0+g/20,E_0+19g/20]\).
- Both squared projection losses between this subspace and \(\mathbb C\Omega\)
  are at most \(\tau/200\).
- There is an actual basis index \(j_0\) with \(\lambda_{j_0}\le E_0+g/20\), and
  every other eigenvalue satisfies \(\lambda_j\ge\lambda_{j_0}+9g/10\).
- Some phase satisfies \(\|v_{j_0}-e^{i\theta}\Omega\|^2\le\tau/100\).

Since the basis is complete and orthonormal, the selected vector is an actual
unit ground eigenvector and its eigenspace is one-dimensional. The eigenvalue
separation is an actual gap bound. No projector-gap inequality for the truncated
matrix is separately returned by this theorem.

## Proof and source comparison

The physical residual gives \(\xi=64e^{3/4}e^{-(t-g)/8}\) on every partially
clipped low space below \(E_0+g\). The explicit threshold proves both
\(t\ge g+11\) and \(\xi\le\tau g/10^6\); the scalar tail condition is derived,
not assumed. Restriction to the two cutoffs \(E_0+g/40\) and \(E_0+19g/20\)
allows the existing QICLean scaled low-cluster theorem to apply. The original
global rank-one gap identifies the original low space with \(\mathbb C\Omega\).

The actual new low space therefore has dimension one. Choose a canonical
eigenvector in it. Every other canonical eigenvector is orthogonal to it and
must lie above \(E_0+19g/20\), giving the stated gap. Projection onto the original
ground line retains squared overlap at least \(1-\tau/200\). The existing
phase-minimization theorem gives the squared vector error \(\tau/100\).

This is a quantitative physical consequence towards [AKLV v1, Theorem 6.1 and
Section 6.3](https://arxiv.org/html/1301.1162v1). The theorem concerns the actual
two exterior truncations of the original chain. It does not replace them by the
three-bulk ALVV construction. The generic finite-dimensional spectral comparison
uses the corrected window count documented in the
[QICLean hard-truncation note](https://sirui-lu.com/QICLean/paper-gaps/alvv16_hard_truncation_windows.pdf).
The middle energy-shift correction and the remaining source scope are recorded in
`docs/paper-gaps/aklv13_two_block_robustness.tex`.

The source's more general formulation with arbitrary exterior operators remains
separate. The explicit logarithmic threshold has not been compared in Lean with
the printed polynomial sufficient threshold. The free accuracy has not been
eliminated to give a single displayed exponential vector-error function of \(t\).
The unrestricted source theorem is not marked complete by the new blueprint entry.
The parameter \(g\) is the original gap lower bound; no bound \(g\le1\) or artificial
gap cap is assumed. In the nontrivial original unique-ground setting, the existing
endpoint trial-vector theorem supplies \(g\le1\) when needed for later comparisons.

## Verification

Production SHA-256:
`0fe5d4087b593b543cfc9861110995483cd6df607240b183c3811500062e7767`.
The strict separate-module check passes in 6.35 seconds with strict implicit
arguments, Mathlib standard linters and warnings as errors. The default heartbeat
limit suffices. Both public declarations have only the standard foundations
`propext`, `Classical.choice`, and `Quot.sound`; inspection commands remain under
`/tmp`, with no permanent fixture. The scoped tactic scan reports no repeated
blocks at its default thresholds.

The checks use the read-only TNLean provider
`8153728de51a3a489c932a8f377690c764892326` with QICLean
`b66600027b2e60ccafea43d041d563cdd00cf05b`. Only new temporary objects are written;
no cache, dependency pin, other worktree, or Mathlib source is changed.
No ordinary build is queued by this contribution. Ordinary module and compiled
blueprint verification remain pending common integration. Place the new chapter
after `ch35_aklv_normalization.tex`.
