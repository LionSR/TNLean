# Finite Gaussian approximation of the original positive chain

The theorem `exists_positive_chain_gaussian_approximation` combines the constructed
physical propagators with positive interval-mass Gaussian quadrature. Its only physical
hypotheses are nearest-neighbor support and the Loewner inequalities $0\le h_i\le I$,
with $q\ge1$. It has no supplied propagator, partition, cut-dependent approximant, spectral
condition, bound on the ground energy or tensor representation among its hypotheses.
The source is [Huang, arXiv:1406.6355v6](https://arxiv.org/pdf/1406.6355v6), Section 5.4,
Lemma 19 and equations (19)–(22), using the global propagation construction of
[Osborne, arXiv:quant-ph/0508031v2](https://arxiv.org/pdf/quant-ph/0508031v2), Figure 2
and equations (12)–(13).

For variance $a\ge0$, energy estimate $E\in\mathbb R$, cutoff $T\ge0$ and errors
$\eta,\rho>0$, put $r=\operatorname{chainPropagationRadius}(L,T,\rho)$. The theorem
constructs one finite sum $Q$ with

$$
 1\le N\le\frac{2T(L+|E|+1)}{\eta}+2,
 \qquad\|G_a(H-EI)-Q\|\le2e^{-T^2/(2a)}+\eta+\rho,
 \qquad\operatorname{OSR}_k(Q)\le Nq^{8r+8}
$$

at every cut $k$. The zero-variance case uses the existing point-mass Gaussian measure;
the displayed tail bound then uses the totalized real-division convention and is merely
coarse. The empty chain, a one-dimensional local space and cutoff zero are included.

The original unshifted positive Hamiltonian is propagated. Writing $w_j$ for exact
nonnegative Gaussian interval masses and $t_j$ for the mesh nodes, the construction is

$$
 Q=\sum_jw_je^{-it_jE}K(-t_j),
 \qquad\|e^{-isH}-K(s)\|\le\rho\quad(|s|\le T).
$$

The sign is determined by $e^{it(H-EI)}=e^{-itE}e^{itH}$. Scalar phases have modulus one
and do not increase operator-Schmidt rank. Since $\sum_jw_j\le1$, the total propagator
replacement error is at most $\rho$. The sample count follows from
$\|H-EI\|\le L+|E|$. Rank subadditivity applies to this one complex-weighted sum at every
cut. The preceding explicit radius bound controls its exponent by
$O(T+\log(L+1)+\log(1/\min\{\rho,1\}))$. No Hilbert–Schmidt norm conversion is used.

The actual module `PhysicalGaussian.lean` passed separate compilation with strict
changed-module flags, all standard linters and warnings treated as errors in 4.98 seconds.
Its SHA-256 is `96a40418b2b5c2e8653d308a8765cca201c1b1945c55a46207df81273ead9949`.
The fixture `scripts/huang_physical_gaussian_regression.lean` imports this actual module
and audits the public theorem. It passed in 3.37 seconds, reporting exactly `propext`,
`Classical.choice` and `Quot.sound`; its SHA-256 is
`a19238819547d6ecdec42c66d35ef2d77d22fafc05016e526f1389a625f8c9e6`.
The checked sources remained unchanged. All compilation outputs went to private temporary
artifacts against existing prebuilt dependencies. No Mathlib source was compiled and no
shared dependency cache was modified. Ordinary integration and compiled blueprint checks
remain pending, through the coordinator's existing verification rather than another
parallel build.

Static blueprint synchronization reports 30,166 declaration references with no missing,
stale or duplicate references, including reverse coverage of the new public theorem.
The chapter passes the repository's LaTeX formatter and ChkTeX configuration. The prose,
whitespace and proof-integrity checks pass; the tactic scan finds no repeated pattern
in the Huang modules at its current thresholds.

The generic Gaussian quadrature and scalar-shift identities belong to the QICLean
Gaussian-filter development. This physical composition belongs to TNLean because its
construction uses actual chain geometry and simultaneous cut ranks. No companion-library
pin is changed. Exact interval masses establish mathematical existence, without claiming
an algorithm for numerical integration.

This contribution proves the finite operator-approximation step. Spectral suppression,
selection of an energy estimate, normalized viability improvement, and the successive
viable-set induction remain separate results. It does not assert the completion of the
unrestricted LVV/Huang algorithm.
