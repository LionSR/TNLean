# Uniform scalar parameters for the finite Gaussian filter

This contribution supplies fixed scalar choices for the Gaussian construction and
natural-degree polynomial bounds whose constants precede the chain length. Its source
is [Huang, arXiv:1406.6355v6](https://arxiv.org/pdf/1406.6355v6), Section 5.4,
equations (19)–(22) and Lemmas 18–19. The choices are conservative supporting estimates,
rather than assertions of the sharper printed constants or gap dependence.

For $c>0$, $\Delta>0$, and a natural length $L$, the definitions are

$$
 \eta_L=\frac{c}{64(c+L+1)},\qquad
 a_L=8\log(1/\eta_L)+8,\qquad \sigma_L=a_L/\Delta^2,
$$
$$
 T_L=\sigma_L+\log(2/\eta_L)+1,\qquad \mu_L=\frac{\Delta}{a_L+1},
$$
$$
 E_L=\left\lceil\frac{2L}{\mu_L}\right\rceil_++1,\qquad
 S_L=\left\lceil\frac{2T_L(2L+1)}{\eta_L}+2\right\rceil_+,
 \qquad R_L=S_Lq^{8r_L+8},
$$

where $r_L=\operatorname{chainPropagationRadius}(L,T_L,\eta_L)$ is the actual radius
of the physical propagator construction. The variance is represented as a nonnegative
real, and its real value is proved to equal $a_L/\Delta^2$.

The proved scalar estimates give $0<\eta_L<1/64$, $a_L\ge8$, $\sigma_L>0$ and $T_L>0$.
The time tail and the approximate-center spectral error obey

$$
 2e^{-T_L^2/(2\sigma_L)}\le\eta_L,\qquad
 e^{-\sigma_L\Delta^2/8}\le\eta_L.
$$

If $|E-E_0|\le\mu_L$, then $|E-E_0|\le\Delta/2$ and
$\sigma_L(E_0-E)^2\le1$. This is precisely the scalar accuracy required by the separate
approximate-center spectral theorem. The proof gives the weighted bound from
$a_L/(a_L+1)^2\le1$, without assuming the true ground energy is small. For $L\ge1$,
$32\eta_L\le c/L$; for any ground amplitude $c_0\ge1/2$ one has $4\eta_L<c_0/2$.
Thus the total four-error budget fits the requested normalization and final overlap
estimates. The energy grid, the amplitude theorem and normalized viability remain
separate constructions.

For clarity, the polynomial constants used in the proofs can be chosen as follows:

$$
 K=64(c+1)/c,\qquad A=8\log K+9,\qquad
 B=A/\Delta^2+\log2+\log K+2,
$$
$$
 D=16\bigl((v+1)B+|\log C_{\rm LR}|+\log K+3\bigr),\qquad
 n=\lceil D\log q\rceil_+,
$$

where $v,C_{\rm LR}>0$ are the fixed propagation constants. Uniformly before $L$,

$$
 1/\eta_L\le K(L+1),\quad a_L+1\le A(\log(L+1)+1),\quad
 T_L\le B(\log(L+1)+1),\quad8r_L+8\le D(\log(L+1)+1).
$$

Consequently $q^{8r_L+8}\le e^n(L+1)^n$. With
$\alpha=2A/\Delta+2$ and $\beta=4BK+3$, the actual counts satisfy
$E_L\le\alpha(L+1)^2$ and $S_L\le\beta(L+1)^3$. Hence

$$
 E_LR_L\le\alpha\beta e^n(L+1)^{n+5}.
$$

Each count and rank budget is a positive integer. This same product bound therefore
dominates $E_L$, $S_L$ and $R_L$. Taking the natural ceiling of its coefficient gives
the headline `exists_huangFilter_uniform_nat_polynomial`: for fixed $q\ge1$, $c>0$
and $\Delta>0$, there exist natural $P,d$, with $P\ge1$, such that all four quantities
are bounded by $P(L+1)^d$ for every natural $L$. The existential choices occur before
the universal length quantifier. This is a polynomial in length with natural degree
and natural coefficient, without an additional hypothesis depending on $L$.

The degree has the explicitly displayed coarse dependence through
$n=\lceil D\log q\rceil_+$ and $B=A/\Delta^2+\log2+\log K+2$; the coefficient contains
$e^n$. No uniform polynomial dependence on inverse gap or on local dimension is claimed.
The spectral and time-cutoff choices are deliberately larger than sharper optimized
choices in the source.

All three actual modules passed separate compilation with strict changed-module options,
standard linters and warnings treated as errors:

| Module | Time | SHA-256 |
|---|---:|---|
| `FilterParameters` | 30.64 s | `d86de9b7c36e9013a531aaaae3a894f03e715882f26abecbfb6dcb6cc2c7f1cf` |
| `FilterGrowth` | 43.56 s | `d499dbe0a8e3b4bb0c84137d11d0709b46efe8a1fc67d520992f4170ee2959e6` |
| `FilterPolynomial` | 38.64 s | `b67a4dfac0d8b5ed6c3938af8f597a5aa2771d44fa6c1c0be5a092fdc9b86f05` |

These wall times fall above the repository's 25-second warning threshold and below its
50-second failure threshold under the current shared load. Sources remained unchanged
during each check. Compilation outputs are private temporary objects, and the dependency
artifacts come from the agent's already seeded worktree. No Mathlib source is compiled,
no shared cache or dependency pin is modified, and no ordinary build is started alongside
the coordinator's verification. Manual foundation checks are kept under `/tmp`; no
permanent Lean test fixture is added. The manual imported foundation audit checked all
26 public declarations in 20.77 seconds and reported exactly `propext`, `Classical.choice`
and `Quot.sound` for each. Its temporary source SHA-256 is
`292069c7e06c39484e9d00b06ad6388dd792a493eea8cb0c5534474d56e37d2c`.
Ordinary integration builds and compiled blueprint declaration checks remain subsequent
verification.

Static blueprint synchronization reports 30,201 declaration references with no missing,
stale or duplicate references, and reverse coverage includes all 26 new declarations.
The chapter passes the repository LaTeX formatter and ChkTeX configuration. Prose,
whitespace and proof-integrity checks pass, and the tactic scan finds no repeated pattern
at its current thresholds.

These modules prove scalar and size estimates. They do not assert that the energy-grid
family, viable-set error-reduction step or successive induction has been assembled.
