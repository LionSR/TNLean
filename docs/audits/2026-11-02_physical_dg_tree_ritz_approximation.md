# Approximation by Ritz extraction from the actual recursive root

The construction starts from the balanced interval spaces of the physical
nearest-neighbour Hamiltonian. It chooses one trimming threshold for that tree
and all final filter-and-trim iterates. The final output is the lowest
$r$-dimensional Ritz space of the terminal native space, where $r$ is the
dimension of the original full ground space. No initial viable space, reference
space, improving family, final approximation or trial-energy estimate is assumed
in the final theorem.

## Mathematical content

The universal constants precede the chain, local dimension and Hamiltonian.
The actual improving families precede the requested accuracy, common threshold,
sampling parameter and child spaces. For each requested $\eta>0$, put

\[
 A=\|H\|-\mu,\qquad c=\gamma/A,\qquad
 \rho=\frac{\eta\gamma}{2A+\eta\gamma},\qquad
 n=\left\lceil\frac4c\log\frac1\rho\right\rceil+1.
\]

The physical spectral assumptions imply $0<c\le1$ and $0<\rho<1$.
A physical reference space is constructed with the same dimension as the ground
space, mutual squared projection error at most
$\varepsilon_{\rm ref}=c^2\rho/32768$, and an all-span MPS bond bound
$b=r^2B$. Its whole-environment interval rank is controlled using the square
of that all-span bond bound; it is not replaced by a one-boundary estimate.

With the actual tree reference bound $D_{\rm tree}$ and physical family
count base $D_{\rm filter}$, choose

\[
 D_*=\max(D_{\rm tree},b),\qquad
 N_*=\left\lceil\frac{100D_{\rm filter}^{12}}{c\rho}\right\rceil,
 \qquad \xi=\frac1{1000D_*N_*\sqrt{L+1}}.
\]

This is at most the admissible tree threshold and satisfies the strict source
condition $\sqrt{Lrb}\,\xi<\eta/(10^4D_{\rm filter}^{12})$.
The actual recursive construction therefore applies at this same threshold.
Its full-chain root is $3/200$-close to the original full ground space.
The literal raw filter $I-H/\|H\|$, followed by the actual collective trim,
is repeated $n$ times. The terminal space $W$ is $\rho$-close to that
same ground space. The actual Ritz space $R\subseteq W$ has dimension $r$
and is mutually $\eta/2$-close to the ground space. The energy conversion is
$A\rho/(1-\rho)=\eta\gamma/2$.

If the recursive dimension bound is $M=D_{\rm filter}^6s^3$, every vector
of $R$ has native MPS bond dimension at most
$10^6(D_*N_*)^2(L+1)M^2$. The second factor of $M$ comes from the finite
span of the recorded trimmed vectors and is retained explicitly.

## Source and scope

The source is arXiv:1602.08828v2, `local_alg_arxiv_v2.tex`, `t:alg1`,
lines 1777–1817, and `eq:algo-xi-dg`, lines 1800–1805. Its (DG)
assumption, lines 275–279, includes a second smallest eigenvalue; the explicit
ν in the physical theorem is therefore part of the source hypotheses.

The recursive witnesses use full block leaves of length at most $4\ell$
and one final collective trim at each long parent. The reference estimates use
$g=\min(\gamma,1)$. The theorem does not establish adaptive joint sampling
probability, the source energy-estimation invariant, the printed final
iteration count or running time. Its explicit count is in the internal
projection target $\rho$; in particular, it is not a proof of the printed
quantitative conclusion. The corrected normalized filter recurrence is
recorded in `docs/paper-gaps/alvv16_final_filter_gain.tex`, and the reference
and modified-tree qualifications remain in
`docs/paper-gaps/alvv16_approximation_parameters.tex`. The new blueprint
entries are supporting lemmas, not completion marks for the unrestricted
source algorithm.

## Verification

Strict actual-module checks used the immutable provider TN
`d316e8cbe52bd5f12bcfbeec687d1dbef7633586` with its own QIC
`d1317fdb229a1048cc65ec5ab1912403ab6bcbc0`. The provider had passed the
15,643-job full build with zero Mathlib source jobs. The new sources and
objects were private, with guards on every selected source/object pair,
root input and the warmed Mathlib object. No cache or provider was changed.

| Module | Strict time | Guarded source/object pairs |
| --- | ---: | ---: |
| `FullIntervalTrimmingMPS` | 5.676 s | 260 |
| `PhysicalDGAutomaticRefinement` | 10.226 s | 747 |
| `PhysicalDGTreeApproximation` | 14.379 s | 766 |

An imported inspection of all three new public theorems passed in 7.765 s
with 767 guarded pairs. Each depends only on `propext`, `Classical.choice`
and `Quot.sound`. The temporary inspection source was deleted. The initial
inspection already reported those foundations but failed only the temporary
file's header and hash-command linters; that attempt is preserved separately,
and the corrected inspection disables only the hash-command linter locally.
No production linter was disabled.

These private checks do not replace the subsequent combined ordinary build,
compiled blueprint declaration check and changed-module timing gates.

The source-level blueprint declaration synchronization, blueprint role check,
reader-facing prose check, whitespace check and scoped tactic-pattern scan
passed. The scan found no repeated tactic pattern at its configured thresholds.
The only existing blueprint sentence changed is the theorem-role word in the
common-radius prerequisite reference, as required by the role checker.
