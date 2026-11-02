# Soft truncation on one interval and its operator representation

For positive nearest-neighbour contractions on a chain, this contribution
constructs one soft Hamiltonian with both low-energy spectral comparisons
and a matrix product operator approximation of prescribed norm accuracy.
It extracts the completed one-interval construction, rather than asserting
the full renormalization algorithm or its running time.

## Mathematical result

Let \(H=\sum_{i=0}^{N-1}h_i\) act on \(N+1\) sites of dimension \(q\ge1\),
with \(0\le h_i\le I\) supported on sites \(i,i+1\). For a prescribed
interval \(J\), write \(A_J\) for its internal sum and \(e_J\) for its
minimum energy. Given \(\eta,w,\delta>0\), set
\[
\rho=\min\{1,w/2,\delta w^2/[2(\eta+2)]\},\qquad
m=\left\lceil12+\frac23\eta+\frac{16}{3}\log(80/\rho)\right\rceil,
\qquad t=3m.
\]
The order is chosen before the chain and interaction. The three disjoint
regional sums have attained minima and a common unit minimizing vector;
subtracting their minima gives an original ground energy in \([0,2]\).
For every \(e_J-10\le\epsilon\le e_J\), define
\[
\widetilde H=H-A_J+\epsilon I+h_{m,t}(A_J-\epsilon I),\qquad
h_{m,t}(x)=t\sum_{j=1}^{m}\frac{(1-e^{-x/t})^j}{j}.
\]
Then \(\widetilde H\le H\), and the two ground energies differ by at most
\(\rho\). Each low-energy space of width \(\eta\), measured from its own
minimum energy, has squared distance at most \(\delta\) from the other
Hamiltonian's space of width \(\eta+w\).

For every \(\xi>0\), the same \(\widetilde H\) has a site-dependent matrix
product operator \(T\) satisfying \(\|\widetilde H-T\|\le\xi\), with
\[
D=1+Nq^2+(m+1)\ell^2q^\ell,
\]
where
\[
W=3m2^{m+1},\qquad b=2(e^{1/3}-1)\in(0,1),\qquad
\ell=\max\left\{1,
\left\lceil\frac{\log\max\{1,N^2\}-\log\log(1+\xi/W)}{-\log b}\right\rceil
\right\}.
\]
No spectral conclusion about the approximating operator \(T\) is asserted.
The construction includes a one-site chain, local dimension one, and empty
or endpoint intervals. No spectral gap or ground-space dimension is supplied.

## Source and corrections

The source is ALVV, arXiv:1602.08828v2,
`References/1602.08828/local_alg_arxiv_v2.tex`: `def:ft` (1152–1157),
`def:soft-trunc` (1178–1185), `lem:exp-approx` (1195–1255),
`lem:exp-approx-eff` (1262–1268), and the cluster argument (1935–2115).
The order and scale satisfy the short-heat-time condition in the source's
operator approximation argument. The heat expansion includes its constant
term and the energy shift.

The printed uniform power estimate and physical-support cluster estimate
remain false. Their counterexamples are preserved in
`docs/paper-gaps/alvv16_soft_truncation_energy_estimate.tex` and
`docs/paper-gaps/alvv16_cluster_approximation.tex`. The new result has a
separate mathematical blueprint entry. The construction instead uses a
regional exponential moment and a normalized interaction-label expansion.
Simultaneous truncation on several regions, the complete improving family,
and a running-time bound remain separate tasks.

## Extraction and dependencies

The source is local TNLean revision
`9ad6cdd3c23da0ce9b5e6cc36edfec99f0211ff7`; the publication base is main
`5fc343a57d70eefd2902780107851ab9b0753a82`. Thirty-one missing modules are
recovered. Current main's circuit geometry, product form and trace-chain
operator definitions are retained. All sixty new public declarations have
mathematical blueprint references.

The finite-dimensional estimates are submitted in
[QICLean #1016](https://github.com/LionSR/QICLean/pull/1016), pinned at
`5594a69a916a0eb7f66f159b218882846b837f62`. They comprise
weighted soft remainders, shifted cutoff comparisons, spectral-window
perturbation, the exact heat expansion, and the inclusion–exclusion bounds.

## Verification

At revision `95e559a90d`, the local target build (4,017 jobs) and the
full library build (15,554 jobs) pass. The compiled whole-library
blueprint declaration check also passes.
Strict Lean checks pass for all 34 changed Lean files and the seven
discovered regression files. Each of the 60 new public declarations
depends only on the standard kernel axioms `propext`, `Classical.choice`
and `Quot.sound`. The QICLean prerequisite has passed its full local build,
hosted checks and 32-declaration axiom audit.

The active blueprint has no duplicate labels, and all references in the new
sections resolve. Hosted policy, inline-diagram, blueprint web and full blueprint PDF
checks pass. The hosted full Lean build remains in progress.

The added chapter sections and the energy-estimate note compile as PDF
excerpts. The chapter excerpt has no overfull boxes; its main estimates and
operator construction were inspected visually. LaTeX lint and prose checks
pass for the changed sections. The theorem-role check reports the same 41
pre-existing mismatches as the frozen main revision, with identical output.
