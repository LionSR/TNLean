# Low-energy improving families on prescribed intervals

This contribution constructs one family of regional operators before the
viable subspace is chosen. It treats every interval of a finite positive
nearest-neighbour chain, including empty intervals and intervals at either
endpoint. No spectral gap or spectral-density hypothesis is supplied.

## Mathematical statement

Fix a bandwidth bound \(\eta_{\mathrm{LD}}>0\). One constant \(A\ge21\)
is chosen before the chain length \(L\ge2\), local dimension \(q\ge2\),
parameter \(\mu>0\), bandwidth
\(2\mu/\log L\le\eta\le\eta_{\mathrm{LD}}\), and interaction. Put
\[
w=\frac{\mu}{3\log L},\quad g=\min\{w,1\},\quad
u=1+\log q+\log(1/g),\quad
\ell=\lceil Au^2/g\rceil,\quad D=(q\ell^2)^{22\ell}.
\]
Writing \(K=22(A+1)[6+2\log(A+1)]\), the count satisfies
\[
\log D\le3K\max\{1,\eta_{\mathrm{LD}}/6\}\frac{\log L}{\mu}
\left[1+\log q+\max\left\{\log\frac{3\log L}{\mu},0\right\}\right]^3.
\]
For each prescribed interval, the actual regional ground energies and a
common minimizing vector determine a centered original Hamiltonian with
attained minimum \(E_0\). There are nested auxiliary subspaces
\(T_-\subseteq T_+\), a family of \(D^2\) regional operators, and
\(\Delta>0\) with \(D^{12}\Delta<10^{-5}\). The original spectral
space below \(E_0+\eta\) is \(1/200\)-close to \(T_+\), and \(T_-\)
is \(1/200\)-close to the original space below \(E_0+\eta-3w\).

The family enlarges every \(\delta\)-viable subspace for \(T_+\),
where \(\delta<1\), to a space of dimension at most \(D^2\) times its
initial dimension and viability error \(\Delta/(1-\delta)^2\) for
\(T_-\). On the original spectral windows, the two comparison losses
instead give the error
\[
2\left(\frac{\Delta}{[1-2(\delta+1/200)]^2}+\frac1{200}\right),
\qquad \delta\ge0,\quad 2(\delta+1/200)<1.
\]
The strict filter tradeoff is not a claim that this latter error can be
arbitrarily small.

Long intervals use inward cuts, the physical five-region truncation, and
its common polynomial family on the prescribed region. Short intervals
use the existing configuration matrix units. The low-density bootstrap,
sampled recursion, efficient central tensor representation and running
time are separate results.

## Source and scope

The source is ALVV, arXiv:1602.08828v2, Theorem `t:aisgapless`, lines
1027–1041 of `References/1602.08828/local_alg_arxiv_v2.tex`. The source
buffer is \(w=\mu/(3\log L)\), so its bandwidth condition gives
\(\eta\ge6w>3w\). The finite theorem retains the restrictions
\(L\ge2\) and \(q\ge2\), the cap on the effective width, and the
explicit count. These qualifications are recorded in
`docs/paper-gaps/alvv16_low_energy_family_buffers.tex`; its blueprint
entry states them explicitly. The absence of a density hypothesis makes
this an improving-family construction, not a low-density area law.

Six completed modules, containing eleven public declarations, are
extracted from local revision `9ad6cdd3c23da0ce9b5e6cc36edfec99f0211ff7`.
They extend the independent-threshold residual in TNLean #10515. The
finite-dimensional estimates come from the accepted QICLean #1016 and
#1017 contributions on their common Mathlib 4.35-compatible revision.
The nested-cutoff viability theorem additionally uses QICLean #1020;
revision `965d1bb07d4903785411cb7b95a5e866a243fd0d` includes that proof.
The existing private short-region spanning lemma is exposed as
`exists_short_actual_region_spanning_family`, with its proof unchanged and
its two existing callers updated. It also receives a mathematical blueprint
entry. There are twelve newly public declarations in total.

## Verification

The extracted statements have been compared with the source and the
explicit buffer calculation. Source-level blueprint synchronization,
declaration roles, generated imports, and whitespace checks pass. The
new mathematical sections and the three-page paper-gap note compile;
their rendered statements have been inspected. The tactic-pattern scan
finds no new repeated pattern requiring a separate abstraction.

Compilation and compiled declaration checks are pending. Verification
records refer to this extracted contribution, not merely to the earlier
local source.
