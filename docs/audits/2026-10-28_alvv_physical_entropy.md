# Physical ground-space entropy: source and dependency audit

This audit concerns the entropy conclusion of Arad, Landau, Vazirani and
Vidick, [arXiv:1602.08828v2](https://arxiv.org/abs/1602.08828v2), Theorem 4.9
(`thm:al-dg`, source lines 1048–1099), and its use of Theorem 4.7 and
Proposition 4.10. The principal declaration is
`TNLean.MPS.AreaLaw.exists_physical_dg_interval_entropy_bound` in
`TNLean/MPS/AreaLaw/PhysicalDGEntropy.lean`.

The statement concerns the original Hamiltonian
$H=\sum_{i=0}^{L-2}h_i$, with each $h_i$ supported on two adjacent sites and
$0\le h_i\le I$. It assumes two spectral values $\mu<\nu$, a number
$\gamma>0$, and
$\operatorname{spec}(H)\subseteq\{\mu\}\cup[\mu+\gamma,\infty)$.
Thus $\mu$ is the ground energy. The second spectral value is already part
of Assumption (DG); it is used to derive $q\ge2$, rather than impose a
separate restriction on the local dimension. The target $G$ is the entire
$\mu$-eigenspace. No ground vector, selected basis of $G$, or prescribed
degeneracy is supplied as an additional hypothesis. This follows the ground-space
cutoff in the proof of Theorem 4.7; the extra ground-energy shift in its printed
statement is corrected in the companion
[spectral-projector note](https://sirui-lu.com/QICLean/paper-gaps/alvv16_spectral_projector_boundary.pdf).

The entropy statement has the quantifier order $\exists C>0$ followed by
every chain, local dimension, interval, Hamiltonian, gap and unit vector
$\psi\in G$. Writing $r=\dim G$ and $g=\min\{\gamma,1\}$, its conclusion is

$$
 S(\rho_J)\le\log r+
 \frac{C}{g}\bigl(1+\log q+\log(1/g)\bigr)^3.
$$

Here $J$ is an interval and $\rho_J$ is the actual reduced state of $\psi$.
The source's fixed-cut entropy conclusion is included by taking $J$ to be
a prefix. The statement does not assert the error-dependent Schmidt-rank
or global matrix product state conclusions of Theorem 4.9.
The argument uses hard spectral truncation. The soft cluster-expansion
construction is a separate part of the paper.

Proposition 4.10 is printed for arbitrary subsets, although its proof uses
the three contiguous blocks of Theorem 4.7. The formalized bootstrap is
restricted to intervals. The restriction is necessary: a product of
adjacent Bell pairs has a unique gapped ground state, while a region
containing one endpoint from each of $m$ pairs has marginal $I/2^m$.
Consequently a $0.015$-viable subspace must have dimension at least
$(197/200)2^m$, whereas the printed bound is independent of $m$ at
$r=1$, $q=2$ and $\gamma=1$. The source restriction and the corrected numerical
constants are recorded in the companion
[bootstrap note](https://sirui-lu.com/QICLean/paper-gaps/alvv16_bootstrap_constants.pdf).
No unrestricted-subset version is claimed here.

The coefficient one on $\log r$ can be checked directly in the rank-tail
argument. One universal scale $A$ determines both the initial viable space
$W_0$ and every accuracy-dependent family. The choice of $W_0$ precedes
the numerical count base $m\ge q$; changing $m$ does not change the physical
local dimension or the tensor coordinates. With $m_i=q2^i$, the resulting
rank thresholds are $rD_0^{24}D_i^2$, and the same spectral probability
distribution of $\rho_J$ satisfies

$$
 \sum_{a\ge rD_0^{24}D_i^2}p_a\le2^{-(i+1)}.
$$

A cubic dyadic majorant bounds these thresholds by
$r2^{B(i+1)^3}$. The finite-probability estimate retains $\log r$ once and
bounds the remainder by $26B\log2+2\log2$. In particular, the argument does
not sum a separate $\log r$ contribution at every scale. The identification
of the coefficient-matrix marginal with $\rho_J$ is proved in the companion
library; it is not an independent coordinate-compatibility hypothesis.

The original entropy draft selected QICLean revision
`3d15bc78a7a20531e836001cbe91dcd27b6d24b9`. That revision does not contain
`QICLean.Analysis.ViableSubspaceEntropy` or the cubic dyadic rank-tail
theorem used above. The required revision is
`af7e5c90650e5ddb06c2befac508df97fd20b2e3`, from
[QICLean #979](https://github.com/LionSR/QICLean/pull/979). It descends from
the main dependency revision and has byte-identical Lean, Mathlib and
dependency build inputs. All five QICLean revision fields in the root and
documentation dependency records must select this same revision.

The combined contribution is integrated on exact TNLean main revision
`c457d2be30e12c770fb7807e822f0ca72739f498`, preserving its removal of theorem
fixtures and its unrelated mathematical additions. Frozen integration
`0341b256badfec30365411d5b77923777fc06208` passes the guarded global target
(9632 jobs), the full library (14996 jobs), all 38 changed-source strict checks
and five existing regression checks with the unchanged 45-second limit.
Actual imported declarations from the ordinary object files pass local
foundation inspection with exactly `propext`, `Classical.choice` and
`Quot.sound`. Pinned blueprint dependencies, source/declaration
synchronization and compiled declaration checks pass. Mathlib artifacts are
prebuilt, and the selected QICLean revision is unchanged. No permanent theorem
test files are included. The subsequent documentation changes state the
source's second-eigenvalue assumption and the remaining capped-gap comparison;
they do not alter any mathematical signature or proof body.
