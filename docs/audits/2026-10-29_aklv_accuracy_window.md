# Accuracy-dependent AKLV windows with actual same-cut filtering

## Proved construction

The universal constant $A$ is chosen before the physical data and accuracy.
For local dimension $q\ge2$, unit ground vector $\Omega$ of the original
supported positive-contraction nearest-neighbour interaction, positive
rank-one projector gap $g$, and actual excited spectral value $\mu+g$,
`exists_aklv_physical_accuracy_window` constructs an approximant at every
cut $k\le L$. It assumes no fitting window, rank comparison, filter,
regional minimum or prior approximation.

For requested squared error $0<\rho\le1$, the explicit parameters are
$u=1+\log q+\log(1/g)$, $s_0=\lceil Au^2/g\rceil$,
$z=\log(128/\rho)$, $m=\lceil\sqrt{\sqrt{z^3/g}}\rceil$,
$s=s_0+2m$, $t=T(g)+16z$, and
$\ell=\lceil z\sqrt{(2t+s)/g}\rceil$.
The actual selected polynomial has squared shrinking coefficient at most
$\rho^2/4096$, and the actual clipped-target contribution is at most
$\rho/12800$. Hence the existing physical refinement gives squared error
at most $\rho$.

The centered-window equivalence retains the exact margins
$\lfloor s/2\rfloor\le k$ and
$s-\lfloor s/2\rfloor+1\le L-k$.
If the enlarged window starting at $a$ fits, the original window starts
at $a_0=a+m$ and has the same central cut. The frozen coherent physical
construction supplies its actual initialized unit vector $x$, including
the actual product vector, initial polynomial and normalized image.
The enlarged-window physical theorem is applied to this same $x$ at this
same cut. The conclusion retains both actual sets of regional minima,
the actual enlarged Hamiltonian, its unit target and projector gap,
polynomial degree, phase and normalized filtered image.
The regional minima can differ between the two widths; no equality of
their reference Hamiltonians is assumed.

If the enlarged window does not fit, use $y=\Omega$ exactly. The existing
endpoint-rank transport theorem gives
$\operatorname{SR}_k(\Omega)\le q^{\min\{k,L-k\}}$,
and the failed margin bounds this by $q^{s-\lfloor s/2\rfloor}$.
This covers endpoint cuts and short chains, without a replacement window
or an independent area-law/MPS theorem.

The all-cut physical theorem has no upper-gap hypothesis: the fitting
case derives $g\le1$ from the original interaction, and the exact boundary
alternative needs no such bound. The actual-first-excited-energy and
local-dimension restrictions remain explicit.

## Exact rank expression and remaining sharp comparison

The source is AKLV, arXiv:1301.1162v1, lines 1503–1517, in the official
local source whose SHA-256 is
`65bf824cd7d4f89bef5d819f713ac751445704bb077e81b4af3eb4ce5f2e4065`.
The exact common rank budget is
$B=\max\{D_0[q(\ell+1)]^E,q^{s-\lfloor s/2\rfloor}\}$,
where $D_0=[q(s_0^2+1)]^{32(2s_0+1)}$ and
$E=32(\lfloor\ell/s\rfloor+\lfloor\sqrt\ell\rfloor+1)$.
`aklvAccuracyRankBound_log` proves exactly
$\log B=\max\{\log D_0+E\log(q(\ell+1)),
(s-\lfloor s/2\rfloor)\log q\}$.
No exponential-in-degree replacement is used.

This checkpoint does **not** prove the uniform fourth-root upper bound for
that logarithmic expression. The remaining scalar target is
$C_A[u^3/g+(z^3/g)^{1/4}(u+\log(z+1))]$ with a universal coefficient
depending only on the already universal $A$. The exact rank identity and
fourth-root increment do not by themselves establish the optimized rate.
The concrete missing comparison and elimination plan are recorded in
`docs/paper-gaps/aklv13_two_block_robustness.tex`.
Marginal discarded-mass bounds, sequential MPS assembly, and any runtime
claim are not asserted here.

## Verification

The three actual production modules passed strict private checks against
fully checked TN mathematical snapshot
`da3ab8dcc9f9149cbbdcc56cae817ff783825f24` and documentation-only successor
`f93bc77b3dddcc292125eea18b96af153225251b`, with exact QIC package
`4276de2eeb5c4122f4482ef5e4fa205be5b71bd9`.
The frozen private parents are TN
`6d94b8b122624fb1ac0a8774293fda2a31509aa6` and QIC
`aa5ede2ad00ab2106c5106549caa743d078b0722`; their source and private-object
hashes remain guarded. A fresh provider guard covers 299 imported source
and ordinary-object pairs, and the selected import roots report zero
pending dependencies.

New objects are confined to a private temporary namespace. The ordinary
provider and frozen parent sources/objects are read-only. No build artifact
was copied, no Mathlib source was built, and no ordinary build was queued.
Strict checks use both automatic implicit options disabled, Mathlib's standard
linters and warnings as errors. The imported foundation audit inspected all
39 public declarations in the selected private modules and frozen parents,
including all 19 new public declarations, and found only the standard
foundations `propext`, `Classical.choice`, and `Quot.sound` (or a subset).
No audit fixture is committed.

Ordinary build and compiled blueprint verification remain integration gates.
Generated aggregators and chapter registration are excluded. The new chapter
belongs after `ch35_aklv_changing_targets.tex`.

### Checked source hashes

| Production source | SHA-256 |
|---|---|
| `TNLean/MPS/AreaLaw/AKLV/CenteredWindow.lean` | `70601b943d62d5323490a182a8e977633e876076e42be0d4f9570674c16abce4` |
| `TNLean/MPS/AreaLaw/AKLV/OptimizedTailParameters.lean` | `afe61de0f66938e544356a59df55029e430679a155ed63fc4553f8c995c94bef` |
| `TNLean/MPS/AreaLaw/AKLV/AccuracyWindow.lean` | `2e5cf54758fef28770c33e12ab189c6c1a57d1f84baf2897ed0898761be3a37f` |
