# Collective trimming through a physical reference space

The principal declaration is
`TNLean.MPS.AreaLaw.exists_physical_dg_collective_trimming_bound`.
It supplies the reference-space trimming step in ALVV,
[arXiv:1602.08828v2](https://arxiv.org/abs/1602.08828v2), proof of
`t:alg1`, lines 1801–1805 of `local_alg_arxiv_v2.tex`.
The source SHA256 is
`19d37facb8bf8da6ea5555cd7185c054d251ad4a06c2f44fcb92593235ad6b92`.

Let $G$ be the full ground space of the original supported positive
nearest-neighbour contractions, with the two distinct spectral values
and positive gap lower bound of source Assumption (DG). Write $r=\dim G$.
For $0<\varepsilon\le1$, the already constructed reference theorem chooses
one space $U$ of dimension $r$, mutually $\varepsilon$-close to $G$, in
which every vector has matrix product bond dimension at most $r^2B$.
The integer $B$ and the space $U$ are chosen before the block or viable
space. The logarithmic bound for $B$ retains the universal constant and
accuracy budget of the reference theorem.

Now let $S$ be an actual $\delta$-viable subspace on the first $i$ sites,
where $0\le i\le N$ and $\delta\ge0$. Choose its orthonormal basis
internally and form the actual collective trim by the existing successive
spectral projections. With $m=\max\{i-1,0\}$,
the two applications of the existing closeness-composition theorem give

$$
\begin{aligned}
S\otimes\mathcal H_R &\text{ is }2(\delta+\varepsilon)\text{-close to }U,\\
\operatorname{Trim}_{\xi}(S)\otimes\mathcal H_R
  &\text{ is }\bigl(2(\delta+\varepsilon)+2\xi\sqrt{m r^2B}\bigr)
    \text{-close to }U,\\
\operatorname{Trim}_{\xi}(S)\otimes\mathcal H_R
  &\text{ is }\bigl(4\delta+6\varepsilon+4\xi\sqrt{m r^2B}\bigr)
    \text{-close to }G.
\end{aligned}
$$

All cut-rank hypotheses needed by collective trimming are derived from
the reference space's exact matrix product bound. The physical theorem
assumes no reference space, approximating vectors, orthonormal basis,
rank estimate, or supplied trimmed object. Its input $S$ and its viability
for $G$ are explicit: the theorem does not construct the sampled viable
spaces required by the algorithm.

The trimming constant is the corrected one in the companion note
[ALVV trimming constant](https://sirui-lu.com/QICLean/paper-gaps/alvv16_trimming_constant.pdf).
The quantitative reference bound uses $g=\min(\gamma,1)$; the comparison
with the printed inverse-gap rate remains restricted to
$0<\gamma\le1$, as documented in
`docs/paper-gaps/alvv16_approximation_parameters.tex`.
No new coefficient-one entropy estimate for the reference space is used.
The sampled viable-space merge tree and the low-density bootstrap remain
open.

The companion revision remains
`af7e5c90650e5ddb06c2befac508df97fd20b2e3`.
No permanent theorem-test files are added.

The two uses of the closeness-composition estimate are deliberately coarse.
In particular, their coefficient $4$ on $\delta$ does not by itself recover
the source's numerical improvement from $.01$ to $.015$ when trimming is
added. A future merge-tree proof must choose a smaller error before trimming
or prove a sharper transfer estimate. No such numerical induction is
claimed here.

For a desired error $0<\tau\le1$, a sufficient allocation is

$$
\delta\le\frac{\tau}{8},\qquad
\varepsilon=\frac{\tau}{24},\qquad
\xi\sqrt{mr^2B}\le\frac{\tau}{16}.
$$

The three contributions to the final bound are then at most
$\tau/2$, $\tau/4$ and $\tau/4$, respectively.

Verification on 28 October 2026 used the frozen production commit
`061e3c57e047fc4c7a03265cba6b7652b9f0de82` and the companion revision
above. The guarded ordinary module build passed 9,644 jobs; the new
module itself took 30 seconds, below the 45-second changed-module limit.
The full library build passed all 15,000 jobs. Both changed Lean source
modules passed the ordinary strict checker with warnings treated as errors
and the same 45-second per-module limit. Actual imports of both new public
declarations have exactly `propext`, `Classical.choice` and `Quot.sound`.
The pinned diagram package, blueprint synchronization, reverse declaration
coverage and compiled blueprint declaration check all passed.

The subsequent completion marks and explanatory error allocation change
no Lean source or declaration list. No full library build is repeated for
these documentation changes. Mathlib uses the pinned prebuilt artifacts.
