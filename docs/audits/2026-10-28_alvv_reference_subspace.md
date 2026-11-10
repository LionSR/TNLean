# A simultaneous reference subspace for collective trimming

The principal declaration is
`TNLean.MPS.AreaLaw.exists_physical_dg_isOpenMPS_reference_subspace`.
It supplies the reference-space step used in ALVV,
[arXiv:1602.08828v2](https://arxiv.org/abs/1602.08828v2), proof of
`t:alg1`, lines 1801–1805 of `local_alg_arxiv_v2.tex`. The official TeX
source has SHA256
`19d37facb8bf8da6ea5555cd7185c054d251ad4a06c2f44fcb92593235ad6b92`.

The input consists of the actual supported nearest-neighbour terms
$0\le h_i\le I$, the first distinct spectral value $\mu$, a second
spectral value, and a positive gap lower bound $\gamma$ above the full
original ground space $G$. An orthonormal basis, approximation vectors,
rank bounds and closeness estimates are all constructed internally.
The second spectral value is part of source Assumption (DG).

For $0<\varepsilon\le1$ and $r=\dim G$, apply the normalized global
approximation theorem at the common accuracy

$$
\delta_{\mathrm{basis}}=\frac{\varepsilon}{2r}.
$$

Every actual orthonormal basis vector has a unit matrix product approximant
of bond at most $rB$ and squared norm error at most $\varepsilon/(4r)$.
The proof uses the explicit norm-error conclusion, so the vectors have
the phases required for a linear basis map. The same integer $B$ precedes
every basis-vector choice.

The map sending the original basis to these approximants differs from
inclusion by squared operator norm at most $\varepsilon/4$. It is
injective, has image $U$ of dimension $r$, and the image and original space
are mutually $\varepsilon$-close. The span is fixed before its arbitrary
vector is chosen. The existing finite-span MPS theorem gives an exact
bond bound $r(rB)=r^2B$ for every vector in $U$.

The explicit logarithmic bound retains the global theorem's universal
constant and uses

$$
g=\min(\gamma,1),\quad
u=1+\log q+\log(1/g),\quad
b=16+\log(1/g)+\log(32r(N+1)/\varepsilon),
$$

$$
\log B\le K\left(\frac{u^3}{g}+g^{-1/4}b^{3/4}u\right)(1+\log b).
$$

The normalized-gap comparison is documented in the shared parameter note.
The reference is used to control collective trimming. It does not replace
the viable spaces built from the Hamiltonian by sampling and filtering.
The sharp entropy coefficient for the original $G$ is a separate result:
the crude whole-reference rank estimate gives only
$2\log r+\log B$, and no coefficient-one entropy theorem for $U$ is
claimed. The merge-tree induction and the low-density bootstrap remain open.

The new proof gave a third use of enlarging an MPS bond bound through cut
ranks. The ordinary monotonicity theorem `IsOpenMPS.mono` replaces that
argument in the uniform polynomial family, the viable-set span and this
reference span. Their mathematical bounds are unchanged.

The selected companion revision remains
`af7e5c90650e5ddb06c2befac508df97fd20b2e3`. The new modules and all
monotonicity consumers pass strict separate-module compilation against
prebuilt dependencies with private outputs. Local inspection of all three
actual imported new declarations gives exactly `propext`, `Classical.choice`
and `Quot.sound`. No permanent theorem-test files are added.

Verification on 28 October 2026 used the frozen production commit
`f5a4fa2e74b5edd38a48153aadd9535bbcd006fa` and the companion revision
above. Both the targeted ordinary build (9,638 jobs) and the full library
build (14,999 jobs) passed through the shared cache-guarded wrapper.
The ordinary strict checker passed all six changed Lean source modules,
with warnings treated as errors and a 45-second limit per module.
An actual-import audit of the ordinary compiled declarations confirmed
exactly the three standard logical axioms listed above. The pinned diagram
package, blueprint declaration synchronization, reverse declaration
coverage and compiled blueprint declaration check all passed.
The completion marks added after these checks do not change Lean source
or the declaration list.
