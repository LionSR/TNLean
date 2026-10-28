# Finite Gaussian quadrature in the unrestricted error-reduction argument

The finite Gaussian quadrature step is implemented independently of the bond-trimming
construction. Its source is Huang, [arXiv:1406.6355v6](https://arxiv.org/pdf/1406.6355v6),
Section 5.4, Lemma 19 and equation (22). The contribution does not construct a matrix
product operator approximation to the full time evolution.

## Statement and construction

For a cutoff $T\ge0$ and mesh $\delta>0$, the construction uses

$$
 N=\lceil2T/\delta\rceil+1,\quad
 I_j=[-T,T]\cap[-T+j\delta,-T+(j+1)\delta),\quad
 t_j=\min\{-T+j\delta,T\}.
$$

The cells are disjoint and cover the closed interval, including its right endpoint.
The weights $w_j=\gamma_h(I_j)$ are exact interval masses of the centered Gaussian of
variance $h\ge0$. They are nonnegative and their sum is the retained Gaussian mass,
at most one. Every node lies in the cutoff interval, even when its cell has zero measure.
The endpoint construction also covers the zero-variance Gaussian without discarding an atom.

For an integrable Banach-space-valued function with Lipschitz constant $M\ge0$ on the
cutoff interval, the truncated quadrature error is at most $M\delta$. If its norm is
everywhere at most one, the full-integral error is bounded by

$$
 2\exp\bigl(-T^2/(2h)\bigr)+M\delta.
$$

The Lean statement uses the total real division operation; at $h=0$ the displayed
exponential contribution is $2$. This is a valid, coarse bound for that degenerate case.
For the positive variance used in the physical filter it is the usual Gaussian tail.
Taking $\delta=\varepsilon/(M+1)$ gives mesh error at most $\varepsilon$ and

$$
 N\le 2T(M+1)/\varepsilon+2.
$$

All nodes and weights are defined before the integrand. Their construction replaces the
rectangular weights displayed in Huang with exact interval masses, preserving the
operator approximation and polynomial sample-count conclusions of this step. It does not
assert an algorithm for evaluating the Gaussian masses to prescribed numerical precision.

## Actual propagator specialization

For a Hermitian matrix $H$, the group law and the existing Duhamel estimate prove
$\|e^{itH}-e^{isH}\|\le\|H\||t-s|$. The quadrature theorem is then applied to the actual
unitary path, with no assumed Lipschitz estimate or approximate output operator. Its
integral is the existing Gaussian filter with the second generator zero and insertion
equal to the identity.

The resulting sample count is at most $2T(\|H\|+1)/\varepsilon+2$. An energy estimate
is incorporated by applying the theorem to $H-E'I$. For the physical range-one chain,
the existing theorem `ChainHamiltonian.norm_operator_le_of_range_one` bounds the
unshifted norm by $2LJ$. A bounded spectral energy grid therefore retains polynomial
sample count. The global matrix product approximation to these propagators remains a
separate missing theorem; no hypothesis asserting that construction appears here.

## Library ownership

The two mathematical modules are temporarily under `TNLean/MPS/AreaLaw/Huang/` to keep
the contribution separate from the completed viable-set work. Neither module imports
any TNLean tensor-network result other than the companion quadrature module itself.
The generic Gaussian integration results and the Hermitian specialization belong in
QICLean, naturally under `Analysis/GaussianFilter/Quadrature.lean` and a companion
unitary-quadrature module. Upstreaming should move these declarations, then leave only
the physical chain application and blueprint treatment in TNLean. No dependency pin
or companion-library source has been changed in this contribution.

## Verification

Both mathematical modules passed actual separate-module compilation with the strict
changed-module flags and warnings treated as errors. Source hashes were unchanged across
each compilation:

| Module | SHA-256 | Compilation time |
|---|---|---|
| `Huang/GaussianQuadrature.lean` | `4f726ed748fc5f968322abb79be0eb344d1d08728b8fbb5d9a154af978a1664c` | 14.53 seconds |
| `Huang/UnitaryQuadrature.lean` | `99b2aa5d98a3887575fd3a67a5fa53e0d99f755eab35d4d312f5256bf0afe7ca` | 13.10 seconds |

The imported fixture `scripts/huang_gaussian_quadrature_regression.lean` passed separately
in 11.31 seconds. Every one of its 15 public declarations depends exactly on
`propext`, `Classical.choice` and `Quot.sound`.
All temporary outputs are confined to a private copy of the warmed artifact namespace.
The authoritative repository and dependency caches are unchanged.

Import generation, the reader-facing prose check and the whitespace check pass. The
new blueprint chapter passes the pinned LaTeX formatter and configured ChkTeX checks.
The tactic-pattern scan of the new directory reports no repeated pattern at its default
threshold. The repeated simplification of the zero-generator propagator is factored
into one private lemma.

The original canonical worktree seed has completed at the exact warmed main revision.
The contribution has also been integrated into the independently seeded worktree. Its
ordinary locked module and full-library builds, strict imported foundation fixture and
compiled blueprint declaration check pass. Completion marks have been added to the new
blueprint chapter. The exact integrated scope is recorded in
[the verification audit](2026-10-28_lvv_integrated_verification.md).
