# The physical AKLV Chebyshev filter

`AKLV/ChebyshevFilter.lean` combines the constructed spectral polynomial of AKLV,
arXiv:1301.1162v1, Lemma 4.1 with the sharp physical rank theorem from Lemma 4.2.
It concerns the actual sum \(G=H_L+\sum_jH_j+H_R\) of the originally supported terms.
No approximate ground-space projector, tensor factorization, coefficient family or
operator Schmidt rank bound is supplied as a hypothesis.

The spectral inputs are precisely the bounded-Hamiltonian data of Section 4: \(G\)
is Hermitian, \(\Gamma\) is a unit eigenvector of energy \(E_0\), and
\(G-E_0I\ge\gamma(I-|\Gamma\rangle\langle\Gamma|)\) with \(\gamma>0\).
Every spectral value is at most \(u\), and \(E_0+\gamma\le u\). The gap may be a
positive lower bound rather than the attained first excited energy.

The theorem constructs a real polynomial \(p\) of exact degree \(\ell\), normalized
by \(p(E_0)=1\). For the same actual operator \(K=p(G)\), it proves

\[
K\Gamma=\Gamma,\qquad
\|K-|\Gamma\rangle\langle\Gamma|\|
\le A_\ell=2e^{-2\ell\sqrt{\gamma/(u-E_0)}},
\]

and

\[
\operatorname{OSR}_{a+\lfloor s/2\rfloor}(K)
\le\bigl(q(\ell+1)\bigr)^{16(\lfloor\ell/s\rfloor+\lfloor\sqrt\ell\rfloor+1)}.
\]

For every unit \(\psi\perp\Gamma\), the output also gives
\(K\psi\perp\Gamma\) and \(\|K\psi\|^2\le A_\ell^2\). The shrinking parameter
is the square of the norm bound, as in the source definition. Zero degree and local
dimension one are included. The real-to-complex coefficient map preserves polynomial
evaluation and does not increase degree; this identifies the operator in the spectral
and spatial estimates exactly.

The scalar and ground-projection argument belongs to the separate QICLean module
`Analysis/ChebyshevGroundFilter.lean`. It derives the actual spectral alternative
from the global gap, constructs the polynomial using the existing isolated-energy
filter, and identifies its canonical projection with the actual rank-one ground
projection. The physical module adds the supported-chain rank estimate. The rank
proof retains the corrected commuting-gap count in
[the QICLean word-count note](https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf).

## Hard truncation and the remaining source step

The spectral ceiling and gap above are source Section 4 inputs; this contribution
does not derive them by replacing an arbitrary original Hamiltonian with a truncated
one. `Matrix.energyTruncation` and its existing QICLean order/Hermiticity bounds give
basic clipping facts. Current ALVV integration additionally contains actual regional
truncation residuals and five-region constructions:

- `RegionalTruncationResidual.norm_consecutive_regional_truncation_low_le` applies to
  actual consecutive regional sums with partially clipped bulks and bounded crossing terms.
- `FiveRegionTruncationResidual.exists_five_region_physical_truncation_residual` constructs
  the five-region truncation and bounds its actual low-energy residual.
- `PhysicalLowEnergyCloseness.exists_five_region_physical_low_energy_closeness` proves
  bidirectional shifted-cutoff closeness, and the scaled-low-cluster theorem closes
  the corresponding degenerate cluster.

These are useful inputs, but the ALVV construction clips three bulks. AKLV Theorem 6.1
uses its specified two outer truncated blocks. The existing five-region theorem is
not substituted for that construction. A source-faithful AKLV two-block robustness
proof, the choice of parameters giving \(D_\ell A_\ell^2\le1/2\), and the entropy
argument remain separate tasks.

## Verification

The actual production modules pass strict private checks with `autoImplicit=false`,
`relaxedAutoImplicit=false`, `maxSynthPendingDepth=3`, Mathlib standard linters and
warnings as errors:

| Module | Time | SHA-256 |
| --- | --- | --- |
| QICLean `Analysis/ChebyshevGroundFilter` | 3.85 s | `5e617faa0a744f6cd4cf806a17c4f8eedee8a225c1e9129e444b4e274667bfa8` |
| TNLean `AKLV/ChebyshevFilter` | 12.49 s | `fd4952308f58f7cb2dd72c244c74970187797fd13bbfb680b33adb2e32f05fa6` |

An imported manual inspection of both public declarations passed in 2.81 seconds.
Only `propext`, `Classical.choice`, and `Quot.sound` occur. No permanent fixture is added.

The checks use the existing seeded context and private temporary objects. Ordinary
verification of these two new modules and compiled blueprint integration remain
pending the combined companion contribution. No dependency pin, hot-main cache or
other worktree was changed; no duplicate full build or Mathlib source build was run.
The new chapter should follow `ch35_aklv_polynomial_rank.tex`.
