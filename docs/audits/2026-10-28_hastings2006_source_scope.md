# Source scope of the Hastings 2006 development

This audit compares the current statements with Hastings, *Solving gapped
Hamiltonians locally*, arXiv:cond-mat/0508554v3, source `proj3new.tex`. It concerns
the mathematical scope of the [local-solution development](https://github.com/LionSR/TNLean/issues/9828).
Numerical experiments are not formalization targets.

| Source claim | Current result | Necessary distinction |
|---|---|---|
| Gaussian filtering, matrix elements, sum, norm and spectral leakage; lines 194–257 | `GaussianFilteredTerm.lean` proves the actual normalized Gaussian identities and leakage bound. | The ground eigenspace may be degenerate. No replacement by a finite commutator polynomial is assumed. |
| Actual truncated dynamics and ground-state approximation; lines 285–391 | `GaussianFilteredMetricTruncation.lean` constructs the source's retained-generator filter. `GaussianGroundStateOverlap.lean` gives an actual ground vector of the approximate Hamiltonian and its overlap bounds. `GaussianZeroRange.lean` proves exact filtering at zero range. | The Gaussian weight and factorization-length corrections remain explicit. Only the original Hamiltonian's spectral gap is assumed. Earlier partial-trace approximants are alternative constructions. |
| Low-energy commutator decay; lines 1548–1601 | `LowEnergyMetricCommutator.lean` proves the graph and physical metric bounds, including the actual truncated Gaussian terms. | Polynomial sphere growth is not required. The observer support cardinality remains explicit, and only the original spectral gap is used. |
| Translation-invariant systems, including growing momentum denominators; lines 1603–1654 | `TranslationFiniteOrbitCommutator.lean` proves the estimate for arbitrary local observables and then for the actual truncated terms. | Cayley–Hamilton on the actual ground-space operator algebra replaces the supercell. The rate is `γ/[4(m+1)]`, where `m=max(1,n₀²)` for ground-space dimension at most `n₀`. Only the Hamiltonian must be invariant; no covariance of the chosen terms or truncation sets is assumed. |
| A basis with a uniformly bounded sum of off-diagonal compressed terms; lines 1678–1708 | Actual bases are constructed in every finite ground-space dimension. Uniform physical sums are proved under polynomial sphere growth. | The unrestricted metric-lattice claim is false. The finite-tree family in `hastings05_tree_basis_counterexample.tex` has fixed local bounds, a two-dimensional ground space and a uniform positive many-body gap, but its off-diagonal sum diverges in every basis. The full family and gap argument are mathematical proofs in the note; the Lean modules certify reusable positive-lifting and hard-core sector estimates, not the whole counterexample. |
| Hierarchical approximation, final energy and state count; lines 609–743 | `exists_periodicPhysicalHierarchy` in `PeriodicPhysicalHierarchy.lean` starts from the original periodic interactions, constructs the actual truncated Gaussian terms, derives their localization, and gives a nearby retained unit vector and the original-gap state count. | Its local ground-vector premise is precisely source (low). The corrected deficiency and one additional closing window are retained; no localization, pair-norm, length, total-error or approximating-gap estimate is supplied as a further premise. Every retained vector belongs to every lower retained space. |
| Quadratic logarithmic physical range; lines 709–720 | The physical radius is `max(ceil R, ceil(A_M/η))`, with `A_M=512(clog₂ M+2)²(1+max(0,log((8J_b/η)/Δ)))` and `J_b=max(J,JC)`. | The cyclic metric and its ball bound are proved. Rounding gives actual pair bound `8ℓJ_b`, independent of system size. The chosen radius determines its own block count and requires neither physical divisibility nor a power-of-two chain length. |
| Higher-dimensional extension; lines 745–756 | The coordinate-slice option is constructed for full finite rectangular boxes in every dimension, with an explicit cubic logarithmic bound. | The stated coordinate support and metric comparison are explicit. The alternative grouping of `2^D` sites is not needed for this option. No unrestricted statement about arbitrary metrics having polynomial volume growth is asserted. |
| Variational lower bound and the filtered instance; lines 856–877 and 1005–1009 | `VariationalLowerBound.lean` treats finite commutator combinations; `GaussianVariationalLowerBound.lean` treats the actual Gaussian integral. | QICLean identifies the Gaussian integral with the convergent even-commutator series, with the documented correction to the printed variance powers. |
| Thermal cluster expansion, inclusion–exclusion, trace error and every-temperature extension; lines 1017–1355 | The actual truncated operator, its product form, cluster estimates, trace-norm error and products of thermal cluster parts are proved. | The even power is positive semidefinite; positive definiteness needs invertibility. The temperature exponent uses the number of factors, bounded by `β/β₀+2`, rather than the smaller printed `β/β₀`. |
| Thermal local index size; lines 1048–1079 and 1259–1320 | The Trotter construction derives the per-site bound `(q²)^(nS)`. Actual retained cluster indices have at most `q²(1+2^M_i)` values, with the corresponding power bounds. | The arbitrary-metric statement counts local interaction centres. Dimensional bounds require a volume hypothesis, proved for the stated integer-coordinate geometries rather than inferred from a metric alone. Empty-support interactions are treated separately. |

No further independent mathematical obligation was found in the audited claims.
This does not turn a corrected statement into the printed statement. The smaller
printed deficiency recurrence, the uncontrolled closing link in the original
final states, strict positivity of the thermal approximation, the printed
temperature factor and the unrestricted uniform basis bound retain their
respective correction records. The source's generalized matrix product
representation is the tree of nested retained spaces; it supplies no bound on
intermediate retained dimensions or on a conventional matrix product bond
dimension.

The new periodic coarsening, approximation and physical assembly modules passed
their ordinary package builds. The public statements are covered by foundation
checks requiring declaration existence and allowing only `propext`,
`Classical.choice` and `Quot.sound`. Aggregate builds, declaration synchronization
and source-level hypotheses are verified separately for the complete programme.
