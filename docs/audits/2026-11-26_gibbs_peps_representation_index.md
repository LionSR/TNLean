# Gibbs operators and PEPS: an index of the representation results

This index records the results that bear on representing thermal operators and ground vectors
by tensor networks, with their hypotheses, normalization, error norm, bond or index bounds,
source anchors and verification status. It answers the interface question of the audit: whether
a complete chain from a thermal operator to a native network with a trace-norm error and a bond
bound exists. It is not a claim that arbitrary Gibbs states have an efficient PEPS
representation.

Every statement below was read in the source files at TNLean `12ebe257d9` (branch
`batch/one-definition`) and QICLean `e1b57080ad`. The QICLean files cited are identical to
those at the QICLean pin `2d0f7b9f40` of that TNLean commit. "Proved" means that the file and
the directories listed contain no `sorry`, `admit`, `native_decide` or `axiom`; no build was run
for this index. Paper-gap notes are cited by path in the repository that holds them; the
QICLean notes are published at `https://sirui-lu.com/QICLean/paper-gaps/<slug>.pdf`.

## Module locations

The modules named in the audit issue have moved. `TNLean/Lattice` was deleted and its
cluster-expansion material is in QICLean.

| Old path | Current module | Repository |
| --- | --- | --- |
| `Lattice/ProductForm` | `QICLean.ManyBody.Sites.ProductForm` | QICLean |
| `Lattice/ClusterExpansion/TruncatedProductForm`, `TruncatedAllTemperatures` | `QICLean.ManyBody.Hamiltonian.ClusterExpansion.ProductForm` | QICLean |
| `Lattice/ClusterExpansion/TruncatedPositivity`, `TemperatureError`, `AllTemperatures`, `TraceNorm` | `QICLean.Analysis.ClusterExpansion.Temperature` | QICLean |
| `Lattice/ClusterExpansion/LocalIndexCount` | `QICLean.ManyBody.Hamiltonian.ClusterExpansion.IndexCount` | QICLean |
| `MPS/AreaLaw/ClusterTruncationMPO` | `TNLean.MPS.AreaLaw.LowEnergyAlgorithm.MPO.OperatorMPOFromCutRank` | TNLean |
| `MPS/AreaLaw/PhysicalSoftTruncationMPOApproximation` | section `PhysicalSoftTruncationMPOApproximation` of `TNLean.MPS.AreaLaw.LowEnergyAlgorithm.MPO.SoftTruncationMPOAccuracy` | TNLean |
| `PEPS/Approximation/ExactTreeRepresentation`, `ExactSquareRepresentation` | `TNLean.PEPS.Approximation.Exact.ExactTreeRepresentation`, `...Exact.ExactSquareRepresentation` | TNLean |
| `PEPS/Approximation/Basic` | `TNLean.PEPS.Tensor.SquareLattice.Basic` | TNLean |
| `PEPS/Approximation/PolynomialPEPSTheorem` | `TNLean.PEPS.Approximation.PolynomialPEPSTheorem` | TNLean |
| `MPS/MPDO/TopologicalPhysicalGibbs`, `CPSVTopologicalPhysicalGibbs` | `TNLean.MPS.MPDO.TopologicalForm.TopologicalPhysicalGibbs` (both parts) | TNLean |
| `PEPS/RegularBoundaryGibbsSupport` | `TNLean.PEPS.Injectivity.Boundary.RegularBoundaryGibbsSupport` | TNLean |

## 1. Hastings' product form at every temperature

Source: M. B. Hastings, *Solving gapped Hamiltonians locally*, arXiv:cond-mat/0508554v3,
`proj3new.tex`, Section IV. All declarations are in QICLean, in the namespaces `ManyBody`,
`ManyBody.ClusterExpansion` and `ClusterExpansion`; all are proved.

| Declaration | Module | Source lines |
| --- | --- | --- |
| `ManyBody.ProductForm`, `ManyBody.HasProductForm` | `ManyBody.Sites.ProductForm` | eq. `mpf`, 1024–1039 |
| `ManyBody.ClusterExpansion.hasProductForm_truncatedExp` | `ManyBody.Hamiltonian.ClusterExpansion.ProductForm` | 1256–1279 |
| `ManyBody.HasProductForm.pow_of_even`, `ManyBody.ClusterExpansion.hasProductForm_truncatedExp_pow_of_even`, `..._of_dist_le`, `..._pow_of_even_of_dist_le` | same | eq. `mplt`, 1303–1317 |
| `ClusterExpansion.posSemidef_truncatedExp_pow`, `ClusterExpansion.evenTemperatureFactors_spec` | `Analysis.ClusterExpansion.Temperature` | 1303–1320 |
| `ClusterExpansion.norm_trace_mul_exp_sub_truncatedExp_pow_le` | same | 1334–1347 |
| `ClusterExpansion.norm_trace_mul_exp_sub_truncatedExp_pow_le_percolation`, `..._percolation_add_two` | same | 1307–1312, 1342–1347 |
| `ClusterExpansion.re_trace_sqrt_sub_le_of_forall_norm_trace_mul_sub_le` | same | 1281–1301 |
| `ClusterExpansion.norm_trace_mul_exp_sub_truncatedExp_le_isLargeDiam_dist`, `ClusterExpansion.exists_percolation_temperature` | `Analysis.ClusterExpansion.Percolation` | 1242–1254 |
| `ManyBody.ClusterExpansion.exists_productForm_truncatedExp_card_index`, `..._pow_card_index`, `..._card_index_of_polynomial_growth`, `..._pow_card_index_of_polynomial_growth` | `ManyBody.Hamiltonian.ClusterExpansion.IndexCount` | 1256–1279, 1311–1320 |

**The object.** `ProductForm X near ρ` is an expansion
`ρ = ∑_α (∏_i F_i(α)) • ⊗_j ρ_j(α_j)` in which `F_i` depends only on the indices `α_j` with
`near i j`. It is a sum over local index assignments with local coefficient functions, not a
contraction of a network on the edges of a graph. The truncated operator is
`truncatedExp (overlapGraph T) (IsLargeSupport near T) Φ.term β` for `Φ : Interaction X T`,
the sum over term sets with no large cluster.

**Hypotheses.**

- `hasProductForm_truncatedExp`: a nonempty finite site set, finite basis types at every site,
  a reflexive relation `near`, any real `β`. No Hermiticity, connectivity or nonempty supports.
- `..._pow_of_even`: in addition every term Hermitian and `m` even. The conclusion is the
  product form of `ρ(β, l)^m` and positive **semidefiniteness**. The source states positive
  definiteness. **Local fix (positivity)**, QICLean `docs/paper-gaps/hastings05_mplt_positivity.tex`.
- `norm_trace_mul_exp_sub_truncatedExp_pow_le`: `H = ∑_k h_k` Hermitian with Hermitian terms,
  `‖h_k‖ ≤ J`, `β ≥ 0`, any `n > 0`, and the boundary inequality `n_C + n_{∂C} ≤ S n_C` for
  every large connected set. The percolation forms add: every large connected set has at least
  `l + 1` terms, at most `N x^k` large connected sets of `k` terms, and
  `0 < x y ≤ 1/2` with `y = (e^{Jβ/n} − 1) e^{SJβ/n}`. The `_add_two` form takes `n` equal to
  `evenTemperatureFactors β β₀`, the least even integer with `β/n ≤ β₀`, for `β, β₀ > 0`.
- The exponent uses the integer number `n` of factors, bounded by `β/β₀ + 2`, in place of the
  source's `β/β₀`. **Local fix**, QICLean `docs/paper-gaps/hastings05_temperature_factor_count.tex`.
- The cluster-size threshold derived from a diameter cutoff is `⌊l_proj/(2R)⌋` and the distance
  form keeps a factor `(xy)^{-1}`. **Local fix**, QICLean
  `docs/paper-gaps/hastings05_percolation_cluster_size.tex`.
- Index counts: a pseudometric on the sites, nonempty basis types, interaction centres `c k`
  with every site of `T k` within `R` of `c k`, and `0 ≤ l`. The polynomial forms add the volume
  hypothesis `#{k : dist i (c k) ≤ l + R} ≤ C (⌈l + R⌉ + 1)^D` explicitly; it is not derived from
  the metric. **Local fix (volume growth)**, QICLean
  `docs/paper-gaps/hastings05_planar_domain_scope.tex`.

**Normalization and error norm.** The thermal operator is the unnormalized `e^{-βH}`. The error
is a trace pairing relative to `Z = Tr e^{-βH}`:

`‖Tr (O (e^{-βH} − ρ(β/n, l)^n))‖ ≤ ‖O‖ (exp(n ∑_C y^{n_C}) − 1) Tr e^{-βH}`,

with `‖O‖` the operator norm (`Matrix.Norms.L2Operator`). The approximant `ρ(β/n, l)^n` is not
normalized by its own trace in any of these statements.
`re_trace_sqrt_sub_le_of_forall_norm_trace_mul_sub_le` turns a bound
`‖Tr (O ρ) − Tr (O σ)‖ ≤ ε ‖O‖ Tr ρ` for all `O` (with `ε ≥ 0`, `0 ≤ Re Tr ρ`) into the trace
norm bound `Re Tr √((ρ − σ)ᴴ (ρ − σ)) ≤ ε Re Tr ρ`, again unnormalized and relative to `Tr ρ`.
No declaration states this trace-norm consequence for the truncated power; the pairing theorem
and the trace-norm lemma are not composed anywhere in either repository.

**Index bounds.** For the actual truncated operator, `card (P.Index i) ≤
(2^{M_i} + 1) |X i|²` with `M_i = #{k : dist i (c k) ≤ l + R}`; for the power `ρ^m`, the `m`-th
power of that bound. Under the volume hypothesis, `|X i|² (1 + 2^{C (⌈l+R⌉+1)^D})` and its
`m`-th power. These are ranges of the local index of the product form, not bond dimensions of a
network.

Adjacent, same source: `ManyBody.Interaction.hasProductForm_lie` and
`exists_productForm_lie_card_index_eq` (`QICLean.ManyBody.Dynamics.ProductFormula`, lines
1053–1077) give the exact product form of a Trotter product, with local index
`|X j|^{2 n c_j}`, `c_j` the number of terms containing `j`.

## 2. The one-dimensional cluster MPO and the soft-truncation MPO

Source: Arad, Landau, Vazirani, Vidick (ALVV), arXiv:1602.08828v2. Module
`TNLean.MPS.AreaLaw.LowEnergyAlgorithm.MPO.OperatorMPOFromCutRank` and the last section of
`TNLean.MPS.AreaLaw.LowEnergyAlgorithm.MPO.SoftTruncationMPOAccuracy`, namespace
`TNLean.MPS.AreaLaw`. Both proved. Source obligations remain with #9847.

| Declaration | Source anchor |
| --- | --- |
| `TNLean.MPS.AreaLaw.exists_mpo_cluster_truncation` | `thm:cluster`, lines 1298–1303, 2014–2115 |
| `TNLean.MPS.AreaLaw.exists_mpo_cluster_approximation` | `thm:cluster-approx`, `thm:cluster`, lines 1270–1303 |
| `TNLean.MPS.AreaLaw.exists_interval_physical_soft_closeness_and_mpo` | `lem:exp-approx`, `lem:exp-approx-eff`, lines 1195–1268 |
| QICLean `ClusterExpansion.norm_exp_sub_truncatedExp_pathGraph_le` | `thm:cluster-approx`, lines 1270–1291, 1935–1968 |
| QICLean `ManyBody.ClusterExpansion.operatorSchmidtRank_truncatedExp_nearestNeighbor_le` | `thm:cluster`, lines 1298–1303, 1971–2013 |

**The object.** `MPOTensor.traceChainOperator A 1` for site-dependent tensors
`A : Fin (N+1) → MPOTensor q D`, the operator with entries `Tr (∏_v A_v(σ_v, τ_v))`. This is a
native one-dimensional operator network.

**Hypotheses and conclusions.**

- `exists_mpo_cluster_truncation`: `1 ≤ q`, `0 < r`, terms `h i` supported on `{i, i+1}`, any
  real `β`. The label truncation `truncatedExp (pathGraph N) (r ≤ |C|) h β` equals
  `traceChainOperator A 1` exactly, with bond `r² q^r`.
- `exists_mpo_cluster_approximation`: in addition `h i` Hermitian, `‖h i‖ ≤ 1`, a supplied
  lower energy `λ • 1 ≤ ∑ h i`, `0 ≤ β` and the high-temperature condition
  `2 (e^β − 1) ≤ 1`. Conclusion:
  `e^{βλ} ‖e^{-β ∑ h_i} − traceChainOperator A 1‖ ≤ exp(N² (2(e^β − 1))^r) − 1`.
- `exists_interval_physical_soft_closeness_and_mpo`: for `η, w, δ > 0` an order `m` given by an
  explicit ceiling, and for every chain, `Φ : BondInteraction (N+1) q` with `0 ≤ Φ.term i ≤ 1`
  and cut points `p ≤ v ≤ N + 1`, spectral-window closeness of the soft-truncated Hamiltonian
  `Hsoft` (scale `3m`) and, for every `ξ > 0`, tensors `T` with
  `‖Hsoft − traceChainOperator T 1‖ ≤ ξ` and bond
  `(1 + N q²) + (ℓ² q^ℓ)(m + 1)`, `ℓ` an explicit logarithmic ceiling in `N` and `ξ`.

**Normalization and error norm.** Operator norm (`Matrix.Norms.L2Operator`). In the cluster
approximation the error is multiplied by `e^{βλ}`, an energy normalization by the supplied lower
energy; it is neither a trace normalization nor a trace-norm bound. The soft-truncation result
approximates the soft-truncated Hamiltonian, not a thermal operator.

**Markers.**

- **Local fix (cutoff and normalization):** connected interaction-label components replace
  physical support, and a supplied lower energy normalizes the error; the printed
  physical-support estimate is false and is not asserted. TNLean
  `docs/paper-gaps/alvv16_cluster_approximation.tex`.
- **Local fix (parameters and corrected estimates)** and **Scope restriction (scale three times
  the order):** the source allows any scale with `t′ < (ln 2/2) t`; the physical result takes
  `t = 3m`. TNLean `docs/paper-gaps/alvv16_soft_truncation_energy_estimate.tex` and
  `docs/paper-gaps/alvv16_cluster_approximation.tex`.

## 3. Exact native PEPS contraction

Source: *Polynomial PEPS approximation of gapped square-grid ground states*, September 24, 2026,
`07-assembly.tex`, lines 203–214, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Namespace
`TNLean.PEPS.ExactTreeRepresentation`. All proved.

| Declaration | Module |
| --- | --- |
| `exists_exact_tensor`, `exists_exact_tree_tensor` | `PEPS.Approximation.Exact.ExactTreeRepresentation` |
| `exists_exact_square_tensor`, `exists_exact_square_tree_tensor`, `exists_exact_unit_square_tensor` | `PEPS.Approximation.Exact.ExactSquareRepresentation` |
| `exists_exact_square_tensor_bounded`, `..._polynomial`, `..._outer_power` | same |

**Hypotheses and conclusions.** `exists_exact_tensor`: a finite linearly ordered vertex type, a
connected graph `G`, `0 < q`, and an arbitrary coefficient function `ψ`. There is a native
`Tensor G q` with positive bonds, every bond at most `q^{|V|}`, and `stateCoeff A = ψ`. The
tree form puts `q^{|V|}` on the edges of a spanning tree and `1` elsewhere. On the `L × L`
square (`0 < L`) the bound is `q^{L²}`; `_bounded` gives `q^{L₀²}` for all `L ≤ L₀`, and the
`_polynomial` and `_outer_power` forms enlarge a prefactor to cover finitely many sizes.

**Normalization and error norm.** Exact equality; for a unit `ψ` the normalized contraction
equals `ψ` with phase one (`exists_exact_unit_square_tensor`). The bond bound is exponential in
the number of sites. This is an exact representation, used for the finitely many small sizes
of the polynomial theorem, not an efficient approximation. The statements concern vectors;
no operator version is stated.

## 4. Polynomial PEPS approximation of gapped ground vectors

Source: the same manuscript, Theorem 1.1, `00-introduction.tex`, lines 36–57, with
`eq:model`, `eq:global-gap`, `eq:target-error`, and the area-law manuscript of the same date,
Theorem 1.1. Namespace `TNLean.PEPS.Approximation`.

| Declaration | Module |
| --- | --- |
| `IsSquareGroundState`, `pepsVector`, `HasPEPSApproximation`, `PolynomialPEPSApproximation` (definitions) | `PEPS.Tensor.SquareLattice.Basic` |
| `polynomialPEPSApproximation : PolynomialPEPSApproximation` | `PEPS.Approximation.PolynomialPEPSTheorem` |
| `polynomialPEPSApproximation_explicit` (constants `pepsBondPrefactor q J Δ`, `pepsBondExponent q J Δ`) | `PEPS.Approximation.PolynomialPEPSClosedConstant` |

**Statement.** For `q ≥ 2` and `J, Δ > 0` there are `C, c > 0` such that for every `L ≥ 2`,
every `h : SquareInteraction L q` (one term per site and per nearest-neighbour edge of the open
square) with Hermitian total sum and `‖h.term i‖ ≤ J`, every `E₀` and every unit `Ω` with
`IsGapped h.hamiltonian E₀ Δ` and `groundSpace h.hamiltonian E₀ = span {Ω}`, there is a native
`Tensor (squareLatticeGraph L L) q` with positive bonds `≤ C L^c`, nonzero contraction, and a
phase `θ` with `‖ pepsVector A / ‖pepsVector A‖ − e^{iθ} Ω ‖ ≤ L⁻¹`. Individual terms need not
be Hermitian.

**Normalization and error norm.** Euclidean norm of the normalized vector, up to a global
phase. The constants are uniform in `L`, the Hamiltonian and `Ω`. The statement concerns a
pure unique gapped ground vector; it is not a finite-temperature or mixed-state theorem.

**Status.** The final theorem takes no hypotheses beyond the proposition, its docstring carries
no marker, and the blueprint entry `thm:openai_polynomial_peps` is `\leanok`. Intermediate
modules of `PEPS/Approximation` and `PEPS/AreaLaw` carry scope-restriction and local-fix
markers on auxiliary declarations (for example `polypeps_*` notes in TNLean
`docs/paper-gaps/`); this index does not audit how each is discharged. A second predicate
`TNLean.PEPS.Approximation.Pinned.HasPEPSApproximation`
(`PEPS.Approximation.GroundState.SourceApproximation`) restates the source's phase convention
for transfer lemmas; it is noted here as a candidate for the one-definition review, not changed.

## 5. Gibbs forms of RFP MPDOs and of the regular PEPS boundary

### 5a. Physical commuting Gibbs decomposition of a renormalization fixed point

Source: Cirac, Pérez-García, Schuch, Verstraete (CPSV16), arXiv:1606.00608, Theorems 4.14 and
4.15, lines 972–1016, Definition 4.8, lines 831–847, Appendix C.4, lines 1929–2046. Module
`TNLean.MPS.MPDO.TopologicalForm.TopologicalPhysicalGibbs`. All proved.

| Declaration | Hypotheses |
| --- | --- |
| `MPOTensor.BNTFusionTensorClause.hasPhysicalTopologicalGibbsDecomposition` | a fusion clause `H` of `M`, `IsMPDO M`, length independence of the coefficient family `ofChi H.chi` |
| `MPOTensor.physicalTopologicalGibbsDecomposition_of_isRFPViaTS` | `IsHorizontalCF M`, `IsMPDO M`, `IsRFPViaTS M`, length independence for the selected clause |
| `MPOTensor.physicalTopologicalGibbsDecomposition_of_isRFPViaTS_of_cpsvCanonicalForm` | `IsCPSVCanonicalForm M.toMPSTensor`, `IsMPDO M`, `IsRFPViaTS M`, length independence for the selected clause |

**Conclusion** (`HasPhysicalTopologicalGibbsDecomposition`). A Hermitian two-site term `ĥ`
whose ring translates commute, nonnegative weights `λ_i`, and for every `N` orthogonal
projections `P̂_i^{(N+2)}`, pairwise orthogonal and commuting with `exp(−Ĥ_{N+2})`, with

`mpo M (N + 2) = ∑_{i : Fin d} λ_i • (P̂_i^{(N+2)} * exp(−Ĥ_{N+2}))`.

This is an exact identity for an already given MPDO, on chains of length at least two. It is
not an approximation of an arbitrary thermal operator and carries no error term or bond bound
beyond the given tensor. Normalization: the MPDO `mpo M (N+2)` as given; no trace
normalization.

**Markers.**

- **Scope restriction (chains of length at least two):** Definition 4.8 fixes no length-one
  convention. TNLean `docs/paper-gaps/cpsv16_topological_gibbs_length_one.tex`.
- **Local fix (physical complement):** zero energy on the orthogonal physical complement.
  TNLean `docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`.
- **Local fix (Figure 11):** fixed-pair support and fusion coisometry, on the CPSV form. TNLean
  `docs/paper-gaps/cpsv16_figure11_per_pair_support.tex`,
  `docs/paper-gaps/cpsv16_figure11_fusion_coisometry.tex`.

### 5b. Regular boundary density: full-space obstruction and invariant-support Gibbs form

Source: Schuch, Cirac, Pérez-García (SCP10), arXiv:1001.3807, Theorem 6.9, lines 2027–2076, and
Definition 5.1, lines 1278–1296; compared with arXiv:1903.09439, Conjecture
`gap2Dboundary1dlocal`, lines 980–1024. Module
`TNLean.PEPS.Injectivity.Boundary.RegularBoundaryGibbsSupport`, namespace `TNLean.PEPS`. All
proved.

| Declaration | Hypotheses | Conclusion |
| --- | --- | --- |
| `regularBoundaryDensity_ne_exp` | finite group with `1 < card G`, any `H` | the density is not `exp H` on the full boundary space |
| `IsGInjective.regularBoundaryGram_ne_exp` | a G-injective open map for the regular representation, `1 < card G` | its virtual Gram operator is not `exp H` |
| `regularBoundarySupportedDensity_eq_exp` | finite group | on the invariant support the density is `exp(−H_c)` for the constant `H_c = log(|G|^n) • 1` |

These are exact support statements. They do not establish locality of a boundary Hamiltonian
or a bulk gap, and they do not resolve the conjecture of arXiv:1903.09439.

## 6. Adjacent exact results

- `TNLean.PEPS.expectation_classicalPEPS`, `stateCoeff_classicalPEPS`
  (`TNLean.PEPS.Examples.Classical`; arXiv:2011.12127, Appendix A, lines 2483–2494): for a
  classical nearest-neighbour model on a torus of width and height at least three, a native PEPS
  with bond indices in `Fin q` has coefficients `e^{−βH(σ)/2}`, and its diagonal expectation
  values equal the normalized classical Gibbs averages. Diagonal observables only; exact.
  **Scope restriction (torus size)**, TNLean `docs/paper-gaps/rmp_peps_examples_small_torus.tex`.
- `TNLean/MPS/MPDO/Purification`: one-dimensional purification results for renormalization
  fixed points; no thermal approximation statement.

## 7. Comparison of conventions

| Chain | Operator or vector | Normalization | Error | Bond or index |
| --- | --- | --- | --- | --- |
| 1 | `e^{-βH}` on any finite site set | unnormalized, relative to `Tr e^{-βH}` | trace pairing with operator-norm observable; trace-norm lemma separate | local index of a product form, `((2^{M_i}+1)|X_i|²)^n` |
| 2 | `e^{-βH}` on a chain, small `β`; `Hsoft` | multiplied by `e^{βλ}`; none for `Hsoft` | operator norm | MPO bond `r² q^r`; `(1+Nq²)+(ℓ²q^ℓ)(m+1)` |
| 3 | any vector on a connected graph | exact | zero | `q^{|V|}` |
| 4 | unique gapped ground vector, square | unit vector, normalized contraction | Euclidean, up to phase, `≤ L⁻¹` | `C L^c` |
| 5a | a given RFP MPDO, length `≥ 2` | as given | exact identity | that of the given tensor |
| 5b | regular boundary density | as given | exact; obstruction on the full space | none |

## 8. The interface question

**Question.** Is there a complete chain: general thermal operator approximation, then
normalization, then a native PEPO or PEPS purification, then a trace-norm error, then a bond
bound?

**Disposition: no such chain exists in TNLean or QICLean at the commits above.** Each link,
with the exact declarations:

1. *Thermal approximation.* Present in general dimension as an operator identity:
   `norm_trace_mul_exp_sub_truncatedExp_pow_le_percolation(_add_two)` approximates `e^{-βH}` by
   `ρ(β/n, l)^n` at every temperature, in trace pairing relative to `Tr e^{-βH}`. In one
   dimension and at high temperature only, `exists_mpo_cluster_approximation` approximates
   `e^{-βH}` in energy-normalized operator norm.
2. *Normalization.* Absent. No indexed declaration compares `e^{-βH}/Z` with
   `ρ^n / Tr ρ^n`, or proves that `Tr ρ^n` is nonzero. Whether a generic lemma passing from a
   relative unnormalized trace-norm bound to normalized states exists elsewhere in QICLean's
   trace-norm layer was not determined here.
3. *Native network.* Absent in two dimensions for thermal operators. The product form of
   chain 1 is a sum with local coefficient functions, and no declaration converts a
   `ManyBody.ProductForm` into a native network. `TNLean.PEPS.Tensor G q` contracts to a vector.
   General contractions that can carry an operator do exist in the `Network` layer:
   `TNLean.Network.DependentBondNetwork.network` contracts tensors on a directed multigraph with
   edge-dependent alphabets and an arbitrary physical type `Phys v` at each vertex (so
   `Phys v = X v × X v` gives an operator), and
   `TNLean.Network.DistributedOperatorContraction` contracts party-local rectangular matrices on
   star and sample links for the polynomial-PEPS protocol (Theorem 5.2, Lemma 8.1). Neither
   module mentions a product form, a truncated exponential or a matrix exponential, and no
   declaration places a thermal operator in either. No two-dimensional purification statement
   exists. The only native network for a thermal operator is the one-dimensional
   `traceChainOperator` of chain 2. The exact PEPS of chain 3 represents vectors with
   exponential bond and is not stated for operators.
4. *Trace-norm error.* The step exists as a standalone lemma,
   `re_trace_sqrt_sub_le_of_forall_norm_trace_mul_sub_le`. Its hypothesis has the form of the
   conclusion of the pairing theorem after `Tr (O (ρ − σ)) = Tr (O ρ) − Tr (O σ)`, but no
   declaration composes them, and no trace-norm error is stated for any network.
5. *Bond complexity.* Present only as the local index range of the product form
   (`exists_productForm_truncatedExp_pow_card_index(_of_polynomial_growth)`), under an explicit
   volume hypothesis, and as the one-dimensional MPO bond `r² q^r` at high temperature.

Chains 4 and 5 do not enter: chain 4 is a pure ground-vector theorem in Euclidean error, and
chain 5 consists of exact identities for given tensors with no approximation, locality or gap
content. None of them may be cited for a thermal-state representation.

**The missing statements.** Stated so that each has one home:

- **M1 (TNLean, network).** A conversion from `ManyBody.ProductForm X near ρ` on the sites of a
  finite graph, with `near` contained in distance `l`, to a native operator network on that
  graph (or on a blocked graph) whose contraction is `ρ`, with each bond bounded by a product of
  the index ranges `card (P.Index j)` over the sites `j` within range of the edge. The
  multigraph contraction `Network.DependentBondNetwork.network` with paired physical indices is
  a candidate target; whether it should serve as the operator network, or a dedicated type is
  wanted, is a design decision left to the owner of M1.
- **M2 (QICLean, matrix estimate).** The trace-norm form of the every-temperature error,
  `‖e^{-βH} − ρ(β/n, l)^n‖₁ ≤ ε Tr e^{-βH}`, composed from the two existing declarations, and its
  normalized form for `e^{-βH}/Z` against `ρ(β/n, l)^n / Tr ρ(β/n, l)^n` for `ε < 1`.
- **M3 (TNLean, assembly).** The composition of M1 and M2 with the index counts: a native
  operator network for the normalized thermal state with an explicit trace-norm error and an
  explicit bond bound. A purification version would additionally need a native PEPS with
  ancilla legs whose reduced operator is the network of M1.

**Owner check.** #9847 owns the ALVV soft-truncation and cluster-MPO obligations (the printed
`eq:Atensor` form, the physical-support selector and the width and buffer restrictions); it is
one-dimensional and does not own M1–M3. #8271 owns the SCP10 ground-state, degeneracy and
topology results, with no thermal item. #8273 tracks the open problems of arXiv:1903.09439,
including the boundary locality conjecture, as open mathematics, with no thermal-network
item. Closed #9854 completed Hastings' corrected thermal construction up to the product form and
the trace-norm lemma; it did not include a network conversion. The tracker #10718 owns the
layer migration, not new mathematics. No open issue owns M1–M3; none is opened by this audit,
and one may be opened after this index is reviewed.

The absence of M1–M3 from this inventory is not a mathematical gap. Hastings' source passes
from the product form to a tensor-network description, and the missing statements are
formalization targets with a known proof route, not open problems.

## 9. Layer placement

The placement already follows `docs/many_body_circuit_architecture.md`. The matrix, support and
thermal estimates of chain 1 and the path-graph cluster estimate are in QICLean
(`Analysis/ClusterExpansion`, `ManyBody/Hamiltonian/ClusterExpansion`, `ManyBody/Sites`). The
statements that mention `MPOTensor`, `traceChainOperator`, `Tensor`, `stateCoeff`, `bondDim`
or the `Network` contractions are in TNLean. M2 belongs in QICLean beside `Analysis.ClusterExpansion.Temperature`;
M1 and M3 belong in TNLean. This audit moves no code and marks no migration complete.

## Verification

- Statements were read in the files named above. The QICLean files were compared with the pin
  `2d0f7b9f40` by `git diff` (no difference).
- No `sorry`, `admit`, `native_decide` or `axiom` occurs in any Lean file of the TNLean
  worktree, nor in the QICLean directories `Analysis/ClusterExpansion`,
  `ManyBody/Hamiltonian/ClusterExpansion` and the file `ManyBody/Sites/ProductForm.lean`
  (search by `grep`, prose occurrences of the word "admit" excluded).
- Blueprint entries `thm:physical_cluster_label_mpo`, `thm:physical_soft_windows_and_mpo`,
  `thm:peps_exact_square`, `thm:openai_polynomial_peps`,
  `thm:peps_regular_boundary_gibbs_obstruction` and the three CPSV16 physical Gibbs entries of
  chapter 21 carry `\leanok`.
- No build was run; the index makes no claim about the current compilation state.
