# Gibbs operators and PEPS: representation index, re-verified

This index records the results that bear on representing thermal operators and ground vectors
by tensor networks: declarations, complete hypotheses, normalization, error norm, bond or index
bounds, source anchors and verification status. It answers the interface question of issue
#10785. It is not a claim that arbitrary Gibbs states have an efficient PEPS representation.

**Commits.** Every statement below was read in the source files on top of TNLean main
`3221ba7e73`, with QICLean pinned at `27230ef676`. This note replaces the earlier index of
2026-11-26 (read at TNLean `12ebe257d9`), which is deleted with it. Against that index it
records three module moves, one missing composition in chain 1, the operator networks with a
trace-norm error in chain 4, and the scope of the Hastings source statement.

**Status conventions.** "Proved" means that no tactic-level `sorry` or `admit`, no `axiom`
declaration and no `native_decide` occurs in any non-`Archive` Lean file of TNLean or in any
Lean file of QICLean (pattern search; prose occurrences excluded). No build was run. "BP" gives
the blueprint label, and `\leanok` is recorded only where both the statement and its proof
carry the tag. TNLean labels are in `blueprint/src/chapter`, QICLean labels in QICLean's
`blueprint/src/chapter`. No declaration in the five chains carries an `**Unfaithful:**` marker.
QICLean paper-gap notes are published at `https://sirui-lu.com/QICLean/paper-gaps/<slug>.pdf`,
TNLean notes at `https://sirui-lu.com/TNLean/paper-gaps/<slug>.pdf`.

## Module locations

| Issue path | Current module | Repository |
| --- | --- | --- |
| `Lattice/ProductForm` | `QICLean.ManyBody.Sites.Product.ProductForm` | QICLean |
| `Lattice/ClusterExpansion/TruncatedProductForm`, `TruncatedAllTemperatures` | `QICLean.ManyBody.Hamiltonian.ClusterExpansion.ProductForm` | QICLean |
| `Lattice/ClusterExpansion/TruncatedPositivity`, `TemperatureError` | `QICLean.Analysis.ClusterExpansion.Temperature` | QICLean |
| `Lattice/ClusterExpansion/LocalIndexCount` | `QICLean.ManyBody.Hamiltonian.ClusterExpansion.IndexCount` | QICLean |
| `MPS/AreaLaw/ClusterTruncationMPO` | `TNLean.MPS.AreaLaw.LowEnergyAlgorithm.MPO.OperatorMPOFromCutRank` | TNLean |
| `MPS/AreaLaw/PhysicalSoftTruncationMPOApproximation` | last section of `TNLean.MPS.AreaLaw.LowEnergyAlgorithm.MPO.SoftTruncationMPOAccuracy` | TNLean |
| `PEPS/Approximation/ExactTreeRepresentation`, `ExactSquareRepresentation` | `TNLean.PEPS.Approximation.Exact.{ExactTreeRepresentation,ExactSquareRepresentation}` | TNLean |
| `PEPS/Approximation/Basic` | `TNLean.PEPS.Tensor.SquareLattice.Basic` | TNLean |
| `PEPS/Approximation/PolynomialPEPSTheorem` | unchanged | TNLean |
| `MPS/MPDO/TopologicalPhysicalGibbs`, `CPSVTopologicalPhysicalGibbs` | `TNLean.MPS.MPDO.TopologicalForm.TopologicalPhysicalGibbs` | TNLean |
| `PEPS/RegularBoundaryGibbsSupport` | `TNLean.PEPS.Injectivity.Boundary.RegularBoundaryGibbsSupport` | TNLean |

The percolation bounds are in `QICLean.Analysis.ClusterExpansion.Percolation`, the path-graph
estimate in `QICLean.Analysis.ClusterExpansion.Path`, and the nearest-neighbour cut rank in
`QICLean.ManyBody.Hamiltonian.ClusterExpansion.NearestNeighbor`.

## 1. Hastings' product form at every temperature

Source: M. B. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, Section IV. All declarations
are in QICLean and proved; all cited labels are `\leanok` in QICLean `ch17_cluster_expansion.tex`.

| Declaration | Source lines | BP (QICLean) |
| --- | --- | --- |
| `ManyBody.ProductForm`, `ManyBody.HasProductForm` | eq. `mpf`, 1024–1039 | `def:hastings_product_form` |
| `ManyBody.ClusterExpansion.hasProductForm_truncatedExp`, `..._of_dist_le` | 1256–1279 | `thm:hastings_truncated_product_form` |
| `ManyBody.HasProductForm.pow_of_even` | eq. `mplt`, 1303–1317 | `thm:hastings_thermal_all_temperatures` |
| `ManyBody.ClusterExpansion.hasProductForm_truncatedExp_pow_of_even`, `..._pow_of_even_of_dist_le` | 1303–1317 | `thm:hastings_truncated_all_temperatures` |
| `ClusterExpansion.posSemidef_truncatedExp_pow` | 1303–1314 | `thm:hastings_truncated_positivity` |
| `ClusterExpansion.evenTemperatureFactors_spec` | 1307–1312 | `thm:hastings_even_temperature_factors` |
| `ClusterExpansion.norm_trace_mul_exp_sub_truncatedExp_pow_le` | 1334–1347 | `thm:hastings_temperature_error` |
| `ClusterExpansion.norm_trace_mul_exp_sub_truncatedExp_pow_le_percolation` | 1342–1347 | `thm:hastings_temperature_error_percolation` |
| `..._percolation_add_two` | 1307–1312, 1334–1347 | `cor:hastings_temperature_error_add_two` |
| `ClusterExpansion.norm_trace_mul_exp_sub_truncatedExp_le_isLargeDiam`, `..._dist` | 1227–1254 | `thm:hastings_percolation_large_diameter` |
| `ClusterExpansion.exists_percolation_temperature` | 1242–1245 | `thm:hastings_percolation_temperature` |
| `ClusterExpansion.re_trace_sqrt_sub_le_of_forall_norm_trace_mul_sub_le` | 1281–1301 | `thm:hastings_thermal_trace_norm` |
| `ManyBody.ClusterExpansion.exists_productForm_truncatedExp_card_index`, `..._pow_card_index`, `..._card_index_of_polynomial_growth`, `..._pow_card_index_of_polynomial_growth` | 1256–1279, 1311–1320 | `thm:hastings_truncated_index_count` |

**Object.** `ProductForm X near ρ` is the data `ρ = ∑_α (∏_i F_i(α)) • ⊗_j ρ_j(α_j)` with each
`F_i` depending only on the `α_j` with `near i j`. It is a sum over local index assignments with
local coefficient functions, not a contraction on the edges of a graph. The thermal operator is
`truncatedExp G large h β`, the sum over term sets with no large connected cluster.

**Hypotheses.**

- `hasProductForm_truncatedExp`: nonempty finite site set, finite basis types, `Φ : Interaction X T`,
  reflexive `near`, any real `β`; no Hermiticity, connectivity or nonempty supports. The large
  clusters are `IsLargeSupport near T`; the `_of_dist_le` form takes a pseudometric and
  `IsLargeDiam T l` with `0 ≤ l`.
- `..._pow_of_even` and `posSemidef_truncatedExp_pow`: in addition Hermitian terms and `m` even.
  Conclusion: product form and positive **semidefiniteness** of `ρ^m`. The source states positive
  definiteness. **Local fix (positivity)**, QICLean `docs/paper-gaps/hastings05_mplt_positivity.tex`.
- `norm_trace_mul_exp_sub_truncatedExp_pow_le`: abstract term graph `G` and predicate `large`;
  `H = ∑_k h_k` Hermitian with Hermitian terms, `‖h_k‖ ≤ J`, `β ≥ 0`, any `n > 0`, and the
  boundary inequality `n_C + n_{∂C} ≤ S n_C` for every large connected set. The `_percolation`
  form adds the **interaction-count cutoff** `l + 1 ≤ #C` (number of terms) for every large
  connected set, the count `#{C : #C = k} ≤ N x^k`, `N, x ≥ 0` and `0 < x y ≤ 1/2` with
  `y = (e^{Jβ/n} − 1) e^{SJβ/n}`. The `_add_two` form fixes `n = evenTemperatureFactors β β₀`, the
  least even integer with `β/n ≤ β₀`, for `β, β₀ > 0`; the exponent carries `β/β₀ + 2`.
  **Local fix (factor count)**, QICLean `docs/paper-gaps/hastings05_temperature_factor_count.tex`.
- `..._isLargeDiam(_dist)`: one factor only. Supports of diameter at most `2R`, `R > 0`, overlap
  degree at most `Δ`, `x = max 1 Δ²`, `S = Δ + 1`, `0 < xy ≤ 1/2`; the size threshold is
  `⌊l_proj/(2R)⌋` and the distance form keeps a factor `(xy)^{-1}`. **Local fix (cluster size)**,
  QICLean `docs/paper-gaps/hastings05_percolation_cluster_size.tex`.
- Index counts: a pseudometric, nonempty basis types, centres `c k` with `dist (c k) j ≤ R` on
  `T k`, `0 ≤ l`, truncation `IsLargeDiam T l`. The polynomial forms add the **volume hypothesis**
  `#{k : dist i (c k) ≤ l + R} ≤ C (⌈l + R⌉ + 1)^D`; it is not derived from the metric.
  **Local fix (volume growth)**, QICLean `docs/paper-gaps/hastings05_planar_domain_scope.tex`.

**Normalization and error norm.** The thermal operator is the unnormalized `e^{-βH}`. The error is
a trace pairing relative to `Z = Tr e^{-βH}`, with `‖O‖` the operator norm:
`‖Tr (O (e^{-βH} − ρ(β/n, l)^n))‖ ≤ ‖O‖ (exp(n ∑_C y^{n_C}) − 1) Tr e^{-βH}`.
`re_trace_sqrt_sub_le_of_forall_norm_trace_mul_sub_le` turns
`‖Tr (O ρ) − Tr (O σ)‖ ≤ ε ‖O‖ Tr ρ` for all `O` (with `ε ≥ 0`, `0 ≤ Re Tr ρ`) into
`Re Tr √((ρ − σ)ᴴ (ρ − σ)) ≤ ε Re Tr ρ`, again unnormalized. A search of both libraries finds no
use of this lemma and no use of the every-temperature bounds outside their own file: the two are
not composed, and the approximant is never divided by its own trace.

**Index bounds.** For the diameter truncation, `card (P.Index i) ≤ (2^{M_i} + 1) |X i|²`,
`M_i = #{k : dist i (c k) ≤ l + R}`; for `ρ^m`, its `m`-th power; under the volume hypothesis,
`|X i|² (1 + 2^{C(⌈l+R⌉+1)^D})` and its `m`-th power. These bound the local index of a product
form, not the bond of a network.

**Gap in chain 1 (new in this note).** The every-temperature error is stated for an abstract
`large` with `hS`, `hl`, `hcount` supplied; the index count is stated for `IsLargeDiam T l`. No
declaration states the every-temperature error for
`truncatedExp (overlapGraph T) (IsLargeDiam T l) Φ.term (β/n) ^ n` with these three hypotheses
discharged from the geometry. The ingredients exist in `Percolation`
(`card_ge_of_isLargeDiam`, `card_add_card_boundary_le`, and the connected-set count used by
`sum_nonempty_powerset_prod_le_percolation_connected`); the single-factor theorem
`norm_trace_mul_exp_sub_truncatedExp_le_isLargeDiam` shows the composition at `n = 1`.

**Source scope.** Hastings states the product form with an index range
`exp[O(ξ_perc^d log(N)^d β/β₀)]` (lines 1314–1356) and calls it a higher-dimensional analogue of
the one-dimensional matrix product form of density matrices (lines 118–122). He states no bond
dimension on the edges of a network and no purification.

Adjacent, same source: `ManyBody.Interaction.hasProductForm_lie` and
`exists_productForm_lie_card_index_eq` (`QICLean.ManyBody.Dynamics.ProductFormula`) give the
exact product form of a Trotter product, with local index `|X j|^{2 n c_j}`.

## 2. The one-dimensional cluster MPO and the soft-truncation MPO

Source: Arad, Landau, Vazirani, Vidick (ALVV), arXiv:1602.08828v2. Namespace
`TNLean.MPS.AreaLaw`. All proved; all labels `\leanok` in TNLean. Source obligations stay with
#9847.

| Declaration | Source anchor | BP |
| --- | --- | --- |
| `exists_mpo_cluster_truncation`, `exists_mpo_cluster_approximation` | `thm:cluster`, `thm:cluster-approx`, 1270–1303, 2014–2115 | `thm:physical_cluster_label_mpo` |
| `exists_shifted_heat_mpo` | `lem:exp-approx-eff`, 1262–1268 | `thm:shifted_regional_heat_mpo` |
| `exists_softTruncation_mpo_of_cluster_order` | `lem:exp-approx-eff`, 1262–1268 | `thm:soft_mpo_cluster_order` |
| `exists_softTruncation_mpo_of_accuracy`, `exists_softTruncatedHamiltonian_mpo_of_accuracy` | `def:soft-trunc`, `lem:exp-approx-eff`, 1178–1185, 1262–1268 | `thm:soft_hamiltonian_mpo_accuracy` |
| `exists_interval_physical_soft_closeness_and_mpo` | `lem:exp-approx`, `lem:exp-approx-eff`, 1195–1268 | `thm:physical_soft_windows_and_mpo` |
| `operatorSchmidtRank_cluster_truncation_all_cuts_le` | `thm:cluster`, 1298–1303, 1971–2013 | `thm:physical_cluster_all_cut_rank` |
| QICLean `ClusterExpansion.norm_exp_sub_truncatedExp_pathGraph_le` | `thm:cluster-approx`, 1270–1291, 1935–1968 | QICLean `thm:normalized_cluster_label_tail` |

**Object.** `MPOTensor.traceChainOperator A 1` for `A : Fin (N+1) → MPOTensor q D`, with entries
`Tr (∏_v A_v(σ_v, τ_v))`: a native one-dimensional operator network.

**Hypotheses and conclusions.**

- `exists_mpo_cluster_truncation`: `1 ≤ q`, `0 < r`, `h i` supported on `{i, i+1}`, any real
  `β`. The interaction-count truncation `truncatedExp (pathGraph N) (r ≤ |C|) h β` equals
  `traceChainOperator A 1` exactly, bond `r² q^r`.
- `exists_mpo_cluster_approximation`: in addition `h i` Hermitian, `‖h i‖ ≤ 1`, a supplied lower
  energy `λ • 1 ≤ ∑ h i`, `0 ≤ β` and `2 (e^β − 1) ≤ 1` (that is, `β ≤ log(3/2)`):
  `e^{βλ} ‖e^{-β ∑ h_i} − traceChainOperator A 1‖ ≤ exp(N² (2(e^β − 1))^r) − 1`.
  `exists_shifted_heat_mpo` states the same bound for `e^{-β(∑ h_i − λ)}` directly.
- `exists_softTruncation_mpo_of_accuracy`: `3m ≤ t`, `0 < ξ`; bond `(r² q^r)(m+1)` with `r` an
  explicit logarithmic ceiling in `N` and `ξ`; error `≤ ξ` for `cfc (softTruncation t m)(∑ h − ε)`.
- `exists_interval_physical_soft_closeness_and_mpo`: for `η, w, δ > 0`, an order `m` given by an
  explicit ceiling; for every chain, `Φ : BondInteraction (N+1) q` with `0 ≤ Φ.term i ≤ 1` and
  cuts `p ≤ v ≤ N + 1`, spectral-window closeness of `Hsoft` (scale `3m`) and, for each `ξ > 0`,
  tensors with `‖Hsoft − traceChainOperator T 1‖ ≤ ξ` and bond `(1 + N q²) + (ℓ² q^ℓ)(m + 1)`.

**Normalization and error norm.** Operator norm (`Matrix.Norms.L2Operator`), unnormalized. The
factor `e^{βλ}` is an energy normalization by the supplied lower energy, not a trace
normalization. The soft-truncation results approximate a Hamiltonian, not a thermal operator.
No declaration multiplies site-dependent `traceChainOperator`s (only `_conjTranspose` and
`_sum_smul_closing` exist), so there is no every-temperature one-dimensional thermal MPO.

**Markers.** **Local fix (cutoff and normalization)**: interaction-label components replace
physical support and a lower energy normalizes the error; the printed physical-support estimate
is false and is not asserted. **Scope restriction (scale)**: `3m ≤ t`, and `t = 3m` in the
physical form, against the source's `t′ < (ln 2/2) t`. TNLean
`docs/paper-gaps/alvv16_cluster_approximation.tex`,
`docs/paper-gaps/alvv16_soft_truncation_energy_estimate.tex`.

## 3. Exact native PEPS contraction

Source: *Polynomial PEPS approximation of gapped square-grid ground states*, September 24, 2026,
`07-assembly.tex`, lines 203–214, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Namespace
`TNLean.PEPS.ExactTreeRepresentation` (last two rows `TNLean.PEPS.Approximation`). All proved; all
labels `\leanok` in TNLean.

| Declaration | Hypotheses | Bond | BP |
| --- | --- | --- | --- |
| `exists_exact_tensor` | finite linearly ordered `V`, `G` connected, `0 < q`, any `ψ` | `q^{|V|}` | `thm:peps_exact_degenerate` |
| `exists_exact_tree_tensor` | the same and `Nontrivial V` | `q^{|V|}` on a spanning tree, `1` elsewhere | `thm:peps_exact_tree` |
| `exists_exact_square_tensor`, `..._tree_tensor`, `exists_exact_unit_square_tensor` | `0 < L` (`2 ≤ L` for the tree form; `‖ψ‖ = 1` for the unit form) | `q^{L²}` | `thm:peps_exact_square` |
| `exists_exact_square_tensor_bounded`, `..._polynomial`, `..._outer_power` | `0 < L ≤ L₀`; `0 ≤ r`; `0 < χ` | `q^{L₀²}`; `max C q^{L₀²} · L^r`; its `χ`-th root form | `thm:peps_exact_small_sizes` |
| `hasPEPSApproximation_of_small_size`, `exists_uniform_small_size_approximation` | `0 < L ≤ L₀` (resp. `2 ≤ L < L₀`), `0 ≤ c`, unit `Ω` | `max C q^{L₀²} · L^c` (resp. one `C' ≥ C`) | `thm:peps_exact_small_size_approximation` |

All conclusions are `stateCoeff A = ψ` with positive bonds: exact, zero error, phase one for unit
`ψ`. The bound is exponential in the number of sites; these cover the finitely many small sizes
of chain 4 and are not an efficient approximation. Only vectors are represented.

## 4. Polynomial PEPS approximation of gapped ground vectors

Source: the same manuscript, Theorem 1.1, `00-introduction.tex`, lines 36–57 (`eq:model`,
`eq:global-gap`, `eq:target-error`), with the companion area-law manuscript, Theorem 1.1.
Namespace `TNLean.PEPS.Approximation`. All proved.

| Declaration | Module | BP |
| --- | --- | --- |
| `IsSquareGroundState`, `pepsVector`, `HasPEPSApproximation`, `PolynomialPEPSApproximation` | `PEPS.Tensor.SquareLattice.Basic` | `def:polynomial_peps_model` |
| `polynomialPEPSApproximation` | `PEPS.Approximation.PolynomialPEPSTheorem` | `thm:openai_polynomial_peps` |
| `polynomialPEPSApproximation_explicit` | `PEPS.Approximation.PolynomialPEPSClosedConstant` | `thm:polynomial_peps_explicit_constants` |
| `DyadicOperatorNetworkAt`, `hasPEPSApproximation_of_dyadicOperatorNetworkAt` | `PEPS.Approximation.Routing.GroundStateApproximation` | `def:peps_large_size_dyadic_operator_network`, `thm:peps_ground_state_approximation_conditional` |
| `dyadicOperatorNetworkAt_of_dyadicProtocolBoundsAt` | `PEPS.Approximation.Protocol.DyadicProtocolCompression` | `thm:peps_large_size_network_from_protocol` |
| `TNLean.Network.operatorNetworkMatrix`, `TNLean.Network.exists_fixInput_network_of_traceNorm_sub_pure_le` | `Network.DependentBond.DependentNetworkColumn` | `def:peps_ket_column_dependent_fix_input`, `thm:peps_ket_column_dependent` |

**Statement.** For `q ≥ 2` and `J, Δ > 0` there are `C, c > 0` (explicitly
`pepsBondPrefactor q J Δ`, `pepsBondExponent q J Δ`) such that for every `L ≥ 2`, every
`h : SquareInteraction L q` with Hermitian total sum (terms need not be Hermitian) and
`‖h.term i‖ ≤ J`, every `E₀` and every unit `Ω` with `IsGapped h.hamiltonian E₀ Δ` and
`groundSpace h.hamiltonian E₀ = span {Ω}`, there is a native `Tensor (squareLatticeGraph L L) q`
with positive bonds `≤ C L^c`, nonzero contraction, and a phase `θ` with
`‖pepsVector A / ‖pepsVector A‖ − e^{iθ} Ω‖ ≤ L⁻¹`.

**Normalization and error norm.** Euclidean norm of the normalized vector, up to a global
phase; constants uniform in `L`, `h` and `Ω`. A unique gapped ground vector, not a
finite-temperature or mixed-state theorem.

**Operator networks with a trace-norm error (new in this note).** The proof passes through a
native operator network. `DyadicOperatorNetworkAt` asks for a party network `N` on dyadic anchors
(at most `B` parties per block, degree `deg`, separation `c`, link dimensions `≤ C₁ L^k`) whose
operator satisfies `‖σ − |Ω⟩⟨Ω|‖₁ ≤ C / L^5`; `dyadicOperatorNetworkAt_of_dyadicProtocolBoundsAt`
produces it from a distribution protocol (a circuit), not from `e^{-βH}`.
`exists_fixInput_network_of_traceNorm_sub_pure_le` takes any edge-dependent operator network
`operatorNetworkMatrix tail head D A B` with `‖σ − |Ω⟩⟨Ω|‖₁ ≤ η < 1`, `Ω` a unit vector, and
returns a product input `z` whose column `ψ = σ|z⟩` is nonzero with phase error `≤ 2η`. Both
require a rank-one target. The other TNLean files that combine a trace norm with a network
contraction (`Routing/VectorColumn`, `Routing/SquareGridColumn`, `Routing/PartyColumnRouting`,
`Network/Party/PartyColumnInput`, `MPS/AreaLaw/SweepPreparation/ProtocolMPSApproximation`) are
consumers or variants of the same column extraction against `|Ω⟩⟨Ω|`.

**Markers.** The final theorem takes no hypothesis beyond the proposition and carries no marker.
Auxiliary modules of `PEPS/Approximation` and `PEPS/AreaLaw` carry scope and local-fix markers
(`docs/paper-gaps/polypeps_*.tex`); this index does not audit them. The second predicate
`TNLean.PEPS.Approximation.Pinned.HasPEPSApproximation`
(`PEPS.Approximation.GroundState.SourceApproximation`) restates the phase convention for transfer
lemmas; it is a candidate for the one-definition review (#10969), not changed here.

## 5. Gibbs forms of RFP MPDOs and of the regular PEPS boundary

### 5a. Physical commuting Gibbs decomposition of a renormalization fixed point

Source: Cirac, Pérez-García, Schuch, Verstraete (CPSV16), arXiv:1606.00608, Theorem 4.14(i),(iii),
lines 972–993, Theorem 4.15, lines 1013–1016 (hypothesis of length independence, lines
995–1010), Definition 4.8, lines 831–847, Appendix C.4, lines 1929–2046. Module
`TNLean.MPS.MPDO.TopologicalForm.TopologicalPhysicalGibbs`. All proved; all `\leanok` in
`ch21_mpdo_rfp_fusion_isometries_recursive_density_spectral_gibbs.tex`.

| Declaration | Hypotheses | BP |
| --- | --- | --- |
| `MPOTensor.BNTFusionTensorClause.hasPhysicalTopologicalGibbsDecomposition` | a fusion clause `H` of `M`, `IsMPDO M`, `(ofChi H.chi).LengthIndependent` | `thm:mpdo_fusion_clause_physical_coordinate_gibbs_at_least_two` |
| `MPOTensor.physicalTopologicalGibbsDecomposition_of_isRFPViaTS` | `IsHorizontalCF M`, `IsMPDO M`, `IsRFPViaTS M`, length independence for the selected clause | `thm:mpdo_physical_coordinate_gibbs_at_least_two` |
| `MPOTensor.physicalTopologicalGibbsDecomposition_of_isRFPViaTS_of_cpsvCanonicalForm` | `IsCPSVCanonicalForm M.toMPSTensor`, `IsMPDO M`, `IsRFPViaTS M`, length independence for the selected clause | `thm:mpdo_literal_cpsv_physical_coordinate_gibbs_at_least_two` |

**Conclusion** (`HasPhysicalTopologicalGibbsDecomposition`). A Hermitian two-site term whose ring
translates commute, nonnegative weights `λ_i` (`i : Fin d`), and for every `N` pairwise orthogonal
projections `P̂_i^{(N+2)}` commuting with `exp(−Ĥ_{N+2})`, with
`mpo M (N + 2) = ∑_i λ_i • (P̂_i^{(N+2)} * exp(−Ĥ_{N+2}))`. Length independence
(`c.coeff L = c.coeff 1` for `0 < L`) is the source's hypothesis. The identity is exact, for an
already given MPDO, on chains of length at least two, with no error term, no trace normalization,
and no bond statement beyond the given tensor.

**Markers.** **Scope restriction (length at least two)**:
`docs/paper-gaps/cpsv16_topological_gibbs_length_one.tex`. **Local fix (physical complement)**:
`docs/paper-gaps/cpsv16_topological_gibbs_physical_complement.tex`. **Local fix (Figure 11)**:
`docs/paper-gaps/cpsv16_figure11_per_pair_support.tex`,
`docs/paper-gaps/cpsv16_figure11_fusion_coisometry.tex`.

### 5b. Regular boundary density: full-space obstruction, invariant-support Gibbs form

Source: Schuch, Cirac, Pérez-García (SCP10), arXiv:1001.3807, Theorem 6.9, lines 2027–2076;
compared with arXiv:1903.09439, Conjecture `gap2Dboundary1dlocal`, lines 980–1024. Namespace
`TNLean.PEPS`. All proved; `\leanok` in `ch24_peps_regular_boundary_gibbs_support.tex`.

| Declaration | Hypotheses | Conclusion | BP |
| --- | --- | --- | --- |
| `regularBoundaryDensity_ne_exp` | finite group, `1 < card G`, any `H` | the density `|G|^{-n} P_inv` on `(Fin (n+1) → G)` is not `exp H` | `thm:peps_regular_boundary_gibbs_obstruction` |
| `IsGInjective.regularBoundaryGram_ne_exp` | G-injective `T` for the regular representation, `1 < card G` | its Gram operator is not `exp H` | same |
| `regularBoundarySupportedDensity_eq_exp` | finite group | on the invariant support, `|G|^{-n} • 1 = exp(−log(|G|^n) • 1)` | `thm:peps_regular_boundary_supported_gibbs` |

Exact support statements. They give no locality of a boundary Hamiltonian, no bulk gap, and do
not resolve the conjecture of arXiv:1903.09439.

## 6. Adjacent exact thermal result

`TNLean.PEPS.stateCoeff_classicalPEPS`, `expectation_classicalPEPS`
(`TNLean.PEPS.Examples.Classical`; arXiv:2011.12127, Appendix A; BP `thm:peps_classical_coeff`,
`thm:peps_classical_expectation`, `\leanok`): for `h : Fin q → Fin q → ℝ` on a torus of width
and height at least three, a native PEPS with legs in `Fin q` has coefficients `e^{−βH(σ)/2}`,
and diagonal expectation values equal normalized classical Gibbs averages. Exact, diagonal
observables only; the PEPS vector is not a purification of `e^{-βH}/Z`. **Scope restriction
(torus size)**, `docs/paper-gaps/rmp_peps_examples_small_torus.tex`. QICLean's
`canonicalPurification ρ` (coefficients `√ρ`, `QICLean.Entropy.MutualInformation.PurificationSplitting`)
is a generic finite-dimensional purification with no locality or network structure.

## 7. Comparison of conventions

| Chain | Object | Normalization | Error | Bond or index |
| --- | --- | --- | --- | --- |
| 1 | `e^{-βH}`, any finite site set | unnormalized, relative to `Tr e^{-βH}` | trace pairing, operator-norm observable; trace-norm lemma separate | local index `((2^{M_i}+1)|X_i|²)^n` |
| 2 | `e^{-βH}` on a chain, `β ≤ log(3/2)`; `Hsoft` | `e^{βλ}`; none for `Hsoft` | operator norm | `r² q^r`; `(1+Nq²)+(ℓ²q^ℓ)(m+1)` |
| 3 | any vector, connected graph | exact | zero | `q^{|V|}` |
| 4 | unique gapped ground vector, square | unit vector, normalized contraction | Euclidean up to phase, `≤ L⁻¹`; operator network `‖σ − |Ω⟩⟨Ω|‖₁ ≤ C L⁻⁵` | `C L^c` |
| 5a | a given RFP MPDO, length `≥ 2` | as given | exact identity | that of the given tensor |
| 5b | regular boundary density | as given | exact; obstruction on the full space | none |

## 8. The interface question

**Question.** Is there a complete chain: general thermal operator approximation, normalization,
native PEPO or PEPS purification, trace-norm error, bond complexity?

**Answer: no, not in TNLean `3221ba7e73` or QICLean `27230ef676`.** Link by link:

1. *Thermal approximation.* Present at every temperature only in the abstract form of chain 1
   (`..._pow_le_percolation(_add_two)`), with `hS`, `hl`, `hcount` supplied. For the concrete
   diameter truncation that carries the index count, only one factor (high temperature) is
   stated. In one dimension, `exists_mpo_cluster_approximation` covers `β ≤ log(3/2)` only.
2. *Normalization.* Absent. No declaration compares `e^{-βH}/Z` with `σ/Tr σ` for
   `σ = ρ(β/n, l)^n`, or proves `Tr σ ≠ 0`. A search of QICLean (`Analysis/TraceNorm`,
   `Algebra/Hermitian/PositiveSemidefiniteNormalization`, patterns `trace.re⁻¹ •`, `normaliz`)
   found no generic lemma passing from a relative unnormalized trace-norm bound to normalized
   states; `Matrix.normalizePosSemidef` normalizes but carries no error estimate.
3. *Native network.* Absent for thermal operators in two dimensions. No declaration converts a
   `ManyBody.ProductForm` into any network. Native operator networks exist
   (`Network.operatorNetworkMatrix`, `MPOTensor.traceChainOperator`), but the only thermal
   operator placed in one is the one-dimensional high-temperature `traceChainOperator` of chain 2.
   No local purification of a thermal operator is stated; `IsLPDO` (`MPS/Operator/Periodic/LPDO`)
   is one-dimensional structure without approximation content.
4. *Trace-norm error.* `re_trace_sqrt_sub_le_of_forall_norm_trace_mul_sub_le` exists but is not
   composed with any thermal bound. The trace-norm errors stated for native networks (chain 4)
   have a rank-one target, and Lemma 8.1 needs it.
5. *Bond complexity.* Present only as product-form index ranges (under an explicit volume
   hypothesis) and as the one-dimensional bond `r² q^r`.

Chains 3, 4, 5 and section 6 do not enter: 3 represents vectors exactly with exponential bond, 4
is a pure ground-vector theorem, 5 consists of exact identities for given tensors, and 6 covers
diagonal observables of classical models. None may be cited for a thermal-state representation.

**First missing statement, in chain order.**

- **M0 (QICLean, `Analysis/ClusterExpansion` or `ManyBody/Hamiltonian/ClusterExpansion`).**
  The every-temperature error for `truncatedExp (overlapGraph T) (IsLargeDiam T l) Φ.term (β/n) ^ n`
  with `hS`, `hl`, `hcount` derived from support diameter `2R` and overlap degree `Δ`, as the
  single-factor `_isLargeDiam` theorem does at `n = 1`. A composition of existing lemmas.
- **M2 (QICLean, beside `Temperature`).** The trace-norm form
  `‖e^{-βH} − σ‖₁ ≤ ε Tr e^{-βH}` from M0 and the trace-norm lemma, and its normalized form. Since
  `σ` is positive semidefinite (`posSemidef_truncatedExp_pow`), `|Tr σ − Z| ≤ ε Z` and an
  elementary estimate gives `‖e^{-βH}/Z − σ/Tr σ‖₁ ≤ 2ε` for `ε < 1`.
- **M1 (TNLean, network).** A conversion of `ManyBody.ProductForm X near ρ` on a finite graph,
  `near` contained in graph distance `l`, into a native operator network whose contraction is
  `ρ`, with bonds bounded by products of `card (P.Index j)`. Since `F_i` reads every index within
  distance `l`, the network lives on the `l`-th power graph or on a blocking into cells of
  diameter about `l`; the choice of target (`Network.operatorNetworkMatrix` or a dedicated type)
  belongs to the owner of M1. This is beyond the printed Hastings statement, which gives index
  ranges only.
- **M3 (TNLean, assembly).** M1 with M2 and the index counts: a native network for the
  normalized thermal state with explicit trace-norm error and bond. A purification version can
  use `σ = (ρ^{n/2})^2` with `ρ^{n/2}` Hermitian and in product form (`HasProductForm.pow`): the
  vector `(ρ^{n/2} ⊗ 1)|Φ⁺⟩` purifies `σ`, and M1 applied to `ρ^{n/2}` gives its network. Not
  formalized; recorded as a route.

**Owner check.** Searched open TNLean issues for "Gibbs", "thermal", "PEPO", "purification",
"product form", "Hastings", "truncatedExp", "finite temperature", "cluster expansion",
"trace norm", "operator network", "matrix product form", "mixed state", "density operator PEPS",
and open QICLean issues for "Gibbs", "thermal", "trace norm cluster", "product form". #9847 owns
the ALVV obligations (printed `eq:Atensor`, physical-support selector, width and buffer
restrictions); it is one-dimensional and owns none of M0–M3. #8271 (SCP10 ground states, degeneracy,
topology) and #8273 (open problems of arXiv:1903.09439) carry no thermal-network item. Closed
#9854 completed Hastings' corrected thermal construction up to product form, index counts and
the trace-norm lemma, without a network conversion. QICLean #1147 (open) ports the
product-form half of the cluster expansion; its listed declarations are present in QICLean at
the pin, and it is a migration, not M0–M3. #10718 and #10963 own layer and tensor-type
migrations. No open issue owns M0–M3; none is opened by this audit.

Absence from this inventory is not a mathematical gap: M0 and M2 are compositions of proved
estimates, and M1 is a formalization target, not an open problem.

## 9. Disposition

Rule: `docs/many_body_circuit_architecture.md`, "Where a declaration goes", read on statements.
Candidates for QICLean, by declaration; no move is made and no migration is marked complete.

| Declaration (TNLean) | Reason | Target | Caveat |
| --- | --- | --- | --- |
| `TNLean.MPS.AreaLaw.operatorSchmidtRank_cluster_truncation_all_cuts_le` | operator Schmidt rank at chain cuts, no network | `ManyBody/Hamiltonian/ClusterExpansion/NearestNeighbor`, beside the interior-cut version | restate for `Interaction (fun _ ↦ Fin q) (chainBond N)`; TNLean's label `thm:physical_cluster_all_cut_rank` duplicates QICLean's label of the same name |
| `TNLean.MPS.AreaLaw.rank_pairedOperator_cutMatrix_eq` | cut rank of the paired vector equals operator Schmidt rank (rule 4) | `ManyBody/Sites/OperatorSchmidtRank` | needs `pairCfgEquiv` (TNLean `MPS/CanonicalForm/VerticalForm/Purity`) moved with it |
| `TNLean.MPS.AreaLaw.softHeat_base_bounds` | `0 < 2(e^{1/3} − 1) < 1` (rule 5) | `Analysis/Real` | trivial; may instead be inlined |
| `TNLean.PEPS.rank_regularBoundaryDensity_lt_card`, `not_isUnit_regularBoundaryDensity`, `regularBoundaryDensity_ne_exp`, `regularBoundarySupportedDensity_eq_exp` | matrices on `(Fin n → G)` from a group representation | `Representation` or `Algebra/Matrix` | only together with `regularBoundaryDensity` and `regularBoundaryProjector` (`PEPS/Tensor/GraphState/RegularBoundaryState`), which carry the PEPS boundary reading |
| M0, M2 (not yet written) | matrix and site estimates | `Analysis/ClusterExpansion/Temperature` | new statements, not moves |

Stay in TNLean: every statement mentioning `MPOTensor`, `traceChainOperator`, `Tensor`,
`stateCoeff`, `bondDim`, a `Network` contraction, `IsGInjective` or a BNT fusion clause, so all
of chains 3, 4, 5a, `IsGInjective.regularBoundaryGram_ne_exp`, and the MPO statements of chain 2.
The spectral-window half of `exists_interval_physical_soft_closeness_and_mpo` (from
`exists_interval_physical_scaled_soft_low_energy_closeness`, `MPS/AreaLaw/LowEnergyAlgorithm/SoftTruncation`)
mentions no network but falls under the area-law exception of the same section. Chain 1 is
already in QICLean. M1 and M3 belong in TNLean.
