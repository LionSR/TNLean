# One-dimensional area law and matrix product state approximation

This document records the Lean statements of the one-dimensional specialization
of the September 24, 2026 manuscripts *A two-dimensional area law from a global
spectral gap* and *Polynomial PEPS approximation of gapped square-grid ground
states*, following the repository note
[`docs/notes/one_dimensional_note`](../notes/one_dimensional_note/one_dimensional_area_law_and_mps.tex)
(Theorems A and B there). The modules live in `TNLean/MPS/AreaLaw/` and
the blueprint chapter is `blueprint/src/chapter/ch35_one_dimensional_chain.tex`.

The model is stated natively on the chain of `L` sites (`Fin L`), with local
dimension `q`, supports of range `R` (nonempty sets of sites of diameter at most
`R`), one Hermitian term of norm at most `J` per support acting as the identity
off its support, and a gapped ground vector in the sense of
`Matrix.IsGappedGroundState`. Regional entropies are QICLean's
`Entropy.regionEntropy`. Nothing is derived from the two-dimensional lattice
development of `TNLean/PEPS/AreaLaw/`; the two finite-dimensional cores (the
marginal tail bound `Entropy.surprisalTail_cut_le` and the buffered discount
`Entropy.two_mul_condEntropy_le`) are QICLean lemmas stated on an arbitrary
finite set of sites, instantiated here on the chain.

## Statements

| Note statement | Formal statement | Status |
|---|---|---|
| Setting: the chain of `L` sites, intervals, supports, Hamiltonians (`eq:ham`, `eq:gap`) | `MPS.AreaLaw.interval`, `MPS.AreaLaw.IsChainSupport`, `MPS.AreaLaw.ChainHamiltonian`, `Matrix.IsGappedGroundState` | Definitions. |
| Lemma 3.1 (marginal tail bound) at a cut | `MPS.AreaLaw.ChainHamiltonian.surprisalTail_regionState_le` with the budget `MPS.AreaLaw.cutLogBudget` | Proved, from the QICLean core. |
| `eq:count`, `eq:BR`: split interactions and cut budget of an interval | `MPS.AreaLaw.card_crossingTerms_interval_le` (`N_R = 2·2^{2R}`), `MPS.AreaLaw.cutLogBudget_interval_le` (`B_R = 1 + N_R log²(e q^{R+1})`) | Proved; the constants are those of the note. |
| Lemma 4.2 (buffered discount) | `MPS.AreaLaw.two_mul_condEntropy_interval_le`, with `MPS.AreaLaw.chainShellCount` (`m`) and `MPS.AreaLaw.chainDiscountConst` | Proved. Shells of width `R` as in the note; energy threshold `Δ/2` in place of the note's `Δ/4`, overlap losses `m log 2` in place of the note's `2 C_E/Δ`, and the shell count omits the note's fourth entry `4096 e (1 + ϑ) B_R`, the term `4096 e ϑ B_R / m` staying explicit in the discount: `docs/paper-gaps/tnlean_one_dimensional_discount_constants.tex`. |
| Araki–Lieb closure, reductions (Section 2) | `MPS.AreaLaw.regionEntropy_le_union_add`, `MPS.AreaLaw.regionEntropy_le_mul_card_boundaryEdges_of_intervals` | Proved. |
| Theorem A for intervals | `MPS.AreaLaw.regionEntropy_interval_le` with the explicit `MPS.AreaLaw.chainIntervalEntropyBound` | Proved; no existential constant. |
| Theorem A, constant linear in `1 + J/Δ` | `MPS.AreaLaw.chainIntervalEntropyBound_le`, `MPS.AreaLaw.chainAreaLawConst` | Proved. |
| Theorem A for subsets of the chain | `MPS.AreaLaw.regionEntropy_le_mul_card_boundaryEdges`, `MPS.AreaLaw.chainAreaLaw` | Proved on the chain of `L` sites (connected domains). |
| Setting on a finite `Λ ⊂ ℤ` (induced path graph, `eq:ham`, `∂_Λ A`) | `MPS.AreaLaw.sitePos`, `MPS.AreaLaw.domainGraph`, `MPS.AreaLaw.IsDomainSupport`, `MPS.AreaLaw.DomainHamiltonian`, `MPS.AreaLaw.domainBoundaryEdges` | Definitions; the sites of `Λ` are labelled in increasing order. |
| Theorem A on a finite `Λ ⊂ ℤ`; first reduction (Section 2) | `MPS.AreaLaw.regionEntropy_le_mul_card_domainBoundaryEdges`, `MPS.AreaLaw.domainAreaLaw` | Proved, with the constant `C₀(q, R)(1 + J/Δ)` of the chain. The reduction uses the zero entropy of the prefixes ending at the gaps of `Λ` (`MPS.AreaLaw.regionEntropy_eq_zero_of_forall_subset_or_disjoint`) and flips of the region on them (`MPS.AreaLaw.regionEntropy_symmDiff_eq_of_eq_zero`) in place of the factorization over components: `docs/paper-gaps/tnlean_one_dimensional_connected_domain_scope.tex` (resolved). |
| Part II, `lem:reset` (information reset) | `MPS.AreaLaw.ChainHamiltonian.information_reset` | Proved on the contiguous chain, with only the original full-system gap. The constants precede all system, region and information-bound data. |
| Part II, `lem:logsep` (information at logarithmic separation) | `MPS.AreaLaw.ChainHamiltonian.mutualInformation_le_of_logarithmic_separation` | Proved on the contiguous chain for a union of at most k₀ intervals and an arbitrary region at distance at least Dₚ log L, including empty or overlapping interval components. |
| Matrix product states, cut matrices | `MPS.AreaLaw.IsOpenMPS`, `MPS.AreaLaw.cutMatrix` | Definitions. |
| Cut ranks bound the bond dimension | `MPS.AreaLaw.isOpenMPS_of_cutMatrix_rank_le` | Proved. |
| Growth between two cuts | `MPS.AreaLaw.rank_cutMatrix_add_le`, `rank_cutMatrix_le_add`, `rank_cutMatrix_le_pow_min_mul`, `rank_cutMatrix_le_pow_forty_mul` | Proved for arbitrary vectors: moving `d` sites across a cut costs at most `q^d` in either direction. Endpoint rank bounds `R` on an interval of length at most `80w` give internal ranks at most `q^(40w) R` when `q ≥ 1`. The endpoint bounds remain hypotheses of this auxiliary result. |
| Proposition 7.1 (`prop:VC`, sequential truncation at prescribed bond dimension) | `MPS.AreaLaw.prefixBasisProjection`, `MPS.AreaLaw.isOpenMPS_sequentialTruncation_prefixBasisProjection` | Proved for every vector and every ordered orthonormal basis at the internal cuts, for all natural `L`, `q` and `D`. The defined product has internal bond dimensions at most `D`, and its error is bounded by the original discarded expectations. Specialization to any ordered marginal eigenbasis gives the source statement, including all choices within degenerate eigenspaces. The former threshold restriction is resolved: `docs/paper-gaps/tnlean_one_dimensional_threshold_truncation.tex`. |
| Sequential truncation at an entropy threshold | `MPS.AreaLaw.exists_sequentialTruncation` | Proved, as a separate statement: eigenvalues at least `exp(-(S_k + w))` are retained, with cut ranks at most `max 1 (exp(S_k + w))` and error `∑_k √tail_k(w)`. The threshold and prescribed-dimension projectors need not coincide; see `docs/paper-gaps/tnlean_one_dimensional_threshold_truncation.tex`. |
| Prefix-cut projection bounds in the proof of Theorem B | `MPS.AreaLaw.ChainHamiltonian.spectralProjectionGE_leftBlock_bounds` | Proved for every natural cut index and `w ≥ 0`: the actual reduced state's projection at `exp(-(C_int + w))` has rank at most `exp(C_int + w)` and discarded mass at most `2 exp(e/2) exp(-w/(32 s))`, where `s = √((1 + J/Δ) B_R)`. |
| Approximation at prescribed accuracy, by the argument for Theorem B | `MPS.AreaLaw.exists_isOpenMPS_norm_sub_le_of_error` | Proved for `0 < ε ≤ 1`, with a normalized approximant and bond bound `⌊exp(C_int + 64 s log(2 L c₀ / ε))⌋`, where `s = √((1 + J/Δ) B_R)` and `c₀ = √(2 exp(e/2))`. |
| Theorem B | `MPS.AreaLaw.exists_isOpenMPS_norm_sub_le` with `MPS.AreaLaw.chainBondDimension`; polynomial form `MPS.AreaLaw.chainBondDimension_le_mul_rpow` | Proved; the bond dimension is `⌊exp(C_int + w(L))⌋ ≤ e^{C_int} (2 c₀)^{64 s} L^{128 s}` with `s = √((1 + J/Δ) B_R)`. The approximant is normalized and within `1/L` of `Ω` itself (the note allows a phase). |

Theorem B is proved both by sequential truncation and by the physical
chain-sweep protocol. The latter has the following proved components:

| Protocol component | Formal statement | Status |
|---|---|---|
| Actual terminal main and auxiliary labels, owners and physical dimensions | `ChainSweep.mainOwner`, `auxiliaryOwner`, `physicalDimension` | Defined with every stage-and-side copy retained; scalar physical outputs occur at parties without main sites. |
| Block sizes, stage margins and party count | `ChainSweep.terminal_length_bounds`, `stage_right_margin`, `stage_left_margin`, `physicalDimension_le`, `card_party_le` | Proved for positive local dimension and width and `L ≥ 60w`; these are geometric bounds, not a count of constructed gates. |
| Product initialization | `ChainSweep.exists_initialization` | Proved: the actual main and auxiliary copies are prepared privately from a constructed product input, with no nonprivate gate. |
| Private terminal regrouping and its physical marginal | `ChainSweep.eval_terminalRegroupingWord`, `physicalDensity_terminalRegrouping` | Proved for every terminal vector, without a product or normalization premise, retaining all auxiliary labels and owners. |
| Terminal copy reference and conditional density error | `ChainSweep.terminalStackReadout_framesVec`, `partialTrace_terminalStackReference`, `rectangularTraceNorm_terminalStackReadout_sub_le` | Proved for the specified terminal frames and positive local dimension: the reference is `Ω ⊗ Ξ` for arbitrary `Ω`, and unit `Ω` gives unit `Ξ` and the pure main marginal. For unit `Ω`, a terminal vector of norm at most one and distance at most `ε` from that reference has density error at most `2ε`; this does not construct a sweep or establish its required vector-error bound. |
| One-band assignments and exact endpoints | `OneBand.main₈_eq_changeOwner`, `aux₄_eq_raw`, `exchange_regions` | Proved with half-open integer bands and the real open exchange window, including odd widths. The two retained auxiliary strips have their actual owners. |
| Eight one-band changes and the boundary death, under primitive information bounds | `OneBand.circuits_of_primitive_information`, `boundary_change_of_primitive_information` | Proved conditionally on the eight stated mutual-information inequalities for the original vector. Each circuit has the stated source, effect, coefficient and gate bounds; the exchange is private. These results do not derive the information inequalities from a gapped Hamiltonian. |
| Stage ownership and retired auxiliary copies | `ChainSweep.birth_environments`, `left_band_owners`, `rightBandMain_eq_stageFrame`, `rightRetiredAuxiliary_eq_raw`, `leftRetiredAuxiliary_eq_raw` | Proved from the actual stage assignments and margins, retaining the original stage-and-side copy labels. |
| Labelled history and chronological frame sequence | `ChainSweep.afterRightFrames_eq_sweepFrames`, `stageBoundaryFrames_eighteen`, `operationFrames_stageBoundary`, `operationFrames_step` | Proved for the specified eighteen-step stages, with one direct first-stage left death followed by seven unchanged boundaries. The zero-stage, one-stage and stationary terminal cases are included. This constructs frame lists, without supplying a circuit between them. |
| Prescribed stage incidence | `ChainSweep.participatingStageIndices_card_le_two`, `scheduledParticipationCount_le_thirtySix` | Proved for the specified participant sets: each party occurs in at most two stages and at most 36 prescribed positions. Actual circuit counts are a separate consequence. |
| Eighteen local circuits from primitive information | `ChainSweep.local_stage_circuits_of_primitive_information` | Proved under the nineteen written information premise forms for the original vector, with their zero-stage and positive-stage guards. Each actual successive-boundary circuit has at most one nonprivate gate and error at most `4 L^(-30)`; the seven first-stage padding circuits are identities. |
| Conditional chronological middle | `ChainSweep.sweepMiddleCircuit_participation_le_forty`, `sweepMiddleCircuit_nonprivateCount_le`, `sweepMiddleCircuit_resource_bounds`, `sweepMiddleCircuit_norm_and_error` | Proved from the same actual local family: lifetime at most 40, at most `18m` nonprivate occurrences, the recorded gate expansion bounds one, and error at most `4(18m)L^(-30)` for a unit original vector. Initialization and terminal readout are separate. |
| Derived gate support and tagged-link congestion | `ChainSweep.sweepMiddleCircuit_participants_subset_stage`, `sweepMiddleCircuit_participants_level_dist_le_two`, `prefixCrossingLinks_card_le_of_originalCircuit`, `compressedMiddle_prefixCrossingLinks_card_le_24960` | Proved: the actual middle gates lie in prescribed stage participant sets and have level distance at most two. For a tagged compression graph whose links share actual original gates and whose incident degree is at most 3120, every prefix has at most 24960 crossing links. The generic original-circuit version has bound `8d`; it does not assert that physical compression hypotheses have been discharged. |
| Cut rank of the distributed identity-bond network | `DependentBondNetwork.rank_flattening_network_one_le`, `DistributedOperatorContraction.rank_flattening_contractedOperator_column_le` | Proved for every party partition and every actual product-basis input column. The rank is bounded by the product of the alphabets of the tagged crossing links, each counted once. Varying and empty alphabets, loops and parallel links are included; placement and crossing counts are separate. These declarations belong to the corresponding `TNLean.PEPS` namespaces. |
| Conditional preparation including initialization and terminal readout | `ChainSweep.exists_preparation_of_local_circuits` | Proved from the actual conditional local family: one constructed product input and one full circuit, at most `18m` nonprivate gates, lifetime at most 40, expansion bounds one, norm at most one, vector error `4(18m)L^(-30)` from the retained-copy reference, and physical density error at most twice that error. Stage support and level distance at most two hold for every original nonprivate gate. |
| Three-party stage support | `ChainSweep.card_le_three_of_subset_stageParticipants` | Proved for every finite subset of the prescribed stage participants. Together with the full preparation support, each original nonprivate gate has at most three participants. |
| Separate arity and lifetime in physical compression | `Approximation.card_incidentDistributedLinks_le_of_arity_lifetime`, `PairEffect.DistributedConstruction.exists_uniform_sampled_network_sub_pure_le_of_arity_lifetime`, `ChainSweep.exists_physical_sampled_network_with_prefixCrossingLinks_le_1600` | Proved: the same sampled network retains its density error, polynomial alphabets and original-gate witnesses, with degree `2*b*(a-1)`. Physical chain data give degree 160 and at most 1280 crossing links at every prefix. No arity or crossing estimate is an additional physical hypothesis. |
| One compressed column for all cuts | `DistributedOperatorContraction.exists_useful_column_of_sub_pure_le`, `ChainSweep.exists_uniform_sampled_block_column` | Proved under the full uniform compression hypotheses and the original-gate distance bound. The polynomial alphabet constants precede all family members; for each member with error less than one, one nonzero actual column works for every prefix. With separate arity `a`, lifetime `b`, and `8*(2*b*(a-1)) <= chi`, its normalized cut ranks are at most `max(1,ceil(C_p L^alpha))^chi`. The generic useful-column declaration belongs to `TNLean.PEPS.Approximation`. |
| Original-site coordinates and cut ranks | `ChainSweep.rank_partyPrefix_eq_cutMatrix`, `rank_partyPrefix_last_eq_cutMatrix`, `rank_cutMatrix_le_of_partyPrefix_bounds` | Proved for the literal inverse main-coordinate vector. Under `q >= 1`, `w >= 1`, `60w <= L` and internal party-prefix ranks at most `R >= 1`, every original-site cut has rank at most `q^(40w) R`. Endpoint and scalar physical factors are retained; no vector normalization premise is needed. |
| Eight original-state information estimates for a band | `OneBand.primitive_separation`, `primitive_information_of_logarithmic_separation` | Proved from physical logarithmic separation, with constants chosen before every chain, state, width and owner assignment. No mutual-information estimate is an input. |
| Birth and first-death information | `ChainSweep.birth_death_separation`, `birth_death_information_of_logarithmic_separation` | Proved for the actual birth environments and the first after-death environment, for the same original ground vector. |
| Local stage circuits from the gapped Hamiltonian | `ChainSweep.local_stage_circuits_of_logarithmic_separation` | Proved with no supplied circuit or information bound. Every actual eighteen-step stage retains the seven first-stage identity circuits. |
| Complete physical preparation | `ChainSweep.exists_preparation_of_gappedGroundState` | Proved with constants before all physical instances: one product input and full circuit, lifetime at most 40, at most `20m <= 2L` nonprivate gates, at most three participants per nonprivate gate and level distance at most two. The vector error is at most `26 L^(-11)` and the standard physical-density error at most `52 L^(-11)`. Physical dimensions are at most `q^(80w) <= K L^s`, with `w = ceil(D log L) >= 1` and `60w <= L`. |
| Uniform physical preparation family | `ChainSweep.preparationConstruction`, `exists_uniform_preparation_family` | Proved for the family of every admissible sufficiently large length, Hamiltonian, ground vector and position map. All compression hypotheses, including arity three and lifetime forty, follow for the same circuit, normalized product input, physical order and standard physical marginal. |
| Polynomial original-site bond dimension | `ChainSweep.polynomial_bond_bound_of_ceil_width`, `isOpenMPS_of_polynomial_partyPrefix_bounds` | Proved for the same inverse-coordinate vector. For every natural `chi`, the prefactor is `q^40*(C_p+1)^chi` and the exponent is `max(1,ceil(40*D*log(q))+chi*alpha)`. Both ceiling corrections are retained; `q = 1`, zero compression prefactor and `chi = 0` are allowed. |
| Theorem B by the physical protocol | `ChainSweep.exists_protocol_isOpenMPS_norm_sub_phase_le` | Proved for `q >= 1` and `Delta > 0`, with `C > 0` and natural `n > 0` chosen before all lengths, Hamiltonians and ground vectors. Every `L >= 2` admits a unit, nonzero open-boundary MPS of bond dimension at most `C L^n` and phase error at most `1/L`. One normalized actual column gives all cuts; shorter lengths use exact representations with the same constants. |

The half-open
lattice bands and the distinction between main physical outputs and retained
auxiliary registers are recorded in
[`tnlean_one_dimensional_band_sweep_corrections.tex`](../paper-gaps/tnlean_one_dimensional_band_sweep_corrections.tex).
The one-band declarations belong to `TNLean.MPS.AreaLaw.OneBand`; the
remaining protocol declarations belong to `TNLean.MPS.AreaLaw.ChainSweep`.
The physical information estimates discharge the local information hypotheses,
and the full prepared family discharges the compression hypotheses. Compression
chooses one actual nonzero column before all cuts; its normalization and the
inverse main-coordinate vector give the same final MPS. The auxiliary reference
is a product by original copy, with no product requirement across final parties.
The physical proof uses arity three and lifetime forty of its constructed circuit.
For the same sampled network, the incident degree is at most 160 and every prefix
has at most 1280 crossing links, hence satisfies the printed bound 1600.
One column from that network gives all prefix ranks with exponent 1600. The broader finite-domain forms of the Part II analytic
estimates remain separate from this contiguous-chain proof.

## Analytic estimates for the physical protocol

For the commutator estimate in Part II, Lemma `lem:LR`,
`QuantumCircuit.norm_heisenberg_commutator_le_graphDistance_finset` proves
graph propagation from an arbitrary finite support S, with prefactor |S| and
constants independent of its diameter, the number of sites and the local
dimension. Its restricted-norm version is
`QuantumCircuit.heisenbergCommutatorNorm_le_graphDistance_finset`.
For support diameter R, support cardinality bound v_R and per-site norm budget
b₀, the explicit constants are C = 2 + 4|b₀| exp(2μR) and
v = 2v_R|b₀| exp(2μR) + 1, for μ ≥ 0.

For localization, under polynomial sphere growth K_g(d + 1)^k,
`QuantumCircuit.norm_heisenberg_sub_siteExpectation_graphNeighborhood_le`
bounds the error of the normalized partial trace onto the union of the radius-ℓ
balls about S by C |S|² ‖A‖ K_g T_k exp(v|t| − ℓ/2), for natural ℓ. Here
C and v are the preceding constants at μ = 1, and
T_k = 2^k k! exp(1/2) / (1 − exp(−1/2)). The pure graph tail estimate is
`QuantumCircuit.sum_exp_neg_edist_compl_graphBall_le`.
Neither result requires a diameter bound or nonemptiness assumption on S.

For the undoubled Hamiltonian on the contiguous chain,
`MPS.AreaLaw.ChainHamiltonian.sum_norm_terms_containing_le` proves the per-site
budget ∑_{X∋x} ‖h_X‖ ≤ 2^(2R+1) J, with the original real bound J.
No sign assumption is added: an actual site supplies the admissible singleton
{x}, whose norm bound implies J ≥ 0; the assertion is vacuous on an empty
chain.

The finite-path graph satisfies `SimpleGraph.pathGraph_edist`: its extended
distance is the absolute coordinate difference. The lemma
`SimpleGraph.pathGraph_card_sphere_le_two` bounds every distance sphere by
two sites, giving growth coefficient 2 and exponent 0 independently of the
chain length. These statements include the empty chain and all natural
radii. They concern the contiguous path; coordinate distance does not replace
graph distance across holes in a disconnected domain.

The matrix-entry condition for support is equivalent to membership in the
supported-operator algebra by `QuantumCircuit.mem_supportedOperators_of_isSupportedOn`
and its converse. The paired two-copy construction
`MPS.AreaLaw.ChainHamiltonian.doubled` keeps the same physical supports and
has local dimension q² and term bound 2J. The equality
`MPS.AreaLaw.ChainHamiltonian.doubled_operator` identifies its sum exactly
with H⊗1+1⊗H in paired coordinates.

On a contiguous chain, `MPS.AreaLaw.norm_heisenberg_commutator_le_chainDistance`
and `MPS.AreaLaw.norm_heisenberg_sub_siteExpectation_chainNeighborhood_le`
prove both estimates with common decay exponent μ = 1/2 and velocity
v = 2(R + 1)|b₀| exp(2R) + 1. The commutator coefficient is
C = 2 + 4|b₀| exp(2R); the localization coefficient is
C′ = 2C exp(1)/(1 − exp(−1/2)). Localization uses the exact closed neighborhood
at every real radius ℓ ≥ 0. Empty supports are allowed; their distance to a
site is infinity, with decay factor zero. Only localization requires q ≥ 1.
These are the chain estimates used in Part II. After the reduction to
connected domains, the note explicitly sets `Λ = {1, …, N}`
(`part1_arealaw.tex`, lines 91–93); Theorem B itself is stated on a chain.
Additional versions on arbitrary finite induced-path domains are not asserted;
see the connected-domain scope note. These chain estimates supply the physical
protocol above.

For an arbitrary region D of the contiguous chain,
`MPS.AreaLaw.IsChainSupport.exists_boundary_window_of_split` places every
split support in a window [p+1−R,p+1+R) about an actual boundary edge {p,p+1}.
`MPS.AreaLaw.card_crossingTerms_le_mul_card_boundaryEdges` therefore bounds
the number of such supports by 2^(2R)|∂D|, including zero range and empty
boundaries. The theorem
`MPS.AreaLaw.ChainHamiltonian.partialSwap_difference_eq_sum_crossing`
expresses the actual perturbation FĤF† − Ĥ as a sum of the two replica
terms over these crossing supports, with at most N_R|∂D| labelled terms.
Each difference is Hermitian, remains supported on its original support,
and has norm at most 2J by
`MPS.AreaLaw.ChainHamiltonian.partialSwap_term_difference_spec`.
The theorem `MPS.AreaLaw.ChainHamiltonian.partialSwap_boundary_spec` places
the perturbation on the actual union of crossing supports, within distance
R of the boundary positions, and bounds its norm by 2J N_R|∂D|.
These assertions retain the original real J and include the empty chain,
zero local dimension and zero range.

The model `MPS.AreaLaw.ChainHamiltonian.swappedDoubled` conjugates every
doubled interaction by the actual paired swap. It retains the same supports
and range, local dimension q² and term bound 2J; its operator identity is
`MPS.AreaLaw.ChainHamiltonian.swappedDoubled_operator`.
The theorem
`MPS.AreaLaw.ChainHamiltonian.doubled_swappedDoubled_isGappedGroundState`
constructs the two ground-state predicates for the actual paired tensor
square Ψ and its swap image Φ. Both vectors are normalized, have energy
2E₀ and inherit the lower gap Δ from the original ground-state predicate
and Δ > 0. No additional positivity or nonemptiness assumption is imposed.

The theorem
`MPS.AreaLaw.ChainHamiltonian.norm_relativeGenerator_sub_siteExpectation_le`
localizes the actual relative-evolution generator
G(t) = exp(itK′)(K′−K)exp(−itK′) onto the exact radius-ℓ neighborhood of Z.
Its error is bounded by 4|J| a (R+1)² N_R L exp(v|t|−ℓ/2), where a and v
are the explicit chain locality coefficients at per-site budget
b₀ = 2^(2R+1)(2J). The proof retains the sharper boundary-cardinality
estimate before bounding it by L. It applies to every real time and radius
ℓ ≥ 0, with q ≥ 1 for the normalized expectation, and needs no spectral
hypothesis. The individual crossing terms are localized before summation.

The existing generic theorem
`TNLean.PEPS.Approximation.exists_regional_physicalBuffer_filter` supplies the
two-sided Gaussian-filter estimates on any finite site set. The theorem
`MPS.AreaLaw.exists_supported_gaussian_integral` constructs a single projected
unitary evolution near Z, before the observable and Gaussian data, and then
the actual supported integral. Its norm is at most the observable norm, and
its error is bounded by C ‖W‖ L²(1+T) exp(vT−ℓ/2), with C,v chosen before
q and all system data and depending only on R,J. This operator is supported on
the exact radius-ℓ neighborhood of Q∪Z. Empty chains, zero variance and
zero cutoff are included. The geometric lemma
`MPS.AreaLaw.chain_reset_support_separation` proves the exact margin w−R
from both cores, using the actual crossing witnesses. The radius-ℓ
neighborhood of Q∪Z is disjoint from the cores whenever ℓ+R≤w. This
geometric statement allows empty cores and all real margins and radii,
without a quantum-state assumption.

The theorem `MPS.AreaLaw.ChainHamiltonian.information_reset` completes the
contiguous-chain information-reset argument. For every p > 0, it chooses
Cₚ > 0 and a natural L₀ ≥ 1 before the length, Hamiltonian, ground vector,
regions and mutual-information bound b. If D,C are disjoint, R₀ ⊆ D,
C₀ ⊆ C, I(D:C) ≤ b, and both cores have distance greater than
w = Cₚ(1+b+log L) from the corresponding complements, then
I(R₀:C₀) ≤ L^(−p) for L ≥ L₀. The proof derives b ≥ 0 and constructs the
Gaussian filter, its supported approximation, a unitary on the same support
and the product marginal after the actual regional replica swap. Only the
original full-system ground-state gap is assumed. The additive constant in
log(e q^|R₀|) is retained, including q = 1. This is the chain setting of
Part II. An additional version on an arbitrary finite induced-path domain is
not asserted; see the connected-domain scope note.

The theorem
`MPS.AreaLaw.ChainHamiltonian.mutualInformation_le_of_logarithmic_separation`
proves the contiguous-chain form of `lem:logsep`. For fixed p > 0 and
k₀ ≥ 1, it chooses Dₚ > 0 and a natural L₀ before all system data.
If T is a union of at most k₀ intervals and E is at pairwise coordinate
distance at least Dₚ log L from T, then I(T:E) ≤ L^(−p) for L ≥ L₀.
No disjointness, nonempty-region or sign hypothesis on J is added.
The exact neighborhood of each nonempty clipped interval expands its
endpoints by floor(ρ); empty intervals retain empty neighborhoods.
`MPS.AreaLaw.regionEntropy_chainNeighborhood_biUnion_intervals_le` bounds
the entropy of the actual enlarged union by the number of intervals times
the uniform interval bound, including overlaps. With c̄ = max(0,C_int),
b = 4k₀c̄ and w = Cₚ(1+b+log L), the proof uses the actual regions
D = N_(w+1)(T) and C = complement N_(2w+2)(T). Their mutual information
is at most 2S(D) ≤ b, and Dₚ = 3Cₚ(2+b)+3 gives both strict reset
margins once log L ≥ 1. `MPS.AreaLaw.ChainHamiltonian.norm_bound_nonneg`
supplies the sign of J from an actual singleton interaction.
These Part II estimates concern the chain used in Theorem B. Versions on
disconnected induced-path domains would be additional results and are not
claimed. The arbitrary-domain entropy theorem above is already proved.

## Constants

The area-law and sequential-truncation constants below are definitions of
`(q, R, J, Δ)` and, for the bond dimension, `L`. The separate compression
statements use existential polynomial constants. In the order the proof fixes
them:

| Name | Value |
|---|---|
| `chainCrossConst R` | `N_R = 2 · 2^{2R}` |
| `chainBudgetConst q R` | `B_R = 1 + N_R log²(e q^{R+1})` |
| `chainShellCount q R J Δ` | `m = ⌈max {4, 32 N_R q^{2(R+1)} J/Δ, 128 √((1 + J/Δ) B_R)}⌉` |
| `chainDiscountConst q R J Δ` | `4096 e (J/Δ) B_R / m + m log 2` |
| `chainIntervalEntropyBound q R J Δ` | `C_int = 8 m R log q + chainDiscountConst` |
| `chainAreaLawConst q R` | `C₀ = (8 R log q + log 2)(5 + 32 N_R q^{2(R+1)} + 128 B_R) + 1024 e B_R`, with `C_int ≤ C₀ (1 + J/Δ)` |
| `chainTruncationWidth q R J Δ L` | `w = 64 √((1 + J/Δ) B_R) log(2 L² √(2 e^{e/2}))` |
| `chainBondDimension q R J Δ L` | `⌊exp(C_int + w)⌋` |

The polynomial factor `q^{2(R+1)}` in `m` is the crude bound of the formal
buffer lemma; Remark 6.3 of the note explains how it can be replaced by
`log²(e q^{R+1})` with the three-lines device, which is not carried out here.


For the physical protocol, let `D >= 1` and `L0 >= 2` be the uniform width
constant and length cutoff, and let `Cp >= 0` and natural `alpha > 0` be the
uniform compression constants. The proof takes
`n = max(1,ceil(40 D log q) + 1600 alpha)` and
`C = max(q^40 (Cp + 1)^1600,q^L0)`.
The second term covers the finite lengths below the cutoff. The first term
retains the additive ones in both integer ceilings. These choices precede
the length, Hamiltonian and ground vector.
