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
| Matrix product states, cut matrices | `MPS.AreaLaw.IsOpenMPS`, `MPS.AreaLaw.cutMatrix` | Definitions. |
| Cut ranks bound the bond dimension | `MPS.AreaLaw.isOpenMPS_of_cutMatrix_rank_le` | Proved. |
| Growth between two cuts | `MPS.AreaLaw.rank_cutMatrix_add_le`, `rank_cutMatrix_le_add`, `rank_cutMatrix_le_pow_min_mul`, `rank_cutMatrix_le_pow_forty_mul` | Proved for arbitrary vectors: moving `d` sites across a cut costs at most `q^d` in either direction. Endpoint rank bounds `R` on an interval of length at most `80w` give internal ranks at most `q^(40w) R` when `q ≥ 1`. The endpoint bounds remain hypotheses of this auxiliary result. |
| Proposition 7.1 (`prop:VC`, sequential truncation at prescribed bond dimension) | `MPS.AreaLaw.prefixBasisProjection`, `MPS.AreaLaw.isOpenMPS_sequentialTruncation_prefixBasisProjection` | Proved for every vector and every ordered orthonormal basis at the internal cuts, for all natural `L`, `q` and `D`. The defined product has internal bond dimensions at most `D`, and its error is bounded by the original discarded expectations. Specialization to any ordered marginal eigenbasis gives the source statement, including all choices within degenerate eigenspaces. The former threshold restriction is resolved: `docs/paper-gaps/tnlean_one_dimensional_threshold_truncation.tex`. |
| Sequential truncation at an entropy threshold | `MPS.AreaLaw.exists_sequentialTruncation` | Proved, as a separate statement: eigenvalues at least `exp(-(S_k + w))` are retained, with cut ranks at most `max 1 (exp(S_k + w))` and error `∑_k √tail_k(w)`. The threshold and prescribed-dimension projectors need not coincide; see `docs/paper-gaps/tnlean_one_dimensional_threshold_truncation.tex`. |
| Prefix-cut projection bounds in the proof of Theorem B | `MPS.AreaLaw.ChainHamiltonian.spectralProjectionGE_leftBlock_bounds` | Proved for every natural cut index and `w ≥ 0`: the actual reduced state's projection at `exp(-(C_int + w))` has rank at most `exp(C_int + w)` and discarded mass at most `2 exp(e/2) exp(-w/(32 s))`, where `s = √((1 + J/Δ) B_R)`. |
| Approximation at prescribed accuracy, by the argument for Theorem B | `MPS.AreaLaw.exists_isOpenMPS_norm_sub_le_of_error` | Proved for `0 < ε ≤ 1`, with a normalized approximant and bond bound `⌊exp(C_int + 64 s log(2 L c₀ / ε))⌋`, where `s = √((1 + J/Δ) B_R)` and `c₀ = √(2 exp(e/2))`. |
| Theorem B | `MPS.AreaLaw.exists_isOpenMPS_norm_sub_le` with `MPS.AreaLaw.chainBondDimension`; polynomial form `MPS.AreaLaw.chainBondDimension_le_mul_rpow` | Proved; the bond dimension is `⌊exp(C_int + w(L))⌋ ≤ e^{C_int} (2 c₀)^{64 s} L^{128 s}` with `s = √((1 + J/Δ) B_R)`. The approximant is normalized and within `1/L` of `Ω` itself (the note allows a phase). |

Theorem B is proved by the sequential-truncation argument. The separate
protocol route has the following proved intermediate results:

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
| Cut rank of the distributed identity-bond network | `DependentBondNetwork.rank_flattening_network_one_le`, `DistributedOperatorContraction.rank_flattening_contractedOperator_column_le` | Proved for every party partition and every actual product-basis input column. The rank is bounded by the product of the alphabets of the tagged crossing links, each counted once. Varying and empty alphabets, loops and parallel links are included; placement and crossing counts are separate. These declarations belong to the corresponding `TNLean.PEPS` namespaces. |

The half-open
lattice bands and the distinction between main physical outputs and retained
auxiliary registers are recorded in
[`tnlean_one_dimensional_band_sweep_corrections.tex`](../paper-gaps/tnlean_one_dimensional_band_sweep_corrections.tex).
The one-band declarations belong to `TNLean.MPS.AreaLaw.OneBand`; the
remaining protocol declarations belong to `TNLean.MPS.AreaLaw.ChainSweep`.
Deriving the physical information inequalities, assembling the complete sweep
circuit, proving its total gate and participation counts and accumulated error,
and applying compression remain separate obligations. The frame identities
identify the required terminal memory; they do not by themselves construct
a circuit reaching it.

## Constants

Every constant is a definition of `(q, R, J, Δ)` and, for the bond dimension,
`L`; no statement carries an existential constant. In the order the proof fixes
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
