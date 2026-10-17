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
| Theorem A for subsets | `MPS.AreaLaw.regionEntropy_le_mul_card_boundaryEdges`, `MPS.AreaLaw.chainAreaLaw` | Proved on the chain of `L` sites (connected domains). The component reduction of the note to disconnected finite subsets of the integers is not formalized: `docs/paper-gaps/tnlean_one_dimensional_connected_domain_scope.tex`. |
| Matrix product states, cut matrices | `MPS.AreaLaw.IsOpenMPS`, `MPS.AreaLaw.cutMatrix` | Definitions. |
| Cut ranks bound the bond dimension | `MPS.AreaLaw.isOpenMPS_of_cutMatrix_rank_le` | Proved. |
| Proposition 7.1 (sequential truncation) | `MPS.AreaLaw.exists_sequentialTruncation` | Threshold form proved: the projectors onto the eigenvalues at least `exp(-(S_k + w))` at a common slack `w`, with cut ranks at most `max 1 (exp(S_k + w))` and error `∑_k √tail_k(w)`. The note's form, projecting every cut onto its `D` largest eigenvalues (all of them when the cut has fewer) for an arbitrary bond dimension `D` with error `∑_k √ε_k(D)`, is not formalized; Theorem B uses only the threshold form: `docs/paper-gaps/tnlean_one_dimensional_threshold_truncation.tex`. |
| Theorem B | `MPS.AreaLaw.exists_isOpenMPS_norm_sub_le` with `MPS.AreaLaw.chainBondDimension`; polynomial form `MPS.AreaLaw.chainBondDimension_le_mul_rpow` | Proved; the bond dimension is `⌊exp(C_int + w(L))⌋ ≤ e^{C_int} (2 c₀)^{64 s} L^{128 s}` with `s = √((1 + J/Δ) B_R)`. The approximant is normalized and within `1/L` of `Ω` itself (the note allows a phase). |

Information reset is proved on the contiguous chain. Births, exchanges, the
sweep and the protocol compression remain unformalized; Theorem B is proved
by the two-line route alone.

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
These are the contiguous-chain estimates needed in the matrix product state
argument. The broader finite-domain reading of the source lemma remains
separate, as recorded in the connected-domain scope note. The full protocol
construction is also separate.

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
log(e q^|R₀|) is retained, including q = 1. The broader finite-domain reading
of the source remains open, as recorded in the connected-domain scope note.

## Constants

Every constant in the chain area-law and sequential-truncation bounds is a
definition of `(q, R, J, Δ)` and, for the bond dimension, `L`; these statements
carry no existential constant. In the order the proof fixes
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
