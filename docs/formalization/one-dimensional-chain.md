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
| Lemma 4.2 (buffered discount) | `MPS.AreaLaw.two_mul_condEntropy_interval_le`, with `MPS.AreaLaw.chainShellCount` (`m`) and `MPS.AreaLaw.chainDiscountConst` | Proved. Shells of width `R` as in the note; the shell count uses the smaller of the note's energy threshold and the logarithmic one of Remark 6.3 (`Entropy.two_mul_condEntropy_le_logarithmic` in QICLean); energy threshold `Δ/2` in place of the note's `Δ/4`, overlap losses `m log 2` in place of the note's `2 C_E/Δ`, and the shell count omits the note's fourth entry `4096 e (1 + ϑ) B_R`, the term `4096 e ϑ B_R / m` staying explicit in the discount: `docs/paper-gaps/tnlean_one_dimensional_discount_constants.tex`. |
| Araki–Lieb closure, reductions (Section 2) | `Lattice.regionEntropy_le_union_add`, `MPS.AreaLaw.regionEntropy_le_mul_card_boundaryEdges_of_intervals` | Proved. |
| Theorem A for intervals | `MPS.AreaLaw.regionEntropy_interval_le` with the explicit `MPS.AreaLaw.chainIntervalEntropyBound` | Proved; no existential constant. |
| Theorem A, constant linear in `1 + J/Δ` | `MPS.AreaLaw.chainIntervalEntropyBound_le`, `MPS.AreaLaw.chainAreaLawConst` | Proved. |
| Theorem A for subsets of the chain | `MPS.AreaLaw.regionEntropy_le_mul_card_boundaryEdges`, `MPS.AreaLaw.chainAreaLaw` | Proved on the chain of `L` sites (connected domains). |
| Setting on a finite `Λ ⊂ ℤ` (induced path graph, `eq:ham`, `∂_Λ A`) | `MPS.AreaLaw.sitePos`, `MPS.AreaLaw.domainGraph`, `MPS.AreaLaw.IsDomainSupport`, `MPS.AreaLaw.DomainHamiltonian`, `MPS.AreaLaw.domainBoundaryEdges` | Definitions; the sites of `Λ` are labelled in increasing order. |
| Theorem A on a finite `Λ ⊂ ℤ`; first reduction (Section 2) | `MPS.AreaLaw.regionEntropy_le_mul_card_domainBoundaryEdges`, `MPS.AreaLaw.domainAreaLaw` | Proved, with the constant `C₀(q, R)(1 + J/Δ)` of the chain. The reduction uses the zero entropy of the prefixes ending at the gaps of `Λ` (`Lattice.regionEntropy_eq_zero_of_forall_subset_or_disjoint`) and flips of the region on them (`Lattice.regionEntropy_symmDiff_eq_of_eq_zero`) in place of the factorization over components: `docs/paper-gaps/tnlean_one_dimensional_connected_domain_scope.tex` (resolved). |
| Matrix product states, cut matrices | `MPS.AreaLaw.IsOpenMPS`, `MPS.AreaLaw.cutMatrix` | Definitions. |
| Cut ranks bound the bond dimension | `MPS.AreaLaw.isOpenMPS_of_cutMatrix_rank_le` | Proved. |
| Proposition 7.1 (sequential truncation) | `MPS.AreaLaw.exists_sequentialTruncation` | Threshold form proved: the projectors onto the eigenvalues at least `exp(-(S_k + w))` at a common slack `w`, with cut ranks at most `max 1 (exp(S_k + w))` and error `∑_k √tail_k(w)`. The note's form, projecting every cut onto its `D` largest eigenvalues (all of them when the cut has fewer) for an arbitrary bond dimension `D` with error `∑_k √ε_k(D)`, is not formalized; Theorem B uses only the threshold form: `docs/paper-gaps/tnlean_one_dimensional_threshold_truncation.tex`. |
| Theorem B | `MPS.AreaLaw.exists_isOpenMPS_norm_sub_le` with `MPS.AreaLaw.chainBondDimension`; polynomial form `MPS.AreaLaw.chainBondDimension_le_mul_rpow` | Proved; the bond dimension is `⌊exp(C_int + w(L))⌋ ≤ e^{C_int} (2 c₀)^{64 s} L^{128 s}` with `s = √((1 + J/Δ) B_R)`. The approximant is normalized and within `1/L` of `Ω` itself (the note allows a phase). |

The protocol route of the note (information reset, births, exchanges, the sweep
and the compression) is not formalized; Theorem B is proved by the two-line route
alone.

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
graph distance across holes in a disconnected domain. Operator-support
conversion and doubled-Hamiltonian transport needed for the protocol's
Lieb–Robinson estimate remain separate.

## Constants

Every constant is a definition of `(q, R, J, Δ)` and, for the bond dimension,
`L`; no statement carries an existential constant. In the order the proof fixes
them:

| Name | Value |
|---|---|
| `chainCrossConst R` | `N_R = 2 · 2^{2R}` |
| `chainBudgetConst q R` | `B_R = 1 + N_R log²(e q^{R+1})` |
| `chainEnergyThreshold q R J Δ` | `E_R J/Δ` with `E_R = min {32 N_R q^{2(R+1)}, 64 e N_R log²(e q^{R+1})}` |
| `chainShellCount q R J Δ` | `m = ⌈max {4, E_R J/Δ, 128 √((1 + J/Δ) B_R)}⌉` |
| `chainDiscountConst q R J Δ` | `4096 e (J/Δ) B_R / m + m log 2` |
| `chainIntervalEntropyBound q R J Δ` | `C_int = 8 m R log q + chainDiscountConst` |
| `chainAreaLawConst q R` | `C₀ = (8 R log q + log 2)(5 + E_R + 128 B_R) + 1024 e B_R`, with `C_int ≤ C₀ (1 + J/Δ)` |
| `chainTruncationWidth q R J Δ L` | `w = 64 √((1 + J/Δ) B_R) log(2 L² √(2 e^{e/2}))` |
| `chainBondDimension q R J Δ L` | `⌊exp(C_int + w)⌋` |

The energy constant `E_R` takes the smaller of two estimates of the energy of
the filtered vector: the squared-dimension bound, which gives the polynomial
factor `q^{2(R+1)}`, and the three-lines bound of Remark 6.3 of the note,
which replaces it by `2 e log²(e q^{R+1})`. The second is smaller once
`q^{R+1}` is moderately large, and makes `m` and `C₀` of order
`(1 + J/Δ) B_R` and `R log q (1 + J/Δ) B_R`.
