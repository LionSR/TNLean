# One-dimensional area law and matrix product state approximation

This document records the Lean statements of the one-dimensional specialization
of the September 24, 2026 manuscripts *A two-dimensional area law from a global
spectral gap* and *Polynomial PEPS approximation of gapped square-grid ground
states*, following the repository note
[`docs/notes/one_dimensional_note`](../notes/one_dimensional_note/one_dimensional_area_law_and_mps.tex)
(Theorems A and B there). The modules live in `TNLean/PEPS/AreaLaw/Chain/` and
the blueprint chapter is `blueprint/src/chapter/ch35_one_dimensional_chain.tex`.

A chain is a one-row domain `Λ ⊂ ℤ × {0}` of the finite-domain model
([`openai-area-law-peps.md`](openai-area-law-peps.md)): the Hamiltonians,
gapped ground vectors and regional entropies are those of the two-dimensional
development, with no new physical definitions. The finite-dimensional cores
(the marginal tail bound and the buffered discount) are the QICLean lemmas that
the two-dimensional buffer lemma also uses; the chain modules supply their
one-dimensional hypotheses and close the argument.

## Statements

| Note statement | Formal statement | Status |
|---|---|---|
| Setting: one-row domains, the chain of `L` sites, intervals | `Chain.IsOneRow`, `Chain.chainDomain`, `Chain.interval`, `Chain.chainSiteEquiv` | Definitions. |
| `eq:count`, `eq:BR`: split interactions and cut budget of an interval | `Chain.card_crossingTerms_interval_le` (`N_R = 2(R+1)μ_R`), `Chain.cutLogBudget_interval_le` (`B_R`) | Proved. The count goes through the sites near the two cut edges, as in the two-dimensional crossing count, so `N_R` differs from the note's `2·4^R`. |
| Lemma 4.2 (buffered discount) | `Chain.two_mul_condEntropy_interval_le`, with `Chain.chainShellCount` (`m`) and `Chain.chainDiscountConst` | Proved. Shells of width `R + 1` and energy threshold `Δ/2`, as in the formal finite-dimensional lemma; the note uses width `R` and threshold `Δ/4`. |
| Araki–Lieb closure, reductions (Lemma 2.1) | `Chain.regionalEntropy_le_union_add`, `Chain.regionalEntropy_le_mul_card_edgeBoundary_of_intervals` | Proved. |
| Theorem A for intervals | `Chain.regionalEntropy_interval_le` with the explicit `Chain.chainIntervalEntropyBound` | Proved; no existential constant. |
| Theorem A, constant linear in `1 + J/Δ` | `Chain.chainIntervalEntropyBound_le`, `Chain.chainAreaLawConst` | Proved. |
| Theorem A for subsets of the chain | `Chain.regionalEntropy_le_mul_card_edgeBoundary`, `Chain.chainUniformAreaLaw` | Proved. The latter is the statement of the two-dimensional target `UniformAreaLaw` restricted to chains, with its constant exhibited. |
| Matrix product states, cut matrices | `Chain.IsOpenMPS`, `Chain.cutMatrix`, `Chain.IsChainMPS` | Definitions. |
| Cut ranks bound the bond dimension | `Chain.isOpenMPS_of_cutMatrix_rank_le` | Proved. |
| Proposition 7.1 (sequential truncation) | `Chain.exists_sequentialTruncation` | Proved, with the error `∑_k √ε_k` of the note. |
| Theorem B | `Chain.exists_isChainMPS_norm_sub_le` with `Chain.chainBondDimension`; polynomial form `Chain.chainBondDimension_le_mul_rpow` | Proved; the bond dimension is `⌊exp(C_int + w(L))⌋ ≤ e^{C_int} (2 c₀)^{64 s} L^{128 s}` with `s = √((1 + J/Δ) B_R)`. |

The protocol route of the note (information reset, births, exchanges, the sweep
and the compression) is not formalized; Theorem B is proved by the two-line route
alone.

## Constants

Every constant is a definition of `(q, R, J, Δ)` and, for the bond dimension,
`L`; no statement carries an existential constant. In the order the proof fixes
them:

| Name | Value |
|---|---|
| `chainCrossConst R` | `N_R = 2 (R + 1) 2^{v_R - 1}`, `v_R = 1 + 2R(R + 1)` |
| `chainBudgetConst q R` | `B_R = 1 + N_R log²(e q^{v_R})` |
| `chainShellCount q R J Δ` | `m = ⌈max {4, 32 N_R q^{2 v_R} J/Δ, 128 √((1 + J/Δ) B_R)}⌉` |
| `chainDiscountConst q R J Δ` | `4096 e (J/Δ) B_R / m + m log 2` |
| `chainIntervalEntropyBound q R J Δ` | `C_int = 8 m (R + 1) log q + chainDiscountConst` |
| `chainAreaLawConst q R` | `C₀ = (8 (R + 1) log q + log 2)(5 + 32 N_R q^{2 v_R} + 128 B_R) + 1024 e B_R`, with `C_int ≤ C₀ (1 + J/Δ)` |
| `chainTruncationWidth q R J Δ L` | `w = 64 √((1 + J/Δ) B_R) log(2 L² √(2 e^{e/2}))` |
| `chainBondDimension q R J Δ L` | `⌊exp(C_int + w)⌋` |

The polynomial factor `q^{2 v_R}` in `m` is the crude bound of the formal
buffer lemma; Remark 6.3 of the note explains how it can be replaced by
`log²(e q^{v_R})` with the three-lines device, which is not carried out here.
