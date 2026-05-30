# Status of Erickson's CPSV16 FT/BNT comments (checked 2026-05-30)

The three analysis documents in this directory date from 2026-05-13 and were
written against the **one-copy `IsCanonicalFormBNT`** surface (with
`mu_strict_anti` / `mu_dom_norm_one`) and the **non-dominant projection /
Plan-A** roadmap. Both have since been **retired and replaced** by the
multi-copy sector structure. Those documents are therefore **superseded as
architecture descriptions**; they are kept as the record that prompted the
overhaul. This note records the current resolution of each concern.

Superseded documents:
- `cpsv16_fundamental_theorem_analysis.md`
- `cpsv16_ft_expanded_proof.tex`
- `cpsv16_bnt_gap_recommendation_examples.tex`

## Item-by-item resolution

| # | Erickson's concern | Current status | Where |
|---|---|---|---|
| 1 | The FT proof should be a per-block existence argument plus injectivity from BNT **minimality**, not a peel-induction needing **combined-family** linear independence. | **Resolved.** `bijective_match_of_sameMPV` routes forward/backward injectivity through `basis_distinct` (minimality), and `combined_family_eventually_li` is used only for coefficient isolation, not a shrinking-pair recursion. | `SectorBNT/StrongMatch.lean`, `SectorBNT/Api.lean` |
| 2 | The one-copy surface (one weight per sector, strict modulus ordering) is weaker than the paper's multi-copy BNT sector with power-sum coefficients $c_N^{(j)}=\sum_q \mu_{j,q}^N$. | **Resolved.** The one-copy `IsCanonicalFormBNT` (with `mu_strict_anti`) is retired; the current `SectorDecomposition` carries the raw power-sum coefficient. Equal-modulus copies ($C\oplus(-C)$) and unequal ($C\oplus\tfrac12 C$) are both represented. | `SharedInfra/SectorDecomposition.lean`, `SectorBNT/Api.lean` (`coeff_eq_sum_weight_pow`) |
| 3 | The dominant-block projection argument fails for non-dominant blocks (both sides decay to $0=0$); use combined-family linear independence + exact coefficient comparison instead. | **Resolved.** The projection route is abandoned. The blueprint states it explicitly: "No projection-limit argument for non-dominant sectors is used." Non-decay comes from the Cesàro lemma. | ch11 intro; `SectorBNT/CesaroNonDecay.lean` (`sum_pow_not_tendsto_zero_of_unit_modulus`) |
| 4 | The ~530-line Plan-A workaround (dominant-adjusted scalar, `finOne` base cases, discrete-rate $\delta_N$ upgrade) was wasted effort; N=0 / zero-tail handling consumed disproportionate effort. | **Resolved.** Plan-A deleted (the `Full/` directory is empty). Residual N=0 / zero-tail bloat cleaned: `SameMPV₂Pos` threaded through the after-blocking chain and the dead zero-tail/common-flat sub-chain removed. | PRs #2153, #2159; commit `1e63d981c` |
| 5 | Vandermonde non-decay of $\sum_q \mu_q^N$ needed a Lean realization. | **Resolved.** Provided by the Cesàro non-decay lemma for unit-modulus sums. | `SectorBNT/CesaroNonDecay.lean` |
| 6 | The matching/equal-MPV theorems carry a **per-sector** unit-modulus hypothesis stronger than CPSV16's single **global** witness (line 246). | **Documented.** Recorded as a scope restriction with an elimination plan; the affected declarations are listed. | `docs/paper-gaps/cpsv16_global_vs_persector_unit_witness.tex` (commit `4605b9381`) |
| 7 | Lemma A.2's $X^\dagger X = c\,\Id$ rescaling is elided in the source ("$=\mathbf 1$"); the Lean should carry the $c\,\Id$ fixed-point conclusion and rescale at the end. | **Needs confirmation (minor).** The gauge-phase extraction lives in the irreducible/primitive fixed-point modules; confirm it carries the scalar-fixed-point conclusion rather than assuming $X^\dagger X=\Id$. Not a blueprint defect. | `MPS/Irreducible/`, `SectorBNT/Supplier.lean` |
| 8 | The proportional ($c_N\neq1$) FT still needs the matched-coefficient identity $c_N^{(\beta(k))}(P)=\zeta_k^N c_N^{(k)}(Q)$ **derived**, not assumed. | **Open — active work.** The source theorems (Cor II.1, Cor II.2) are honestly `\notready`; the conditional theorems take the identity as a hypothesis. Tracked by **issue #1749**. | `SectorBNT/Fundamental.lean`, `SectorBNT/CoeffIdentity.lean` |

## Summary

Erickson's substantive structural recommendations are **implemented**: the
multi-copy sector decomposition (2), abandoning the non-dominant projection
argument (3) in favour of combined-family linear independence and Cesàro
non-decay (5), and the per-block-existence-plus-minimality matching structure
(1). The N=0 / Plan-A waste (4) is cleaned. The per-sector-vs-global unit
witness (6) is documented as a tracked scope restriction. The one remaining
genuine gap is the proportional matched-coefficient identity (8), which is
active work under issue #1749, with the source theorems honestly marked
`\notready`.
