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
| 3 | The dominant-block projection argument fails for non-dominant blocks (both sides decay to $0=0$); use combined-family linear independence + exact coefficient comparison instead. | **Resolved.** The projection route is abandoned. The blueprint states it explicitly: "No projection-limit argument for non-dominant sectors is used." Non-decay is supplied by `coeff_not_eventually_zero` (BNT linear independence; no modulus assumption), replacing the former Cesàro lemma. `SectorBNT/CesaroNonDecay.lean` was deleted in the exact-route cleanup (PR #2257). | ch11 intro; `SectorBNT/ExactMatch.lean` |
| 4 | The ~530-line Plan-A workaround (dominant-adjusted scalar, `finOne` base cases, discrete-rate $\delta_N$ upgrade) was wasted effort; N=0 / zero-tail handling consumed disproportionate effort. | **Resolved.** Plan-A deleted (the `Full/` directory is empty). Residual N=0 / zero-tail bloat cleaned: `SameMPV₂Pos` threaded through the after-blocking chain and the dead zero-tail/common-flat sub-chain removed. | PRs #2153, #2159; commit `1e63d981c` |
| 5 | Vandermonde non-decay of $\sum_q \mu_q^N$ needed a Lean realization. | **Resolved (differently).** The Cesàro non-decay lemma (`sum_pow_not_tendsto_zero_of_unit_modulus`) was written and used in the asymptotic route, but both that lemma and the asymptotic route were retired when the exact matcher was adopted. Non-decay is now supplied by `coeff_not_eventually_zero` with no modulus assumption; `SectorBNT/CesaroNonDecay.lean` was deleted in PR #2257. | `SectorBNT/Basic.lean` (`coeff_not_eventually_zero`) |
| 6 | The matching/equal-MPV theorems carry a **per-sector** unit-modulus hypothesis stronger than CPSV16's single **global** witness (line 246). | **Documented.** Recorded as a scope restriction with an elimination plan; the affected declarations are listed. | `docs/paper-gaps/cpsv16_global_vs_persector_unit_witness.tex` (commit `4605b9381`) |
| 7 | Lemma A.2's $X^\dagger X = c\,\Id$ rescaling is elided in the source ("$=\mathbf 1$"); the Lean should carry the $c\,\Id$ fixed-point conclusion and rescale at the end. | **Needs confirmation (minor).** The gauge-phase extraction lives in the irreducible/primitive fixed-point modules; confirm it carries the scalar-fixed-point conclusion rather than assuming $X^\dagger X=\Id$. Not a blueprint defect. | `MPS/Irreducible/`, `SectorBNT/Supplier.lean` |
| 8 | The proportional ($c_N\neq1$) FT still needs the matched-coefficient identity $c_N^{(\beta(k))}(P)=\zeta_k^N c_N^{(k)}(Q)$ **derived**, not assumed. | **Resolved (PR #2254).** `MPSTensor.fundamentalTheorem_proportional_canonicalForm` is proved with no per-sector unit-modulus hypothesis and no coefficient-limit / Cesàro route. The mechanism is the exact fixed-length matcher (`exists_block_match_exact_of_eventuallyProportional`): the proportionality scalar $c_N$ rescales only the aggregate $Q$-side coefficients, so the isolated $P$-coefficient is detected by `coeff_not_eventually_zero` without any per-sector modulus assumption. Blueprint `thm:cpgsv_multiblock_ft_source` (ch11) flipped to `\leanok`. | `SectorBNT/FundamentalCoord.lean` (`MPSTensor.fundamentalTheorem_proportional_canonicalForm`) |

## Summary

Erickson's substantive structural recommendations are **implemented**: the
multi-copy sector decomposition (2), abandoning the non-dominant projection
argument (3) in favour of combined-family linear independence and exact
coefficient comparison via `coeff_not_eventually_zero` (5), and the
per-block-existence-plus-minimality matching structure (1). The N=0 / Plan-A
waste (4) is cleaned. The per-sector-vs-global unit witness (6) is now fully
resolved: the exact matcher requires no per-sector unit-modulus hypothesis;
see `cpsv16_global_vs_persector_unit_witness.tex` for the current declaration
path. Item (8), the proportional matched-coefficient identity, is also
resolved: `MPSTensor.fundamentalTheorem_proportional_canonicalForm` is proved
without the per-sector or coefficient-limit assumptions (PR #2254). Both
headline CPSV16 results (Theorem II.1 and Corollary II.2) are now `\leanok`
in the blueprint.
