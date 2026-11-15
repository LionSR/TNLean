# Gaussian-filter integral splitting

Base: main `eb588dc15332a3798431015e6c27ecbaf329b2d1`, pinned Mathlib `625d8914199bc567cca9b91f90e8e5afafa5ae51`.

- Three repeated indicator/integrability calculations now use Mathlib's `integral_add_compl`, `norm_setIntegral_le_of_norm_le_const` and the weighted `norm_integral_le_of_norm_le` directly. The same decomposition already appears in GaussianNegativeFrequencyLocality; no new lemma or tactic is introduced.
- The weighted increment retains the integrable absolute-time envelope and the original commutator estimate. Explicit measure arguments fix the restricted measures before finiteness goals are elaborated.
- All 18 public declaration headers, all imports, constants and Blueprint anchors are unchanged. The mass-level theorem retains arbitrary real filter parameters and empty windows when T is negative; zero variance and every existing positivity premise keep their original scope.
- Locality decreases from 193 to 175 lines, truncation from 435 to 418 and increment from 197 to 187: net minus 45 Lean lines. This dated pattern record leaves the occupied central tactic ledger untouched.
- Header/import equality, integrity/prose/line-length/whitespace checks and focused tactic scanning pass. Pinned API inspection and read-only proof review found no concrete mismatch. Local Lean/Lake/cache are unavailable; hosted compiler and linter acceptance remain pending.
