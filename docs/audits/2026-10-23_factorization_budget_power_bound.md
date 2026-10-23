# The power bound of the Lemma 1 error budget

This audit records one public declaration removed from
`TNLean/MPS/AreaLaw/Hastings/FactorizationBudget.lean`. It is the audit note required by
`docs/project_conventions.md` §Style. Every non-`Archive` use on `main` has been migrated, no
open pull request uses the removed name, no blueprint `\lean{...}` tag cites it, and no
compatibility alias is kept.

## Removed declarations

| Removed | Replacement |
|---|---|
| `TNLean.MPS.AreaLaw.Hastings.pow_mul_exp_neg_div_sixteen_le` | `TNLean.MPS.AreaLaw.Hastings.pow_mul_exp_neg_add_le` with `r = 1/48`, `δ = 1/24` |

The removed lemma bounded `x^n e^{-x/16}` by `48^n n! e^{-x/48}`. The replacement gives
`(24n/e)^n e^{-x/48}`. The error budget uses only `n = 1` and `n = 4`, where `e ≥ 2` gives
`24/e ≤ 48` and `(96/e)^4 ≤ 48^4 · 24`, so the constants of `errorBudget_twoMu_div_le` and
`errorBudget_boundary_le` are unchanged.
