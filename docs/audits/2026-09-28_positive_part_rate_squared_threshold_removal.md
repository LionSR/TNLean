# Squared-rate threshold replaced by the rate threshold for every γ < 1

This audit records the removal of one theorem. It is the audit note required by
`docs/project_conventions.md` §Style. All non-`Archive` uses are migrated, no
blueprint `\lean{...}` tag cites the removed name, and no compatibility alias is
kept.

## Removed declaration and its replacement

In `TNLean/MPS/Preparation/PositivePartRate.lean`:

- `MPSTensor.lt_exp_neg_div_correlationLength_sq`: for `0 < γ < 1/2`, every
  `a < 1` with `a ≤ |λ₂|` satisfies `a < (e^{-γ/ξ})²`.

Replacement: `MPSTensor.lt_exp_neg_div_correlationLength`, in the same file:
for `0 < γ < 1`, every `a < 1` with `a ≤ |λ₂|` satisfies `a < e^{-γ/ξ}`.

The two statements differ, so this is not a rename. The old threshold served a
transfer-map rate at `2γ`, which the Hölder bound `‖√X - √Y‖ ≤ √‖X - Y‖`
(arXiv:2103.13367, Supplemental Material, eq. `eq:intermediate`) then halved to
a positive-part rate at `γ`, forcing `γ < 1/2`. The positive-part rate now
comes from the Lipschitz bound for the square root at a positive-definite
point (`IsStrictlyPositive.exists_norm_sqrt_sub_sqrt_le`), which loses no
exponent. So the transfer-map rate is needed only at `γ` itself, for every
`γ < 1`. The one use, in the proof of
`MPSTensor.exists_norm_transferMap_pow_sub_le`, now calls the replacement.

The approximation-error argument (`MPSTensor.exists_approximationError_le`)
calls the normalization bound `MPSTensor.exists_abs_norm_mpvState_sq_sub_one_le`
at the rate `γ` itself, `|‖φ_N‖² - 1| ≤ K e^{-γN/ξ}`. The second-order rate
`e^{-2γq/ξ}` of the error then comes from `N = Mq ≥ 2q` when `M ≥ 2`, with the
case `M = 1` treated separately; the rewriting of `e^{-2γ/ξ}` as `(e^{-γ/ξ})²`
uses `MPSTensor.exp_neg_two_mul_div_correlationLength`.
