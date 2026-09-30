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

Where the approximation-error argument still needs a rate at `2γ` for the
normalization, it rewrites `e^{-2γ/ξ}` as `(e^{-γ/ξ})²` with the new
`MPSTensor.exp_neg_two_mul_div_correlationLength`.
