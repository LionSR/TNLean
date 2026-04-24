# Issue #778 — resolvent Hansen-compression endpoint

## Scope

Follow-up to `audits/2026-04-22_issue138_op_convexity_blocker.md` for issue
#778 (operator Jensen package for Wolf Corollary 5.2). This pass adds the
explicit *diagonal-inverse rewrite* and the *resolvent Hansen-compression
bound* flagged by the earlier audit as the remaining unfinished algebraic
step on the finite-POVM compression side.

No change was made to the three Cor. 5.2 declarations in
`TNLean/Channel/Schwarz/OperatorMonotone.lean`; they still depend on the
three axioms in `TNLean/Axioms/OperatorConvexity.lean`.

## What landed

Two new lemmas in `TNLean/Channel/Schwarz/OperatorJensenAux.lean`:

* `TNLean.OperatorJensen.povmDiagonal_inv` — the pointwise inverse identity
  $(\operatorname{diag}(w_i, t))^{-1} = \operatorname{diag}(w_i^{-1}, t^{-1})$
  for strictly positive weights.
* `TNLean.OperatorJensen.povm_resolvent_compression_le` — the resolvent
  bound
  $$
  \Bigl(\sum_i w_i\, C_i C_i^{\dagger} + t\, S S^{\dagger}\Bigr)^{-1}
  \le
  \sum_i w_i^{-1}\, C_i C_i^{\dagger} + t^{-1}\, S S^{\dagger},
  $$
  valid whenever $\sum_i C_i C_i^{\dagger} + S S^{\dagger} = 1$ and all
  weights are strictly positive. The proof combines the four existing
  ingredients: `povmIsometry_star_mul`, `povmIsometry_compress_diagonal`,
  `povmDiagonal_inv`, and `Matrix.PosDef.inverse_compression_le`.

Both lemmas are honest proofs. No new `sorry`, `admit`, `axiom`,
`native_decide`, or proof-integrity workaround was introduced.

## What remains blocked

The three target declarations

* `IsPositiveMap.cor52_item1_rpow_of_subunital`
* `IsPositiveMap.cor52_item2_rpow_of_subunital`
* `IsPositiveMap.cor52_item3_log_of_subunital`

are still gated by the three axioms

* `posMap_rpow_concave_jensen`
* `posMap_rpow_convex_jensen`
* `posMap_log_concave_jensen`

in `TNLean/Axioms/OperatorConvexity.lean`. Upstream Mathlib v4.29 still
carries the TODOs that block a genuine discharge:

* operator concavity of `rpow` on $[0,1]$ and operator convexity of `rpow`
  on $[1,2]$ are flagged as TODOs in
  `Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Order.lean`;
* operator concavity of `log` is flagged as a TODO in
  `Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog/Order.lean`;
* a general operator Jensen theorem for positive (sub)unital maps is
  absent from Mathlib.

## How the new endpoint fits the proof plan

The Hansen--Pedersen operator Jensen inequality factors through a
compression/resolvent step. The finite-POVM side of that compression is now
closed modulo the Löwner integral representation of `rpow`:

1. Reduce the operator Jensen inequality for a positive subunital map to the
   Hansen compression inequality via the POVM dilation `povmIsometry`
   (already in `OperatorJensenAux.lean`).
2. Reduce the Hansen compression inequality on `rpow` to the resolvent
   Hansen-compression bound via the Löwner integral representation
   $x^p = C_p \int_0^\infty t^{p-1}\, x(x+t)^{-1}\,dt$.
   This step is the remaining Mathlib gap
   (`CFC.Rpow.IntegralRepresentation`).
3. Verify the resolvent bound by combining the POVM dilation with the
   inverse-of-compression/compression-of-inverse inequality.
   This is now `povm_resolvent_compression_le`.

## Recommended next step

Either

* move upstream and contribute the missing `CFC.Rpow.IntegralRepresentation`
  concavity lemmas to Mathlib, so that step (2) above becomes available; or
* prove a finite-POVM Löwner-integral variant directly at the matrix level,
  using only `Matrix.PosDef.inverse_compression_le` and the new
  `povm_resolvent_compression_le`, which sidesteps the Mathlib TODO at the
  cost of duplicating the integral representation locally.

The three Cor. 5.2 declarations should continue to reference the axioms in
`TNLean/Axioms/OperatorConvexity.lean` until one of the two routes above
lands.
