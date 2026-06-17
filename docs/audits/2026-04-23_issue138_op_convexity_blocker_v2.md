# Issue #138 blocker audit v2 — operator Jensen after the 2026-04-23 scratch pass

## Scope

This pass re-opened the remaining Wolf Chapter 5 operator-Jensen gap on top of
current `origin/main`, after the earlier audit-only PR #711 had already merged.
The target declarations remain

- `IsPositiveMap.cor52_item1_rpow_of_subunital`
- `IsPositiveMap.cor52_item2_rpow_of_subunital`
- `IsPositiveMap.cor52_item3_log_of_subunital`

from `TNLean/Channel/Schwarz/OperatorMonotone.lean`.

I did **not** land a proof edit to those declarations in this pass. I did,
however, push the direct finite-POVM route much further than the 2026-04-22
audit: for the **concave** real-power case, the obstacle now looks less like an
upstream impossibility and more like a still-unfinished but plausible local
implementation.

## Re-scout of current Mathlib / TNLean state

### Mathlib still available

The same upstream facts remain available and relevant:

- `CFC.rpow_le_rpow`, `CFC.monotone_rpow`
- `CFC.log_le_log`, `CFC.log_monotoneOn`
- `Real.exists_measure_rpow_eq_integral`
- `CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁`
- Schur-complement APIs `Matrix.PosDef.fromBlocks₁₁` and
  `Matrix.PosDef.fromBlocks₂₂`
- positivity-preserving congruence lemmas such as
  `Matrix.PosSemidef.mul_mul_conjTranspose_same`
- positive-definite compression lemma
  `Matrix.PosDef.conjTranspose_mul_mul_same`

### Mathlib still explicitly missing

The upstream TODOs are unchanged on this toolchain:

- `Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Order.lean`
  lines 24–28 still list
  - operator concavity of `rpow` on `[0,1]`
  - operator convexity of `rpow` on `[1,2]`
- `Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog/Order.lean`
  lines 26–29 still list operator concavity of `log`
- I still found **no** bundled Hansen–Pedersen / Choi–Davis operator Jensen
  theorem for positive (sub)unital maps.

So the general operator-convexity route is still absent upstream.

## What changed in this pass

The 2026-04-22 audit treated the finite-POVM Jensen package purely as a blocker
statement. In this pass I tried to prove the **concave** finite-POVM real-power
inequality directly, without introducing a general operator-convexity API.

The proof strategy is:

1. Reduce the finite-POVM family `Bᵢ` with `∑ᵢ Bᵢ ≤ 1` to an isometric
   compression by adjoining a defect block.
2. Prove the compression inverse inequality
   $$
   (W^\dagger Y W)^{-1} \le W^\dagger Y^{-1} W
   $$
   for positive-definite `Y` and an isometry `W`, using the Schur-complement
   lemmas `Matrix.PosDef.fromBlocks₁₁` and `Matrix.PosDef.fromBlocks₂₂`.
3. Specialize `Y` to a block-diagonal matrix with diagonal entries
   `λᵢ + t` and `t`, obtaining the finite-POVM resolvent inequality
   $$
   \left(\sum_i \lambda_i B_i + t I\right)^{-1}
   \le
   \sum_i (\lambda_i + t)^{-1} B_i + t^{-1}\!\left(I - \sum_i B_i\right).
   $$
4. Rearrange this into the Jensen inequality for the Löwner integrand
   $$
   x \mapsto t^p\bigl(t^{-1} - (t+x)^{-1}\bigr)
   = \operatorname{rpowIntegrand}_{0,1}(p,t,x),
   $$
   then integrate against the measure supplied by
   `Real.exists_measure_rpow_eq_integral` /
   `CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁`.

## Concrete scratch progress

In a local scratch file (not committed), I successfully formalized the following
core lemmas for the direct finite-POVM route:

- `inverse_compression_le`
- `povmIsometry_star_mul`
- `povmIsometry_compress_diagonal`
- `povmDiagonal_posDef`
- `povmDiagonal_inv`
- `povm_resolvent_inv_le`

In other words: the **resolvent/compression** half of the concave real-power
argument now appears formalizable in the current repository.

## What is still unfinished

I did **not** finish the full chain to a committed theorem. The remaining work
for the concave real-power branch is now more specific:

1. **Committed finite-POVM packaging**
   - turn the scratch dilation / defect construction into clean reusable lemmas
   - connect it to the spectral decomposition `A = ∑ᵢ λᵢ Pᵢ` in the actual
     `IsPositiveMap.rpow_concave_jensen` proof

2. **Integral-to-`rpow` closing step**
   - either rewrite the matrix resolvent integrand directly as
     `cfcₙ (rpowIntegrand₀₁ p t)`
   - or set up the scalar/matrix integral comparison carefully enough to invoke
     the existing `exists_measure_*_integral_*` results without introducing a
     fake order-by-Bochner step

3. **Endpoint hygiene / theorem packaging**
   - split off `p = 0` and `p = 1`
   - rewrite the current axiom-backed theorem surface in
     `TNLean/Channel/Schwarz/OperatorConvexity.lean`

I stopped before landing this because the remaining integral plumbing was still
substantial, and I did not want to half-commit a large proof skeleton.

## Consequence for the three Cor. 5.2 declarations

### Updated status assessment

- `cor52_item1_rpow_of_subunital`
  - **not proved in this pass**
  - but the direct finite-POVM / Löwner-integral route now looks genuinely
    plausible with current Mathlib + TNLean
- `cor52_item2_rpow_of_subunital`
  - still honestly blocked in this pass
  - the convex branch `r ∈ [1,2]` still lacks a comparable completed direct
    argument, and the upstream operator-convexity/Jensen TODOs remain relevant
- `cor52_item3_log_of_subunital`
  - still not closed in this pass
  - likely needs either
    - a direct logarithmic resolvent integral route, or
    - a completed concave-`rpow` theorem plus a careful `p → 0+` limit argument
      and strict-positivity packaging for `T A`

So the honest bottom line is still:

- item 1: **not yet closed**
- item 2: **not yet closed**
- item 3: **not yet closed**

but the reason is now more nuanced than in the previous audit: the **concave
real-power** case may no longer be fundamentally blocked by upstream absence of
a general operator Jensen theorem.

## Revised blocker picture

### Still-upstream blockers

These remain real blockers for the broad, reusable API:

- operator concavity of `rpow` in Mathlib
- operator convexity of `rpow` in Mathlib
- operator concavity of `log` in Mathlib
- a general Hansen–Pedersen / Choi–Davis Jensen theorem for positive maps

### Likely local-only bottleneck now

For the specific theorem `posMap_rpow_concave_jensen` / Cor. 5.2(1), the direct
finite-POVM proof now seems to require **local proof engineering**, not a new
upstream theorem statement:

- a clean finite-POVM dilation API
- diagonal inverse bookkeeping
- matrix/scalar integral comparison plumbing

That is a materially sharper conclusion than the earlier audit.

## Ando–Lieb

Nothing changed on the Ando–Lieb side. The usual integral representation
$$
A^s B^{1-s} = \frac{\sin(\pi s)}{\pi} \int_0^\infty t^{s-1} A(A+tB)^{-1}B\,dt
$$
and the surrounding operator-mean API are still absent from Mathlib, so the
Lieb/Ando theorem remains outside reach in this pass.

## Recommended next step

A focused follow-up should now target exactly one theorem:

- `posMap_rpow_concave_jensen`

using the direct finite-POVM route above. The scratch work suggests that the
hardest algebraic compression step is already under control; the remaining work
is to package the resolvent inequality and carry the Löwner integral through to
`rpow` in committed code.

If that lands, then:

- `IsPositiveMap.rpow_concave_jensen` becomes genuine,
- `cor52_item1_rpow_of_subunital` should collapse immediately,
- and the repository will have a concrete template for deciding whether the log
  case can be finished by a `p \to 0+` limit or needs a separate integral proof.
