# Audit of `ch15_correlations.tex` against Lean

## Scope

Read:

- `blueprint/src/chapter/ch15_correlations.tex`
- all files in `TNLean/MPS/RFP/`
- correlation/connected files:
  - `TNLean/MPS/Core/Correlations.lean`
  - `TNLean/Spectral/CrossCorrelation.lean`
  - `TNLean/MPS/ParentHamiltonian/Decorrelation.lean`

## Bottom line

The main overclaims are exactly the two the user flagged:

1. `connectedCorrelator_eq_sum`
2. `connectedCorrelator_bound`

In Lean, both are only wrapper lemmas that restate an already-supplied decomposition/bound. They do **not** derive the spectral expansion or decay estimate from normality, spectral theory, or the transfer map.

There are also a few weaker mismatches/oversells around the RFP/ZCL discussion, mostly because the Lean formalization only covers a simplified single-tensor notion.

## Major statement mismatches

### 1. `connectedCorrelator_eq_sum` is a strong overclaim

- Blueprint statement: `blueprint/src/chapter/ch15_correlations.tex:63-73`
- Lean declaration: `TNLean/MPS/Core/Correlations.lean:73-83`

Blueprint says:

- for a normal MPS, the connected correlator admits a spectral expansion
- the coefficients are tied to subleading transfer eigenvalues

Lean actually proves only:

- if one is given functions `c lam : Fin (D * D - 1) → ℂ`
- and a hypothesis
  `hdecomp : ∀ n, connectedCorrelator ... n = ∑ j, c j * (lam j)^n`
- then the same formula holds for all `n`

So the Lean theorem is only an identity wrapper around an assumed expansion. It does **not** prove:

- existence of `c_j`
- existence of `λ_j`
- that the `λ_j` are eigenvalues
- that they are the subleading eigenvalues
- that normality or QPF hypotheses imply such a decomposition

Conclusion:

- `\leanok` is incorrect here.
- This should either be rewritten to match the wrapper theorem, or marked `\notready`.

### 2. `connectedCorrelator_bound` is also a strong overclaim

- Blueprint statement: `blueprint/src/chapter/ch15_correlations.tex:81-90`
- Lean declaration: `TNLean/MPS/Core/Correlations.lean:89-96`

Blueprint says:

- if the subleading eigenvalues satisfy `|\lambda_j| ≤ |\lambda_2| < 1`
- then there exists `C_{XY} ≥ 0` such that
  `|C(X,Y;n)| ≤ C_{XY} |\lambda_2|^n`

Lean actually proves only:

- given `CXY : ℝ`, `lam₂ : ℂ`, and a hypothesis
  `hbound : ∀ n, ‖connectedCorrelator ... n‖ ≤ CXY * ‖lam₂‖^n`
- then the same bound holds for all `n`

So again this is only a packaging lemma for an already-supplied estimate. It does **not** derive:

- the existence of `CXY`
- the bound from the spectral expansion
- the use of subleading eigenvalues
- the strict inequality `|\lambda_2| < 1`

Conclusion:

- `\leanok` is incorrect here.
- This should either be rewritten to match the wrapper theorem, or marked `\notready`.

## Other mismatches / oversells

### 3. `IsLocallyOrthogonal` is simplified in Lean

- Blueprint: `blueprint/src/chapter/ch15_correlations.tex:241-249`
- Lean definition: `TNLean/MPS/RFP/ZeroCorrelationLength.lean:51-66`

Lean defines

- `IsLocallyOrthogonal A := IsRFP A`

for a single tensor. The blueprint text is mostly careful, but the sentence about the full multi-block BNT notion can be read as if the tagged declaration already formalizes that richer notion. It does not. The mixed-transfer-operator vanishing is not part of the declaration tagged here.

This is not as bad as the two correlation theorems, but the prose is broader than the actual object being tagged.

### 4. `zcl_iff_idempotent_transfer` is a simplified single-tensor theorem

- Blueprint: `blueprint/src/chapter/ch15_correlations.tex:311-319`
- Lean theorem: `TNLean/MPS/RFP/ZeroCorrelationLength.lean:113-131`

The blueprint statement matches the **local definitions used in the chapter**:

- `IsZCL A := IsLocallyOrthogonal A ∧ IsCID A`
- `IsLocallyOrthogonal A := IsRFP A`

So the statement is not false relative to Lean. But it is worth noting that the Lean result is much closer to a single-tensor definitional equivalence than to a full formalization of the richer multiblock theorem from the paper.

I would not call this an incorrect `\leanok`, but I would call it slightly oversold if readers are meant to understand it as the full theorem from the cited source.

### 5. `rg_flow_converges_of_cf` is slightly weaker/more specific in the blueprint wording

- Blueprint: `blueprint/src/chapter/ch15_correlations.tex:252-263`
- Lean theorem: `TNLean/MPS/RFP/Convergence.lean:50-60`

Lean proves the convergence for a **chosen block** `k`, and the convergence statement is for **all matrices** `ρ`, not just density matrices.

So the blueprint should ideally say "for each block `k`" to match the quantification more explicitly. This is not an overclaim; if anything, the blueprint is slightly less explicit than the Lean type.

### 6. `correlation_length_bound` prose overspecifies the rate

- Blueprint: `blueprint/src/chapter/ch15_correlations.tex:174-190`
- Lean theorem: `TNLean/Spectral/QuantitativeGap.lean:316-400`

The formal statement is fine: existence of `C > 0` and `ξ > 0` with an exponential bound on traceless inputs.

But the final prose sentence says the decay rate is

- `ξ = -1 / log ρ(E_A - P)`

Lean does not prove that exact formula for the witness `ξ`; it produces `ξ` from an auxiliary `r < 1` coming from a geometric bound. So this is a prose overspecification, not a statement mismatch.

## `\leanok` / `\notready` issues

### Incorrect `\leanok`

These should not currently carry `\leanok` in their present blueprint form:

- `blueprint/src/chapter/ch15_correlations.tex:65` for `MPSTensor.connectedCorrelator_eq_sum`
- `blueprint/src/chapter/ch15_correlations.tex:83` for `MPSTensor.connectedCorrelator_bound`

Reason:

- the blueprint states derived spectral results
- Lean only has wrapper lemmas assuming those results as hypotheses

### Missing `\notready`

If the blueprint text is kept as-is, the two items above should be marked `\notready`.

There is also an unsupported untagged remark:

- `blueprint/src/chapter/ch15_correlations.tex:277-282`

This remark claims:

- `E^2 = E` is equivalent to vanishing subleading spectrum
- equivalently `ξ = 0`

The Lean files read here do not establish those spectral equivalences. They do support separation-independence of the connected correlator from idempotence, but not the full spectral/`ξ = 0` formulation. Since this remark is untagged, the issue is not an incorrect `\leanok`, but it is still not backed by the cited Lean material and likely deserves either softening or `\notready`.

## Formalization-speak

I did not see major remaining formalization-speak in this chapter.

The only phrase I would consider mildly proof-assistant-flavored is:

- `blueprint/src/chapter/ch15_correlations.tex:273`:
  "The witness `E_\infty = P` ..."

More natural mathematical prose would be:

- "One may take `E_\infty = P` ..."

## Per-tag checklist

### Tags that look fine relative to Lean

- `MPSTensor.onePointExpectation`
- `MPSTensor.twoPointExpectation`
- `MPSTensor.connectedCorrelator`
- `MPSTensor.correlationLength`
- `MPSTensor.correlationLength_pos`
- `MPSTensor.exponential_convergence_of_primitive`
- `MPSTensor.correlation_length_bound` (statement fine; rate formula in prose is stronger than Lean)
- `MPSTensor.spectral_gap_of_injective`
- `MPSTensor.IsRFP`
- `MPSTensor.rg_flow_converges_of_cf` (quantification over block `k` should be made more explicit)
- `MPSTensor.IsCID` (though the universal quantification over all PosDef fixed points could be stated more explicitly)
- `MPSTensor.isCID_implies_isRFP`
- `MPSTensor.zcl_iff_idempotent_transfer` (single-tensor simplified version)

### Tags with real statement mismatch

- `MPSTensor.connectedCorrelator_eq_sum`
- `MPSTensor.connectedCorrelator_bound`

## Suggested priority fixes

1. Remove `\leanok` from the two correlation theorems or rewrite them to match the actual Lean wrappers.
2. Add `\notready` to those two theorems if the mathematical statements are kept.
3. Soften the zero-correlation-length remark at `:277-282`, or mark it `\notready`.
4. Make the `rg_flow_converges_of_cf` quantification over blocks explicit.
5. Consider clarifying that the chapter's `IsLocallyOrthogonal` / `zcl_iff_idempotent_transfer` are single-tensor simplifications of the fuller multiblock story.
