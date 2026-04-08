# Audit of `blueprint/src/chapter/ch02_mps.tex`

Date: 2026-04-08

## Scope

Read in full:

- `blueprint/src/chapter/ch02_mps.tex`
- all `.lean` files in `TNLean/MPS/Core/`
- `TNLean/MPS/Defs.lean`

Additional files inspected because tagged declarations live there:

- `TNLean/MPS/Periodic/Defs.lean`
- `TNLean/MPS/Overlap/Basic.lean`
- `TNLean/MPS/FundamentalTheorem/Multi.lean`
- `TNLean/MPS/Core/Transfer.lean`

No files matched `TNLean/MPS/Basic*.lean`.

## Executive Summary

- All 33 `\lean{}` tags resolve to existing Lean declarations.
- I found no `sorry`, `admit`, or `axiom` in the files defining these tagged declarations.
- So the current `\leanok` / `\notready` status is fine at the proof-status level: no tag needs `\notready` for lack of formalization.
- There are, however, 5 substantive statement/prose mismatches with the actual Lean signatures:
  1. `MPSTensor.mpv` is a coefficient function in Lean, not the full vector/family described in the blueprint.
  2. `MPSTensor.SameMPV` and `MPSTensor.SameMPV₂` quantify over all `N : ℕ`, including `N = 0`; the blueprint says `N ≥ 1`.
  3. `MPSTensor.CanonicalForm` is a Lean structure of block data with no `r ≥ 1` field, not a predicate “for a tensor”.
  4. `MPSTensor.mpv_toTensorFromBlocks_eq_sum` is a coefficient-wise theorem, not a vector-valued identity.
  5. `MPSTensor.mpvOverlap_eq_of_pos_mpv_eq` is a two-sided replacement theorem; the blueprint states only a one-sided corollary.
- There is some formalization-facing prose, especially the “alias” language in the periodic section.

Unless explicitly noted below, the tagged declaration does not carry any extra `[NeZero D]`-style hypotheses beyond the visible variables.

## Detailed Findings

### 1. `MPSTensor.mpv` is not the full vector

- Blueprint lines 60-93 present `\lean{MPSTensor.mpv}` as “the matrix product vector at system size `N`”.
- Actual Lean declaration at `TNLean/MPS/Defs.lean:69` is:
  `def mpv (A : MPSTensor d D) {N : ℕ} (σ : Fin N → Fin d) : ℂ`
- So the tagged declaration is the coefficient function `σ ↦ tr(A^σ)`, not the vector in `(\C^d)^{\otimes N}`.
- The later `\lean{MPSTensor.mpvState}` is the bundled Hilbert-space vector.

Suggested fix:

- Either rewrite Definition 2.4 as a coefficient-function definition, or retag the vector packaging with `\lean{MPSTensor.mpvState}` and make `mpv` the coefficient notation.

### 2. `SameMPV` / `SameMPV₂` are all-length, not positive-length

- Blueprint lines 172-188 say equality for every `N ≥ 1`.
- Actual Lean declarations at `TNLean/MPS/Defs.lean:82` and `:89` quantify over all `N : ℕ`.
- This also affects the reading of `\lean{MPSTensor.GaugeEquiv.sameMPV}` and `\lean{MPSTensor.SameMPV.blockTensor}`: both prove the stronger all-`N` statement.

Suggested fix:

- Change “for every system size `N ≥ 1`” to “for every `N : ℕ`” if you want the blueprint to match Lean exactly.

### 3. `CanonicalForm` prose does not match the Lean structure

- Blueprint lines 330-350 describe `\lean{MPSTensor.CanonicalForm}` as if it were a canonical-form predicate/data package for a tensor, with `r ≥ 1`.
- Actual Lean declaration at `TNLean/MPS/Core/MultiBlock.lean:24-34` is a structure with fields:
  `numBlocks`, `blockDim`, `blockTensor`, `μ`, `block_injective`.
- There is no field asserting `numBlocks ≥ 1`.
- The associated tensor is not part of the structure fields; it is a derived construction (`CanonicalForm.toTensor`), and the raw constructor used in the blueprint section is `toTensorFromBlocks`.

Suggested fix:

- Rewrite this definition as “a structure consisting of block data ...” rather than a property “for a tensor”.
- Remove the explicit `r ≥ 1` unless you intend to add that hypothesis in Lean later.

### 4. `mpv_toTensorFromBlocks_eq_sum` is coefficient-wise

- Blueprint lines 379-393 state a vector identity:
  `|V^{(N)}(A)> = Σ_k μ_k^N |V^{(N)}(A_k)>`
- Actual Lean theorem at `TNLean/MPS/FundamentalTheorem/Multi.lean:231` states only:
  `mpv (toTensorFromBlocks μ A) σ = ∑ k, (μ k)^N • mpv (A k) σ`
  for a fixed configuration `σ : Fin N → Fin d`.
- The second sentence in the blueprint (“Equivalently, for each configuration ...”) matches Lean; the displayed vector equation is not the actual Lean signature.

Suggested fix:

- Keep only the coefficient-wise statement under the `\lean{}` tag, or explicitly say the vector statement is the informal reformulation of the formal coefficient theorem.

### 5. `mpvOverlap_eq_of_pos_mpv_eq` is more general than stated

- Blueprint lines 551-558 say:
  if `V^{(N)}(A)_σ = V^{(N)}(B)_σ` for all `N > 0`, then `O_AC(N) = O_BC(N)` for all positive `N`.
- Actual Lean theorem at `TNLean/MPS/Overlap/Basic.lean:69-75` has two hypotheses:
  one for replacing `A` by `A'`, and one for replacing `B` by `B'`.
- So Lean proves a two-sided replacement theorem:
  positive-length equality on both sides implies equality of overlaps.
- The blueprint statement is a corollary (take the second replacement to be reflexive on `C`), but it is not the theorem’s actual signature.

Suggested fix:

- Either restate the theorem in its two-sided form, or change the tag to a dedicated corollary if you add one later.

## Per-Tag Checklist

Legend:

- `Exists`: declaration exists in Lean.
- `Match`: `Exact`, `Mostly`, or `Mismatch`.
- `Ready`: whether current `\leanok` status is accurate.

| BP line | Tag | Lean location | Exists | Match | Ready | Notes |
| --- | --- | --- | --- | --- | --- | --- |
| 12 | `MPSTensor` | `TNLean/MPS/Defs.lean:22` | Yes | Exact | `\leanok` correct | `abbrev MPSTensor (d D : ℕ) := Fin d → Matrix (Fin D) (Fin D) ℂ`. |
| 29 | `MPSTensor.evalWord` | `TNLean/MPS/Defs.lean:30` | Yes | Exact | `\leanok` correct | Recursive word evaluation with empty word sent to `1`. |
| 48 | `MPSTensor.evalWord_append` | `TNLean/MPS/Defs.lean:41` | Yes | Exact | `\leanok` correct | Matches multiplicativity under append. |
| 61 | `MPSTensor.mpv` | `TNLean/MPS/Defs.lean:69` | Yes | Mismatch | `\leanok` correct | Lean `mpv` is a coefficient function `σ ↦ ℂ`, not the bundled vector/family. |
| 96 | `MPSTensor.transferMap` | `TNLean/MPS/Core/Transfer.lean:23` | Yes | Exact | `\leanok` correct | Linear map `X ↦ ∑ i, A i * X * (A i)ᴴ`. |
| 122 | `MPSTensor.PeriodicMPSTensor` | `TNLean/MPS/Periodic/Defs.lean:22` | Yes | Exact | `\leanok` correct | Alias to `MPSChainTensor d D m`. |
| 130 | `MPSTensor.PeriodicMPSTensor.SameState` | `TNLean/MPS/Periodic/Defs.lean:37` | Yes | Exact | `\leanok` correct | Abbrev to chain-level `SameState`. |
| 131 | `MPSTensor.PeriodicMPSTensor.GaugeEquiv` | `TNLean/MPS/Periodic/Defs.lean:41` | Yes | Exact | `\leanok` correct | Abbrev to chain-level `GaugeEquiv`. |
| 142 | `MPSTensor.PeriodicMPSTensor.instEquivalenceSameState` | `TNLean/MPS/Periodic/Defs.lean:56` | Yes | Exact | `\leanok` correct | Bundled `Equivalence` structure. |
| 143 | `MPSTensor.PeriodicMPSTensor.instEquivalenceGaugeEquiv` | `TNLean/MPS/Periodic/Defs.lean:76` | Yes | Exact | `\leanok` correct | Bundled `Equivalence` structure. |
| 153 | `MPSTensor.GaugeEquiv` | `TNLean/MPS/Defs.lean:77` | Yes | Exact | `\leanok` correct | `∃ X : GL ..., ∀ i, B i = X * A i * X⁻¹`. |
| 173 | `MPSTensor.SameMPV` | `TNLean/MPS/Defs.lean:82` | Yes | Mostly | `\leanok` correct | Lean quantifies over all `N : ℕ`, not only `N ≥ 1`. |
| 182 | `MPSTensor.SameMPV₂` | `TNLean/MPS/Defs.lean:89` | Yes | Mostly | `\leanok` correct | Same all-`N` issue as above; heterogeneous in bond dimension. |
| 199 | `MPSTensor.ProportionalMPV₂` | `TNLean/MPS/Defs.lean:93` | Yes | Exact | `\leanok` correct | Quantifies over all `N : ℕ`; blueprint already says “for every `N`”. |
| 209 | `MPSTensor.evalWord_smul` | `TNLean/MPS/Defs.lean:51` | Yes | Exact | `\leanok` correct | Formal statement uses `fun i => ζ • A i`. |
| 228 | `MPSTensor.GaugePhaseEquiv` | `TNLean/MPS/Defs.lean:97` | Yes | Exact | `\leanok` correct | Includes explicit hypothesis `ζ ≠ 0`. |
| 248 | `MPSTensor.evalWord_gauge` | `TNLean/MPS/Defs.lean:165` | Yes | Exact | `\leanok` correct | Matches gauge covariance of word evaluation. |
| 263 | `MPSTensor.GaugeEquiv.sameMPV` | `TNLean/MPS/Defs.lean:187` | Yes | Mostly | `\leanok` correct | Result is into Lean’s all-`N` `SameMPV`. |
| 282 | `MPSTensor.IsInjective` | `TNLean/MPS/Defs.lean:106` | Yes | Exact | `\leanok` correct | Span of `Set.range A` equals `⊤`. |
| 291 | `MPSTensor.IsNBlkInjective` | `TNLean/MPS/Defs.lean:127` | Yes | Exact | `\leanok` correct | No extra positivity or nonzero-dimension hypotheses. |
| 301 | `MPSTensor.IsNormal` | `TNLean/MPS/Defs.lean:133` | Yes | Exact | `\leanok` correct | `∃ N, IsNBlkInjective A N`. |
| 331 | `MPSTensor.CanonicalForm` | `TNLean/MPS/Core/MultiBlock.lean:24` | Yes | Mismatch | `\leanok` correct | Lean structure of block data; no `r ≥ 1` field; associated tensor is derived, not part of the tagged definition. |
| 366 | `MPSTensor.toTensorFromBlocks` | `TNLean/MPS/FundamentalTheorem/Multi.lean:29` | Yes | Exact | `\leanok` correct | Raw block-diagonal assembly map. |
| 380 | `MPSTensor.mpv_toTensorFromBlocks_eq_sum` | `TNLean/MPS/FundamentalTheorem/Multi.lean:231` | Yes | Mismatch | `\leanok` correct | Lean theorem is coefficient-wise for fixed `σ`, not a vector identity. |
| 411 | `MPSTensor.blockTensor` | `TNLean/MPS/Core/Blocking.lean:54` | Yes | Exact | `\leanok` correct | Physical dimension is `blockPhysDim d L`, canonically equal to `d^L`. |
| 426 | `MPSTensor.evalWord_blockTensor` | `TNLean/MPS/Core/Blocking.lean:70` | Yes | Exact | `\leanok` correct | Matches flattening/concatenation description. |
| 446 | `MPSTensor.mpv_blockTensor_eq_mpv` | `TNLean/MPS/Core/Blocking.lean:203` | Yes | Exact | `\leanok` correct | Gives existence of flattened configuration `σflat`. |
| 468 | `MPSTensor.SameMPV.blockTensor` | `TNLean/MPS/Core/Blocking.lean:235` | Yes | Mostly | `\leanok` correct | Again inherits Lean’s all-`N` `SameMPV`. |
| 491 | `MPSTensor.mpvState` | `TNLean/MPS/Overlap/Basic.lean:39` | Yes | Mostly | `\leanok` correct | Lean target is `MPVSpace d N = EuclideanSpace ℂ (Fin N → Fin d)`, canonically equivalent to `ℂ^(d^N)`. |
| 504 | `MPSTensor.mpvInner` | `TNLean/MPS/Overlap/Basic.lean:48` | Yes | Exact | `\leanok` correct | Standard complex inner product, conjugate-linear in first argument. |
| 520 | `MPSTensor.mpvOverlap` | `TNLean/MPS/Overlap/Basic.lean:53` | Yes | Exact | `\leanok` correct | `∑ σ, mpv A σ * star (mpv B σ)`. |
| 538 | `MPSTensor.mpvOverlap_eq_star_mpvInner` | `TNLean/MPS/Overlap/Basic.lean:61` | Yes | Exact | `\leanok` correct | Matches stated conjugation relation. |
| 553 | `MPSTensor.mpvOverlap_eq_of_pos_mpv_eq` | `TNLean/MPS/Overlap/Basic.lean:69` | Yes | Mismatch | `\leanok` correct | Lean theorem is two-sided in `(A,A')` and `(B,B')`; blueprint states only a one-sided corollary. |

## Readiness Check

- Every theorem/lemma/definition environment in the chapter has a `\lean{}` tag and a readiness marker.
- For the 33 tagged declarations, the current `\leanok` markers are all accurate.
- I found no missing `\notready` markers caused by absent declarations or proof gaps in the files defining these declarations.

## Formalization-Speak / Lean-Jargon Notes

These are not proof-status errors, but they do read as repository-facing rather than mathematical prose:

- Lines 119-121: “Periodic-chain aliases” / “Periodic-chain tensor alias”.
  This is code-language. A more mathematical title would be “Periodic Chains” / “Periodic-chain tensors”.
- Lines 141-148: “Equivalence structures for periodic relations”.
  “Equivalence relations” is mathematical; “structures” sounds like the Lean instance bundle.
- Lines 192-195: “same-bond-dimension specialization” and “same-dimension and different-dimension forms”.
  This is formalization-driven wording.
- Line 551: “positive-length MPV”.
  Better: “for all `N > 0`”.

## Hypothesis Notes

- None of the 33 tagged declarations requires an extra `[NeZero D]` hypothesis.
- The nearest relevant theorem is `neZero_d_of_isInjective` in `TNLean/MPS/Defs.lean:114`, but it is not tagged in this chapter.
- The only important hidden hypothesis drift I found is positivity of `N` in `mpvOverlap_eq_of_pos_mpv_eq`, and all-vs-positive-length quantification in `SameMPV` / `SameMPV₂`.
