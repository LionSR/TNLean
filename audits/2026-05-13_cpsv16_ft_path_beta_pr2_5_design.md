# Path β PR 2.5 design memo: the analytic discharge of `hNoCancel` for non-dominant `k₀`

**Date:** 2026-05-13
**Branch:** `feat/mps-ft-path-beta-pr2-5-design-memo`
**Status:** **Design / open-gap analysis.**  Does not deliver code beyond this memo.
**Context:** Path β PRs 1 (#1643, #1644, #1645), 1.5/1.6 (#1655, #1657, #1664), and the paper-gap doc #1665 are merged.  PR 2 (#1664) delivered the algebraic skeleton `fixed_*_sectorDecomp_twoLayer` and `fixed_*_paperFaithful_twoLayer`, both consuming an abstract `hNoCancel`.  PR 2.5 was to **discharge** that `hNoCancel` for non-dominant `k₀` and thereby unlock PR 3.  This memo records the analysis showing that PR 2.5 as scoped is **blocked on a missing analytic input** (rate-quantified cross-overlap decay), proposes the precise statement of that input, and lays out the route to either supply it or document a new paper-gap.

## Executive summary

The non-dominant `_CFBNT` sorries at `Full/NondecayingOverlap/FixedBlockDecay.lean:107, 152` are **not** dischargeable on the two-layer `IsBNTCanonicalFormSD` surface using the per-block-projection skeleton alone.  After tracing through the natural strategies:

* **Strategy A (factor out `λ_A^{(0)}`, mirroring dominant block):** runs the dominant-block proof verbatim with `b_0` replaced by `k₀`.  The renormalized RHS factor `(μ_B^{(k_0)})^{-N} · \langle V_N(B), V_N(B_{k_0})\rangle` is a sum over `k` whose `k < k_0` (more-dominant) terms contain the factor `(μ_B^{(k)} / μ_B^{(k_0)})^N`, which **grows geometrically**.  For the sum to tend to a nonzero limit, the cross-overlap `\langle V_N(B_k), V_N(B_{k_0})\rangle` must decay at rate `o((μ_B^{(k_0)} / μ_B^{(k)})^N)`.  The qualitative `cross_overlap_tendsto_zero` available from `IsCanonicalFormBNT` / `IsBNTCanonicalFormSD` does **not** quantify this rate.
* **Strategy B (factor out `λ_B^{(k_0)}`, renormalise the assembled overlap):** equivalent to Strategy A after rewriting; same obstruction.
* **Strategy C (use Lem1 combined-family LI directly):** already ruled out by the LI scout (execution `e0a5ec0f6a31`); the `{V(A_j)} ∪ {V(B_k)}` combined family is generically dependent in the FT regime.

The common analytic input missing from all three strategies is the same: **rate-quantified cross-overlap decay** comparing the spectral-gap-induced decay of `\langle V_N(B_k), V_N(B_{k_0})\rangle` to the BNT weight ratios `μ_B^{(k)} / μ_B^{(k_0)}`.

## Detailed analysis

### Setup

Fix two BNT canonical-form families `(μ_A, A)`, `(μ_B, B)` with `IsCanonicalFormBNT μ_A A`, `IsCanonicalFormBNT μ_B B`, satisfying eventual nonzero proportionality of the assembled tensors.  Fix a non-dominant block index `k_0 \in {1, \ldots, r_B - 1}` with all overlaps `\langle V_N(A_j), V_N(B_{k_0})\rangle \to 0` as `N \to \infty`.  The proof obligation is: derive `False`.

### Mirror of the dominant-block proof

The dominant-block proof (`fixed_right_dominant_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT`, `FixedBlockDecay.lean:178`) proceeds via:

1. Extract the dominant-adjusted scalar `c_N` with `\|c_N \cdot (μ_B^{(0)} / μ_A^{(0)})^N\| \to 1` (`exists_dominant_adjusted_scalar_tendsto_norm_one_of_eventuallyNonzeroProportionalMPV₂_CFBNT`).
2. Express LHS overlap as a sum over `A`-blocks; multiply by `(μ_A^{(0)})^{-N}`.
3. Each summand `(μ_A^{(0)})^{-N} \cdot (μ_A^{(j)})^N \cdot \langle V_N(A_j), V_N(B_0)\rangle = (μ_A^{(j)} / μ_A^{(0)})^N \cdot \text{decay-to-0}`.  Since `|μ_A^{(j)} / μ_A^{(0)}| \le 1` by `mu_strict_anti`, each summand is bounded × decay → 0.
4. Hence `(μ_A^{(0)})^{-N} \cdot \text{LHS overlap} \to 0`.
5. By proportionality, `(μ_A^{(0)})^{-N} \cdot c_N \cdot \text{RHS overlap} \to 0`.
6. Factor RHS overlap: `(μ_B^{(0)})^{-N} \cdot \langle V_N(B), V_N(B_0)\rangle = \sum_k (μ_B^{(k)} / μ_B^{(0)})^N \cdot \langle V_N(B_k), V_N(B_0)\rangle`.
7. For `k = 0`: `1 \cdot \langle V_N(B_0), V_N(B_0)\rangle \to 1` (`HasNormalizedSelfOverlap`).
8. For `k \ne 0`: `|μ_B^{(k)} / μ_B^{(0)}| < 1` (bounded), and `\langle V_N(B_k), V_N(B_0)\rangle \to 0` (`cross_overlap_tendsto_zero`); product → 0.
9. Hence `(μ_B^{(0)})^{-N} \cdot \text{RHS overlap} \to 1`.
10. Combining with the dominant-adjusted scalar: `(μ_A^{(0)})^{-N} \cdot c_N \cdot \text{RHS overlap} = (c_N \cdot (μ_B^{(0)} / μ_A^{(0)})^N) \cdot ((μ_B^{(0)})^{-N} \cdot \text{RHS overlap})`, both factors have modulus → 1, so product modulus → 1.  Contradicts (5).

### What breaks at non-dominant `k_0`

Replace `b_0` by `k_0` in Step 7--10:

* **Step 7' (`k = k_0`):** `(μ_B^{(k_0)})^{-N} \cdot \langle V_N(B_{k_0}), V_N(B_{k_0})\rangle \to 1` is fine if we replace `μ_B^{(0)}` by `μ_B^{(k_0)}` in the renormalization.  But then the dominant-adjusted scalar in Step 10' becomes `c_N \cdot (μ_B^{(k_0)} / μ_A^{(0)})^N`, with `|μ_B^{(k_0)} / μ_A^{(0)}| < 1` (because `μ_A^{(0)}` is the larger dominant of the two families' dominants).  This factor has modulus → 0, not 1.  So even if Step 9' produces a limit of `1`, the product in Step 10' has modulus → 0, not 1.  **Vacuous: 0 = 0, no contradiction.**

Equivalently: renormalising by `μ_A^{(0)}` and by `μ_B^{(k_0)}` are *not* compatible because the dominant on the `A` side is `μ_A^{(0)}` but the relevant `B` scale is `μ_B^{(k_0)}`.

### Strategy A (factor out `μ_A^{(0)}`)

Stick with Step 6: `(μ_A^{(0)})^{-N} \cdot c_N \cdot \text{RHS overlap} = ?`.  We have:

```
(μ_A^{(0)})^{-N} · c_N · ⟨V_N(B), V_N(B_{k_0})⟩
  = c_N · ∑_k (μ_B^{(k)} / μ_A^{(0)})^N · ⟨V_N(B_k), V_N(B_{k_0})⟩.
```

For `k = 0` (more dominant than `k_0`): `(μ_B^{(0)} / μ_A^{(0)})^N` is bounded (modulus `\le 1`, since `μ_B^{(0)}` could be even smaller than `μ_A^{(0)}`, but never larger if `μ_A^{(0)}` is the joint dominant; in general the ratio could go either way).  Multiplied by `\langle V_N(B_0), V_N(B_{k_0})\rangle \to 0`, this term → 0.

For `k = k_0`: `(μ_B^{(k_0)} / μ_A^{(0)})^N` has modulus → 0 (strictly less than 1 since `μ_A^{(0)}` is dominant).  Multiplied by `\langle V_N(B_{k_0}), V_N(B_{k_0})\rangle \to 1`, this term → 0.

For `k < k_0` (more dominant than `k_0`, but possibly not as dominant as `A`'s dominant): `(μ_B^{(k)} / μ_A^{(0)})^N` has modulus `\le 1`.  Multiplied by `\langle V_N(B_k), V_N(B_{k_0})\rangle \to 0`, this term → 0.

For `k > k_0`: same as `k = k_0`.

**Result:** the entire RHS sum → 0 trivially.  So `c_N · ((μ_A^{(0)})^{-N} \cdot \text{RHS overlap}) \to 0` becomes `(\text{bounded}) · 0 \to 0`, which is consistent with proportionality and yields **no contradiction**.

The dominant-block proof exploited the special property of `k_0 = 0` that the `(μ_B^{(0)} / μ_A^{(0)})` and `(μ_B^{(0)})^{-N} \cdot \text{self-overlap}` factors *combine* to give the unit modulus.  For `k_0 \ne 0`, this combination is broken.

### Strategy B (factor out `μ_B^{(k_0)}`)

Re-normalise the RHS to `(μ_B^{(k_0)})^{-N} \cdot \text{RHS overlap}` and absorb the matching factor into the scalar:

```
(μ_B^{(k_0)})^{-N} · ⟨V_N(B), V_N(B_{k_0})⟩
  = ∑_k (μ_B^{(k)} / μ_B^{(k_0)})^N · ⟨V_N(B_k), V_N(B_{k_0})⟩.
```

For `k = k_0`: → `1 \cdot 1 = 1`.  Good.

For `k > k_0` (less dominant): `|μ_B^{(k)} / μ_B^{(k_0)}| < 1`, bounded × decay → 0.

For `k < k_0` (more dominant): `|μ_B^{(k)} / μ_B^{(k_0)}| > 1`, **geometric blow-up**.  The cross-overlap `\langle V_N(B_k), V_N(B_{k_0})\rangle` decays geometrically with some rate `η^N`, `η < 1`, set by the transfer-matrix spectral gap (via `mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left_of_irreducible_TP`).  For the product `(μ_B^{(k)} / μ_B^{(k_0)})^N \cdot η^N → 0`, we need:

```
η · |μ_B^{(k)} / μ_B^{(k_0)}| < 1   (for all k < k_0).
```

Equivalently:

```
|μ_B^{(k)} / μ_B^{(k_0)}| < 1/η.
```

The generic BNT canonical form does **not** impose this — the weight ratios and the transfer-matrix spectral gap are *independent* analytic inputs.  Without additional structure, the bound `|μ_B^{(k)} / μ_B^{(k_0)}| < 1/η` may fail.

### Strategy C (Lem1 combined-family LI)

The LI scout (execution `e0a5ec0f6a31`) showed that the natural combined family `{V_N(A_j)} ∪ {V_N(B_k)}` is **generically dependent** in the FT regime — when the matched-partner conclusion `V_N(B_k) ∝ V_N(A_{σ(k)})` holds, the combined family has rank at most `r_A`.  So Lem1 applied to the combined family is vacuous.

The narrower family `{V_N(A_0)} ∪ {V_N(B_k): k \ne k_0}` (excluding the targeted `k_0`) does eventually have rank `r_A + r_B - 1`, but it does **not** include `V_N(A_j)` for `j \ne 0`.  After projecting the proportionality identity onto its span and using the matched-partner relations, the residual identity becomes:

```
0 = c_N · (μ_B^{(k_0)})^N · ⟨V_N(B), V_N(B_{k_0})⟩ + ∑_{k \ne k_0} c_N · (μ_B^{(k)})^N · ⟨V_N(B_k), V_N(B_{k_0})⟩.
```

The off-target sum has the same `(μ_B^{(k)} / μ_B^{(k_0)})^N` issue when normalised by `(μ_B^{(k_0)})^N`.  Same obstruction.

## Required analytic input

The common gap across all three strategies is the missing rate-quantified cross-overlap decay.  The precise statement needed is:

> **Rate-quantified BNT cross-overlap decay.**  Let `μ : Fin r → ℂ` and `A : (k : Fin r) → MPSTensor d (dim k)` satisfy `IsCanonicalFormBNT μ A`.  Then for every pair `(j, k)` with `j \ne k`, there exist constants `C_{j,k} \ge 0` and a rate `η_{j,k} < 1` with:
> ```
> ∀ N, ‖⟨V_N(A_j), V_N(A_k)⟩‖ ≤ C_{j,k} · η_{j,k}^N.
> ```
> Moreover, the rate `η_{j,k}` can be chosen *uniformly small enough* relative to the BNT weight ratios:
> ```
> η_{j,k} · |μ_j / μ_k| < 1   (for all j, k).
> ```

The second condition (rate vs. weight ratio) is the non-trivial one: it requires that the BNT separation guarantees a spectral gap on the transfer matrix products that beats the weight ratios.

**Status in the existing formalisation.**  The qualitative version (`cross_overlap_tendsto_zero`) is established via `mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left_of_irreducible_TP`.  The quantitative version with explicit `(C_{j,k}, η_{j,k})` is **not** present.  The geometric-rate ingredient is implicit in the transfer-matrix spectral analysis (e.g. `TNLean/Spectral/SpectralRadius.lean`) but has not been packaged in a form consumed by the FT chain.

**Status in CPSV16.**  Theorem 1 (lines 1170--1192) does not explicitly state a rate.  The argument in the source is presented as if the cross-overlap decay automatically beats the weight ratios; in practice, the BNT condition (CPSV21 Definition 4.3, "eventually linear independent") together with strict ordering of moduli is intended to encode this rate comparison, but a formal proof would extract the rate via spectral-gap analysis on the BNT-induced TM.

## Path forward

Three options, in increasing order of difficulty:

### Option 1: Strengthen `IsBNTCanonicalFormSD` with a rate field

Add a hypothesis to `IsBNTCanonicalFormSD` declaring the rate-quantified cross-overlap decay as an additional structural input.  This is the **least invasive** option:

* Adds `crossOverlap_rate_decay : ∀ j k, j ≠ k → ∃ C η, η < 1 ∧ η · |μ_j / μ_k| < 1 ∧ ∀ N, ‖overlap(basis j, basis k) N‖ ≤ C η^N`.
* Discharge the two `_CFBNT` sorries on the strengthened structure.
* Document the new field as an "analytic strengthening" matching CPSV21 Definition 4.3.
* **Cost:** the adapter `IsCanonicalFormBNT.toIsBNTCanonicalFormSD` no longer goes through unconditionally — it would require an additional input derived from the BNT spectral gap.  This pushes the rate-quantification gap to a new paper-gap module (`docs/paper-gaps/cpsv16_bnt_rate_quantification.tex`).

### Option 2: Prove the rate-quantified decay from spectral gap

Connect the existing transfer-matrix spectral-radius analysis to the rate-quantified cross-overlap decay:

* Prove a lemma stating that for irreducible block tensors `A_j, A_k` with `j ≠ k`, the cross-overlap decays at the rate `(σ_2(A_j ⊗ A_k))^N` where `σ_2` is the subdominant spectral radius.
* Compare `σ_2(A_j ⊗ A_k)` to the BNT weight ratios via the dominant-block condition.
* Likely requires substantial new spectral machinery (200-400 LoC of new analytic content).

### Option 3: Use CPSV16's actual proof strategy

Re-read CPSV16 lines 1170--1192 carefully and replicate the paper's actual argument, which may avoid the rate-quantification issue altogether (e.g. by working with renormalised states from the outset).  This option is **research-level**: the paper's argument is dense and may itself rely on the rate-quantified decay implicitly.

## Recommendation

**Adopt Option 1** for the immediate next step:

1. Strengthen `IsBNTCanonicalFormSD` with a `crossOverlap_rate_decay` field.
2. Implement the analytic discharge of `hNoCancel` for non-dominant `k_0` on the strengthened structure (~300-500 LoC of analytic Lean).
3. Document the new structural hypothesis as a paper-gap (`docs/paper-gaps/cpsv16_bnt_rate_quantification.tex`).
4. Adjust the `IsCanonicalFormBNT.toIsBNTCanonicalFormSD` adapter to expose the rate-quantification gap as an additional input (or split into two adapter variants).

This option closes the two `_CFBNT` sorries under an honest hypothesis matching CPSV21 Definition 4.3's intent, and isolates the remaining gap (Option 2) as a separate analytic obligation that can be addressed independently in the future.

## Open caveats

* The rate-quantified decay is not the only analytic input needed.  The renormalised self-overlap limit `(μ_B^{(k_0)})^{-N} \cdot \langle V_N(B_{k_0}), V_N(B_{k_0})\rangle \to ?` also needs justification for non-dominant `k_0`; it is the within-sector unit-modulus power sum that this memo's analysis assumes converges to a nonzero limit by `unitModulus_power_sum_not_tendsto_zero`.
* The scalar `c_N` lower bound on the rescaled SD surface, after the adapter `IsCanonicalFormBNT.toIsBNTCanonicalFormSD`, comes from the dominant-adjusted scalar `exists_dominant_adjusted_scalar_tendsto_norm_one_of_eventuallyNonzeroProportionalMPV₂_CFBNT`.  Under the dominant normalisation `\|λ_0\| = 1`, this scalar is bounded below by a constant on the rescaled surface (the geometric problem dissolves, as recorded in path β scout PR 1.5).  This is **independent** of the rate-quantification issue and does not require Option 1.

## References

* CPSV16 (arXiv:1606.00608), Theorem 1, lines 1170--1192.
* CPSV21 (arXiv:2011.12127), Definition 4.3 (BNT eventual LI).
* `audits/2026-05-13_cpsv16_ft_path_beta_scout.md` — path β architecture.
* `audits/2026-05-13_cpsv16_ft_bridge_gap.md` — original bridge-gap analysis.
* `audits/2026-05-13_cpsv16_ft_exact_leading_coeff.md` — path α infeasibility.
* `docs/paper-gaps/cpsv16_nondominant_per_block_projection.tex` — non-dominant CFBNT obstruction at the `IsCanonicalFormBNT` level.
* `docs/paper-gaps/cpsv16_two_layer_sector_refinement.tex` — two-layer SD refinement.
* `TNLean/MPS/FundamentalTheorem/SectorDecomposition/PerBlockProjection.lean` — two-layer algebraic skeleton.
* `TNLean/MPS/FundamentalTheorem/SectorDecomposition/HNoCancelDischarge.lean` — one-layer analytic discharge.
* `TNLean/MPS/FundamentalTheorem/Full/NondecayingOverlap/FixedBlockDecay.lean:107, 152` — the two open sorries.
* `TNLean/MPS/FundamentalTheorem/Full/NondecayingOverlap/FixedBlockDecay.lean:178, 458` — dominant-block discharges.
* `TNLean/Spectral/SpectralRadius.lean` — transfer-matrix spectral analysis.

## Issue tracking

* #1641 (Plan C tracker) — to be updated with this memo and Option 1 dispatch.
* #1607 (original CFBNT sorry tracker) — remains open until Option 1 lands.

## Forbidden directions (carry forward)

* NO combined-family LI / RSE / Option-LI hypotheses (vacuous in FT regime per execution `e0a5ec0f6a31`).
* NO induction-via-exact-coefficient (path α infeasible per `cpsv16_ft_exact_leading_coeff.md`).
* NO peel-arbitrary-`k_0` induction architecture.
* NO new `sorry` / `axiom` / `unsafe` without explicit factored documented sub-lemma.
