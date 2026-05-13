# Path β scout: design for closing the two `_CFBNT` sorries

**Date:** 2026-05-13
**Branch:** `feat/mps-ft-path-beta-scout`
**Context:** Probe verdict on path α (`audits/2026-05-13_cpsv16_ft_exact_leading_coeff.md`) declared the induction-via-exact-coefficient route **fundamentally infeasible** on the `IsCanonicalFormBNT` surface.  This memo records the path β scout findings.

## Executive summary

Neither of the two architectural variants described in the original scout brief works as stated:

* **Variant (a)** — drop `mu_strict_anti` from `IsCanonicalFormBNT` — has a 32-site blast radius; it breaks the already-closed equal-MPV FT (`fundamentalTheorem_equalMPV_CFBNT_hetero`) and re-opens the multiplicity-recovery gap.
* **Variant (b)** — adapter `IsCanonicalFormBNT → IsBNTCanonicalFormSD` via `weight = μ / ‖μ‖` — is mathematically unsound for `r ≥ 2`: the assembled tensor with rescaled weights differs from `toTensorFromBlocks μ A` by per-block `‖μ_j‖^N` factors, and these factors cannot be absorbed into a single proportionality scalar.  Concretely, this is the same obstruction that defeated path α.

**Recommended:** **variant (b′)** — extend `IsBNTCanonicalFormSD` to a **two-layer** form (CPSV21 Def 4.2: spectral level `λ_j` × within-sector unit-modulus `ν_{j,q}`); build the thin adapter via `trivialSectorDecomp` keeping `P.toTensor` MPV-equal to `toTensorFromBlocks μ A`.  See below.

## Variant (a) — drop `mu_strict_anti`

Direct uses of `mu_strict_anti` across TNLean (32 sites):

* **Load-bearing (20 sites)** — proof requires `StrictAnti`:
  - `EqualProportional.lean:96, 114` — consumed by `fundamentalTheorem_canonicalForm` directly.
  - `PiAlgebra/CanonicalFormSep.lean:596` — `block_separation_all_words` needs strict.
  - `Full/NondecayingOverlap.lean:186, 214, 301, 308, 389, 410` — dominant-block separation, `‖μ_j/μ_0‖ < 1` for `j ≠ 0`.
  - `Full/NondecayingOverlap.lean:517, 526, 656, 689` — tail-reduction induction needs `mu_strict_anti.comp_strictMono`.
  - `Full/NondecayingOverlap/FixedBlockDecay.lean:270, 356` — inside the closed `_dominant_*_CFBNT` proofs.
  - `Full/ProportionalDominant.lean:197, 278, 344, 357` — dominant-adjusted scalar limits.
  - `Full/DominantWeight.lean:179, 193` — dominant-block dominance.
* **Incidental (12 sites)** — projections and forwards in `BNT/Construction.lean`, `CanonicalForm/...`.

Weakening to `Antitone` would require rewriting (i) `fundamentalTheorem_canonicalForm`, (ii) the full tail-reduction induction in `NondecayingOverlap.lean`, (iii) the dominant-adjusted scalar machinery in `ProportionalDominant.lean`, and (iv) the closed `_dominant_*_CFBNT` proofs.

Even harder: with `r_j > 1` allowed, the SCOPE-restricted same-block-structure equal-MPV theorem either needs an explicit `r_j = 1` hypothesis added (defeating the point) or needs to be re-proved on top of multi-copy data.  The re-proof opens the multiplicity-recovery gap (`docs/paper-gaps/ft_one_copy_scope_restriction.tex`) — Newton-Girard recovery of multiplicities from `∑_q μ_{j,q}^N` — which is a paper-level obligation, not a refactor.

**Verdict for (a): high-risk, high-effort, low-reversibility.  Rejected.**

## Variant (b) — `IsCanonicalFormBNT → IsBNTCanonicalFormSD` via phase extraction

The literal proposal sets `P.sectors.weight j 0 := μ_j / ‖μ_j‖` (unit modulus by construction).  Using `mpv_toTensor_eq_sum_sectors` and `mpv_toTensorFromBlocks_eq_sum`:

```
mpv P.toTensor σ              = ∑_j (μ_j / ‖μ_j‖)^N · mpv (A_j) σ
mpv (toTensorFromBlocks μ A) σ = ∑_j (μ_j)^N · mpv (A_j) σ
                              = ∑_j ‖μ_j‖^N · (μ_j / ‖μ_j‖)^N · mpv (A_j) σ
```

The two assembled tensors differ by per-block scalars `‖μ_j‖^N`.  For `r ≥ 2` with distinct moduli (which `mu_strict_anti` forces), **no single scalar `α_N` satisfies `mpv (toTensorFromBlocks μ A) σ = α_N · mpv P.toTensor σ` for all `σ`** — the σ-dependence through `mpv (A_j) σ` would need to be in a 1-dimensional span, which BNT eventual linear independence forbids generically.

Consequence: `EventuallyNonzeroProportionalMPV₂ (toTensorFromBlocks μA A) (toTensorFromBlocks μB B)` does **not** transfer to `EventuallyNonzeroProportionalMPV₂ P.toTensor Q.toTensor` after phase extraction.  This is structurally the same counterexample as the path-α exact-leading-coefficient probe at `r_A = r_B = 2`: distinct moduli prevent a single scalar from intertwining LHS and RHS once dominant decay has been factored out.

**Verdict for (b) literal: mathematically unsound for non-dominant blocks.**

## Variant (b′) — two-layer extension of `IsBNTCanonicalFormSD`

Adopt the genuine CPSV21 Def 4.2 structure: keep the assembled tensor as `toTensorFromBlocks μ A`, but expose **two layers** at the type level:

* **Spectral level** `λ : Fin P.basisCount → ℂ` with `λ_j ≠ 0` and `StrictAnti (‖λ·‖)`.
* **Within-sector weights** `P.sectors.weight j q = λ_j · ν_{j,q}` with `‖ν_{j,q}‖ = 1`.

Under one-copy-per-sector (`copies j = 1`), the adapter sets `λ_j = μ_j` and `ν_{j,0} = μ_j / ‖μ_j‖`, with `P.toTensor = trivialSectorDecomp μ A`.  Crucially, `P.toTensor` is then MPV-equal to `toTensorFromBlocks μ A`, so proportionality transfers cleanly.

The non-cancellation analytic step in `HNoCancelDischarge.lean` generalizes: after factoring out `(λ_{k₀})^N`, the residual depends only on `ν_{j,q}` (unit-modulus), and `unitModulus_power_sum_not_tendsto_zero` applies as before.  The `hc_lower` hypothesis becomes a *geometric* lower bound `δ · ‖λ_B^{(k₀)} / λ_A^{(0)}‖^N ≤ ‖c_N‖`, which is exactly what `exists_dominant_adjusted_scalar_tendsto_norm_one_*` produces.

## Comparison

| Criterion | (a) drop strict-anti | (b) literal | (b′) two-layer |
|---|---|---|---|
| Effort | Very high (~5 PRs, 20+ sites) | Low (1 PR) | Medium (3 PRs) |
| Risk | Breaks equal-MPV FT, re-opens multiplicity gap | Mathematically unsound | Localized to SD surface |
| Paper-faithfulness | Partial (matches CPSV16 §II generally; ignores CPSV21 Def 4.2 two layers) | None (collapses spectral level into phases) | **Direct** (implements Def 4.2) |
| Downstream impact | Breaks 20+ existing proofs | None (because nothing transfers) | Zero impact on existing `IsCanonicalFormBNT` callers |
| Reversibility | Hard (multiplicity gap) | n/a | Easy (additive, adapter is pure construction) |

## Recommended PR roadmap

### PR 1 — Two-layer structure + adapter (~250 LoC, low risk)

* Extend `TNLean/MPS/FundamentalTheorem/SectorDecomposition/IsBNTCanonicalFormSD.lean` with the two-layer fields `spectralLevel`, `spectralLevel_ne_zero`, `spectralLevel_strict_anti`, and a factoring witness `weight_factor : ∀ j q, ‖P.sectors.weight j q / spectralLevel j‖ = 1`.
* Add an adapter `IsCanonicalFormBNT.toIsBNTCanonicalFormSD` in the same file (or a new `TwoLayer/Adapter.lean`) producing a `SectorDecomposition` via `trivialSectorDecomp` together with `SameMPV₂ P.toTensor (toTensorFromBlocks μ A)`.
* No `_CFBNT` sorries closed yet.

### PR 2 — Generalize `PerBlockProjection.fixed_*_sectorDecomp` to two-layer (~400-600 LoC, medium risk)

* Re-state the per-block-projection theorems using the two-layer hypothesis.
* The `unit_modulus` hypothesis becomes `weight_factor` (unit-modulus on `ν_{j,q}` after factoring out `λ_j`).
* The `hNoCancel` discharge in `HNoCancelDischarge.lean` is upgraded to accept a *geometric* lower bound on `‖c_N‖` (`δ · ‖λ_B^{(k₀)} / λ_A^{(0)}‖^N`); the analytic content (`unitModulus_power_sum_not_tendsto_zero`) carries over after the `(λ_{k₀})^N` extraction.
* No `_CFBNT` sorries closed yet.

### PR 3 — Discharge the two `_CFBNT` sorries (~200-400 LoC, low-medium risk)

* Replace the `sorry` at `Full/NondecayingOverlap/FixedBlockDecay.lean:107, 152` with proofs that:
  1. Build the two-layer SD from `hA` (resp. `hB`) via the PR 1 adapter.
  2. Translate the `IsCanonicalFormBNT`-side proportionality and decay hypotheses to the SD-side via the adapter's `SameMPV₂`.
  3. Apply the PR 2 generalized `fixed_*_sectorDecomp_twoLayer`.
  4. Fold the conclusion back to the `_CFBNT` signature.
* Closes the two `_CFBNT` sorries.

### PR 4 (optional cleanup)

* Update blueprint `\leanok` tags.
* Remove "Open obligation (non-dominant `k₀`)" docstring sections.
* Close issue #1607.
* Audit whether `exists_nondecaying_dominant_overlap_*_CFBNT` becomes obsoleted by the general lemma.

## Open caveats

### Multiplicity recovery is still out of scope

Even after PR 3, the `_CFBNT` sorries are closed only under the one-copy-per-sector restriction (the adapter consumes `IsCanonicalFormBNT` with `r_j = 1`).  The full multi-copy CPSV16 BNT canonical form with multiplicity recovery via Newton-Girard on `∑_q μ_{j,q}^N` is a separate paper-level gap and is not addressed by path β.  Path β makes the *SD surface* multi-copy-ready, but the *adapter from `IsCanonicalFormBNT`* only feeds the trivial multiplicity.  A future PR (out of scope here) would build the adapter from the more general construction in `PhaseClassSectorData.lean` (`exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks`).

### `c_lower`-geometric vs. `c_lower`-constant

The current `hc_lower` in `HNoCancelDischarge.lean` asks for a *constant* lower bound `‖c_N‖ ≥ δ`.  Under the two-layer adapter, the available lower bound is *geometric*: `‖c_N‖ ≥ δ · ‖λ_B^{(k₀)} / λ_A^{(0)}‖^N`.  PR 2 must generalize the discharge to accept the geometric form, or equivalently prove the contradiction after multiplying through by `(λ_B^{(k₀)} / λ_B^{(0)})^N` so that the rescaled scalar `c̃_N := c_N · (λ_B^{(k₀)} / λ_A^{(0)})^N` has a constant lower bound.  This rescaling is the non-trivial analytic step in PR 2; it is the path-α obstruction in a different guise, but resolvable because the two-layer form gives separate access to `λ_j`.

### Naming

The existing one-layer stub `IsBNTCanonicalFormSD` in `IsBNTCanonicalFormSD.lean` has no consumers (per `bridge_b_status.md`).  Replace it in-place with the two-layer version; no API break.

## References

* CPSV16 (arXiv:1606.00608) §II, particularly Theorem `thm1` and the BNT discussion.
* CPSV21 (arXiv:2011.12127) Definition 4.2 (two-layer BNT canonical form).
* `audits/2026-05-13_cpsv16_ft_bridge_gap.md` — original bridge-gap analysis identifying the mismatch.
* `audits/2026-05-13_cpsv16_ft_exact_leading_coeff.md` — probe ruling out path α (induction).
* `audits/2026-05-13_cpsv16_ft_bridge_b_status.md` — PR #1645 (Plan C, Objective B) status memo.
* Issue #1641 (Plan C tracker).
