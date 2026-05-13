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

## PR 1 implementation record (2026-05-13)

PR 1 of path β has landed on `feat/mps-ft-path-beta-pr1-two-layer`.  This section records the signatures, decisions, and the pick-up point for PR 2.

### Signatures in PR 1

The file `TNLean/MPS/FundamentalTheorem/SectorDecomposition/IsBNTCanonicalFormSD.lean` now exposes:

* `structure IsBNTCanonicalFormSD (P : SectorDecomposition d) : Prop` with two fields
  - `exists_spectralLevel : ∃ lam : Fin P.basisCount → ℂ, (∀ j, lam j ≠ 0) ∧ StrictAnti (fun j => ‖lam j‖) ∧ (∀ j q, ‖P.sectors.weight j q / lam j‖ = 1)`
  - `bnt_data : HasBNTSectorData P`
* `noncomputable def IsBNTCanonicalFormSD.spectralLevel : IsBNTCanonicalFormSD P → Fin P.basisCount → ℂ` (via `Classical.choose`)
* `theorem IsBNTCanonicalFormSD.spectralLevel_ne_zero`
* `theorem IsBNTCanonicalFormSD.spectralLevel_strict_anti`
* `theorem IsBNTCanonicalFormSD.weight_factor : ‖P.sectors.weight j q / h.spectralLevel j‖ = 1`
* `theorem IsCanonicalFormBNT.toIsBNTCanonicalFormSD : IsCanonicalFormBNT μ A → ∃ P, IsBNTCanonicalFormSD P ∧ SameMPV₂ P.toTensor (toTensorFromBlocks μ A)`

### Structural decision: `∃`-packaged spectral level

The brief described `spectralLevel` as a direct structure field.  Lean 4 rejects `Prop`-valued structures with `Type`-valued fields (`failed to generate projection ... field must be a proof`), so the spectral level is packaged inside `exists_spectralLevel : ∃ lam, …` and exposed via `Classical.choose` accessors.  This keeps the predicate genuinely `Prop`-valued (matching the rest of the canonical-form predicate family) and is transparent to downstream users because the four accessor lemmas (`spectralLevel`, `spectralLevel_ne_zero`, `spectralLevel_strict_anti`, `weight_factor`) provide the layer data on demand.

### Adapter construction

The adapter `IsCanonicalFormBNT.toIsBNTCanonicalFormSD` uses the existing `trivialSectorDecomp` and `sameMPV₂_trivialSectorDecomp` from `TNLean/MPS/CanonicalForm/BNTGrouping.lean`, with:

* `spectralLevel := μ`,
* `spectralLevel_ne_zero := hCF.toIsCanonicalForm.mu_ne_zero`,
* `spectralLevel_strict_anti := hCF.mu_strict_anti`,
* `weight_factor := fun j q => …` discharged by `div_self (hμne j)` (since `(trivialSectorDecomp μ A).sectors.weight j q = μ j` and `μ j / μ j = 1`),
* `bnt_data := hCF.isBNT.eventually_li` (the trivial sector decomposition has `basis = A`, so `HasBNTSectorData` reduces to eventual linear independence on the original blocks, which is the `eventually_li` field of `IsCanonicalFormBNT.isBNT`).

No new helper lemmas were needed — `trivialSectorDecomp`, `sameMPV₂_trivialSectorDecomp`, and `IsCanonicalFormBNT.isBNT` already existed.

### Naming and file placement decisions

* **Replaced the one-layer stub in place.**  The previous `IsBNTCanonicalFormSD` had fields `unit_modulus` and `bnt_data`; both are gone in the two-layer version.  No consumers needed updates (only `TNLean.lean` registered the module; no callers existed).
* **No new files.**  The adapter lives in the same file as the structure definition (`IsBNTCanonicalFormSD.lean`), matching the co-location pattern of `IsCanonicalFormBNT.isBNT` in `MPS/BNT/Construction.lean`.  `TNLean.lean` already imports `TNLean.MPS.FundamentalTheorem.SectorDecomposition.IsBNTCanonicalFormSD` at line 231; no registration change was needed.

### PR 2 pick-up

PR 2 ("Generalize `PerBlockProjection.fixed_*_sectorDecomp` to two-layer") will:

1. Re-state the per-block-projection theorems in `SectorDecomposition/PerBlockProjection.lean` using `IsBNTCanonicalFormSD` (replacing the implicit `unit_modulus` hypothesis with `weight_factor`).
2. Upgrade `HNoCancelDischarge.lean` to accept the *geometric* lower bound `‖c_N‖ ≥ δ · ‖λ_B^{(k₀)} / λ_A^{(0)}‖^N`, either directly or via the rescaled-scalar substitution `c̃_N := c_N · (λ_B^{(k₀)} / λ_A^{(0)})^N`.
3. Keep `_CFBNT` callers untouched.  PR 3 then closes the two `_CFBNT` sorries at `Full/NondecayingOverlap/FixedBlockDecay.lean:107, 152` by composing the PR 1 adapter with the PR 2 generalized per-block-projection theorems.

## PR 1.5 amendment (2026-05-13) — dominant normalization `‖λ_0‖ = 1`

### Why the amendment is needed

The PR 2 scout (`/executions/c58263cc3990/report`) found that without
the dominant normalization `‖λ_0‖ = 1`, the analytic discharge on the
non-dominant `k₀` branch in `HNoCancelDischarge.lean` has a fundamental
gap: the lower bound on `‖c_N‖` is only *geometric*
(`δ · ‖λ_B^{(k₀)} / λ_A^{(0)}‖^N`), not constant.  The one-layer
analytic argument (`unitModulus_power_sum_not_tendsto_zero` applied to
the rescaled scalar `c̃_N`) requires the constant lower bound, and the
geometric form does not transfer without an additional uniform bound
on `‖coeff N j‖`.

Under the dominant normalization, every spectral level satisfies
`‖λ_j‖ ≤ 1` (`spectralLevel_norm_le_one`), so `‖coeff N j‖ ≤ copies j`
uniformly in `N` — exactly the one-layer regime.  The geometric
problem dissolves and the existing analytic discharge lifts
mechanically.

This matches CPSV21 Definition 4.2 (the paper-faithful normalization
form), so it is the correct structural fix rather than a workaround.

### What was added

In `TNLean/MPS/FundamentalTheorem/SectorDecomposition/IsBNTCanonicalFormSD.lean`:

* The existential `exists_spectralLevel` gained a fourth clause
  `(∀ h : 0 < P.basisCount, ‖lam ⟨0, h⟩‖ = 1)`.  This is vacuous when
  `P.basisCount = 0` and asserts unit modulus of the dominant level
  otherwise, exactly mirroring `IsNormalCanonicalFormBNT.mu_dom_norm_one`
  in `TNLean/MPS/BNT/Construction.lean`.
* A new accessor `IsBNTCanonicalFormSD.spectralLevel_dom_norm_one`
  extracts the dominant unit-modulus condition.
* A new corollary `IsBNTCanonicalFormSD.spectralLevel_norm_le_one`
  combines the dominant normalization with `spectralLevel_strict_anti`
  to give a uniform bound `‖λ_j‖ ≤ 1`.

### Adapter choice (Choice B — rescale at adapter level)

The adapter `IsCanonicalFormBNT.toIsBNTCanonicalFormSD` was rewritten
to rescale internally.  Three options were considered:

* **Choice A** (require `IsNormalCanonicalFormBNT`): cleaner type
  signature but forces every `_CFBNT` caller (the FixedBlockDecay
  sorries at `:107` and `:152`) to switch input hypotheses.
* **Choice B** (rescale at adapter level): the adapter consumes
  `IsCanonicalFormBNT` (no signature change for PR 3 callers), defines
  `ρ := ‖μ_0‖` (or `1` when `r = 0`), sets `λ_j := μ_j / ρ`, and
  exposes the assembled-tensor relation as `NonzeroProportionalMPV₂
  P.toTensor (toTensorFromBlocks μ A)` with per-length scalar
  `(ρ^N)⁻¹`.  The original `SameMPV₂` output is *replaced* (it could
  no longer be true once the dominant block is normalized).
* **Choice C** (both variants): unnecessary complexity; no caller of
  the old `SameMPV₂`-form adapter existed yet.

**Choice B was selected** because the `_CFBNT` sorries
(`Full/NondecayingOverlap/FixedBlockDecay.lean:107, 152`) take
`IsCanonicalFormBNT μA A` / `IsCanonicalFormBNT μB B` as inputs.
Switching the adapter to `IsNormalCanonicalFormBNT` (Choice A) would
have required either re-statinging those lemmas or providing a thin
wrapper at every call site.  Rescaling internally keeps the adapter as
the single point where the normalization is absorbed.

The output relation `NonzeroProportionalMPV₂ P.toTensor
(toTensorFromBlocks μ A)` is composable with the
`EventuallyNonzeroProportionalMPV₂` hypothesis on the
`toTensorFromBlocks` surface: PR 3 will chain
`NonzeroProportionalMPV₂.symm` (or its eventual form) twice to
transfer proportionality between `P_A.toTensor` and `P_B.toTensor` on
the SD surface.

### Updated adapter signature

```lean
theorem IsCanonicalFormBNT.toIsBNTCanonicalFormSD
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    {μ : Fin r → ℂ} {A : (k : Fin r) → MPSTensor d (dim k)}
    (hCF : IsCanonicalFormBNT μ A) :
    ∃ P : SectorDecomposition d,
      IsBNTCanonicalFormSD P ∧
      NonzeroProportionalMPV₂ P.toTensor
        (toTensorFromBlocks (d := d) (μ := μ) A)
```

### Consequences for PR 2 scope

The original PR 2 scope (generalize `PerBlockProjection.fixed_*_sectorDecomp`
to the two-layer setting, lift `HNoCancelDischarge` to accept geometric
`c_lower`) is now **achievable as-is, without rate-controlled
hypotheses**.  Specifically:

* `‖coeff N j‖ ≤ copies j` is uniform in `N`
  (`spectralLevel_norm_le_one` + `weight_factor`), so the
  `coeff_bound_uniform` step in `HNoCancelDischarge` reduces to the
  one-layer case.
* The `c_lower` problem becomes constant (not geometric) on every
  branch, including the non-dominant `k₀` branch identified in the PR 2
  scout report.
* The rescaling factor `(ρ^N)⁻¹` between `P.toTensor` and
  `toTensorFromBlocks μ A` is uniform, so it absorbs cleanly into the
  per-length proportionality scalar produced by
  `EventuallyNonzeroProportionalMPV₂` in PR 3.

### Downstream impact

* No pre-existing proofs needed touching.  The two `_CFBNT` sorries in
  `Full/NondecayingOverlap/FixedBlockDecay.lean` and all other callers
  of `IsCanonicalFormBNT` / `IsNormalCanonicalFormBNT` are unchanged.
* `lake build` succeeds (8675/8675 jobs, no new errors; pre-existing
  `sorry` count unchanged).
