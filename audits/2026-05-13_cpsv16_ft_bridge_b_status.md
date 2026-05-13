# CPSV16 FT — `IsCanonicalFormBNT` → `SectorDecomposition` status memo (Plan C, Objective B)

**Date:** 2026-05-13 (revised after corrective restoration)
**Scope:** Plan C follow-up workstream B (per issue #1641 — branch
`feat/mps-ft-plan-c-B-bridge-wrapper`).
**Status:** Dominant-block discharge added; general `_CFBNT` sorries
explicitly open with documented obstruction.

## Summary

This memo documents the current state of the connection between
`IsCanonicalFormBNT` (the existing one-copy-per-sector local hypothesis in
`TNLean/MPS/BNT/Construction.lean`) and the paper-faithful per-block
projection lemmas of
`TNLean/MPS/FundamentalTheorem/SectorDecomposition/PerBlockProjection.lean`
(Plan C, PR #1643).

A previous revision of this workstream attempted to close the two `_CFBNT`
fixed-block sorries by routing the analytic non-cancellation content
through an explicit hypothesis `hAdjustedOverlapNoDecay`.  That hypothesis
is **false for any non-dominant fixed block** under
`IsCanonicalFormBNT.mu_strict_anti` (the dominant-adjusted scalar times the
projected self-overlap on `B_{k₀}` with `k₀ ≠ 0` decays geometrically), so
the resulting lemma was vacuously true by ex-falso rather than genuinely
discharged.  Reviewers (claude review §1a/§1b on PR #1645 and the PR
author) flagged this; the present revision restores the sorries with an
honest **Open obligation** docstring section and adds the genuinely-closed
dominant-block specialisations.

This workstream now delivers:

* a paper-faithful BNT canonical-form predicate
  `IsBNTCanonicalFormSD` on the `SectorDecomposition` surface, staged for
  the eventual upstream refactor (no consumers in this PR — see
  Constraints honoured below);
* the dominant-block discharges
  `fixed_right_dominant_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT`
  and
  `fixed_left_dominant_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT`
  in `TNLean/MPS/FundamentalTheorem/Full/NondecayingOverlap/FixedBlockDecay.lean`,
  proved unconditionally from `IsCanonicalFormBNT` plus the existing
  dominant-adjusted scalar limit
  `exists_dominant_adjusted_scalar_tendsto_norm_one_of_eventuallyNonzeroProportionalMPV₂_CFBNT`;
* an upstream specialisation
  `exists_nondecaying_dominant_overlap_of_nonzeroProportionalMPV₂_CFBNT`
  in `TNLean/MPS/FundamentalTheorem/Full/NondecayingOverlap.lean`
  consuming the two dominant-block discharges.

The two general `_CFBNT` sorries are **explicitly open**.  The upstream
caller `exists_nondecaying_overlap_of_nonzeroProportionalMPV₂_CFBNT` keeps
its prior (merge-base) signature, so the blueprint `\leanok` tags at
`blueprint/src/chapter/ch11_fundamental_theorem_proof.tex` remain valid for
the statements they were attached to.

## Status of the `_CFBNT` sorries

* **`fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT`**
  — **open for non-dominant `k₀`**.  Dominant case
  (`k₀ = ⟨0, _⟩`) closed by
  `fixed_right_dominant_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT`.
* **`fixed_left_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT`**
  — **open for non-dominant `j₀`**.  Dominant case
  (`j₀ = ⟨0, _⟩`) closed by
  `fixed_left_dominant_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_CFBNT`.

Resolving the general case requires the structural refactor described in
`audits/2026-05-13_cpsv16_ft_bridge_gap.md` §Resolution — splitting
`IsCanonicalFormBNT` into a spectral level (`λ_j` with strict
modulus ordering) and a within-sector unit-modulus level
(`μ_{j,q}` with `‖μ_{j,q}‖ = 1`).  Without that split, the unit-modulus
hypothesis required by
`TNLean.MPS.FundamentalTheorem.SectorDecomposition.PerBlockProjection`
fails for every non-dominant weight under
`IsCanonicalFormBNT.mu_strict_anti`, and the analytic non-cancellation
argument cannot be transported across the surfaces.

## Dominant-block discharge

`fixed_right_dominant_…_CFBNT` proves the case `k₀ = ⟨0, _⟩` of the right
fixed-block contradiction.  The proof combines:

1. the LHS-overlap expansion `∑_j (μA j)^N · ⟨V^{(N)}(A_j), V^{(N)}(B_0)⟩`
   normalised by `(μA ⟨0,_⟩)^N`, with each summand tending to zero by
   `bounded_mul_tendsto_zero` (geometric `(μA j / μA ⟨0,_⟩)^N` against
   `hAllDecay` for `j ≠ ⟨0,_⟩`; direct `hAllDecay` for `j = ⟨0,_⟩`);
2. the RHS-overlap expansion
   `∑_k (μB k)^N · ⟨V^{(N)}(B_k), V^{(N)}(B_0)⟩` normalised by
   `(μB ⟨0,_⟩)^N`, with the diagonal `k = ⟨0,_⟩` term contributing the
   self-overlap limit `1`
   (`hB.toHasNormalizedSelfOverlap.overlap_tendsto_one`) and off-diagonal
   `k ≠ ⟨0,_⟩` terms decaying geometrically against
   `hB.cross_overlap_tendsto_zero`;
3. the dominant-weight-adjusted scalar limit
   `‖c N · (μB ⟨0,_⟩ / μA ⟨0,_⟩)^N‖ → 1` from
   `exists_dominant_adjusted_scalar_tendsto_norm_one_of_eventuallyNonzeroProportionalMPV₂_CFBNT`.

Combining (1) gives the asymptotic
`(μA ⟨0,_⟩)^{-N} · c N · ⟨V^{(N)}(toTensorFromBlocks μB B), V^{(N)}(B_0)⟩ → 0`,
while combining (2) and (3) shows the same quantity has modulus tending to
`1`.  Contradiction.

`fixed_left_dominant_…_CFBNT` reduces to the right form by swapping
families via `eventuallyNonzeroProportionalMPV₂_symm` and using
`tendsto_mpvOverlap_zero_swap`.

## Files added / modified (this revision)

| Path | Change |
| --- | --- |
| `TNLean/MPS/FundamentalTheorem/Full/NondecayingOverlap/FixedBlockDecay.lean` | Restored the two `_CFBNT` sorries with open-obligation docstrings; added the two `_dominant_…_CFBNT` lemmas |
| `TNLean/MPS/FundamentalTheorem/Full/NondecayingOverlap.lean` | Restored prior signature of `exists_nondecaying_overlap_…_CFBNT`; added `exists_nondecaying_dominant_overlap_…_CFBNT` |
| `TNLean/MPS/FundamentalTheorem/SectorDecomposition/IsBNTCanonicalFormSD.lean` | Trimmed to just the `IsBNTCanonicalFormSD` structure + paper docstring; removed the unused `dominantPhaseSectorDecomp` adapter, `of_isCanonicalFormBNT`, and `hc_lower_of_isCanonicalFormBNT` |
| `audits/2026-05-13_cpsv16_ft_bridge_b_status.md` | This revised memo |

`IsBNTCanonicalFormSD` is the eventual landing target of the upstream
refactor in `audits/2026-05-13_cpsv16_ft_bridge_gap.md` §Resolution.  It is
staged here without consumers in this PR; the follow-on PR that introduces
its first consumer will also add the corresponding blueprint entry.

## Constraints honoured

* **No new `sorry` / `axiom` / `unsafe`** beyond the two restored sorries
  (which carry the merge-base statement; the blueprint `\leanok` tags
  remain valid).
* **No combined-family LI / RSE / Option-LI hypotheses.**
* **No peel-arbitrary-`k₀` induction architecture.**
* **No `ProportionalDecompositionData` arrays.**
* **No edits to the wrong-direction-cleanup retired modules from #1639.**
* **`lake build` passes** (8673 jobs).

## References

* arXiv:1606.00608 Theorem `thm1`, lines 1170--1192 (paper Step 1).
* arXiv:2011.12127 Definition 4.2 (the two-layer BNT canonical form).
* `audits/2026-05-13_cpsv16_ft_bridge_gap.md` (structural obstruction
  analysis; §Resolution describes the upstream refactor needed to close
  the non-dominant case).
* `audits/2026-05-13_cpsv16_ft_definition_audit.md` §10 (Plan C YES
  verdict).
* `docs/paper-gaps/ft_one_copy_scope_restriction.tex` (scope restriction).
* `docs/paper-gaps/cpsv16_fixed_block_cancellation.tex` (cancellation
  obligation tracker for the open non-dominant case).
* Issue #1641 (Plan C workplan).
* Issue #1607 (fixed-block contradiction tracker).
* PR #1643 (Plan C, `SectorDecomposition` surface).
* PR #1644 (Plan C, branch A, `hNoCancel` analytic discharge — companion).
* PR #1645 (this PR, with review feedback prompting the corrective
  restoration).
