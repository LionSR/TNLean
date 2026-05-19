# CPSV16 FT — Paper-Faithful Multi-Copy Clean-Slate Plan

**Date:** 2026-05-13 (post issue #1678 final confirmation).
**Source of authority:** `blueprint/comments202605/cpsv16_bnt_gap_recommendation_examples.tex` (user-uploaded recommendation document).
**User directive (verbatim):**
* "we should thoroughly implment this and retire the other paths"
* "dont do this one copy interfaces anywhere anymore"
* "i want to be doing this cleanly from scrtach and retire all the wrong approaches anywhere comprehensivley"
* "dont build any adapters because they may have mathmeatical obstructions"

## Executive summary

This memo plans the **complete retirement** of the one-copy `IsCanonicalFormBNT` surface and the **clean-slate construction** of a CPSV multi-copy BNT canonical form, on which the entire FT chain (and its downstream consumers in RFP, ParentHamiltonian, PiAlgebra) will be re-proved from first principles.

**Hard constraints (from the user's directives):**

1. **No adapter from `IsCanonicalFormBNT` to the new structure.** The mathematical obstructions in such adapters (e.g., the Choice B rescaling residue, the multiplicity-recovery Newton-Girard gap) are not CPSV facts; any adapter would carry assumptions we cannot discharge.
2. **No use of the one-copy surface in new work**, anywhere in the codebase.
3. **The new structure must stand on its own** — defined directly from `SectorDecomposition` data without reference to `IsCanonicalFormBNT`.
4. **All theorems formerly proved on `IsCanonicalFormBNT` must be re-proved** on the new surface, not adapted.
5. **The `IsCanonicalFormBNT` surface, its associated machinery (cross_overlap_tendsto_zero, IsNormalCanonicalFormBNT, etc.), and all derived modules in `MPS/FundamentalTheorem/Full/`, `MPS/RFP/`, `MPS/ParentHamiltonian/BiCF/`, `MPS/ParentHamiltonian/DegenerateGS.lean`, and `MPS/PiAlgebra/CanonicalFormSep*.lean` must eventually be DELETED.**

## What's wrong with `IsCanonicalFormBNT`

`IsCanonicalFormBNT μ A` carries:
- `μ : Fin r → ℂ` — one weight per "block."
- `A : (k : Fin r) → MPSTensor d (dim k)` — one normal tensor per block.
- `mu_strict_anti : StrictAnti (fun k => ‖μ k‖)` — strict modulus ordering.
- BNT eventual LI on the basis blocks.
- Normalized self-overlap, irreducibility, left-canonical, block injectivity.

The CPSV16/CPSV21 paper's structure carries:
- Sectors `j ∈ Fin g` with multiplicities `r_j ≥ 1`.
- Within each sector `j`: `r_j` copies of the same normal tensor `A_j`, each carrying a weight `μ_{j,q}` (where `q ∈ Fin r_j`).
- Equal modulus within sector: `‖μ_{j,1}‖ = ⋯ = ‖μ_{j,r_j}‖ = λ_j` (the spectral level).
- Strict ordering between sectors: `λ_1 > λ_2 > ⋯ > λ_g`.

The one-copy surface is the specialization `r_j = 1` for all `j`. The user's recommendation document gives explicit counterexamples (the `C ⊕ (-C)` and `C ⊕ e^{iθ}C` examples in §2-3) showing that this specialization **collapses** genuine CPSV data: `V_N(C ⊕ -C) = (1 + (-1)^N) V_N(C)` cannot be written as `μ^N V_N(C)` for any single scalar `μ`.

## The CPSV structure

The new primary predicate `IsBNTCanonicalForm` (or chosen name) carries, given a `SectorDecomposition P : SectorDecomposition d`:

* **Spectral level** `λ : Fin P.basisCount → ℂ` with
  * `λ j ≠ 0` for every sector `j`,
  * `StrictAnti (fun j => ‖λ j‖)`,
  * `‖λ ⟨0, _⟩‖ = 1` (dominant normalization);
* **Within-sector unit-modulus weights** `ω : (j : Fin P.basisCount) → Fin (P.copies j) → ℂ` with
  * `P.sectors.weight j q = λ j * ω j q`,
  * `‖ω j q‖ = 1`;
* **Sector basis blocks** `P.basis : (j : Fin P.basisCount) → MPSTensor d (P.basisDim j)` (carried by `SectorDecomposition`);
* **Eventual linear independence** of basis blocks: `HasBNTSectorData P` (already in place);
* **Per-block normality data**: each `P.basis j` is a normal MPS tensor (injective TM, irreducible, left-canonical, normalized self-overlap).

The MPV assembly:
```
mpv P.toTensor σ
  = ∑_{j : Fin P.basisCount} P.coeff N j · mpv (P.basis j) σ
  = ∑_{j : Fin P.basisCount} (λ j)^N · (∑_{q : Fin (P.copies j)} (ω j q)^N) · mpv (P.basis j) σ.
```

The factor `(λ j)^N · (∑_q (ω j q)^N)` is the **sector coefficient** described in §1 of the user's recommendation document. Setting `r_j = 1` (one copy per sector) and `ω j 0 = 1` gives one-copy as a degenerate case, but we do not bridge.

**Note:** `IsBNTCanonicalFormSD` (from path β, currently on main at `TNLean/MPS/FundamentalTheorem/SectorDecomposition/IsBNTCanonicalFormSD.lean`) is **almost** this structure but with the `ω j q` factor packaged inside an existential. It also lacks the per-block normality data (irreducibility, etc.). For clean-slate construction, **rename/replace** `IsBNTCanonicalFormSD` with a properly-organized `IsBNTCanonicalForm` that exposes all fields and per-block normality.

## Retirement scope (everything to delete eventually)

### Modules using `IsCanonicalFormBNT` (242 references in 21 files)

#### Tier 1 — FT core (must be re-proved on new surface, then deleted)
* `TNLean/MPS/FundamentalTheorem/Full/NondecayingOverlap.lean` (27 refs) — including the equal-MPV `_sameMPV₂` non-decaying overlap proof.
* `TNLean/MPS/FundamentalTheorem/Full/NondecayingOverlap/FixedBlockDecay.lean` (7 refs).
* `TNLean/MPS/FundamentalTheorem/Full/NondecayingOverlap/CombinedLI.lean` (6 refs) — the weak existential we just built.
* `TNLean/MPS/FundamentalTheorem/Full/BlocksMatch.lean` (5 refs).
* `TNLean/MPS/FundamentalTheorem/Full/DominantWeight.lean` (3 refs).
* `TNLean/MPS/FundamentalTheorem/Full/NondecayingPartnerUnique.lean` (15 refs).
* `TNLean/MPS/FundamentalTheorem/Full/ProportionalDominant.lean` (18 refs).
* `TNLean/MPS/FundamentalTheorem/Full.lean` (6 refs).
* `TNLean/MPS/FundamentalTheorem/EqualProportional.lean` (8 refs).

#### Tier 2 — path β rate-quantified retired stack (delete entirely)
* `TNLean/MPS/FundamentalTheorem/Full/NondecayingOverlap/FixedBlockDecay_RateQuantified.lean` (52 refs).
* `TNLean/MPS/FundamentalTheorem/SectorDecomposition/RateQuantifiedDischarge.lean`.
* `TNLean/MPS/FundamentalTheorem/SectorDecomposition/RateQuantifiedDecay.lean` (1 ref).
* `TNLean/MPS/FundamentalTheorem/SectorDecomposition/CrossFamilyRateDecay.lean`.
* `TNLean/MPS/FundamentalTheorem/SectorDecomposition/RenormalizedNonCancellation.lean`.

#### Tier 3 — `SectorDecomposition` machinery (mostly clean, but adapters retired)
* `TNLean/MPS/FundamentalTheorem/SectorDecomposition/IsBNTCanonicalFormSD.lean` (11 refs) — KEEP the structure definition; **delete** the `IsCanonicalFormBNT.toIsBNTCanonicalFormSD` adapter at line 227.
* `TNLean/MPS/FundamentalTheorem/SectorDecomposition/PerBlockProjection.lean` (1 ref).
* `TNLean/MPS/FundamentalTheorem/SectorDecomposition/HNoCancelDischarge.lean` (2 refs).
* `TNLean/MPS/FundamentalTheorem/SectorDecomposition.lean` (1 ref).

#### Tier 4 — non-FT consumers (re-prove on new surface, then retire the one-copy import)
* `TNLean/MPS/BNT/Construction.lean` (28 refs) — defines `IsCanonicalFormBNT` itself, plus `cross_overlap_tendsto_zero`, `isBNT`, etc.
* `TNLean/MPS/RFP/StructuralForm.lean` (1 ref).
* `TNLean/MPS/ParentHamiltonian/BiCF/BlockDiagonalCommutant.lean` (30 refs).
* `TNLean/MPS/ParentHamiltonian/DegenerateGS.lean` (18 refs).
* `TNLean/PiAlgebra/CanonicalFormSep.lean` (1 ref).
* `TNLean/PiAlgebra/CanonicalFormSepAux.lean` (1 ref).

### Bridging machinery to delete

* `bntSectorDecomp` definitional adapter in `FixedBlockDecay_RateQuantified.lean` (carries one-copy → SD bridging).
* `IsCanonicalFormBNT.toIsBNTCanonicalFormSD` existential adapter in `IsBNTCanonicalFormSD.lean:227`.
* Any `_CFBNT` suffix lemmas that route through `IsCanonicalFormBNT` data.

### One-copy lemmas to retire (selection)

* `mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left_of_irreducible_TP` — actually a general-purpose tensor lemma; keep but ensure no spurious one-copy dependence in callers.
* `cross_overlap_tendsto_zero_of_separated_normalCFBNT_data` — re-state on new surface.
* `IsNormalCanonicalFormBNT.mu_dom_norm_one` — re-state with `λ` on new surface.

## Phased implementation plan

### Phase 0 — preserve the plan
**This memo.** Land it as documentation. No code changes.

### Phase 1 — design the new primary predicate

Create `TNLean/MPS/FundamentalTheorem/SectorBNT/Basic.lean` (or chosen location, NOT under `SectorDecomposition/`) with:

```lean
structure IsBNTCanonicalForm (P : SectorDecomposition d) : Prop where
  /-- Spectral level: one nonzero complex number per sector. -/
  spectralLevel : Fin P.basisCount → ℂ
  spectralLevel_ne_zero : ∀ j, spectralLevel j ≠ 0
  spectralLevel_strict_anti : StrictAnti (fun j => ‖spectralLevel j‖)
  spectralLevel_dom_norm_one : ∀ h : 0 < P.basisCount, ‖spectralLevel ⟨0, h⟩‖ = 1
  /-- Within-sector unit-modulus phase weights. -/
  phaseWeight : (j : Fin P.basisCount) → Fin (P.copies j) → ℂ
  phaseWeight_norm_one : ∀ j q, ‖phaseWeight j q‖ = 1
  /-- Factorization of the sector weights. -/
  weight_factor : ∀ j q, P.sectors.weight j q = spectralLevel j * phaseWeight j q
  /-- Per-block normality data. -/
  basis_injective : ∀ j, IsInjective (P.basis j)
  basis_irreducible : ∀ j, IsIrreducible (P.basis j)
  basis_left_canonical : ∀ j, IsLeftCanonical (P.basis j)
  basis_normalized_self_overlap : ∀ j,
    Tendsto (fun N => mpvOverlap (P.basis j) (P.basis j) N) atTop (nhds 1)
  /-- BNT eventual linear independence of basis blocks. -/
  bnt_data : HasBNTSectorData P
  /-- Distinctness of basis blocks (no gauge-phase equivalence between distinct sectors). -/
  basis_distinct : ∀ j k, j ≠ k → ¬ GaugePhaseEquiv (P.basis j) (P.basis k)
```

(Field names tentative; final names chosen to match Mathlib conventions and to avoid `_BNT` / `_SD` suffix patterns that signaled the migration state.)

**Examples** (must compile cleanly to validate the structure):
* `C ⊕ -C` example (one sector, two copies, `phaseWeight = (1, -1)`).
* `C ⊕ e^{iθ}C` (one sector, two copies, `phaseWeight = (1, e^{iθ})`).
* `C` alone (one sector, one copy, vacuous phase factor).

**Accessors** for the cross-overlap decay and self-overlap limits that current proofs need.

### Phase 2 — basic API

Prove (DIRECTLY on the new surface, no adapter):
* `weight_pow_decomp : P.sectors.weight j q ^ N = (spectralLevel j)^N · (phaseWeight j q)^N`.
* `coeff_eq : P.coeff N j = (spectralLevel j)^N · ∑_q (phaseWeight j q)^N`.
* `norm_coeff_le : ‖P.coeff N j‖ ≤ ‖spectralLevel j‖^N · P.copies j`.
* `cross_overlap_basis_tendsto_zero : ∀ j k, j ≠ k → Tendsto (fun N => mpvOverlap (P.basis j) (P.basis k) N) atTop (nhds 0)` — derived from `basis_distinct` + irreducibility (re-prove the existing `mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_*` chain on this surface).
* `eventually_linearIndependent_combined : (full pairwise A↔B decay) → combined LI` (re-use `eventually_linearIndependent_of_two_family_overlap_tendsto_orthonormal` from `BNT/Basic.lean:195`, which doesn't depend on `IsCanonicalFormBNT`).

### Phase 3 — re-prove the combined-family weak existential

`exists_nondecaying_overlap_pair_of_eventuallyProportional` directly on the new surface, mirroring the proof we wrote in `CombinedLI.lean` (commit `dd83c0b1`) but with one-copy references stripped.

### Phase 4 — re-prove the equal-MPV non-decaying overlap

Mirror the ~540-line `exists_nondecaying_overlap_of_sameMPV₂_CFBNT` proof for the new surface. Use the multi-copy sector coefficient `(λ_j)^N · ∑_q (ω_{j,q})^N` throughout. The dominant matching argument uses spectral level + dominant normalization.

### Phase 5 — block matching, equal-MPV FT, proportional FT

Re-prove `BlocksMatch`, `EqualProportional`, etc. on the new surface.

### Phase 6 — non-FT consumers

Port `RFP/StructuralForm`, `ParentHamiltonian/BiCF/BlockDiagonalCommutant`, `ParentHamiltonian/DegenerateGS`, `PiAlgebra/CanonicalFormSep*` to the new surface.

### Phase 7 — DELETE the one-copy surface

Once nothing imports `IsCanonicalFormBNT` from new work:
* Delete `IsCanonicalFormBNT` itself in `BNT/Construction.lean`.
* Delete all derived lemmas (`cross_overlap_tendsto_zero` from CFBNT, `isBNT` from CFBNT, etc.).
* Delete `IsBNTCanonicalFormSD` (replaced by `IsBNTCanonicalForm`).
* Delete the path β stack entirely (`RateQuantifiedDischarge.lean`, `FixedBlockDecay_RateQuantified.lean`, `RenormalizedNonCancellation.lean`, `RateQuantifiedDecay.lean`, `CrossFamilyRateDecay.lean`).
* Delete `Full/NondecayingOverlap/CombinedLI.lean` (was on one-copy surface; replaced by Phase 3).
* Delete `Full/NondecayingOverlap/FixedBlockDecay.lean` (one-copy).
* Delete the `_sameMPV₂_CFBNT` chain (replaced by Phase 4).

## Order of execution

Phase 0 is this memo (PR delivering it).

Phases 1-2 are the foundational PR (new structure + basic API). Estimated 800-1200 LoC.

Phase 3 is a focused PR (weak existential on new surface). Estimated 200-300 LoC.

Phase 4 is the largest PR (equal-MPV non-decaying overlap, mirroring 540-line proof on new surface). Estimated 600-900 LoC.

Phase 5 ports the equal-MPV FT downstream chain (BlocksMatch, EqualProportional, NondecayingPartnerUnique, etc.). Estimated 1000-1500 LoC across multiple PRs.

Phase 6 ports non-FT consumers. Estimated 500-1000 LoC across multiple PRs.

Phase 7 is the cleanup — file deletions. Net negative LoC.

**Estimated total scope:** 6-12 PRs, 3000-6000 LoC of new code, with corresponding deletions giving a net reduction.

## Anti-patterns / forbidden directions (carry forward, strict)

* **NO `IsCanonicalFormBNT → IsBNTCanonicalForm` adapter, ever.** Including `bntSectorDecomp` or `toIsBNTCanonicalForm` constructions.
* **NO `_CFBNT` suffix lemmas in new work.** Replace with clean names.
* **NO `mu_strict_anti` accessor in new work.** Use `spectralLevel_strict_anti`.
* **NO `mu : Fin r → ℂ` parameter in new lemmas.** Replace with `IsBNTCanonicalForm P` taking `P : SectorDecomposition d`.
* **NO claim that `IsCanonicalFormBNT` and `IsBNTCanonicalForm` are equivalent up to renaming.** They are not (multiplicity-recovery is a real paper-gap).
* **NO per-block projection / rate-quantified work** on the new surface — issue #1678 has ruled this out.
* **Per CPSV recommendation §8, items 4-5**: keep dominant projection as a useful special lemma; do not claim universal nondecay from it.

## Open paper-gap commitments to preserve

* `docs/paper-gaps/ft_one_copy_scope_restriction.tex` — currently records the multiplicity-recovery gap. **Reclassify**: the new surface eliminates this gap as a scope restriction. The paper-gap doc should be updated or retired once Phase 7 completes.
* `docs/paper-gaps/cpsv16_nondominant_per_block_projection.tex` — non-dominant projection failure. **Permanent paper-gap**: the analysis showing per-block projection fails for non-dominant blocks remains a useful informational document.

## What is preserved (NOT retired)

* `TNLean/MPS/BNT/Basic.lean` — `eventually_linearIndependent_of_two_family_overlap_tendsto_orthonormal` (line 195) and `coefficient_eventually_eq_of_eventually_linearIndependent` (line 172). These are the analytic engines, applicable to any normal MPS family with appropriate decay. They will be **used** by the new surface, not deleted.
* `SectorDecomposition` infrastructure — the abstract sector-decomposition machinery (basis, coeff, weights). This is fine and not one-copy.
* `mpvOverlap`, `mpvInner`, `mpvState`, `IsInjective`, `IsIrreducible`, `IsLeftCanonical`, `GaugePhaseEquiv`, all the low-level normal-tensor lemmas. They are not coupled to one-copy.

## Risk assessment

* **Highest risk:** Phase 4 (equal-MPV non-decaying overlap proof on multi-copy). The 540-line proof uses dominant-pair matching + tail reduction. Multi-copy may introduce additional complications. Mitigation: stage Phase 4 as multiple sub-PRs (dominant case, tail reduction with multi-copy bookkeeping, packaging).
* **Medium risk:** Phase 5 downstream (BlocksMatch handles the matching permutation; on multi-copy, the matching could be sector-level or sector-and-copy-level — need to commit to a shape early).
* **Low risk:** Phases 1-3 (foundational, mostly mechanical given the design).
* **Low risk:** Phase 6 (consumers).
* **Trivial:** Phase 7 (mechanical deletions).

## Decision point (user input required before Phase 1)

The choice of MATCHING SHAPE in Phase 5 matters:
* **Option α**: matching is sector-level (the multi-copy structure within each sector is preserved as a separate datum). Cleaner downstream.
* **Option β**: matching pairs (sector, copy) on each side. More expressive but requires more bookkeeping.

CPSV21 uses Option α implicitly (sector-level). I recommend Option α as the default.

## Status

This memo is the entirety of Phase 0. After landing, Phase 1 dispatches the new structure + examples + basic API.
