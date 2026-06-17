# CPSV16 FT — bridge gap between `IsCanonicalFormBNT` and `SectorDecomposition`

**Date:** 2026-05-13
**Scope:** Plan C, Objective 3 (per issue #1641).
**Status:** Identified blocker; bridge not direct.  See "Resolution" below.

## Context

Plan C (issue #1641) re-states Paper Step 1 of arXiv:1606.00608 Theorem `thm1`
on the paper-faithful `SectorDecomposition` + `HasBNTSectorData` surface, in

  `TNLean/MPS/FundamentalTheorem/SectorDecomposition/PerBlockProjection.lean`

The lemmas

  `fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_sectorDecomp`
  `fixed_left_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_sectorDecomp`

require the **unit-modulus** hypothesis on at least one family's sector
weights:

  `(hP_unit : ∀ j q, ‖P.sectors.weight j q‖ = 1)`
  (`hQ_unit : ∀ k q, ‖Q.sectors.weight k q‖ = 1)`

This is the spectral-radius-1 normalization paper-faithful CPSV16 imposes at
every block in the BNT canonical form (every sector lives at the unit circle,
multiplicity is recovered inside the sector via Newton identities on
unit-modulus `μ_{j,q}`).

Objective 3 of #1641 asks to bridge this surface to the existing local
hypothesis `IsCanonicalFormBNT μ A` driving the two `sorry`s in

  `TNLean/MPS/FundamentalTheorem/Full/NondecayingOverlap.lean`

at the lemmas `_CFBNT` (`fixed_right_…_CFBNT`, `fixed_left_…_CFBNT`).

## The mismatch

`IsCanonicalFormBNT` (`TNLean/MPS/BNT/Construction.lean:99`) bundles, among
other fields, the **strict-anti** weight ordering:

```
mu_strict_anti : StrictAnti (fun k : Fin r => ‖μ k‖)
```

This is the one-copy-per-sector restriction (`copies j = 1`, `r_j = 1` for
every sector); the file's own scope comment names this explicitly:

> SCOPE(one-copy-per-sector): `mu_strict_anti` forces `r_j = 1`; all
> downstream FT theorems are restricted to this special case.

Under `StrictAnti`, the moduli `‖μ k‖` are pairwise distinct.  CPSV16's
paper-faithful canonical form normalizes the dominant weight to `‖μ 0‖ = 1`
and then has `‖μ k‖ < 1` for every `k ≥ 1` (a geometric decay).  In
particular, the unit-modulus hypothesis `∀ k, ‖μ k‖ = 1` is satisfied
**only at `k = 0`** and **fails for `k ≥ 1`**.

The Plan C theorems therefore do not directly apply to the
`IsCanonicalFormBNT` data shape: the bridge would need to supply `hP_unit` /
`hQ_unit`, and the strict-anti ordering forbids it for `r ≥ 2`.

## Why a direct bridge fails

The naive bridge would be:

1. From `IsCanonicalFormBNT μ A` (with `μ : Fin r → ℂ`,
   `A : Fin r → MPSTensor d _`) construct a `SectorDecomposition`
   `P_{μ,A}` with `basisCount = r`, `copies j = 1`, `weight j 0 = μ j`,
   `basis j = A j`.

2. Note `toTensor (P_{μ,A})` is propositionally equal to
   `toTensorFromBlocks μ A` (as the assembled block-diagonal tensor).

3. Derive `HasBNTSectorData` from the existing BNT linear-independence
   construction for separated CF blocks.

4. **Provide `hP_unit`.**  Here the bridge breaks: under `mu_strict_anti`,
   `‖μ j‖ ≠ 1` whenever `j ≥ 1` (after the normalization `‖μ 0‖ = 1` that
   CPSV16 uses; for general data, all `‖μ j‖` are distinct so unit-modulus
   fails for at least `r - 1` indices).

A rescaling that turns each `‖μ j‖` into 1 would require multiplying `μ j` by
`μ j / ‖μ j‖` (i.e., conjugating by `‖μ j‖`), but this is **not** an allowed
transformation: it changes the assembled MPV vectors by length-dependent
factors, breaking the proportionality hypothesis.  Equivalently, we cannot
rescale the blocks `A j` individually without breaking the left-canonical
normalization (`hCF.toIsLeftCanonicalBlockFamily`) and the self-overlap
limit (`hCF.toHasNormalizedSelfOverlap`).

## What the paper does instead

CPSV16's argument lives one layer up: the BNT canonical form sits *inside*
each spectral sector, with the sector weight `μ_{j,q}` all carrying modulus
1 *within sector* `j`, and the sector index `j` carrying a separate scaling
`λ_j` with `|λ_j| < |λ_0|` for `j ≥ 1`.  The Plan C `hP_unit` is about the
inside-sector weights `μ_{j,q}`, not about the sector-level `λ_j`.

The current `IsCanonicalFormBNT` formalization conflates these two layers
into a single one-copy-per-sector index, with `μ_k = λ_k` (no inside-sector
multiplicity recovered).  In particular it does **not** carry data of the
form

  "spectral level `λ_j` with associated within-sector weights `μ_{j,q}`,
   all of modulus 1, with multiplicity `r_j`."

To bridge cleanly, we need a refactor that splits `IsCanonicalFormBNT` into
two layers, or a new structure `IsBNTCanonicalForm` over `SectorDecomposition`
that bakes in `hP_unit` / `hQ_unit` at the sector-weight layer.

## Resolution

Objective 3 of #1641 is **NOT-STARTED** (intentional): the bridge cannot be
produced without a structural refactor of `IsCanonicalFormBNT` to expose the
two-layer spectral/within-sector decomposition.  Objective 4 (discharge of
the existing `_CFBNT` sorries) is therefore also **NOT-STARTED**.

The Plan C algebraic skeleton on the `SectorDecomposition` surface is in
place and stands on its own — `PerBlockProjection.lean` builds cleanly,
introduces no new `sorry`s, and is referenced from `TNLean.lean`.  The
follow-up workstream is to:

1. Introduce a `SectorDecomposition`-level "BNT canonical form" wrapper
   bundling `hP_unit` / `hQ_unit` (sector-weight unit-modulus) alongside
   `HasBNTSectorData`, decay of self/cross-overlaps inside the basis, and
   the dominant-weight normalization.  Call it `IsBNTCanonicalForm` (or
   similar) over a `SectorDecomposition`.

2. Provide the unconditional construction of this wrapper from the
   irreducible-primitive-TP block input (extending the existing
   `exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks` in
   `TNLean/MPS/CanonicalForm/PhaseClassSectorData.lean`).

3. Retire the strict-anti restriction inside `IsCanonicalFormBNT`, or pull
   it apart into a strict-anti wrapper over `IsBNTCanonicalForm`.

4. Discharge the load-bearing `hNoCancel` hypothesis of the Plan C lemmas
   for the new wrapper.  This is the analytic content: almost-periodicity
   of `∑_q μ_{j,q}^N` for unit-modulus weights, plus the dominant-weight-
   adjusted scalar limit from `ProportionalScalar.lean`.

5. Use the wrapper to rewrite `_CFBNT` callers in `NondecayingOverlap.lean`.

This is a multi-PR sequence and outside the time budget of #1641.

## Related infrastructure

* `TNLean/MPS/CanonicalForm/PhaseClassSectorData.lean` already provides
  `exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks` returning a
  `SectorDecomposition` + `HasBNTSectorData` from TP/primitive/irreducible
  block input.  It produces the assembled `P.toTensor` equal in MPV to the
  original `toTensorFromBlocks μ A`.  This is the natural foundation for
  the wrapper in step 1 above.

* `TNLean/MPS/FundamentalTheorem/Full/ProportionalScalar.lean` has
  `tendsto_norm_adjusted_weighted_mpvState_scalar_of_eventually_tendsto_norm_one`
  which controls `|c_N (ν/μ)^N| → 1` and is the input for the dominant-weight
  side of `hNoCancel`.

* `TNLean/Algebra/ScalarPowerSumIdentity.lean` is the natural home for the
  Newton-identity / almost-periodicity sub-lemma `coeff_N k₀ ↛ 0` for
  unit-modulus sector weights.

## References

* arXiv:1606.00608 Theorem `thm1`, lines 1170–1192 (the per-block
  projection argument).
* arXiv:2011.12127 Definition 4.2 (the two-layer BNT canonical form).
* `audits/2026-05-13_cpsv16_ft_definition_audit.md` §10 (Plan C YES verdict
  on the SectorDecomposition surface).
* `audits/2026-05-13_cpsv16_ft_discharge_attempt.md` (Plan A blocker on the
  restricted `IsCanonicalFormBNT` surface).
* Issue #1641 (Plan C workplan).
* PR #1639 (the wrong-direction-cleanup baseline).
