/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.BNTGrouping
import TNLean.MPS.FundamentalTheorem.Proportional
import TNLean.MPS.Overlap.CastLemmas
import TNLean.MPS.Structure.PrimitivityBridge

open scoped Matrix BigOperators
open Filter

/-!
# Equal-norm bridge: from BNT properties to BNT grouping hypotheses

This file bridges the gap between the BNT overlap/spectral theory and the
BNT grouping theorem (`exists_bnt_grouping`), which requires `hDimEq` and `hMPVEq`
for equal-norm blocks.

## Background (Issue #243)

The existence reduction pipeline (`Assembly.lean`) produces TP + primitive blocks with
nonzero weights.  The BNT grouping theorem groups blocks by weight norm into a
`SectorDecomposition`, but requires two hypotheses for equal-norm blocks:

* `hDimEq`: equal-norm blocks have the same bond dimension.
* `hMPVEq`: equal-norm blocks have `SameMPV₂`.

In the BNT theory (CPGSV17, §2.3), two blocks from the same decomposition with the same
weight norm are gauge-phase equivalent.  Gauge-phase equivalence gives `dim j = dim k`
and `mpv(B)(σ) = ζ^N * mpv(A)(σ)` with `‖ζ‖ = 1`.

## Strategy: gauge-phase-aware BNT grouping

Instead of deriving `SameMPV₂` (which requires `ζ = 1` exactly), we provide a variant
of the BNT grouping theorem (`exists_bnt_grouping_of_gaugePhaseEquiv`) that accepts
gauge-phase equivalence data and absorbs the gauge phase into the sector weights.

For block k gauge-phase equivalent to representative block j via `(X, ζ)`:
- `mpv(blocks k)(σ) = ζ^N * mpv(blocks j)(σ)`
- Contribution to total: `(μ_k)^N * mpv(blocks k)(σ) = (ζ * μ_k)^N * mpv(blocks j)(σ)`
- Effective sector weight: `ζ * μ_k`, with `‖ζ * μ_k‖ = ‖μ_k‖` (since `‖ζ‖ = 1`)

## Main results

* `exists_bnt_grouping_of_gaugePhaseEquiv` — BNT grouping theorem taking gauge-phase
  equivalence data (rather than `SameMPV₂`) for equal-norm blocks.  The gauge phases
  are absorbed into the sector weights.  **Fully proved.**

* `norm_gaugePhase_eq_one_of_irr_TP_primitive` — The gauge phase between two
  TP-normalized irreducible primitive blocks has unit norm.  **Fully proved.**

* `gaugePhaseEquiv_of_equal_norm_blocks` — Equal-norm blocks from the same TP +
  primitive + irreducible decomposition are gauge-phase equivalent.  **Contains one
  sorry** (the internal proportionality argument, see §1).

* `exists_sectorDecomp_of_tp_primitive_irr_blocks` — Pipeline endpoint connecting
  the reduction output to a BNT-grouped `SectorDecomposition`.  **Proved modulo
  the sorry in `gaugePhaseEquiv_of_equal_norm_blocks`.**

## Remaining gap

The one remaining `sorry` is in `gaugePhaseEquiv_of_equal_norm_blocks` (§1).
See its docstring for the precise mathematical argument needed.

## References

- [CPGSV17, Definition 2.6, Proposition 2.7]: BNT minimality and grouping.
- [CPGSV17, §2.3]: Equal-norm blocks are gauge-phase equivalent.
- GitHub issue #243: BNT grouping for weight norm separation.
-/

namespace MPSTensor

variable {d : ℕ}

/-! ### Auxiliary cast lemma -/

/-- Casting the bond dimension preserves the primitivity of the transfer map. -/
private lemma isPrimitive_transferMap_cast_dim {d D₁ D₂ : ℕ} (h : D₁ = D₂)
    (A : MPSTensor d D₁) :
    _root_.IsPrimitive (transferMap (d := d) (D := D₂)
      (cast (congr_arg (MPSTensor d) h) A)) ↔
    _root_.IsPrimitive (transferMap (d := d) (D := D₁) A) := by
  subst h; rfl

/-! ### §1. Gauge-phase equivalence from equal norms (key gap) -/

/-- **Equal-norm blocks from the same BNT decomposition are gauge-phase equivalent.**

Given a family of TP + primitive + irreducible blocks with nonzero weights,
two blocks j, k with `‖μ j‖ = ‖μ k‖` and `j ≠ k` must be gauge-phase equivalent.

**Paper argument (CPGSV17, §2.3 / Appendix A):**
1. Both blocks contribute at the same rate `‖μ‖^N` in the BNT expansion.
2. Taking the overlap of the full tensor with block k isolates the contribution
   of blocks with non-decaying overlaps.
3. At the level of individual blocks, `‖μ j‖ = ‖μ k‖` and the asymptotic
   orthonormality of the BNT family forces the overlaps to satisfy a matrix
   identity whose only solution (given primitivity) is proportional MPVs.
4. `gaugePhaseEquiv_of_proportionalMPV₂_of_overlap_tendsto_one_of_irreducible_TP`
   converts proportional MPVs to gauge-phase equivalence.

Step 3 requires spectral analysis of the joint transfer map for blocks j and k,
which is not yet formalized.  Specifically, one needs:
- From `‖μ j‖ = ‖μ k‖`, the N-th powers `(μ j)^N` and `(μ k)^N` have the same
  absolute growth rate.
- BNT linear independence (from `isBNT_of_separated_CFBNT_data`) implies that
  if the coefficient ratio `(μ j / μ k)^N` does not converge, then the overlaps
  between blocks j and k must still be controlled by the spectral gap of the
  joint transfer map.
- The resulting proportionality is then fed to the existing
  `gaugePhaseEquiv_of_proportionalMPV₂_of_overlap_tendsto_one_of_irreducible_TP`.

NOTE: This sorry represents the key mathematical gap identified in issue #243. -/
theorem gaugePhaseEquiv_of_equal_norm_blocks
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hTP : ∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1)
    (hIrr : ∀ k, IsIrreducibleTensor (blocks k))
    (hPrim : ∀ k, _root_.IsPrimitive (transferMap (d := d) (D := dim k) (blocks k)))
    (hμne : ∀ k, μ k ≠ 0)
    (j k : Fin r) (hjk : j ≠ k) (hNorm : ‖μ j‖ = ‖μ k‖) :
    ∃ hdim : dim j = dim k,
      GaugePhaseEquiv (d := d)
        (cast (congr_arg (MPSTensor d) hdim) (blocks j)) (blocks k) := by
  -- TODO(#243): prove the proportionality step needed to upgrade equal-norm
  -- TP-normalized irreducible primitive blocks to gauge-phase equivalence.
  sorry

/-! ### §2. BNT grouping with gauge-phase equivalence -/

/-- **BNT grouping step with gauge-phase equivalence for equal-norm blocks.**

This is a variant of `exists_bnt_grouping` that takes gauge-phase equivalence data
(rather than `SameMPV₂`) for equal-norm blocks.  The gauge phases are absorbed into
the sector weights, preserving norm-class membership since `‖ζ‖ = 1`.

Given a weighted block family `(μ, blocks)` where some blocks may share the same norm
`‖μ j‖ = ‖μ k‖`, and given that equal-norm blocks are gauge-phase equivalent with
unit-norm phases, there exists a `SectorDecomposition P` with:

1. `SameMPV₂ P.toTensor (toTensorFromBlocks μ blocks)`.
2. `StrictAnti` on the BNT-level norms (one norm value per group).

**Proof**: The construction is identical to `exists_bnt_grouping` (§5 of
`BNTGrouping.lean`), except that the sector weight for copy q of group j is
`ζ_{j,q} * μ_{enum(j,q)}` where `ζ_{j,q}` is the gauge phase relating
`blocks(enum(j,q))` to `blocks(repr(j))`.  The `SameMPV₂` identity uses the
factorization `(ζ * μ)^N = ζ^N * μ^N` to replace `mpv(blocks(repr j))` with
`mpv(blocks(enum j q))`. -/
theorem exists_bnt_grouping_of_gaugePhaseEquiv
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hμne : ∀ k, μ k ≠ 0)
    -- Equal-norm blocks are gauge-phase equivalent with unit-norm phase.
    (hGPE : ∀ j k : Fin r, ‖μ j‖ = ‖μ k‖ →
      ∃ ζ : ℂ, ζ ≠ 0 ∧ ‖ζ‖ = 1 ∧
        ∀ (N : ℕ) (σ : Fin N → Fin d),
          mpv (blocks k) σ = ζ ^ N * mpv (blocks j) σ) :
    ∃ P : SectorDecomposition d,
      SameMPV₂ P.toTensor (toTensorFromBlocks (d := d) (μ := μ) blocks) ∧
      StrictAnti (fun j : Fin P.basisCount =>
        ‖P.sectors.weight j ⟨0, P.sectors.copies_pos j⟩‖) := by
  classical
  let classes := normClassGroupingData μ
  let reprFn : Fin classes.g → Fin r := fun j => classes.enum j ⟨0, classes.copies_pos j⟩
  have hRepr_norm : ∀ j, ‖μ (reprFn j)‖ = classes.vals j :=
    fun j => classes.enum_norm j ⟨0, classes.copies_pos j⟩
  -- ── Step 1: Extract gauge-phase data for each norm class ─────────────────
  have hGPE_repr : ∀ j q,
      ∃ ζ : ℂ, ζ ≠ 0 ∧ ‖ζ‖ = 1 ∧ ∀ (N : ℕ) (σ : Fin N → Fin d),
        mpv (blocks (classes.enum j q)) σ = ζ ^ N * mpv (blocks (reprFn j)) σ :=
    fun j q => hGPE (reprFn j) (classes.enum j q)
      (hRepr_norm j |>.trans (classes.enum_norm j q).symm)
  let ζFn : (j : Fin classes.g) → Fin (classes.copies j) → ℂ :=
    fun j q => (hGPE_repr j q).choose
  have hζ_ne : ∀ j q, ζFn j q ≠ 0 := fun j q => (hGPE_repr j q).choose_spec.1
  have hζ_norm : ∀ j q, ‖ζFn j q‖ = 1 := fun j q => (hGPE_repr j q).choose_spec.2.1
  have hζ_mpv : ∀ j (q : Fin (classes.copies j)) (N : ℕ) (σ : Fin N → Fin d),
      mpv (blocks (classes.enum j q)) σ = (ζFn j q) ^ N * mpv (blocks (reprFn j)) σ :=
    fun j q N σ => (hGPE_repr j q).choose_spec.2.2 N σ
  -- ── Step 2: Build the SectorDecomposition ────────────────────────────────
  let sectors : SectorWeightData classes.g := {
    copies         := classes.copies
    copies_pos     := classes.copies_pos
    weight         := fun j q => ζFn j q * μ (classes.enum j q)
    weight_ne_zero := fun j q => mul_ne_zero (hζ_ne j q) (hμne (classes.enum j q))
  }
  let P : SectorDecomposition d := {
    basisCount := classes.g
    basisDim   := fun j => dim (reprFn j)
    basis      := fun j => blocks (reprFn j)
    sectors    := sectors
  }
  refine ⟨P, ?_, ?_⟩
  · -- ── SameMPV₂ proof ──────────────────────────────────────────────────────
    intro N σ
    calc mpv P.toTensor σ
        = ∑ j : Fin P.basisCount,
            ∑ q : Fin (P.copies j), (P.weight j q) ^ N * mpv (P.basis j) σ :=
            P.mpv_toTensor_eq_sum_sectors σ
      _ = ∑ j : Fin classes.g,
            ∑ q : Fin (classes.copies j),
              (ζFn j q * μ (classes.enum j q)) ^ N * mpv (blocks (reprFn j)) σ := rfl
      _ = ∑ j : Fin classes.g,
            ∑ q : Fin (classes.copies j),
              (μ (classes.enum j q)) ^ N * mpv (blocks (classes.enum j q)) σ := by
              refine Finset.sum_congr rfl (fun j _ =>
                Finset.sum_congr rfl (fun q _ => ?_))
              rw [mul_pow]
              -- Goal: ζFn j q ^ N * μ(enum j q) ^ N * mpv(blocks(repr j)) σ
              --     = μ(enum j q) ^ N * mpv(blocks(enum j q)) σ
              -- Use: mpv(blocks(enum j q)) = ζFn j q ^ N * mpv(blocks(repr j))
              rw [hζ_mpv j q N σ]
              ring
      _ = ∑ k : Fin r, (μ k) ^ N * mpv (blocks k) σ :=
            classes.regroup (fun k => (μ k) ^ N * mpv (blocks k) σ)
      _ = mpv (toTensorFromBlocks (d := d) (μ := μ) blocks) σ := by
              symm
              simpa [smul_eq_mul] using mpv_toTensorFromBlocks_eq_sum μ blocks σ
  · -- ── StrictAnti proof ────────────────────────────────────────────────────
    intro i j hij
    change ‖ζFn j ⟨0, classes.copies_pos j⟩ * μ (classes.enum j ⟨0, classes.copies_pos j⟩)‖ <
      ‖ζFn i ⟨0, classes.copies_pos i⟩ * μ (classes.enum i ⟨0, classes.copies_pos i⟩)‖
    simp only [norm_mul, hζ_norm, one_mul]
    rw [classes.enum_norm j ⟨0, classes.copies_pos j⟩,
      classes.enum_norm i ⟨0, classes.copies_pos i⟩]
    exact classes.vals_strictAnti hij

/-! ### §3. Pipeline connection -/

/-- **Pipeline endpoint: from TP + primitive + irreducible blocks to BNT-grouped
`SectorDecomposition`.**

This theorem connects the output of the existence reduction pipeline
(`exists_tp_primitive_blockDecomp_after_blocking` in `Assembly.lean`) to a
`SectorDecomposition` with strictly decreasing BNT-level norms.

The one `sorry` is in `gaugePhaseEquiv_of_equal_norm_blocks`, which establishes
that equal-norm blocks from the same decomposition are gauge-phase equivalent.
Once that theorem is proved, this pipeline connection becomes sorry-free. -/
theorem exists_sectorDecomp_of_tp_primitive_irr_blocks
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hTP : ∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1)
    (hIrr : ∀ k, IsIrreducibleTensor (blocks k))
    (hPrim : ∀ k, _root_.IsPrimitive (transferMap (d := d) (D := dim k) (blocks k)))
    (hμne : ∀ k, μ k ≠ 0) :
    ∃ P : SectorDecomposition d,
      SameMPV₂ P.toTensor (toTensorFromBlocks (d := d) (μ := μ) blocks) ∧
      StrictAnti (fun j : Fin P.basisCount =>
        ‖P.sectors.weight j ⟨0, P.sectors.copies_pos j⟩‖) := by
  -- Step 1: Derive gauge-phase equivalence for equal-norm blocks.
  have hGPE_raw : ∀ j k : Fin r, j ≠ k → ‖μ j‖ = ‖μ k‖ →
      ∃ hdim : dim j = dim k,
        GaugePhaseEquiv (d := d)
          (cast (congr_arg (MPSTensor d) hdim) (blocks j)) (blocks k) := by
    intro j k hjk hNorm
    exact gaugePhaseEquiv_of_equal_norm_blocks μ blocks hTP hIrr hPrim hμne j k hjk hNorm
  -- Step 2: Derive GPE data with unit-norm phase for the grouping theorem.
  have hGPEζ : ∀ j k : Fin r, ‖μ j‖ = ‖μ k‖ →
      ∃ ζ : ℂ, ζ ≠ 0 ∧ ‖ζ‖ = 1 ∧
        ∀ (N : ℕ) (σ : Fin N → Fin d),
          mpv (blocks k) σ = ζ ^ N * mpv (blocks j) σ := by
    intro j k hNorm
    by_cases hjk : j = k
    · -- Self-case: ζ = 1.
      subst hjk
      exact ⟨1, one_ne_zero, norm_one, fun N σ => by simp⟩
    · -- Different blocks: use gauge-phase equivalence data.
      obtain ⟨hdim, X, ζ, hζne, hX⟩ := hGPE_raw j k hjk hNorm
      have hmpv : ∀ (N : ℕ) (σ : Fin N → Fin d),
          mpv (blocks k) σ = ζ ^ N * mpv (blocks j) σ := by
        intro N σ
        rw [mpv_eq_pow_mul_of_gaugePhase
          (A := cast (congr_arg (MPSTensor d) hdim) (blocks j))
          (B := blocks k) X ζ hX N σ,
          mpv_cast_dim hdim (blocks j) N σ]
      -- Show ‖ζ‖ = 1 using the overlap analysis.
      -- Cast blocks j to have dimension dim k (using hdim).
      have hζ_norm : ‖ζ‖ = 1 := by
        exact norm_gaugePhase_eq_one_of_irr_TP_primitive
          (cast (congr_arg (MPSTensor d) hdim) (blocks j))
          (blocks k)
          ((isIrreducibleTensor_cast_dim hdim (blocks j)).mpr (hIrr j))
          (hIrr k)
          ((leftCanonical_cast_dim hdim (blocks j)).mpr (hTP j))
          (hTP k)
          ((isPrimitive_transferMap_cast_dim hdim (blocks j)).mpr (hPrim j))
          (hPrim k)
          X ζ hX
      exact ⟨ζ, hζne, hζ_norm, hmpv⟩
  -- Step 3: Apply the gauge-phase-aware BNT grouping theorem.
  exact exists_bnt_grouping_of_gaugePhaseEquiv μ blocks hμne hGPEζ

end MPSTensor
