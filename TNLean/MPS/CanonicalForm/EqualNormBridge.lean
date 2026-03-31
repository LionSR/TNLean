/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.CanonicalForm.BNTGrouping
import TNLean.MPS.FundamentalTheorem.Proportional
import TNLean.MPS.Overlap.CastLemmas
import TNLean.MPS.Overlap.CastDecay
import TNLean.MPS.Structure.PrimitivityBridge
import TNLean.Spectral.SpectralGapNT

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

* `gaugePhaseEquiv_of_nonDecaying_overlap` — Non-decaying cross-overlap between two
  TP + irreducible blocks implies equal bond dimensions and gauge-phase equivalence.
  Uses the spectral dichotomy from `SpectralGap.lean`.  **Fully proved.**

* `nonDecaying_overlap_of_equal_norm_blocks` — Equal-norm blocks from the same
  canonical-form decomposition have non-decaying cross-overlaps.  **Contains one sorry**
  (the BNT expansion argument from CPGSV17 Appendix A, §1b).

* `gaugePhaseEquiv_of_equal_norm_blocks` — Equal-norm blocks from the same TP +
  primitive + irreducible decomposition are gauge-phase equivalent.  **Proved** by
  combining the above two results (sorry flows from
  `nonDecaying_overlap_of_equal_norm_blocks`).

* `exists_bnt_grouping_of_gaugePhaseEquiv` — BNT grouping theorem taking gauge-phase
  equivalence data (rather than `SameMPV₂`) for equal-norm blocks.  **Fully proved.**

* `exists_sectorDecomp_of_tp_primitive_irr_blocks` — Pipeline endpoint connecting
  the reduction output to a BNT-grouped `SectorDecomposition`.  **Proved modulo**
  the sorry in `nonDecaying_overlap_of_equal_norm_blocks`.

## Remaining gap

The one remaining `sorry` is in `nonDecaying_overlap_of_equal_norm_blocks` (§1b).
This requires the BNT coefficient extraction argument from the canonical-form
decomposition structure, specifically showing that the linear independence of the BNT
family combined with equal growth rates forces non-decaying cross-overlaps.

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

/-! ### §1. Gauge-phase equivalence from non-decaying overlaps -/

/-- **Gauge-phase equivalence from non-decaying cross-overlap.**

If two TP + irreducible blocks have a cross-overlap that does not decay to zero,
then they must have equal bond dimensions and be gauge-phase equivalent.

The proof uses the **spectral dichotomy** (proved in `SpectralGap.lean` and
`SpectralGapNT.lean`): for injective TP-normalized blocks, either
- `spectralRadius(F_{AB}) < 1`, which forces `mpvOverlap A B N → 0`, or
- `spectralRadius(F_{AB}) ≥ 1`, which forces `GaugePhaseEquiv A B`.

If the overlap does NOT decay, we are in the second case. Dimension equality
follows from `mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP` (contrapositive).

This factored-out lemma replaces the previous monolithic sorry in
`gaugePhaseEquiv_of_equal_norm_blocks`. -/
theorem gaugePhaseEquiv_of_nonDecaying_overlap
    {D₁ D₂ : ℕ} [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hA_irr : IsIrreducibleTensor A) (hB_irr : IsIrreducibleTensor B)
    (hA_TP : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_TP : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hNonDecay : ¬ Tendsto (fun N => mpvOverlap (d := d) A B N) atTop (nhds 0)) :
    ∃ hdim : D₁ = D₂,
      GaugePhaseEquiv (d := d)
        (cast (congr_arg (MPSTensor d) hdim) A) B := by
  -- Step 1: Dimension equality (contrapositive of dim-mismatch decay).
  have hdim : D₁ = D₂ := by
    by_contra hne
    exact hNonDecay
      (mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP A B hA_irr hB_irr hA_TP hB_TP hne)
  refine ⟨hdim, ?_⟩
  -- Step 2: Gauge-phase equivalence (contrapositive of non-GPE decay).
  by_contra hNotGPE
  exact hNonDecay
    (mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left_of_irreducible_TP
      hdim A B hA_irr hB_irr hA_TP hB_TP hNotGPE)

/-! ### §1b. Non-decaying overlap from canonical-form structure (remaining gap) -/

/-- Overlap expansion along a finite MPV decomposition on the left.

This local helper mirrors the overlap-expansion infrastructure used in
`BNT/PermutationRigidity.lean`, specialized for this bridge file. -/
private lemma mpvOverlap_eq_sum_of_decomp_left
    {Dtot : ℕ} {r : ℕ} {dim : Fin r → ℕ}
    (A_total : MPSTensor d Dtot)
    (A : (j : Fin r) → MPSTensor d (dim j))
    {N : ℕ} (c : Fin r → ℂ)
    (hdecomp : ∀ (σ : Fin N → Fin d),
      mpv A_total σ = ∑ j : Fin r, c j * mpv (A j) σ)
    {D' : ℕ} (B : MPSTensor d D') :
    mpvOverlap (d := d) A_total B N =
      ∑ j : Fin r, c j * mpvOverlap (d := d) (A j) B N := by
  classical
  calc
    mpvOverlap (d := d) A_total B N =
        ∑ σ : Cfg d N, (∑ j : Fin r, c j * mpv (A j) σ) * star (mpv B σ) := by
          simp only [mpvOverlap]
          congr 1; ext σ; rw [hdecomp σ]
    _ = ∑ σ : Cfg d N, ∑ j : Fin r, c j * (mpv (A j) σ * star (mpv B σ)) := by
          congr 1; ext σ; rw [Finset.sum_mul]; congr 1; ext j; ring
    _ = ∑ j : Fin r, ∑ σ : Cfg d N, c j * (mpv (A j) σ * star (mpv B σ)) := by
          simpa using
            (Finset.sum_comm (s := (Finset.univ : Finset (Cfg d N)))
              (t := (Finset.univ : Finset (Fin r)))
              (f := fun σ j => c j * (mpv (A j) σ * star (mpv B σ))))
    _ = ∑ j : Fin r, c j * ∑ σ : Cfg d N, mpv (A j) σ * star (mpv B σ) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          simpa [mul_assoc] using
            (Finset.mul_sum (s := (Finset.univ : Finset (Cfg d N)))
              (f := fun σ : Cfg d N => mpv (A j) σ * star (mpv B σ)) (a := c j)).symm
    _ = ∑ j : Fin r, c j * mpvOverlap (d := d) (A j) B N := by
          simp [mpvOverlap]

/-- **Non-decaying overlap for equal-norm blocks from a canonical-form decomposition.**

When blocks are obtained from the canonical-form decomposition of an MPS tensor,
blocks with equal weight norms have non-decaying cross-overlaps.

**Paper argument (CPGSV17, Appendix A, Corollary A.43):** The BNT expansion of the
full tensor expresses its MPV as `∑_k μ_k^N * V(A_k)`. Taking the inner product
with `V(A_j)` and using the asymptotic orthonormality of non-gauge-phase-equivalent
blocks isolates the contribution from the norm class of block j. If all equal-norm
blocks had decaying cross-overlaps with block j, the coefficient of `V(A_j)` in the
BNT expansion would vanish for large N, contradicting the non-degeneracy of the
decomposition.

This argument requires the blocks to be connected through the full tensor's
BNT structure — it is NOT provable from the individual block properties alone
(TP, irreducible, primitive). The `hFullTensor` hypothesis captures the connection
between the blocks and a parent tensor.

NOTE: This sorry is the precise remaining gap from issue #243/#299.
Once proved, `exists_sectorDecomp_of_tp_primitive_irr_blocks` becomes sorry-free. -/
theorem nonDecaying_overlap_of_equal_norm_blocks
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hTP : ∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1)
    (hIrr : ∀ k, IsIrreducibleTensor (blocks k))
    (hPrim : ∀ k, _root_.IsPrimitive (transferMap (d := d) (D := dim k) (blocks k)))
    (hμne : ∀ k, μ k ≠ 0)
    -- The blocks come from decomposing a single tensor: the MPV of the full tensor
    -- is the weighted sum of the block MPVs. This connects the blocks through the
    -- BNT structure and is automatically satisfied by `toTensorFromBlocks`.
    {D_total : ℕ} (A_total : MPSTensor d D_total)
    (hFullTensor : ∀ (N : ℕ) (σ : Fin N → Fin d),
        N > 0 → mpv A_total σ = ∑ k, (μ k) ^ N * mpv (blocks k) σ)
    (j k : Fin r) (hjk : j ≠ k) (hNorm : ‖μ j‖ = ‖μ k‖) :
    ¬ Tendsto (fun N => mpvOverlap (d := d) (blocks j) (blocks k) N) atTop (nhds 0) := by
  -- TODO(#299): Remaining Appendix-A extraction step.
  --
  -- Current status:
  -- * The spectral half is already available via
  --   `gaugePhaseEquiv_of_nonDecaying_overlap`.
  -- * This theorem is the complementary "non-decay from equal norm" half.
  --
  -- Planned formal route (matching CPGSV17 Appendix A and the BNT infrastructure):
  -- 1. Normalize coefficients by a dominant representative and use
  --    `HasStrictOrderedNonzeroWeights.coeff_ratio_tendsto` / the canonical-form
  --    wrappers in `FundamentalTheorem/CoefficientConvergence.lean`.
  -- 2. Pair `hFullTensor` with overlap-expansion lemmas from
  --    `BNT/PermutationRigidity.lean` to extract the contribution of a fixed block.
  -- 3. Use equal growth (`hNorm`) plus nonzero limits (`hμne`) to rule out complete
  --    cancellation of all equal-norm cross terms.
  -- 4. Conclude that assuming decay of the (j,k)-overlap contradicts the extracted
  --    nonzero limit.
  --
  -- Note: the hypotheses `hTP`, `hIrr`, and `hPrim` are intentionally retained here;
  -- they provide the overlap dichotomy tools needed immediately downstream.
  sorry

/-- **Equal-norm blocks from the same decomposition are gauge-phase equivalent.**

Given a family of TP + primitive + irreducible blocks with nonzero weights
that decompose a total tensor's MPV, two blocks j, k with `‖μ j‖ = ‖μ k‖`
and `j ≠ k` must have equal bond dimensions and be gauge-phase equivalent.

This combines `nonDecaying_overlap_of_equal_norm_blocks` (which shows the
cross-overlap doesn't decay, using the canonical-form structure) with
`gaugePhaseEquiv_of_nonDecaying_overlap` (which converts non-decaying overlap
to gauge-phase equivalence via the spectral dichotomy). -/
theorem gaugePhaseEquiv_of_equal_norm_blocks
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hTP : ∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1)
    (hIrr : ∀ k, IsIrreducibleTensor (blocks k))
    (hPrim : ∀ k, _root_.IsPrimitive (transferMap (d := d) (D := dim k) (blocks k)))
    (hμne : ∀ k, μ k ≠ 0)
    {D_total : ℕ} (A_total : MPSTensor d D_total)
    (hFullTensor : ∀ (N : ℕ) (σ : Fin N → Fin d),
        N > 0 → mpv A_total σ = ∑ k, (μ k) ^ N * mpv (blocks k) σ)
    (j k : Fin r) (hjk : j ≠ k) (hNorm : ‖μ j‖ = ‖μ k‖) :
    ∃ hdim : dim j = dim k,
      GaugePhaseEquiv (d := d)
        (cast (congr_arg (MPSTensor d) hdim) (blocks j)) (blocks k) :=
  gaugePhaseEquiv_of_nonDecaying_overlap
    (blocks j) (blocks k)
    (hIrr j) (hIrr k) (hTP j) (hTP k)
    (nonDecaying_overlap_of_equal_norm_blocks μ blocks hTP hIrr hPrim hμne
      A_total hFullTensor j k hjk hNorm)

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

The `hFullTensor` hypothesis connects the blocks to a parent tensor, which is
needed for the equal-norm bridge (the cross-overlap non-decay argument uses
the BNT structure of the full decomposition).

The one remaining `sorry` is in `nonDecaying_overlap_of_equal_norm_blocks`. -/
theorem exists_sectorDecomp_of_tp_primitive_irr_blocks
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hTP : ∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1)
    (hIrr : ∀ k, IsIrreducibleTensor (blocks k))
    (hPrim : ∀ k, _root_.IsPrimitive (transferMap (d := d) (D := dim k) (blocks k)))
    (hμne : ∀ k, μ k ≠ 0)
    {D_total : ℕ} (A_total : MPSTensor d D_total)
    (hFullTensor : ∀ (N : ℕ) (σ : Fin N → Fin d),
        N > 0 → mpv A_total σ = ∑ k, (μ k) ^ N * mpv (blocks k) σ) :
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
    exact gaugePhaseEquiv_of_equal_norm_blocks μ blocks hTP hIrr hPrim hμne
      A_total hFullTensor j k hjk hNorm
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
