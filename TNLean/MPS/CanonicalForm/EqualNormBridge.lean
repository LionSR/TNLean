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
    (hDim : ∀ k, 0 < dim k)
    (j k : Fin r) (hjk : j ≠ k) (hNorm : ‖μ j‖ = ‖μ k‖) :
    ∃ hdim : dim j = dim k,
      GaugePhaseEquiv (d := d)
        (cast (congr_arg (MPSTensor d) hdim) (blocks j)) (blocks k) := by
  sorry

/-! ### §2. Norm of gauge phase is one -/

/-- The gauge phase ζ in a gauge-phase equivalence between two TP-normalized
irreducible blocks with primitive transfer maps satisfies `‖ζ‖ = 1`.

This follows from `norm_eq_one_of_selfOverlap_scale`: self-overlap scaling
under gauge-phase transform forces the phase to have unit modulus. -/
theorem norm_gaugePhase_eq_one_of_irr_TP_primitive
    {D : ℕ} [NeZero D]
    (A B : MPSTensor d D)
    (hA_irr : IsIrreducibleTensor A)
    (hB_irr : IsIrreducibleTensor B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hA_prim : _root_.IsPrimitive (transferMap (d := d) (D := D) A))
    (hB_prim : _root_.IsPrimitive (transferMap (d := d) (D := D) B))
    (X : GL (Fin D) ℂ) (ζ : ℂ) (_hζne : ζ ≠ 0)
    (hX : ∀ i : Fin d,
      B i = ζ • ((X : Matrix (Fin D) (Fin D) ℂ) * A i *
        ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))) :
    ‖ζ‖ = 1 := by
  -- From hX, mpv B σ = ζ^N * mpv A σ for all N, σ.
  have hmpv : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv B σ = ζ ^ N * mpv A σ :=
    mpv_eq_pow_mul_of_gaugePhase A B X ζ hX
  -- Self-overlap of B scales from self-overlap of A.
  have hScale : ∀ N,
      mpvOverlap (d := d) B B N =
        (ζ * starRingEnd ℂ ζ) ^ N * mpvOverlap (d := d) A A N := by
    intro N
    simp only [mpvOverlap]
    rw [Finset.mul_sum]
    congr 1; ext σ
    rw [hmpv N σ]
    simp [star_mul, mul_pow, star_pow]
    ring
  -- Both blocks have self-overlap → 1 (from primitivity).
  have hA_pf : HasPrimitiveFixedPoint A :=
    hasPrimitiveFixedPoint_of_peripheralPrimitive_of_irreducible A hA_irr hA_norm hA_prim
  have hB_pf : HasPrimitiveFixedPoint B :=
    hasPrimitiveFixedPoint_of_peripheralPrimitive_of_irreducible B hB_irr hB_norm hB_prim
  have hAA : Tendsto (fun N => ‖mpvOverlap (d := d) A A N‖) atTop (nhds 1) := by
    convert hA_pf.overlap_tendsto_one.norm using 1; simp
  have hBB : Tendsto (fun N => ‖mpvOverlap (d := d) B B N‖) atTop (nhds 1) := by
    convert hB_pf.overlap_tendsto_one.norm using 1; simp
  exact norm_eq_one_of_selfOverlap_scale hAA hBB hScale

/-! ### §3. BNT grouping with gauge-phase equivalence -/

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
    -- Equal-norm blocks have the same dimension.
    (_hDimEq : ∀ j k : Fin r, ‖μ j‖ = ‖μ k‖ → dim j = dim k)
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
  -- ── Step 1: Set up the norm image and a strictly-decreasing listing ─────
  let normImage : Finset ℝ := Finset.univ.image (fun k : Fin r => ‖μ k‖)
  let g := normImage.card
  let vals : Fin g → ℝ := fun j => normImage.orderEmbOfFin rfl (Fin.rev j)
  have hvals_anti : StrictAnti vals :=
    (normImage.orderEmbOfFin rfl).strictMono.comp_strictAnti Fin.rev_strictAnti
  have hvals_inj : Function.Injective vals := hvals_anti.injective
  have hvals_mem : ∀ j, vals j ∈ normImage :=
    fun j => Finset.orderEmbOfFin_mem normImage rfl (Fin.rev j)
  -- ── Step 2: Norm classes ──────────────────────────────────────────────────
  let normClass : Fin g → Finset (Fin r) :=
    fun j => Finset.univ.filter (fun k => ‖μ k‖ = vals j)
  have hClass_nonempty : ∀ j, (normClass j).Nonempty := by
    intro j
    have hmem := hvals_mem j
    simp only [normImage, Finset.mem_image, Finset.mem_univ, true_and] at hmem
    obtain ⟨k, hk⟩ := hmem
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩
  have hClass_disj :
      Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin g)) : Set (Fin g)) normClass := by
    intro j₁ _ j₂ _ hne
    apply Finset.disjoint_left.mpr
    intro k hk1 hk2
    exact hne (hvals_inj
      ((Finset.mem_filter.mp hk1).2.symm.trans (Finset.mem_filter.mp hk2).2))
  have hClass_cover : Finset.biUnion Finset.univ normClass = Finset.univ := by
    ext k
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, iff_true]
    have hmem : ‖μ k‖ ∈ normImage :=
      Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
    rw [← Finset.image_orderEmbOfFin_univ normImage rfl] at hmem
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
    refine ⟨Fin.rev i, ?_⟩
    change k ∈ Finset.univ.filter (fun k => ‖μ k‖ = vals (Fin.rev i))
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    change ‖μ k‖ = normImage.orderEmbOfFin rfl (Fin.rev (Fin.rev i))
    rw [Fin.rev_rev]
    exact hi.symm
  -- ── Step 3: Enumeration ───────────────────────────────────────────────────
  let copiesFn : Fin g → ℕ := fun j => (normClass j).card
  have hcopies_pos : ∀ j, 0 < copiesFn j :=
    fun j => Finset.card_pos.mpr (hClass_nonempty j)
  let enumFn : (j : Fin g) → Fin (copiesFn j) → Fin r :=
    fun j => (normClass j).orderEmbOfFin rfl
  have hEnum_norm : ∀ j q, ‖μ (enumFn j q)‖ = vals j := fun j q =>
    (Finset.mem_filter.mp ((normClass j).orderEmbOfFin_mem rfl q)).2
  let reprFn : Fin g → Fin r := fun j => enumFn j ⟨0, hcopies_pos j⟩
  have hRepr_norm : ∀ j, ‖μ (reprFn j)‖ = vals j :=
    fun j => hEnum_norm j ⟨0, hcopies_pos j⟩
  -- ── Step 4: Extract gauge-phase data ──────────────────────────────────────
  have hGPE_repr : ∀ j q,
      ∃ ζ : ℂ, ζ ≠ 0 ∧ ‖ζ‖ = 1 ∧ ∀ (N : ℕ) (σ : Fin N → Fin d),
        mpv (blocks (enumFn j q)) σ = ζ ^ N * mpv (blocks (reprFn j)) σ :=
    fun j q => hGPE (reprFn j) (enumFn j q)
      (hRepr_norm j |>.trans (hEnum_norm j q).symm)
  let ζFn : (j : Fin g) → Fin (copiesFn j) → ℂ :=
    fun j q => (hGPE_repr j q).choose
  have hζ_ne : ∀ j q, ζFn j q ≠ 0 := fun j q => (hGPE_repr j q).choose_spec.1
  have hζ_norm : ∀ j q, ‖ζFn j q‖ = 1 := fun j q => (hGPE_repr j q).choose_spec.2.1
  have hζ_mpv : ∀ j (q : Fin (copiesFn j)) (N : ℕ) (σ : Fin N → Fin d),
      mpv (blocks (enumFn j q)) σ = (ζFn j q) ^ N * mpv (blocks (reprFn j)) σ :=
    fun j q N σ => (hGPE_repr j q).choose_spec.2.2 N σ
  -- ── Step 5: Build the SectorDecomposition ────────────────────────────────
  let sectors : SectorWeightData g := {
    copies         := copiesFn
    copies_pos     := hcopies_pos
    weight         := fun j q => ζFn j q * μ (enumFn j q)
    weight_ne_zero := fun j q => mul_ne_zero (hζ_ne j q) (hμne (enumFn j q))
  }
  let P : SectorDecomposition d := {
    basisCount := g
    basisDim   := fun j => dim (reprFn j)
    basis      := fun j => blocks (reprFn j)
    sectors    := sectors
  }
  refine ⟨P, ?_, ?_⟩
  · -- ── SameMPV₂ proof ──────────────────────────────────────────────────────
    intro N σ
    have hRegroup : ∀ (f : Fin r → ℂ),
        ∑ j : Fin g, ∑ q : Fin (copiesFn j), f (enumFn j q) = ∑ k : Fin r, f k := by
      intro f
      have inner_eq : ∀ j : Fin g,
          ∑ q : Fin (copiesFn j), f (enumFn j q) = ∑ k ∈ normClass j, f k := by
        intro j
        rw [← Finset.map_orderEmbOfFin_univ (normClass j) rfl, Finset.sum_map]
        rfl
      simp_rw [inner_eq]
      calc ∑ j : Fin g, ∑ k ∈ normClass j, f k
          = ∑ k ∈ Finset.biUnion Finset.univ normClass, f k :=
              (Finset.sum_biUnion hClass_disj).symm
        _ = ∑ k ∈ Finset.univ, f k := by rw [hClass_cover]
        _ = ∑ k : Fin r, f k := rfl
    calc mpv P.toTensor σ
        = ∑ j : Fin P.basisCount,
            ∑ q : Fin (P.copies j), (P.weight j q) ^ N * mpv (P.basis j) σ :=
            P.mpv_toTensor_eq_sum_sectors σ
      _ = ∑ j : Fin g,
            ∑ q : Fin (copiesFn j),
              (ζFn j q * μ (enumFn j q)) ^ N * mpv (blocks (reprFn j)) σ := rfl
      _ = ∑ j : Fin g,
            ∑ q : Fin (copiesFn j),
              (μ (enumFn j q)) ^ N * mpv (blocks (enumFn j q)) σ := by
              refine Finset.sum_congr rfl (fun j _ =>
                Finset.sum_congr rfl (fun q _ => ?_))
              rw [mul_pow]
              -- Goal: ζFn j q ^ N * μ(enum j q) ^ N * mpv(blocks(repr j)) σ
              --     = μ(enum j q) ^ N * mpv(blocks(enum j q)) σ
              -- Use: mpv(blocks(enum j q)) = ζFn j q ^ N * mpv(blocks(repr j))
              rw [hζ_mpv j q N σ]
              ring
      _ = ∑ k : Fin r, (μ k) ^ N * mpv (blocks k) σ :=
            hRegroup (fun k => (μ k) ^ N * mpv (blocks k) σ)
      _ = mpv (toTensorFromBlocks (d := d) (μ := μ) blocks) σ := by
              symm
              simpa [smul_eq_mul] using mpv_toTensorFromBlocks_eq_sum μ blocks σ
  · -- ── StrictAnti proof ────────────────────────────────────────────────────
    intro i j hij
    change ‖ζFn j ⟨0, hcopies_pos j⟩ * μ (enumFn j ⟨0, hcopies_pos j⟩)‖ <
      ‖ζFn i ⟨0, hcopies_pos i⟩ * μ (enumFn i ⟨0, hcopies_pos i⟩)‖
    simp only [norm_mul, hζ_norm, one_mul]
    rw [hEnum_norm j ⟨0, hcopies_pos j⟩, hEnum_norm i ⟨0, hcopies_pos i⟩]
    exact hvals_anti hij

/-! ### §4. Pipeline connection -/

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
    (hμne : ∀ k, μ k ≠ 0)
    (hDim : ∀ k, 0 < dim k) :
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
    exact gaugePhaseEquiv_of_equal_norm_blocks μ blocks hTP hIrr hPrim hμne hDim j k hjk hNorm
  -- Step 2: Derive the dimension equality hypothesis for all equal-norm blocks.
  have hDimEq : ∀ j k : Fin r, ‖μ j‖ = ‖μ k‖ → dim j = dim k := by
    intro j k hNorm
    by_cases hjk : j = k
    · exact congr_arg dim hjk
    · exact (hGPE_raw j k hjk hNorm).choose
  -- Step 3: Derive GPE data with unit-norm phase for the grouping theorem.
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
          X ζ hζne hX
      exact ⟨ζ, hζne, hζ_norm, hmpv⟩
  -- Step 4: Apply the gauge-phase-aware BNT grouping theorem.
  exact exists_bnt_grouping_of_gaugePhaseEquiv μ blocks hμne hDimEq hGPEζ

end MPSTensor
