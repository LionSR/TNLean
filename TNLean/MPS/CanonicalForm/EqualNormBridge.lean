/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.BNT.Construction
import TNLean.MPS.CanonicalForm.BNTGrouping
import TNLean.MPS.CanonicalForm.PhaseCover
import TNLean.MPS.CanonicalForm.PhaseClassSectorData
import TNLean.MPS.FundamentalTheorem.SectorDecomposition
import TNLean.MPS.Overlap.CastDecay
import TNLean.MPS.Overlap.CastLemmas
import TNLean.MPS.SharedInfra.GaugePhase
import TNLean.MPS.Structure.PrimitivityBridge
import TNLean.Spectral.SpectralGapNT

open scoped Matrix BigOperators
open Filter

/-!
# Equal-norm comparison for restricted norm-class collapse hypotheses

This file relates the BNT overlap/spectral theory to the restricted norm-class
collapse: blocks with the same weight norm must already generate the same MPS
family before they can be represented by one sector.

## Background

The canonical-form reduction produces TP + primitive blocks with
nonzero weights. The restricted norm-class collapse groups blocks by weight norm into a
sector decomposition, and requires one mathematical input for equal-norm blocks:

* equal-norm blocks generate the same MPS family.

The grouped sector's bond dimension is fixed by the chosen representative of each
norm class, so no separate equal-dimension hypothesis is needed.

## Strategy: gauge-phase-aware norm-class collapse

When equal-norm blocks are known to be gauge-phase equivalent (e.g., because they
originate from the cyclic-sector decomposition of a single irreducible block, or
because the Fundamental Theorem matches them), the gauge phases can be absorbed
into sector weights.

For block k gauge-phase equivalent to representative block j via `(X, ζ)`:
- `mpv(blocks k)(σ) = ζ^N * mpv(blocks j)(σ)`
- Contribution to total: `(μ_k)^N * mpv(blocks k)(σ) = (ζ * μ_k)^N * mpv(blocks j)(σ)`
- Effective sector weight: `ζ * μ_k`, with `‖ζ * μ_k‖ = ‖μ_k‖` (since `‖ζ‖ = 1`)

## Important: equal-norm blocks are NOT automatically gauge-phase equivalent

The BNT of a tensor (Cirac--Perez-Garcia--Schuch--Verstraete 2017,
Proposition A.6) is constructed so that all pairs of BNT elements have
*decaying* cross-overlaps. In particular, two BNT elements can
share the same weight norm while being completely independent (non-GPE).  The BNT
already groups gauge-equivalent blocks together; remaining blocks are pairwise
non-gauge-equivalent.  A counter-example shows that the
MPV-level hypothesis `hFullTensor` alone cannot force non-decaying cross-overlaps.

To obtain GPE for equal-norm blocks, one must derive the non-decay property from
structural properties of the decomposition (cyclic-sector origin, Fundamental
Theorem matching, etc.).

## Main results

* `gaugePhaseEquiv_of_nonDecaying_overlap` — Non-decaying cross-overlap between two
  TP + irreducible blocks implies equal bond dimensions and gauge-phase equivalence.
  Uses the spectral dichotomy from `SpectralGap.lean`.  **Fully proved.**

* `exists_bnt_grouping_of_gaugePhaseEquiv` — restricted collapse taking gauge-phase
  equivalence data (rather than `SameMPV₂`) for equal-norm blocks.  **Fully proved.**

* `exists_sectorDecomp_of_tp_primitive_irr_blocks` — Construction connecting
  the reduction result to a BNT-grouped `SectorDecomposition`.  **Fully proved.**
  Requires a `hNonDecay` hypothesis for equal-norm blocks.

* `exists_eventually_linearIndependent_of_overlap_tendsto_orthonormal` —
  turns asymptotic orthonormality of MPV overlaps into the existential eventual
  linear-independence form used by `HasBNTSectorData`.

* `exists_eventually_linearIndependent_of_tp_primitive_irr_blocks_of_blocksNotGaugePhaseEquiv` —
  derives that eventual linear independence from TP / primitive / irreducible
  blocks once the family is already separated by non-gauge-phase-equivalence.

* `exists_bnt_sectorDecomp_of_linearIndependent` — conditional construction
  toward the `HasBNTSectorData` predicate.  It forms the granular
  `trivialSectorDecomp` as a BNT sector decomposition when the actual BNT
  linear-independence condition is supplied explicitly.

* `exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks_of_blocksNotGaugePhaseEquiv` —
  the separated-family constructor: it retains all separated basis blocks,
  including equal-modulus ones, and proves `HasBNTSectorData` from overlap
  asymptotics rather than from an explicit linear-independence hypothesis.

* `exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks` — the representative
  construction: it quotients arbitrary TP / primitive / irreducible blocks by MPV phase
  equivalence, absorbs the scalar factors into sector weights, proves representative
  separation, and then obtains `HasBNTSectorData` from the separated-family theorem.

* `exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks_of_linearIndependent` —
  signature-compatible reformulation retaining the TP / primitive / irreducible
  hypotheses used by the one-sided BNT construction chain.

* `mpv_span_eq_of_common_phase_cover` — finite-length MPV span equality for
  block families arising from a common family covered surjectively up to MPV phase.

* `MPVCommonPhaseCover` — common-family, class-map, phase, and
  surjectivity data for the same span-equality theorem.

* `SectorBasisPreMatching.commonPhaseCover` — turns BNT pre-matching data into
  a common MPV phase cover, hence into finite-length basis-span equality.

* `nonempty_mpvCommonPhaseCover_of_separated_normalCFBNT_data` — the
  span-equality-free BNT proportional-decomposition comparison gives
  common-cover existence.

## References

- [Cirac--Perez-Garcia--Schuch--Verstraete 2017, Lemma A.2]: Overlap dichotomy for Normal Tensors.
- [Cirac--Perez-Garcia--Schuch--Verstraete 2017, Proposition A.6]: BNT construction and minimality.
- [Cirac--Perez-Garcia--Schuch--Verstraete 2017, Definition 2.6, Proposition 2.7]:
  BNT minimality and grouping.
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

/-! ### Section 1. Gauge-phase equivalence from non-decaying overlaps -/

/-- **Gauge-phase equivalence from non-decaying cross-overlap.**

If two TP + irreducible blocks have a cross-overlap that does not decay to zero,
then they must have equal bond dimensions and be gauge-phase equivalent.

The proof uses the **spectral dichotomy** (proved in `SpectralGap.lean` and
`SpectralGapNT.lean`): for injective TP-normalized blocks, either
- `spectralRadius(F_{AB}) < 1`, which forces `mpvOverlap A B N → 0`, or
- `spectralRadius(F_{AB}) ≥ 1`, which forces `GaugePhaseEquiv A B`.

If the overlap does NOT decay, we are in the second case. Dimension equality
follows from `mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP` (contrapositive).

This factored-out lemma replaces the previous monolithic placeholder proof in
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

/-! ### Section 2. Restricted norm-class collapse with gauge-phase equivalence -/

/-- **Restricted norm-class collapse with gauge-phase equivalence for equal-norm blocks.**

This form of `exists_bnt_grouping` uses gauge-phase equivalence data
(rather than `SameMPV₂`) for equal-norm blocks.  The gauge phases are absorbed into
the sector weights, preserving norm-class membership since `‖ζ‖ = 1`.

Given a weighted block family `(μ, blocks)` where some blocks may share the same norm
`‖μ j‖ = ‖μ k‖`, and given that equal-norm blocks are gauge-phase equivalent with
unit-norm phases, there exists a `SectorDecomposition P` with:

1. `SameMPV₂ P.toTensor (toTensorFromBlocks μ blocks)`.
2. `StrictAnti` on the BNT-level norms (one norm value per group).

**Proof**: The construction is identical to `exists_bnt_grouping` (Section 5 of
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

/-! ### Section 3. Construction of sector decomposition -/

/-- **From TP + primitive + irreducible blocks to BNT-grouped
`SectorDecomposition`.**

This theorem relates the result of the existence reduction
(`exists_tp_primitive_blockDecomp_after_blocking` in `Assembly.lean`) to a
`SectorDecomposition` with strictly decreasing BNT-level norms.  It does not by
itself prove `HasBNTSectorData`: that predicate means eventual linear
independence of the basis MPV states, not merely TP / irreducible / primitive
block data.

The `hNonDecay` hypothesis states that equal-norm blocks have non-decaying
cross-overlaps.  This is NOT automatic from the block properties alone (see
issue #299 for counter-example).  It must be derived from structural
properties of the decomposition, such as:

* Blocks originating from cyclic-sector decomposition of a single irreducible
  block (rotated copies have non-decaying overlaps by construction).
* Fundamental Theorem matching between two canonical-form decompositions. -/
theorem exists_sectorDecomp_of_tp_primitive_irr_blocks
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hTP : ∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1)
    (hIrr : ∀ k, IsIrreducibleTensor (blocks k))
    (hPrim : ∀ k, _root_.IsPrimitive (transferMap (d := d) (D := dim k) (blocks k)))
    (hμne : ∀ k, μ k ≠ 0)
    -- The non-decay hypothesis is not automatic from the block properties alone.
    (hNonDecay : ∀ j k : Fin r, j ≠ k → ‖μ j‖ = ‖μ k‖ →
      ¬ Tendsto (fun N => mpvOverlap (d := d) (blocks j) (blocks k) N) atTop (nhds 0)) :
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
    exact gaugePhaseEquiv_of_nonDecaying_overlap
      (blocks j) (blocks k) (hIrr j) (hIrr k) (hTP j) (hTP k)
      (hNonDecay j k hjk hNorm)
  -- Step 2: Derive GPE data with unit-norm phase for the collapse lemma.
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
  -- Step 3: Apply the gauge-phase-aware collapse lemma.
  exact exists_bnt_grouping_of_gaugePhaseEquiv μ blocks hμne hGPEζ

/-- One-sector specialization of the TP + primitive + irreducible grouping route.

This is a genuine restricted result: if all weights lie in a single norm class
and every block has non-decaying overlap with a chosen representative, then the whole family
collapses to a one-basis `SectorDecomposition`. -/
theorem bnt_grouping_single_norm_class_of_tp_primitive_irr_blocks
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (k0 : Fin r)
    (hTP : ∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1)
    (hIrr : ∀ k, IsIrreducibleTensor (blocks k))
    (hPrim : ∀ k, _root_.IsPrimitive (transferMap (d := d) (D := dim k) (blocks k)))
    (hμne : ∀ k, μ k ≠ 0)
    (hNorm : ∀ k : Fin r, ‖μ k‖ = ‖μ k0‖)
    (hNonDecay : ∀ k : Fin r, k ≠ k0 →
      ¬ Tendsto (fun N => mpvOverlap (d := d) (blocks k0) (blocks k) N) atTop (nhds 0)) :
    ∃ P : SectorDecomposition d,
      P.basisCount = 1 ∧
      P.totalCopies = r ∧
      SameMPV₂ P.toTensor (toTensorFromBlocks (d := d) (μ := μ) blocks) ∧
      (∀ s : Fin P.totalCopies, ‖P.flatWeight s‖ = ‖μ k0‖) := by
  have hPhase : ∀ k : Fin r,
      ∃ ζ : ℂ, ζ ≠ 0 ∧ ‖ζ‖ = 1 ∧
        ∀ (N : ℕ) (σ : Fin N → Fin d),
          mpv (blocks k) σ = ζ ^ N * mpv (blocks k0) σ := by
    intro k
    by_cases hk : k = k0
    · subst hk
      exact ⟨1, one_ne_zero, norm_one, fun N σ => by simp⟩
    · obtain ⟨hdim, X, ζ, hζne, hX⟩ := gaugePhaseEquiv_of_nonDecaying_overlap
        (blocks k0) (blocks k) (hIrr k0) (hIrr k) (hTP k0) (hTP k)
        (hNonDecay k hk)
      have hmpv : ∀ (N : ℕ) (σ : Fin N → Fin d),
          mpv (blocks k) σ = ζ ^ N * mpv (blocks k0) σ := by
        intro N σ
        rw [mpv_eq_pow_mul_of_gaugePhase
          (A := cast (congr_arg (MPSTensor d) hdim) (blocks k0))
          (B := blocks k) X ζ hX N σ,
          mpv_cast_dim hdim (blocks k0) N σ]
      have hζ_norm : ‖ζ‖ = 1 := by
        exact norm_gaugePhase_eq_one_of_irr_TP_primitive
          (cast (congr_arg (MPSTensor d) hdim) (blocks k0))
          (blocks k)
          ((isIrreducibleTensor_cast_dim hdim (blocks k0)).mpr (hIrr k0))
          (hIrr k)
          ((leftCanonical_cast_dim hdim (blocks k0)).mpr (hTP k0))
          (hTP k)
          ((isPrimitive_transferMap_cast_dim hdim (blocks k0)).mpr (hPrim k0))
          (hPrim k)
          X ζ hX
      exact ⟨ζ, hζne, hζ_norm, hmpv⟩
  exact bnt_grouping_single_norm_class μ blocks k0 hμne hNorm hPhase

end MPSTensor
