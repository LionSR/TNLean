/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.BNT.Construction
import TNLean.MPS.CanonicalForm.BNTGrouping
import TNLean.MPS.FundamentalTheorem.SectorDecomposition
import TNLean.MPS.Overlap.CastDecay
import TNLean.MPS.Overlap.CastLemmas
import TNLean.MPS.SharedInfra.GaugePhase
import TNLean.MPS.Structure.PrimitivityBridge
import TNLean.Spectral.SpectralGapNT

open scoped Matrix BigOperators
open Filter

/-!
# Equal-norm connection: from BNT properties to BNT grouping hypotheses

This file relates the BNT overlap/spectral theory to the
BNT grouping theorem (`exists_bnt_grouping`), which requires `hMPVEq`
for equal-norm blocks.

## Background (Issue #243)

The existence reduction chain (`Assembly.lean`) produces TP + primitive blocks with
nonzero weights.  The BNT grouping theorem groups blocks by weight norm into a
`SectorDecomposition`, and requires one hypothesis for equal-norm blocks:

* `hMPVEq`: equal-norm blocks have `SameMPV₂`.

The grouped sector's bond dimension is fixed by the chosen representative of each
norm class, so no separate equal-dimension hypothesis is needed.

## Strategy: gauge-phase-aware BNT grouping

When equal-norm blocks are known to be gauge-phase equivalent (e.g., because they
originate from the cyclic-sector decomposition of a single irreducible block, or
because the Fundamental Theorem matches them), the gauge phases can be absorbed
into sector weights.

For block k gauge-phase equivalent to representative block j via `(X, ζ)`:
- `mpv(blocks k)(σ) = ζ^N * mpv(blocks j)(σ)`
- Contribution to total: `(μ_k)^N * mpv(blocks k)(σ) = (ζ * μ_k)^N * mpv(blocks j)(σ)`
- Effective sector weight: `ζ * μ_k`, with `‖ζ * μ_k‖ = ‖μ_k‖` (since `‖ζ‖ = 1`)

## Important: equal-norm blocks are NOT automatically gauge-phase equivalent

The BNT of a tensor (CPGSV17, Proposition A.6) is constructed so that all pairs of
BNT elements have *decaying* cross-overlaps.  In particular, two BNT elements can
share the same weight norm while being completely independent (non-GPE).  The BNT
already groups gauge-equivalent blocks together; remaining blocks are pairwise
non-gauge-equivalent.  See issue #299 for the counter-example showing that the
MPV-level hypothesis `hFullTensor` alone cannot force non-decaying cross-overlaps.

To obtain GPE for equal-norm blocks, one must derive the non-decay property from
structural properties of the decomposition (cyclic-sector origin, Fundamental
Theorem matching, etc.).

## Main results

* `gaugePhaseEquiv_of_nonDecaying_overlap` — Non-decaying cross-overlap between two
  TP + irreducible blocks implies equal bond dimensions and gauge-phase equivalence.
  Uses the spectral dichotomy from `SpectralGap.lean`.  **Fully proved.**

* `exists_bnt_grouping_of_gaugePhaseEquiv` — BNT grouping theorem taking gauge-phase
  equivalence data (rather than `SameMPV₂`) for equal-norm blocks.  **Fully proved.**

* `exists_sectorDecomp_of_tp_primitive_irr_blocks` — Construction connecting
  the reduction output to a BNT-grouped `SectorDecomposition`.  **Fully proved.**
  Requires a `hNonDecay` hypothesis for equal-norm blocks.

* `exists_eventually_linearIndependent_of_overlap_tendsto_orthonormal` —
  turns asymptotic orthonormality of MPV overlaps into the existential eventual
  linear-independence form used by `HasBNTSectorData`.

* `exists_eventually_linearIndependent_of_tp_primitive_irr_blocks_of_blocksNotGaugePhaseEquiv` —
  derives that eventual linear independence from TP / primitive / irreducible
  blocks once the family is already separated by non-gauge-phase-equivalence.

* `exists_bnt_sectorDecomp_of_linearIndependent` — conditional construction
  toward the post-#886 `HasBNTSectorData` predicate.  It forms the granular
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
  inputs expected by the one-sided BNT construction chain.

* `mpv_span_eq_of_common_phase_cover` — finite-length live-block span equality
  from a common family covered surjectively up to MPV phase.

* `MPVCommonPhaseCover` — bundled common-family, class-map, phase, and
  surjectivity data for the same span-equality theorem.

## References

- [CPGSV17, Lemma A.2]: Overlap dichotomy for Normal Tensors.
- [CPGSV17, Proposition A.6]: BNT construction and minimality.
- [CPGSV17, Definition 2.6, Proposition 2.7]: BNT minimality and grouping.
- GitHub issue #243: BNT grouping for weight norm separation.
- GitHub issue #299: Counter-example showing `hFullTensor` is insufficient.
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

/-! ### §3. Construction of sector decomposition -/

/-- **From TP + primitive + irreducible blocks to BNT-grouped
`SectorDecomposition`.**

This theorem relates the output of the existence reduction
(`exists_tp_primitive_blockDecomp_after_blocking` in `Assembly.lean`) to a
`SectorDecomposition` with strictly decreasing BNT-level norms.  It does not by
itself prove `HasBNTSectorData`: after #886 that predicate means eventual linear
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

/-- One-sector specialization of the TP + primitive + irreducible grouping route.

This is a genuine restricted result toward Gap §1: if all weights lie in a single norm class
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

/-! ### §4. MPV phase-class representatives -/

/-- Heterogeneous MPV phase equivalence between two individual blocks.

`MPVBlockPhaseEquiv A B` means that the finite-chain MPV of `B` is a nonzero
scalar power times the finite-chain MPV of `A`, uniformly in the chain length and
physical word.  The bond dimensions of `A` and `B` may differ. -/
def MPVBlockPhaseEquiv {d DA DB : ℕ} (A : MPSTensor d DA) (B : MPSTensor d DB) : Prop :=
  ∃ ζ : ℂ, ζ ≠ 0 ∧ ∀ (N : ℕ) (σ : Fin N → Fin d),
    mpv B σ = ζ ^ N * mpv A σ

namespace MPVBlockPhaseEquiv

/-- Reflexivity of heterogeneous MPV phase equivalence. -/
lemma refl {D : ℕ} (A : MPSTensor d D) : MPVBlockPhaseEquiv A A := by
  exact ⟨1, one_ne_zero, fun N σ => by simp⟩

/-- Symmetry of heterogeneous MPV phase equivalence. -/
lemma symm {DA DB : ℕ} {A : MPSTensor d DA} {B : MPSTensor d DB}
    (h : MPVBlockPhaseEquiv A B) : MPVBlockPhaseEquiv B A := by
  rcases h with ⟨ζ, hζ, hmpv⟩
  refine ⟨ζ⁻¹, inv_ne_zero hζ, ?_⟩
  intro N σ
  rw [hmpv N σ]
  rw [inv_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero N hζ), one_mul]

/-- Transitivity of heterogeneous MPV phase equivalence. -/
lemma trans {DA DB DC : ℕ} {A : MPSTensor d DA} {B : MPSTensor d DB}
    {C : MPSTensor d DC} (hAB : MPVBlockPhaseEquiv A B)
    (hBC : MPVBlockPhaseEquiv B C) : MPVBlockPhaseEquiv A C := by
  rcases hAB with ⟨ζ, hζ, hζmpv⟩
  rcases hBC with ⟨η, hη, hηmpv⟩
  refine ⟨η * ζ, mul_ne_zero hη hζ, ?_⟩
  intro N σ
  rw [hηmpv N σ, hζmpv N σ, mul_pow]
  ring

/-- Gauge-phase equivalence after a dimension cast gives heterogeneous MPV phase equivalence. -/
lemma of_gaugePhaseEquiv_cast {DA DB : ℕ} (A : MPSTensor d DA) (B : MPSTensor d DB)
    (hdim : DA = DB)
    (hGPE : GaugePhaseEquiv (d := d)
      (cast (congr_arg (MPSTensor d) hdim) A) B) :
    MPVBlockPhaseEquiv A B := by
  rcases hGPE with ⟨X, ζ, hζ, hX⟩
  refine ⟨ζ, hζ, ?_⟩
  intro N σ
  rw [mpv_eq_pow_mul_of_gaugePhase
    (A := cast (congr_arg (MPSTensor d) hdim) A) (B := B) X ζ hX N σ,
    mpv_cast_dim hdim A N σ]

/-- Heterogeneous MPV phase equivalence gives a scalar-power equality of MPV state vectors. -/
lemma exists_mpvState_eq_smul {DA DB : ℕ} {A : MPSTensor d DA} {B : MPSTensor d DB}
    (h : MPVBlockPhaseEquiv A B) (N : ℕ) :
    ∃ ζ : ℂ, ζ ≠ 0 ∧ mpvState (d := d) B N = ζ ^ N • mpvState (d := d) A N := by
  rcases h with ⟨ζ, hζ, hmpv⟩
  refine ⟨ζ, hζ, ?_⟩
  ext σ
  simp only [PiLp.smul_apply, smul_eq_mul, mpvState_apply]
  exact hmpv N σ

end MPVBlockPhaseEquiv

/-- Bundled common MPV-phase cover for two live-block families.

The data record the finite common family, the class maps from the two
live-block families to it, the MPV-phase equivalences to the chosen common
blocks, and surjectivity of both class maps.  They are the exact paper-level
input needed by the current span adapter; constructing this package from the
full structural `SameMPV₂` data is a separate comparison theorem. -/
structure MPVCommonPhaseCover {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    (blocksA : (j : Fin rA) → MPSTensor d (dimA j))
    (blocksB : (k : Fin rB) → MPSTensor d (dimB k)) where
  rC : ℕ
  dimC : Fin rC → ℕ
  common : (c : Fin rC) → MPSTensor d (dimC c)
  classA : Fin rA → Fin rC
  classB : Fin rB → Fin rC
  phaseA : ∀ j : Fin rA, MPVBlockPhaseEquiv (common (classA j)) (blocksA j)
  phaseB : ∀ k : Fin rB, MPVBlockPhaseEquiv (common (classB k)) (blocksB k)
  surjA : Function.Surjective classA
  surjB : Function.Surjective classB

/-- MPV phase equivalence for a dependent block family.

`MPVPhaseEquiv blocks j k` means that block `k` has the same MPV family as
block `j` after multiplying length-`N` vectors by a nonzero scalar power
`ζ ^ N`.  Gauge-phase equivalence implies this relation, and quotienting a
finite family by this relation is enough to absorb all repeated scalar-power
copies into sector weights.

This is the family-indexed specialization of `MPVBlockPhaseEquiv`, so the
homogeneous phase-class relation shares the heterogeneous block-level relation
rather than duplicating it. -/
def MPVPhaseEquiv {r : ℕ} {dim : Fin r → ℕ}
    (blocks : (k : Fin r) → MPSTensor d (dim k)) (j k : Fin r) : Prop :=
  MPVBlockPhaseEquiv (blocks j) (blocks k)

/-- MPV phase equivalence is reflexive. -/
lemma MPVPhaseEquiv.refl {r : ℕ} {dim : Fin r → ℕ}
    (blocks : (k : Fin r) → MPSTensor d (dim k)) (j : Fin r) :
    MPVPhaseEquiv blocks j j :=
  MPVBlockPhaseEquiv.refl (blocks j)

/-- MPV phase equivalence is symmetric. -/
lemma MPVPhaseEquiv.symm {r : ℕ} {dim : Fin r → ℕ}
    (blocks : (k : Fin r) → MPSTensor d (dim k)) {j k : Fin r}
    (h : MPVPhaseEquiv blocks j k) : MPVPhaseEquiv blocks k j :=
  MPVBlockPhaseEquiv.symm h

/-- MPV phase equivalence is transitive. -/
lemma MPVPhaseEquiv.trans {r : ℕ} {dim : Fin r → ℕ}
    (blocks : (k : Fin r) → MPSTensor d (dim k)) {i j k : Fin r}
    (hij : MPVPhaseEquiv blocks i j) (hjk : MPVPhaseEquiv blocks j k) :
    MPVPhaseEquiv blocks i k :=
  MPVBlockPhaseEquiv.trans hij hjk

/-- A gauge-phase equivalence between equal-dimension blocks gives MPV phase equivalence. -/
lemma MPVPhaseEquiv.of_gaugePhaseEquiv_cast {r : ℕ} {dim : Fin r → ℕ}
    (blocks : (k : Fin r) → MPSTensor d (dim k)) {j k : Fin r}
    (hdim : dim j = dim k)
    (hGPE : GaugePhaseEquiv (d := d)
      (cast (congr_arg (MPSTensor d) hdim) (blocks j)) (blocks k)) :
    MPVPhaseEquiv blocks j k :=
  MPVBlockPhaseEquiv.of_gaugePhaseEquiv_cast (blocks j) (blocks k) hdim hGPE

/-- MPV phase equivalence gives a scalar-power equality of finite-length MPV state vectors. -/
lemma MPVPhaseEquiv.exists_mpvState_eq_smul {r : ℕ} {dim : Fin r → ℕ}
    {blocks : (k : Fin r) → MPSTensor d (dim k)} {j k : Fin r}
    (h : MPVPhaseEquiv blocks j k) (N : ℕ) :
    ∃ ζ : ℂ, ζ ≠ 0 ∧
      mpvState (d := d) (blocks k) N = ζ ^ N • mpvState (d := d) (blocks j) N :=
  MPVBlockPhaseEquiv.exists_mpvState_eq_smul h N

/-- Span inclusion for live blocks covered by another family up to MPV phase.

For each block in `blocksA`, choose a block in `blocksB` whose MPV state differs only by a
nonzero scalar power. Then, at every finite length, the MPV span of `blocksA` is contained in
the MPV span of `blocksB`. -/
theorem mpv_span_le_of_phase_cover {rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    (blocksA : (j : Fin rA) → MPSTensor d (dimA j))
    (blocksB : (k : Fin rB) → MPSTensor d (dimB k))
    (hcover : ∀ j : Fin rA, ∃ k : Fin rB, MPVBlockPhaseEquiv (blocksB k) (blocksA j))
    (N : ℕ) :
    Submodule.span ℂ (Set.range (fun j : Fin rA => mpvState (d := d) (blocksA j) N)) ≤
    Submodule.span ℂ (Set.range (fun k : Fin rB => mpvState (d := d) (blocksB k) N)) := by
  refine Submodule.span_le.2 ?_
  intro v hv
  rcases hv with ⟨j, rfl⟩
  obtain ⟨k, hphase⟩ := hcover j
  obtain ⟨ζ, _hζ, hstate⟩ := hphase.exists_mpvState_eq_smul N
  have hmem : ζ ^ N • mpvState (d := d) (blocksB k) N ∈
      Submodule.span ℂ (Set.range (fun k : Fin rB => mpvState (d := d) (blocksB k) N)) :=
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  simpa [hstate] using hmem

/-- Mutual MPV-phase covers give equality of finite-length live-block MPV spans. -/
theorem mpv_span_eq_of_mutual_phase_cover {rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    (blocksA : (j : Fin rA) → MPSTensor d (dimA j))
    (blocksB : (k : Fin rB) → MPSTensor d (dimB k))
    (hA_le_B : ∀ j : Fin rA, ∃ k : Fin rB, MPVBlockPhaseEquiv (blocksB k) (blocksA j))
    (hB_le_A : ∀ k : Fin rB, ∃ j : Fin rA, MPVBlockPhaseEquiv (blocksA j) (blocksB k))
    (N : ℕ) :
    Submodule.span ℂ (Set.range (fun j : Fin rA => mpvState (d := d) (blocksA j) N)) =
    Submodule.span ℂ (Set.range (fun k : Fin rB => mpvState (d := d) (blocksB k) N)) :=
  le_antisymm
    (mpv_span_le_of_phase_cover blocksA blocksB hA_le_B N)
    (mpv_span_le_of_phase_cover blocksB blocksA hB_le_A N)

/-- A surjective common MPV-phase quotient preserves finite-length live-block spans.

This is the abstract span step needed after a common live-block theorem has identified a family
of representative blocks and shown that every live block maps onto it up to MPV phase. -/
theorem mpv_span_eq_of_surjective_phase_cover {r rC : ℕ}
    {dim : Fin r → ℕ} {dimC : Fin rC → ℕ}
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (common : (c : Fin rC) → MPSTensor d (dimC c))
    (classOf : Fin r → Fin rC)
    (hphase : ∀ k : Fin r, MPVBlockPhaseEquiv (common (classOf k)) (blocks k))
    (hsurj : Function.Surjective classOf)
    (N : ℕ) :
    Submodule.span ℂ (Set.range (fun k : Fin r => mpvState (d := d) (blocks k) N)) =
    Submodule.span ℂ (Set.range (fun c : Fin rC => mpvState (d := d) (common c) N)) := by
  refine mpv_span_eq_of_mutual_phase_cover blocks common ?_ ?_ N
  · intro k
    exact ⟨classOf k, hphase k⟩
  · intro c
    obtain ⟨k, hk⟩ := hsurj c
    refine ⟨k, ?_⟩
    rw [← hk]
    exact (hphase k).symm

/-- Two live-block families with a common surjective MPV-phase quotient have equal finite-length
MPV spans.

This theorem is deliberately independent of the sector weights.  It records the precise
linear-algebra input needed by the exact-live after-blocking theorem once a future common-blocking
result supplies a common family of live representatives and shows that both sides cover it. -/
theorem mpv_span_eq_of_common_phase_cover {rA rB rC : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ} {dimC : Fin rC → ℕ}
    (blocksA : (j : Fin rA) → MPSTensor d (dimA j))
    (blocksB : (k : Fin rB) → MPSTensor d (dimB k))
    (common : (c : Fin rC) → MPSTensor d (dimC c))
    (classA : Fin rA → Fin rC) (classB : Fin rB → Fin rC)
    (hAphase : ∀ j : Fin rA, MPVBlockPhaseEquiv (common (classA j)) (blocksA j))
    (hBphase : ∀ k : Fin rB, MPVBlockPhaseEquiv (common (classB k)) (blocksB k))
    (hAsurj : Function.Surjective classA) (hBsurj : Function.Surjective classB)
    (N : ℕ) :
    Submodule.span ℂ (Set.range (fun j : Fin rA => mpvState (d := d) (blocksA j) N)) =
    Submodule.span ℂ (Set.range (fun k : Fin rB => mpvState (d := d) (blocksB k) N)) := by
  calc
    Submodule.span ℂ (Set.range (fun j : Fin rA => mpvState (d := d) (blocksA j) N))
        = Submodule.span ℂ (Set.range (fun c : Fin rC => mpvState (d := d) (common c) N)) :=
          mpv_span_eq_of_surjective_phase_cover blocksA common classA hAphase hAsurj N
    _ = Submodule.span ℂ (Set.range (fun k : Fin rB => mpvState (d := d) (blocksB k) N)) :=
          (mpv_span_eq_of_surjective_phase_cover blocksB common classB hBphase hBsurj N).symm

namespace MPVCommonPhaseCover

variable {rA rB : ℕ}
variable {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
variable {blocksA : (j : Fin rA) → MPSTensor d (dimA j)}
variable {blocksB : (k : Fin rB) → MPSTensor d (dimB k)}

/-- The bundled common cover gives equality of the finite-length live-block MPV spans. -/
theorem span_eq (C : MPVCommonPhaseCover blocksA blocksB) (N : ℕ) :
    Submodule.span ℂ (Set.range (fun j : Fin rA => mpvState (d := d) (blocksA j) N)) =
    Submodule.span ℂ (Set.range (fun k : Fin rB => mpvState (d := d) (blocksB k) N)) :=
  mpv_span_eq_of_common_phase_cover (d := d) blocksA blocksB C.common
    C.classA C.classB C.phaseA C.phaseB C.surjA C.surjB N

end MPVCommonPhaseCover

/-- Equivalence relation on block indices given by MPV phase equivalence. -/
def mpvPhaseSetoid {r : ℕ} {dim : Fin r → ℕ}
    (blocks : (k : Fin r) → MPSTensor d (dim k)) : Setoid (Fin r) where
  r := MPVPhaseEquiv blocks
  iseqv := {
    refl := MPVPhaseEquiv.refl blocks
    symm := fun {_ _} h => MPVPhaseEquiv.symm blocks h
    trans := fun {_ _ _} h₁ h₂ => MPVPhaseEquiv.trans blocks h₁ h₂
  }

/-- Quotient set of MPV phase equivalence classes. -/
abbrev MPVPhaseClass {r : ℕ} {dim : Fin r → ℕ}
    (blocks : (k : Fin r) → MPSTensor d (dim k)) :=
  Quotient (mpvPhaseSetoid blocks)

/-- The finite quotient by MPV phase classes is finite. -/
noncomputable instance instFintypeMPVPhaseClass {r : ℕ} {dim : Fin r → ℕ}
    (blocks : (k : Fin r) → MPSTensor d (dim k)) : Fintype (MPVPhaseClass blocks) := by
  dsimp [MPVPhaseClass]
  infer_instance

/-- Finite class data for the MPV phase relation.

The data consist of an enumeration of the quotient classes, a choice of
representative per class, the scalar-power relation from each representative to
each member, the separation property for the representatives, and the regrouping
identity for finite sums over the original blocks. -/
structure MPVPhaseClassData {r : ℕ} {dim : Fin r → ℕ}
    (blocks : (k : Fin r) → MPSTensor d (dim k)) where
  g : ℕ
  copies : Fin g → ℕ
  copies_pos : ∀ j, 0 < copies j
  enum : (j : Fin g) → Fin (copies j) → Fin r
  repr : Fin g → Fin r
  enum_phase : ∀ j q, MPVPhaseEquiv blocks (repr j) (enum j q)
  blocks_not_equiv : BlocksNotGaugePhaseEquiv (d := d) (fun j => blocks (repr j))
  regroup : ∀ f : Fin r → ℂ,
    ∑ j : Fin g, ∑ q : Fin (copies j), f (enum j q) = ∑ k : Fin r, f k

namespace MPVPhaseClassData

variable {r : ℕ} {dim : Fin r → ℕ}
variable {blocks : (k : Fin r) → MPSTensor d (dim k)}

/-- Every original block index occurs in the finite enumeration of MPV phase classes. -/
lemma exists_enum_eq (classes : MPVPhaseClassData blocks) (k : Fin r) :
    ∃ j : Fin classes.g, ∃ q : Fin (classes.copies j), classes.enum j q = k := by
  classical
  by_contra h
  push Not at h
  have hzero :
      (∑ j : Fin classes.g, ∑ q : Fin (classes.copies j),
        (if classes.enum j q = k then (1 : ℂ) else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    apply Finset.sum_eq_zero
    intro q _
    simp [h j q]
  have hone : (∑ x : Fin r, (if x = k then (1 : ℂ) else 0)) = 1 := by
    simp
  have hregroup := classes.regroup (fun x : Fin r => if x = k then (1 : ℂ) else 0)
  rw [hzero, hone] at hregroup
  exact zero_ne_one hregroup

/-- The chosen MPV phase-class representatives span exactly the same finite-length MPV
subspace as the original block family.

Each representative is one of the original blocks, giving one inclusion. Conversely, every
original block occurs in a phase class and is a nonzero scalar-power multiple of that class's
representative at each length, hence lies in the representative span. -/
theorem representative_mpv_span_eq (classes : MPVPhaseClassData blocks) (N : ℕ) :
    Submodule.span ℂ (Set.range (fun j : Fin classes.g =>
      mpvState (d := d) (blocks (classes.repr j)) N)) =
    Submodule.span ℂ (Set.range (fun k : Fin r =>
      mpvState (d := d) (blocks k) N)) := by
  classical
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    intro v hv
    rcases hv with ⟨j, rfl⟩
    exact Submodule.subset_span ⟨classes.repr j, rfl⟩
  · refine Submodule.span_le.2 ?_
    intro v hv
    rcases hv with ⟨k, rfl⟩
    obtain ⟨j, q, hq⟩ := classes.exists_enum_eq k
    have hphase : MPVPhaseEquiv blocks (classes.repr j) k := by
      simpa [hq] using classes.enum_phase j q
    change mpvState (d := d) (blocks k) N ∈
      Submodule.span ℂ (Set.range (fun j : Fin classes.g =>
        mpvState (d := d) (blocks (classes.repr j)) N))
    obtain ⟨ζ, _hζ, hstate⟩ := hphase.exists_mpvState_eq_smul N
    rw [hstate]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end MPVPhaseClassData

/-- Construct the finite MPV phase classes of a block family.

The representative of each class is the first element in the finite enumeration
of that class.  If two representatives were gauge-phase equivalent, then they
would be MPV-phase equivalent and hence lie in the same quotient class; this
proves that distinct representatives are pairwise not gauge-phase equivalent. -/
noncomputable def mpvPhaseClassData {r : ℕ} {dim : Fin r → ℕ}
    (blocks : (k : Fin r) → MPSTensor d (dim k)) : MPVPhaseClassData blocks := by
  classical
  let cls := MPVPhaseClass blocks
  let e : cls ≃ Fin (Fintype.card cls) := Fintype.equivFin cls
  let g := Fintype.card cls
  let classOf : Fin g → cls := e.symm
  let classFinset : Fin g → Finset (Fin r) :=
    fun j => Finset.univ.filter (fun k => Quotient.mk (mpvPhaseSetoid blocks) k = classOf j)
  have hClass_nonempty : ∀ j, (classFinset j).Nonempty := by
    intro j
    obtain ⟨k, hk⟩ := Quotient.exists_rep (classOf j)
    refine ⟨k, ?_⟩
    simp [classFinset, hk]
  have hClass_disj :
      Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin g)) : Set (Fin g)) classFinset := by
    intro j _ k _ hne
    apply Finset.disjoint_left.mpr
    intro x hxj hxk
    have hxj' : Quotient.mk (mpvPhaseSetoid blocks) x = classOf j :=
      (Finset.mem_filter.mp hxj).2
    have hxk' : Quotient.mk (mpvPhaseSetoid blocks) x = classOf k :=
      (Finset.mem_filter.mp hxk).2
    have hclass : classOf j = classOf k := hxj'.symm.trans hxk'
    apply hne
    simpa [classOf, e] using congrArg e hclass
  have hClass_cover : Finset.biUnion Finset.univ classFinset = Finset.univ := by
    ext k
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, iff_true]
    refine ⟨e (Quotient.mk (mpvPhaseSetoid blocks) k), ?_⟩
    simp [classFinset, classOf, e]
  let copiesFn : Fin g → ℕ := fun j => (classFinset j).card
  have hcopies_pos : ∀ j, 0 < copiesFn j :=
    fun j => Finset.card_pos.mpr (hClass_nonempty j)
  let enumFn : (j : Fin g) → Fin (copiesFn j) → Fin r :=
    fun j => (classFinset j).orderEmbOfFin rfl
  let reprFn : Fin g → Fin r := fun j => enumFn j ⟨0, hcopies_pos j⟩
  have hrepr_mem : ∀ j, Quotient.mk (mpvPhaseSetoid blocks) (reprFn j) = classOf j := by
    intro j
    exact (Finset.mem_filter.mp ((classFinset j).orderEmbOfFin_mem rfl ⟨0, hcopies_pos j⟩)).2
  have hEnum_phase : ∀ j q, MPVPhaseEquiv blocks (reprFn j) (enumFn j q) := by
    intro j q
    have hrepr : Quotient.mk (mpvPhaseSetoid blocks) (reprFn j) = classOf j := hrepr_mem j
    have henum : Quotient.mk (mpvPhaseSetoid blocks) (enumFn j q) = classOf j :=
      (Finset.mem_filter.mp ((classFinset j).orderEmbOfFin_mem rfl q)).2
    exact Quotient.exact (hrepr.trans henum.symm)
  have hBlocks : BlocksNotGaugePhaseEquiv (d := d) (fun j => blocks (reprFn j)) := by
    intro j k hjk hdim hGPE
    have hphase : MPVPhaseEquiv blocks (reprFn j) (reprFn k) :=
      MPVPhaseEquiv.of_gaugePhaseEquiv_cast blocks hdim hGPE
    have hquot : Quotient.mk (mpvPhaseSetoid blocks) (reprFn j) =
        Quotient.mk (mpvPhaseSetoid blocks) (reprFn k) :=
      Quotient.sound hphase
    have hclass : classOf j = classOf k := by
      exact (hrepr_mem j).symm.trans (hquot.trans (hrepr_mem k))
    apply hjk
    simpa [classOf, e] using congrArg e hclass
  have hRegroup : ∀ (f : Fin r → ℂ),
      ∑ j : Fin g, ∑ q : Fin (copiesFn j), f (enumFn j q) = ∑ k : Fin r, f k := by
    intro f
    have inner_eq : ∀ j : Fin g,
        ∑ q : Fin (copiesFn j), f (enumFn j q) = ∑ k ∈ classFinset j, f k := by
      intro j
      rw [← Finset.map_orderEmbOfFin_univ (classFinset j) rfl, Finset.sum_map]
      rfl
    simp_rw [inner_eq]
    calc ∑ j : Fin g, ∑ k ∈ classFinset j, f k
        = ∑ k ∈ Finset.biUnion Finset.univ classFinset, f k :=
            (Finset.sum_biUnion hClass_disj).symm
      _ = ∑ k ∈ Finset.univ, f k := by rw [hClass_cover]
      _ = ∑ k : Fin r, f k := rfl
  exact {
    g := g
    copies := copiesFn
    copies_pos := hcopies_pos
    enum := enumFn
    repr := reprFn
    enum_phase := hEnum_phase
    blocks_not_equiv := hBlocks
    regroup := hRegroup
  }

/-! ### §5. Eventual independence from separated overlap data -/

/-- **Eventual BNT linear independence for an already separated normal family.**

For TP primitive irreducible blocks that are pairwise not gauge-phase equivalent,
self-overlaps tend to `1` and cross-overlaps tend to `0`.  Hence their MPV states
are eventually linearly independent.  This supplies the missing linear-independence
step after a future one-sided BNT construction has chosen separated representatives
and absorbed all repeated gauge phases into sector weights. -/
theorem exists_eventually_linearIndependent_of_tp_primitive_irr_blocks_of_blocksNotGaugePhaseEquiv
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hTP : ∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1)
    (hIrr : ∀ k, IsIrreducibleTensor (blocks k))
    (hPrim : ∀ k, _root_.IsPrimitive (transferMap (d := d) (D := dim k) (blocks k)))
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) blocks) :
    ∃ N0 : ℕ, ∀ N > N0,
      LinearIndependent ℂ (fun k : Fin r => mpvState (d := d) (blocks k) N) := by
  apply exists_eventually_linearIndependent_of_overlap_tendsto_orthonormal blocks
  · intro k
    exact overlap_tendsto_one_of_peripheralPrimitive_of_irreducible
      (blocks k) (hIrr k) (hTP k) (hPrim k)
  · intro j k hjk
    exact cross_overlap_tendsto_zero_of_separated_normalCFBNT_data blocks
      (HasIrreducibleBlocks.ofForall hIrr)
      (IsLeftCanonicalBlockFamily.ofForall hTP)
      hBlocks j k hjk

/-- **Separated-family BNT sector construction.**

If the TP primitive irreducible input blocks are already pairwise separated by
non-gauge-phase-equivalence, the granular sector decomposition is a genuine BNT
sector decomposition: it represents the original weighted block sum and satisfies
`HasBNTSectorData` by the overlap-derived eventual linear independence above.

This theorem does not collapse gauge-phase-equivalent input blocks.  Instead it
identifies the exact remaining task for the full one-sided construction: first
choose separated representatives and absorb the corresponding phases into sector
weights, then apply this constructor. -/
theorem exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks_of_blocksNotGaugePhaseEquiv
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hTP : ∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1)
    (hIrr : ∀ k, IsIrreducibleTensor (blocks k))
    (hPrim : ∀ k, _root_.IsPrimitive (transferMap (d := d) (D := dim k) (blocks k)))
    (hμne : ∀ k, μ k ≠ 0)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) blocks) :
    ∃ P : SectorDecomposition d,
      SameMPV₂ P.toTensor (toTensorFromBlocks (d := d) (μ := μ) blocks) ∧
      HasBNTSectorData (d := d) P := by
  refine ⟨trivialSectorDecomp μ blocks hμne,
    sameMPV₂_trivialSectorDecomp μ blocks hμne, ?_⟩
  simpa [trivialSectorDecomp] using
    exists_eventually_linearIndependent_of_tp_primitive_irr_blocks_of_blocksNotGaugePhaseEquiv
      blocks hTP hIrr hPrim hBlocks

/-- The concrete sector decomposition obtained from representatives of MPV phase classes. -/
private noncomputable def collapsedBntSectorDecomp
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hμne : ∀ k, μ k ≠ 0) : SectorDecomposition d :=
  let classes := mpvPhaseClassData blocks
  let ζFn : (j : Fin classes.g) → Fin (classes.copies j) → ℂ :=
    fun j q => (classes.enum_phase j q).choose
  let hζ_ne : ∀ j q, ζFn j q ≠ 0 :=
    fun j q => (classes.enum_phase j q).choose_spec.1
  let sectors : SectorWeightData classes.g := {
    copies := classes.copies
    copies_pos := classes.copies_pos
    weight := fun j q => ζFn j q * μ (classes.enum j q)
    weight_ne_zero := fun j q => mul_ne_zero (hζ_ne j q) (hμne (classes.enum j q))
  }
  {
    basisCount := classes.g
    basisDim := fun j => dim (classes.repr j)
    basis := fun j => blocks (classes.repr j)
    sectors := sectors
  }

private theorem collapsedBntSectorDecomp_sameMPV₂
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hμne : ∀ k, μ k ≠ 0) :
    SameMPV₂ (collapsedBntSectorDecomp (d := d) μ blocks hμne).toTensor
      (toTensorFromBlocks (d := d) (μ := μ) blocks) := by
  classical
  let classes := mpvPhaseClassData blocks
  let ζFn : (j : Fin classes.g) → Fin (classes.copies j) → ℂ :=
    fun j q => (classes.enum_phase j q).choose
  have hζ_mpv : ∀ j q (N : ℕ) (σ : Fin N → Fin d),
      mpv (blocks (classes.enum j q)) σ = (ζFn j q) ^ N * mpv (blocks (classes.repr j)) σ :=
    fun j q N σ => (classes.enum_phase j q).choose_spec.2 N σ
  let P := collapsedBntSectorDecomp (d := d) μ blocks hμne
  intro N σ
  calc mpv P.toTensor σ
      = ∑ j : Fin P.basisCount,
          ∑ q : Fin (P.copies j), (P.weight j q) ^ N * mpv (P.basis j) σ :=
          P.mpv_toTensor_eq_sum_sectors σ
    _ = ∑ j : Fin classes.g,
          ∑ q : Fin (classes.copies j),
            (ζFn j q * μ (classes.enum j q)) ^ N *
              mpv (blocks (classes.repr j)) σ := by
            rfl
    _ = ∑ j : Fin classes.g,
          ∑ q : Fin (classes.copies j),
            (μ (classes.enum j q)) ^ N * mpv (blocks (classes.enum j q)) σ := by
            refine Finset.sum_congr rfl (fun j _ =>
              Finset.sum_congr rfl (fun q _ => ?_))
            rw [mul_pow, hζ_mpv j q N σ]
            ring
    _ = ∑ k : Fin r, (μ k) ^ N * mpv (blocks k) σ :=
          classes.regroup (fun k => (μ k) ^ N * mpv (blocks k) σ)
    _ = mpv (toTensorFromBlocks (d := d) (μ := μ) blocks) σ := by
            symm
            simpa [smul_eq_mul] using mpv_toTensorFromBlocks_eq_sum μ blocks σ

private theorem collapsedBntSectorDecomp_hasBNT
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hTP : ∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1)
    (hIrr : ∀ k, IsIrreducibleTensor (blocks k))
    (hPrim : ∀ k, _root_.IsPrimitive (transferMap (d := d) (D := dim k) (blocks k)))
    (hμne : ∀ k, μ k ≠ 0) :
    HasBNTSectorData (d := d) (collapsedBntSectorDecomp (d := d) μ blocks hμne) := by
  classical
  let classes := mpvPhaseClassData blocks
  let P := collapsedBntSectorDecomp (d := d) μ blocks hμne
  have hLI : ∃ N0 : ℕ, ∀ N > N0,
      LinearIndependent ℂ
        (fun j : Fin classes.g => mpvState (d := d) (blocks (classes.repr j)) N) :=
    exists_eventually_linearIndependent_of_tp_primitive_irr_blocks_of_blocksNotGaugePhaseEquiv
      (fun j : Fin classes.g => blocks (classes.repr j))
      (fun j => hTP (classes.repr j))
      (fun j => hIrr (classes.repr j))
      (fun j => hPrim (classes.repr j))
      classes.blocks_not_equiv
  simpa [P, collapsedBntSectorDecomp] using hLI

/-- **Unconditional one-sided BNT sector construction for primitive irreducible blocks.**

Starting from arbitrary trace-preserving primitive irreducible blocks with
nonzero weights, quotient the block indices by MPV phase equivalence.  One
representative is chosen for each class; for every original block in the class,
the associated phase is multiplied into its sector weight.  Gauge-phase-equivalent
blocks land in the same MPV phase class, so the chosen representatives satisfy
`BlocksNotGaugePhaseEquiv`.  The separated-family BNT independence theorem then
proves `HasBNTSectorData` for the constructed sector decomposition. -/
theorem exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hTP : ∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1)
    (hIrr : ∀ k, IsIrreducibleTensor (blocks k))
    (hPrim : ∀ k, _root_.IsPrimitive (transferMap (d := d) (D := dim k) (blocks k)))
    (hμne : ∀ k, μ k ≠ 0) :
    ∃ P : SectorDecomposition d,
      SameMPV₂ P.toTensor (toTensorFromBlocks (d := d) (μ := μ) blocks) ∧
      HasBNTSectorData (d := d) P := by
  refine ⟨collapsedBntSectorDecomp (d := d) μ blocks hμne, ?_, ?_⟩
  · exact collapsedBntSectorDecomp_sameMPV₂ (d := d) μ blocks hμne
  · exact collapsedBntSectorDecomp_hasBNT (d := d) μ blocks hTP hIrr hPrim hμne

/-- **Phase-class BNT sector construction with one-sided overlap data.**

Starting from trace-preserving primitive irreducible blocks with nonzero weights,
quotient the block indices by MPV phase equivalence. The constructed sector
decomposition represents the original weighted block sum, satisfies the BNT
linear-independence condition, and its chosen basis blocks carry the
single-family overlap-orthogonality data needed for the primitive
overlap-rigidity route.

The theorem also records that if the original blocks are one-site injective,
then the chosen basis blocks are injective. It does not claim the remaining
two-family input: equality of the finite-length MPV spans between two
independently constructed bases is a separate Gap §1 task. -/
theorem exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks_with_overlapOrtho
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hTP : ∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1)
    (hIrr : ∀ k, IsIrreducibleTensor (blocks k))
    (hPrim : ∀ k, _root_.IsPrimitive (transferMap (d := d) (D := dim k) (blocks k)))
    (hμne : ∀ k, μ k ≠ 0) :
    ∃ P : SectorDecomposition d,
      SameMPV₂ P.toTensor (toTensorFromBlocks (d := d) (μ := μ) blocks) ∧
      HasBNTSectorData (d := d) P ∧
      SectorBasisOverlapOrthoHypotheses P ∧
      ((∀ k, IsInjective (blocks k)) → ∀ j, IsInjective (P.basis j)) := by
  classical
  let classes := mpvPhaseClassData blocks
  let P := collapsedBntSectorDecomp (d := d) μ blocks hμne
  have hSame : SameMPV₂ P.toTensor (toTensorFromBlocks (d := d) (μ := μ) blocks) :=
    collapsedBntSectorDecomp_sameMPV₂ (d := d) μ blocks hμne
  have hBNT : HasBNTSectorData (d := d) P :=
    collapsedBntSectorDecomp_hasBNT (d := d) μ blocks hTP hIrr hPrim hμne
  refine ⟨P, hSame, hBNT, ?_, ?_⟩
  · refine {
      dim_pos := ?_
      normalized := ?_
      self_overlap := ?_
      off_overlap := ?_
    }
    · intro j
      simpa [P, collapsedBntSectorDecomp] using NeZero.pos (dim (classes.repr j))
    · intro j
      simpa [P, collapsedBntSectorDecomp] using hTP (classes.repr j)
    · intro j
      simpa [P, collapsedBntSectorDecomp] using
        overlap_tendsto_one_of_peripheralPrimitive_of_irreducible
        (blocks (classes.repr j)) (hIrr (classes.repr j))
        (hTP (classes.repr j)) (hPrim (classes.repr j))
    · intro i j hij
      simpa [P, collapsedBntSectorDecomp] using
        cross_overlap_tendsto_zero_of_separated_normalCFBNT_data
        (fun j : Fin classes.g => blocks (classes.repr j))
        (HasIrreducibleBlocks.ofForall (fun j => hIrr (classes.repr j)))
        (IsLeftCanonicalBlockFamily.ofForall (fun j => hTP (classes.repr j)))
        classes.blocks_not_equiv i j hij
  · intro hInj j
    simpa [P, collapsedBntSectorDecomp] using hInj (classes.repr j)

/-- Concrete one-sided data for the construction using representatives of MPV phase-equivalence
classes, including the finite-length representative-span identity.

This private auxiliary lemma consolidates the proof of the common fields shared by the
public one-sided overlap data theorems. -/
private theorem bntSectorDecomp_overlapData_basisSpan_aux
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hTP : ∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1)
    (hIrr : ∀ k, IsIrreducibleTensor (blocks k))
    (hPrim : ∀ k, _root_.IsPrimitive (transferMap (d := d) (D := dim k) (blocks k)))
    (hInj : ∀ k, IsInjective (blocks k))
    (hμne : ∀ k, μ k ≠ 0) :
    ∃ P : SectorDecomposition d,
      SameMPV₂ P.toTensor (toTensorFromBlocks (d := d) (μ := μ) blocks) ∧
      HasBNTSectorData (d := d) P ∧
      (∀ j : Fin P.basisCount, 0 < P.basisDim j) ∧
      (∀ j : Fin P.basisCount, IsInjective (P.basis j)) ∧
      (∀ j : Fin P.basisCount, (∑ i : Fin d, (P.basis j i)ᴴ * (P.basis j i)) = 1) ∧
      (∀ j : Fin P.basisCount,
        Filter.Tendsto (fun N => mpvOverlap (d := d) (P.basis j) (P.basis j) N)
          Filter.atTop (nhds (1 : ℂ))) ∧
      (∀ i j : Fin P.basisCount, i ≠ j →
        Filter.Tendsto (fun N => mpvOverlap (d := d) (P.basis i) (P.basis j) N)
          Filter.atTop (nhds 0)) ∧
      (∀ N,
        Submodule.span ℂ (Set.range (fun j : Fin P.basisCount =>
          mpvState (d := d) (P.basis j) N)) =
        Submodule.span ℂ (Set.range (fun k : Fin r =>
          mpvState (d := d) (blocks k) N))) := by
  classical
  let classes := mpvPhaseClassData blocks
  let P := collapsedBntSectorDecomp (d := d) μ blocks hμne
  have hSame : SameMPV₂ P.toTensor (toTensorFromBlocks (d := d) (μ := μ) blocks) :=
    collapsedBntSectorDecomp_sameMPV₂ (d := d) μ blocks hμne
  have hBNT : HasBNTSectorData (d := d) P :=
    collapsedBntSectorDecomp_hasBNT (d := d) μ blocks hTP hIrr hPrim hμne
  refine ⟨P, hSame, hBNT, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    simpa [P, collapsedBntSectorDecomp] using NeZero.pos (dim (classes.repr j))
  · intro j
    simpa [P, collapsedBntSectorDecomp] using hInj (classes.repr j)
  · intro j
    simpa [P, collapsedBntSectorDecomp] using hTP (classes.repr j)
  · intro j
    simpa [P, collapsedBntSectorDecomp] using
      overlap_tendsto_one_of_peripheralPrimitive_of_irreducible
      (blocks (classes.repr j)) (hIrr (classes.repr j)) (hTP (classes.repr j))
      (hPrim (classes.repr j))
  · intro i j hij
    simpa [P, collapsedBntSectorDecomp] using
      cross_overlap_tendsto_zero_of_separated_normalCFBNT_data
      (fun j : Fin classes.g => blocks (classes.repr j))
      (HasIrreducibleBlocks.ofForall (fun j => hIrr (classes.repr j)))
      (IsLeftCanonicalBlockFamily.ofForall (fun j => hTP (classes.repr j)))
      classes.blocks_not_equiv i j hij
  · intro N
    simpa [P, collapsedBntSectorDecomp] using classes.representative_mpv_span_eq (d := d) N

/-- **Phase-class BNT sector construction with primitive overlap data.**

This strengthens `exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks` by exposing the
properties of the chosen representative basis blocks that are needed by the overlap-rigidity
layer. The extra `hInj` hypothesis is intentional: the one-sided BNT constructor assumes
irreducibility, primitivity, and trace preservation, while
`SectorBasisOverlapSpanHypotheses` consumes length-1 MPS-injectivity.

The finite-span comparison between two independently constructed sector bases is not part of
this one-sided theorem; it depends on comparing the two sides. -/
theorem exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks_with_overlapData
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hTP : ∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1)
    (hIrr : ∀ k, IsIrreducibleTensor (blocks k))
    (hPrim : ∀ k, _root_.IsPrimitive (transferMap (d := d) (D := dim k) (blocks k)))
    (hInj : ∀ k, IsInjective (blocks k))
    (hμne : ∀ k, μ k ≠ 0) :
    ∃ P : SectorDecomposition d,
      SameMPV₂ P.toTensor (toTensorFromBlocks (d := d) (μ := μ) blocks) ∧
      HasBNTSectorData (d := d) P ∧
      (∀ j : Fin P.basisCount, 0 < P.basisDim j) ∧
      (∀ j : Fin P.basisCount, IsInjective (P.basis j)) ∧
      (∀ j : Fin P.basisCount, (∑ i : Fin d, (P.basis j i)ᴴ * (P.basis j i)) = 1) ∧
      (∀ j : Fin P.basisCount,
        Filter.Tendsto (fun N => mpvOverlap (d := d) (P.basis j) (P.basis j) N)
          Filter.atTop (nhds (1 : ℂ))) ∧
      (∀ i j : Fin P.basisCount, i ≠ j →
        Filter.Tendsto (fun N => mpvOverlap (d := d) (P.basis i) (P.basis j) N)
          Filter.atTop (nhds 0)) := by
  obtain ⟨P, hSame, hBNT, hPos, hBasisInj, hBasisTP, hSelfOverlap, hCrossOverlap, _hSpan⟩ :=
    bntSectorDecomp_overlapData_basisSpan_aux
      (d := d) μ blocks hTP hIrr hPrim hInj hμne
  exact ⟨P, hSame, hBNT, hPos, hBasisInj, hBasisTP, hSelfOverlap, hCrossOverlap⟩

/-- **Phase-class BNT sector construction with overlap data and the quotient span identity.**

This strengthens `exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks_with_overlapData` by
also exposing the finite-length span invariant of the phase-class representative
construction: at every length, the chosen MPV phase-class representatives span the same
MPV subspace as the original block
family.  This removes the quotient/enumeration bookkeeping from later two-sided span
comparisons; the remaining comparison is the genuine equality of the two original live-block
spans. -/
theorem exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks_with_overlapData_and_basisSpan
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hTP : ∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1)
    (hIrr : ∀ k, IsIrreducibleTensor (blocks k))
    (hPrim : ∀ k, _root_.IsPrimitive (transferMap (d := d) (D := dim k) (blocks k)))
    (hInj : ∀ k, IsInjective (blocks k))
    (hμne : ∀ k, μ k ≠ 0) :
    ∃ P : SectorDecomposition d,
      SameMPV₂ P.toTensor (toTensorFromBlocks (d := d) (μ := μ) blocks) ∧
      HasBNTSectorData (d := d) P ∧
      (∀ j : Fin P.basisCount, 0 < P.basisDim j) ∧
      (∀ j : Fin P.basisCount, IsInjective (P.basis j)) ∧
      (∀ j : Fin P.basisCount, (∑ i : Fin d, (P.basis j i)ᴴ * (P.basis j i)) = 1) ∧
      (∀ j : Fin P.basisCount,
        Filter.Tendsto (fun N => mpvOverlap (d := d) (P.basis j) (P.basis j) N)
          Filter.atTop (nhds (1 : ℂ))) ∧
      (∀ i j : Fin P.basisCount, i ≠ j →
        Filter.Tendsto (fun N => mpvOverlap (d := d) (P.basis i) (P.basis j) N)
          Filter.atTop (nhds 0)) ∧
      (∀ N,
        Submodule.span ℂ (Set.range (fun j : Fin P.basisCount =>
          mpvState (d := d) (P.basis j) N)) =
        Submodule.span ℂ (Set.range (fun k : Fin r =>
          mpvState (d := d) (blocks k) N))) := by
  exact bntSectorDecomp_overlapData_basisSpan_aux
    (d := d) μ blocks hTP hIrr hPrim hInj hμne

/-- **Two-sided overlap-span data from live-block span equality.**

Apply the construction using representatives of MPV phase-equivalence classes on both live
block families. The one-sided quotient span identity above transports a finite-length span
equality for the original live blocks to the two independently chosen sector bases. Thus the
theorem provides all fields of `SectorBasisOverlapSpanHypotheses` without assuming that
structure directly.

The remaining paper-level task, not proved here, is to derive the displayed live-block span
equality from the global `SameMPV₂` and structural reduction data. -/
theorem exists_bnt_sectorDecomp_pair_with_overlapSpan_of_block_span_eq
    {rA rB : ℕ} {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    (μA : Fin rA → ℂ)
    (blocksA : (k : Fin rA) → MPSTensor d (dimA k))
    (μB : Fin rB → ℂ)
    (blocksB : (k : Fin rB) → MPSTensor d (dimB k))
    (hTPA : ∀ k, ∑ i : Fin d, (blocksA k i)ᴴ * blocksA k i = 1)
    (hTPB : ∀ k, ∑ i : Fin d, (blocksB k i)ᴴ * blocksB k i = 1)
    (hIrrA : ∀ k, IsIrreducibleTensor (blocksA k))
    (hIrrB : ∀ k, IsIrreducibleTensor (blocksB k))
    (hPrimA : ∀ k, _root_.IsPrimitive (transferMap (d := d) (D := dimA k) (blocksA k)))
    (hPrimB : ∀ k, _root_.IsPrimitive (transferMap (d := d) (D := dimB k) (blocksB k)))
    (hInjA : ∀ k, IsInjective (blocksA k))
    (hInjB : ∀ k, IsInjective (blocksB k))
    (hμA : ∀ k, μA k ≠ 0)
    (hμB : ∀ k, μB k ≠ 0)
    (hBlockSpan : ∀ N,
      Submodule.span ℂ (Set.range (fun k : Fin rA =>
        mpvState (d := d) (blocksA k) N)) =
      Submodule.span ℂ (Set.range (fun k : Fin rB =>
        mpvState (d := d) (blocksB k) N))) :
    ∃ P Q : SectorDecomposition d,
      SameMPV₂ P.toTensor (toTensorFromBlocks (d := d) (μ := μA) blocksA) ∧
      SameMPV₂ Q.toTensor (toTensorFromBlocks (d := d) (μ := μB) blocksB) ∧
      HasBNTSectorData (d := d) P ∧
      HasBNTSectorData (d := d) Q ∧
      SectorBasisOverlapSpanHypotheses P Q := by
  obtain ⟨P, hPblocks, hPbnt, hPdim, hPinj, hPnorm, hPself, hPoff, hPspan⟩ :=
    exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks_with_overlapData_and_basisSpan
      (d := d) μA blocksA hTPA hIrrA hPrimA hInjA hμA
  obtain ⟨Q, hQblocks, hQbnt, hQdim, hQinj, hQnorm, hQself, hQoff, hQspan⟩ :=
    exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks_with_overlapData_and_basisSpan
      (d := d) μB blocksB hTPB hIrrB hPrimB hInjB hμB
  have hSpan : ∀ N,
      Submodule.span ℂ (Set.range (fun j : Fin P.basisCount =>
        mpvState (d := d) (P.basis j) N)) =
      Submodule.span ℂ (Set.range (fun k : Fin Q.basisCount =>
        mpvState (d := d) (Q.basis k) N)) := by
    intro N
    calc
      Submodule.span ℂ (Set.range (fun j : Fin P.basisCount =>
          mpvState (d := d) (P.basis j) N))
          = Submodule.span ℂ (Set.range (fun k : Fin rA =>
              mpvState (d := d) (blocksA k) N)) := hPspan N
      _ = Submodule.span ℂ (Set.range (fun k : Fin rB =>
              mpvState (d := d) (blocksB k) N)) := hBlockSpan N
      _ = Submodule.span ℂ (Set.range (fun k : Fin Q.basisCount =>
              mpvState (d := d) (Q.basis k) N)) := (hQspan N).symm
  refine ⟨P, Q, hPblocks, hQblocks, hPbnt, hQbnt, ?_⟩
  exact {
    left_dim_pos := hPdim
    right_dim_pos := hQdim
    left_injective := hPinj
    right_injective := hQinj
    left_normalized := hPnorm
    right_normalized := hQnorm
    left_self_overlap := hPself
    left_off_overlap := hPoff
    right_self_overlap := hQself
    right_off_overlap := hQoff
    span_eq := hSpan
  }

/-! ### §6. Conditional sector construction under BNT linear independence -/

/-- **Minimal granular sector decomposition carrying current `HasBNTSectorData`.**

This is the post-#886 formulation of the conditional sector construction.  The
predicate `HasBNTSectorData` now means eventual linear independence of the sector
basis MPV states.  TP, irreducibility, primitivity, and nonzero weights do not by
themselves provide that linear-independence statement for the granular basis; the
genuine one-sided BNT construction must first choose / collapse to a basis of normal
tensors.

Accordingly this theorem gives the simplest construction: if the granular input
basis is already known to satisfy the current BNT linear-independence hypothesis,
then `trivialSectorDecomp` gives the requested `SectorDecomposition` and the
`HasBNTSectorData` certificate is exactly the supplied `hLI`. -/
theorem exists_bnt_sectorDecomp_of_linearIndependent
    {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (hμne : ∀ k, μ k ≠ 0)
    (hLI : ∃ N0 : ℕ, ∀ N > N0,
      LinearIndependent ℂ (fun k : Fin r => mpvState (blocks k) N)) :
    ∃ P : SectorDecomposition d,
      SameMPV₂ P.toTensor (toTensorFromBlocks (d := d) (μ := μ) blocks) ∧
      HasBNTSectorData (d := d) P := by
  refine ⟨trivialSectorDecomp μ blocks hμne,
    sameMPV₂_trivialSectorDecomp μ blocks hμne, ?_⟩
  simpa [trivialSectorDecomp] using hLI

/-- Signature-compatible reformulation for TP / primitive / irreducible block data.

The extra block-normality hypotheses are intentionally retained here to match the
shape expected by the one-sided BNT-construction route, but only nonzero weights and the
current BNT linear-independence hypothesis are used.  Use
`exists_bnt_sectorDecomp_of_linearIndependent` when those extra hypotheses are not
already present. -/
theorem exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks_of_linearIndependent
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (μ : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k))
    (_hTP : ∀ k, ∑ i : Fin d, (blocks k i)ᴴ * blocks k i = 1)
    (_hIrr : ∀ k, IsIrreducibleTensor (blocks k))
    (_hPrim : ∀ k, _root_.IsPrimitive (transferMap (d := d) (D := dim k) (blocks k)))
    (hμne : ∀ k, μ k ≠ 0)
    (hLI : ∃ N0 : ℕ, ∀ N > N0,
      LinearIndependent ℂ (fun k : Fin r => mpvState (blocks k) N)) :
    ∃ P : SectorDecomposition d,
      SameMPV₂ P.toTensor (toTensorFromBlocks (d := d) (μ := μ) blocks) ∧
      HasBNTSectorData (d := d) P :=
  exists_bnt_sectorDecomp_of_linearIndependent μ blocks hμne hLI

end MPSTensor
