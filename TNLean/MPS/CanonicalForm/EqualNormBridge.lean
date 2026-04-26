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

* `exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks` — the collapsed-representative
  construction: it quotients arbitrary TP / primitive / irreducible blocks by MPV phase
  equivalence, absorbs the scalar factors into sector weights, proves representative
  separation, and then obtains `HasBNTSectorData` from the separated-family theorem.

* `exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks_of_linearIndependent` —
  signature-compatible reformulation retaining the TP / primitive / irreducible
  inputs expected by the one-sided BNT construction chain.

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

/-! ### §4. Collapsed representatives from MPV phase classes -/

/-- MPV phase equivalence for a dependent block family.

`MPVPhaseEquiv blocks j k` means that block `k` has the same MPV family as
block `j` after multiplying length-`N` vectors by a nonzero scalar power
`ζ ^ N`.  Gauge-phase equivalence implies this relation, and quotienting a
finite family by this relation is enough to absorb all repeated scalar-power
copies into sector weights. -/
def MPVPhaseEquiv {r : ℕ} {dim : Fin r → ℕ}
    (blocks : (k : Fin r) → MPSTensor d (dim k)) (j k : Fin r) : Prop :=
  ∃ ζ : ℂ, ζ ≠ 0 ∧ ∀ (N : ℕ) (σ : Fin N → Fin d),
    mpv (blocks k) σ = ζ ^ N * mpv (blocks j) σ

/-- MPV phase equivalence is reflexive. -/
lemma MPVPhaseEquiv.refl {r : ℕ} {dim : Fin r → ℕ}
    (blocks : (k : Fin r) → MPSTensor d (dim k)) (j : Fin r) :
    MPVPhaseEquiv blocks j j := by
  exact ⟨1, one_ne_zero, fun N σ => by simp⟩

/-- MPV phase equivalence is symmetric. -/
lemma MPVPhaseEquiv.symm {r : ℕ} {dim : Fin r → ℕ}
    (blocks : (k : Fin r) → MPSTensor d (dim k)) {j k : Fin r}
    (h : MPVPhaseEquiv blocks j k) : MPVPhaseEquiv blocks k j := by
  rcases h with ⟨ζ, hζ, hmpv⟩
  refine ⟨ζ⁻¹, inv_ne_zero hζ, ?_⟩
  intro N σ
  rw [hmpv N σ]
  rw [inv_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero N hζ), one_mul]

/-- MPV phase equivalence is transitive. -/
lemma MPVPhaseEquiv.trans {r : ℕ} {dim : Fin r → ℕ}
    (blocks : (k : Fin r) → MPSTensor d (dim k)) {i j k : Fin r}
    (hij : MPVPhaseEquiv blocks i j) (hjk : MPVPhaseEquiv blocks j k) :
    MPVPhaseEquiv blocks i k := by
  rcases hij with ⟨ζ, hζ, hζmpv⟩
  rcases hjk with ⟨η, hη, hηmpv⟩
  refine ⟨η * ζ, mul_ne_zero hη hζ, ?_⟩
  intro N σ
  rw [hηmpv N σ, hζmpv N σ, mul_pow]
  ring

/-- A gauge-phase equivalence between equal-dimension blocks gives MPV phase equivalence. -/
lemma MPVPhaseEquiv.of_gaugePhaseEquiv_cast {r : ℕ} {dim : Fin r → ℕ}
    (blocks : (k : Fin r) → MPSTensor d (dim k)) {j k : Fin r}
    (hdim : dim j = dim k)
    (hGPE : GaugePhaseEquiv (d := d)
      (cast (congr_arg (MPSTensor d) hdim) (blocks j)) (blocks k)) :
    MPVPhaseEquiv blocks j k := by
  rcases hGPE with ⟨X, ζ, hζ, hX⟩
  refine ⟨ζ, hζ, ?_⟩
  intro N σ
  rw [mpv_eq_pow_mul_of_gaugePhase
    (A := cast (congr_arg (MPSTensor d) hdim) (blocks j))
    (B := blocks k) X ζ hX N σ,
    mpv_cast_dim hdim (blocks j) N σ]

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

/-- **Unconditional one-sided BNT sector construction for primitive irreducible blocks.**

Starting from arbitrary trace-preserving primitive irreducible blocks with
nonzero weights, quotient the block indices by MPV phase equivalence.  One
representative is chosen for each class; for every original block in the class,
the associated phase is multiplied into its sector weight.  Gauge-phase-equivalent
blocks land in the same MPV phase class, so the chosen representatives satisfy
`BlocksNotGaugePhaseEquiv`.  The separated-family BNT independence theorem then
proves `HasBNTSectorData` for the collapsed sector decomposition. -/
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
  classical
  let classes := mpvPhaseClassData blocks
  let ζFn : (j : Fin classes.g) → Fin (classes.copies j) → ℂ :=
    fun j q => (classes.enum_phase j q).choose
  have hζ_ne : ∀ j q, ζFn j q ≠ 0 := fun j q => (classes.enum_phase j q).choose_spec.1
  have hζ_mpv : ∀ j q (N : ℕ) (σ : Fin N → Fin d),
      mpv (blocks (classes.enum j q)) σ = (ζFn j q) ^ N * mpv (blocks (classes.repr j)) σ :=
    fun j q N σ => (classes.enum_phase j q).choose_spec.2 N σ
  let sectors : SectorWeightData classes.g := {
    copies := classes.copies
    copies_pos := classes.copies_pos
    weight := fun j q => ζFn j q * μ (classes.enum j q)
    weight_ne_zero := fun j q => mul_ne_zero (hζ_ne j q) (hμne (classes.enum j q))
  }
  let P : SectorDecomposition d := {
    basisCount := classes.g
    basisDim := fun j => dim (classes.repr j)
    basis := fun j => blocks (classes.repr j)
    sectors := sectors
  }
  refine ⟨P, ?_, ?_⟩
  · intro N σ
    calc mpv P.toTensor σ
        = ∑ j : Fin P.basisCount,
            ∑ q : Fin (P.copies j), (P.weight j q) ^ N * mpv (P.basis j) σ :=
            P.mpv_toTensor_eq_sum_sectors σ
      _ = ∑ j : Fin classes.g,
            ∑ q : Fin (classes.copies j),
              (ζFn j q * μ (classes.enum j q)) ^ N *
                mpv (blocks (classes.repr j)) σ := rfl
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
  · have hLI : ∃ N0 : ℕ, ∀ N > N0,
        LinearIndependent ℂ
          (fun j : Fin classes.g => mpvState (d := d) (blocks (classes.repr j)) N) :=
      exists_eventually_linearIndependent_of_tp_primitive_irr_blocks_of_blocksNotGaugePhaseEquiv
        (fun j : Fin classes.g => blocks (classes.repr j))
        (fun j => hTP (classes.repr j))
        (fun j => hIrr (classes.repr j))
        (fun j => hPrim (classes.repr j))
        classes.blocks_not_equiv
    simpa [P] using hLI

/-- **Collapsed BNT sector construction with primitive overlap data.**

This strengthens `exists_bnt_sectorDecomp_of_tp_primitive_irr_blocks` by exposing the
properties of the chosen representative basis blocks that are needed by the overlap-rigidity
layer. The extra `hInj` hypothesis is intentional: the one-sided BNT constructor assumes
irreducibility, primitivity, and trace preservation, while
`SectorBasisOverlapSpanHypotheses` consumes one-letter injectivity.

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
  classical
  let classes := mpvPhaseClassData blocks
  let ζFn : (j : Fin classes.g) → Fin (classes.copies j) → ℂ :=
    fun j q => (classes.enum_phase j q).choose
  have hζ_ne : ∀ j q, ζFn j q ≠ 0 := fun j q => (classes.enum_phase j q).choose_spec.1
  have hζ_mpv : ∀ j q (N : ℕ) (σ : Fin N → Fin d),
      mpv (blocks (classes.enum j q)) σ = (ζFn j q) ^ N * mpv (blocks (classes.repr j)) σ :=
    fun j q N σ => (classes.enum_phase j q).choose_spec.2 N σ
  let sectors : SectorWeightData classes.g := {
    copies := classes.copies
    copies_pos := classes.copies_pos
    weight := fun j q => ζFn j q * μ (classes.enum j q)
    weight_ne_zero := fun j q => mul_ne_zero (hζ_ne j q) (hμne (classes.enum j q))
  }
  let P : SectorDecomposition d := {
    basisCount := classes.g
    basisDim := fun j => dim (classes.repr j)
    basis := fun j => blocks (classes.repr j)
    sectors := sectors
  }
  have hSame : SameMPV₂ P.toTensor (toTensorFromBlocks (d := d) (μ := μ) blocks) := by
    intro N σ
    calc mpv P.toTensor σ
        = ∑ j : Fin P.basisCount,
            ∑ q : Fin (P.copies j), (P.weight j q) ^ N * mpv (P.basis j) σ :=
            P.mpv_toTensor_eq_sum_sectors σ
      _ = ∑ j : Fin classes.g,
            ∑ q : Fin (classes.copies j),
              (ζFn j q * μ (classes.enum j q)) ^ N *
                mpv (blocks (classes.repr j)) σ := rfl
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
  have hBNT : HasBNTSectorData (d := d) P := by
    have hLI : ∃ N0 : ℕ, ∀ N > N0,
        LinearIndependent ℂ
          (fun j : Fin classes.g => mpvState (d := d) (blocks (classes.repr j)) N) :=
      exists_eventually_linearIndependent_of_tp_primitive_irr_blocks_of_blocksNotGaugePhaseEquiv
        (fun j : Fin classes.g => blocks (classes.repr j))
        (fun j => hTP (classes.repr j))
        (fun j => hIrr (classes.repr j))
        (fun j => hPrim (classes.repr j))
        classes.blocks_not_equiv
    simpa [P] using hLI
  refine ⟨P, hSame, hBNT, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact NeZero.pos (dim (classes.repr j))
  · intro j
    exact hInj (classes.repr j)
  · intro j
    exact hTP (classes.repr j)
  · intro j
    exact overlap_tendsto_one_of_peripheralPrimitive_of_irreducible
      (blocks (classes.repr j)) (hIrr (classes.repr j)) (hTP (classes.repr j))
      (hPrim (classes.repr j))
  · intro i j hij
    exact cross_overlap_tendsto_zero_of_separated_normalCFBNT_data
      (fun j : Fin classes.g => blocks (classes.repr j))
      (HasIrreducibleBlocks.ofForall (fun j => hIrr (classes.repr j)))
      (IsLeftCanonicalBlockFamily.ofForall (fun j => hTP (classes.repr j)))
      classes.blocks_not_equiv i j hij

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
