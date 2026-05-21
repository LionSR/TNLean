/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.SectorBNT.Api
import TNLean.MPS.FundamentalTheorem.SectorBNT.WeakExistential
import TNLean.MPS.Overlap.Basic
import TNLean.MPS.Overlap.CastDecay
import TNLean.Analysis.ConvergenceHelpers

/-!
# Single-block gauge-phase matching for BNT canonical forms

This module produces the **gauge-phase match** for a single BNT basis block of
one BNT canonical form against some block of the other, under `SameMPV₂` of
the assembled tensors.

The module has three layers:

1. **Lemma 1** — interpret `SameMPV₂` as a special case of
   `EventuallyNonzeroProportionalMPV₂` with constant scalar `1`.
2. **Lemma 2** — specialise the Phase 3 weak existential
   (`exists_nondecaying_overlap_pair_of_eventuallyProportional`,
   `SectorBNT/WeakExistential.lean`) to the `SameMPV₂` hypothesis: some pair
   of basis blocks has a non-decaying cross-overlap.
3. **Lemma 3** — the **block matching** statement: for any sector
   `j₀ : Fin P.basisCount`, the structural per-block unit-modulus witness
   gives a block `k₀` of `Q` of equal bond dimension, gauge-phase
   equivalent (cast-left shape) to the `P`-block at `j₀`,
   and with a non-decaying cross-overlap.

## Hypothesis structure

The block matching at a **user-supplied** sector index
`j₀ : Fin P.basisCount` (with an externally provided unit-modulus
witness) does not single out any particular sector internally: the
`IsBNTCanonicalForm` fields are deliberately invariant under
relabelling of sectors.  Following the CPSV16 §II.C line-246
normalization convention, `IsBNTCanonicalForm` carries the modulus-bound
field

* `weight_norm_le_one : ∀ j q, ‖weight j q‖ ≤ 1`  — CPSV16 line 246, the
  modulus bound.  Lemma 3 below feeds this in via `hP.weight_norm_le_one`
  and `hQ.weight_norm_le_one`.

The per-block unit-modulus convention `∀ j, ∃ q, ‖weight j q‖ = 1` is
**not** a structural field — CPSV16 line 246 is **global** (the
unit-modulus copy can sit in any sector), while CPSV21 Section IV.A,
Definition 4.2 (lines 1846–1850), defines the BNT basis, and the display at
lines 1864–1884 normalizes the spectral radius of the *basis* tensors, not
the copy
coefficients.  The matching theorem below therefore takes
the unit-modulus sector as an **explicit parameter** `j₀ : Fin P.basisCount`
together with a per-sector unit-modulus existential
`hUnitP_at_j₀ : ∃ q, ‖P.weight j₀ q‖ = 1`.  The non-decay of the matched
sector's coefficient is then derived inside the proof via
`IsBNTCanonicalForm.coeff_not_tendsto_zero_at_block`
(`SectorBNT/Api.lean`), now also taking the same per-block hypothesis.

These hypotheses are weaker than the older already-separated canonical-form
hypotheses, which combined strict weight-modulus ordering with a single
per-sector spectral-level weight. They are also weaker than the optional
`HasEqualModulusWeightLayer` layer of `SectorBNT/EqualModulus.lean`, which would
imply both bounds via the `spectral_level_dom_norm_one` +
`spectral_level_antitone` + `phase_weight` factorisation.

## Output for Phase 4b-iii

The matched gauge-phase witnesses produced here will be consumed in Phase 4b-iii
(matched-sector subtraction) together with `SectorBNT/DropSector.lean`
(Phase 4a) and `SectorBNT/NewtonGirard.lean` (Phase 4b-i) to drive the
strong-induction step of the CPSV16 equal-MPV corollary argument.

## References

* CPSV16: Cirac–Pérez-García–Schuch–Verstraete, *Matrix Product Density
  Operators: Renormalization Fixed Points and Boundary Theories*,
  Ann. Phys. **378**, 100 (2017); arXiv:1606.00608.  Source-line tags:
  217–246 (global modulus normalization; dominant-norm-1 weight assumption),
  234–246 (the BNT basis block is selected by normality + modulus-1 dominant
  weight), 264–279 (gauge-phase grouping rule), 287–301 (raw two-layer BNT
  display), 1080–1091 (overlap dichotomy), 1172–1188 (equal-MPV corollary proof:
  BNT basis block projection forces non-decay; multiplicity recovery via
  power-sum coefficient comparison).
* CPSV21: Cirac–Pérez-García–Schuch–Verstraete,
  *Matrix product states and projected entangled pair states*, Rev. Mod.
  Phys. **93**, 045003 (2021); arXiv:2011.12127.  Definition 4.2
  (lines 1846–1850), Proposition 4.3 (lines 1852–1859), the two-layer
  display (lines 1864–1884), Theorem 4.4 (lines 1891–1894), and
  Corollary 4.5 (lines 1896–1900).

## Tags

matrix product states, fundamental theorem, BNT, BNT basis block,
gauge-phase equivalence, non-decaying overlap, BNT canonical
form
-/

open scoped Matrix BigOperators
open Filter Topology

namespace MPSTensor

variable {d : ℕ}

/-! ### Lemma 1: `SameMPV₂` as a special case of eventual nonzero proportionality

`SameMPV₂` is the equal-MPV hypothesis.  By taking the proportionality scalar
to be the constant `1`, it is a degenerate special case of
`EventuallyNonzeroProportionalMPV₂` (per-`N` nonzero scalar with
eventual scope).  The conversion is a direct `Filter.Eventually` argument.

Paper anchor: CPSV16 equal-MPV corollary, lines 1172–1192, instantiates
`thm1` with equal MPV; the proportionality scalar is `1`.
-/
theorem SameMPV₂Pos.toEventuallyNonzeroProportionalMPV₂
    {d D₁ D₂ : ℕ} {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    (h : SameMPV₂Pos A B) :
    EventuallyNonzeroProportionalMPV₂ A B := by
  refine Filter.eventually_atTop.mpr ⟨1, fun N hN => ?_⟩
  refine ⟨1, one_ne_zero, fun σ => ?_⟩
  simpa using h N hN σ

theorem SameMPV₂.toEventuallyNonzeroProportionalMPV₂
    {d D₁ D₂ : ℕ} {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    (h : SameMPV₂ A B) :
    EventuallyNonzeroProportionalMPV₂ A B :=
  h.toSameMPV₂Pos.toEventuallyNonzeroProportionalMPV₂

/-! ### Lemma 2: weak non-decay existential for `SameMPV₂`

The Phase 3 weak existential
(`exists_nondecaying_overlap_pair_of_eventuallyProportional`,
`SectorBNT/WeakExistential.lean`) immediately specialises to the
`SameMPV₂` hypothesis via Lemma 1.

Paper anchor: CPSV16 lines 1121–1132 (Lem1, combined-family eventual LI),
applied along the contrapositive route of the CPSV16 equal-MPV corollary,
lines 1172–1192.
-/
theorem exists_nondecaying_overlap_pair_of_sameMPVPos
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hQ_pos : 0 < Q.basisCount)
    (hEqual : SameMPV₂Pos P.toTensor Q.toTensor) :
    ∃ j : Fin P.basisCount, ∃ k : Fin Q.basisCount,
      ¬ Tendsto (fun N => mpvOverlap (d := d) (P.basis j) (Q.basis k) N)
          atTop (𝓝 0) :=
  exists_nondecaying_overlap_pair_of_eventuallyProportional
    (P := P) (Q := Q) hP hQ hQ_pos hEqual.toEventuallyNonzeroProportionalMPV₂

theorem exists_nondecaying_overlap_pair_of_sameMPV
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hQ_pos : 0 < Q.basisCount)
    (hEqual : SameMPV₂ P.toTensor Q.toTensor) :
    ∃ j : Fin P.basisCount, ∃ k : Fin Q.basisCount,
      ¬ Tendsto (fun N => mpvOverlap (d := d) (P.basis j) (Q.basis k) N)
          atTop (𝓝 0) :=
  exists_nondecaying_overlap_pair_of_sameMPVPos
    (P := P) (Q := Q) hP hQ hQ_pos hEqual.toSameMPV₂Pos

/-! ### Lemma 3: block matching at a user-supplied index `j₀`

The main result of Phase 4b-ii: under `SameMPV₂` plus a unit-modulus
witness `∃ q, ‖P.weight j₀ q‖ = 1` at a user-supplied sector index
`j₀ : Fin P.basisCount`, the block `P.basis j₀` of `P` has a `Q`-side
match `Q.basis k₀` of equal bond dimension, gauge-phase equivalent in
the cast-left shape, and with a non-decaying cross-overlap.

The proof is a direct read of the CPSV16 Appendix MPV proof, lines 1172–1188,
unit-block projection: assume by contradiction that **all** cross-overlaps
`mpvOverlap (P.basis j₀) (Q.basis k)` decay; project the `SameMPV₂`
identity onto `mpvState (P.basis j₀)` (taking the bilinear overlap with
the `j₀`-th `P`-block).

* The LHS = `∑_j P.coeff N j · overlap(P.basis j, P.basis j₀) N`
  is `P.coeff N j₀ + (small)` thanks to:
  – `basis_normalized_self_overlap` at `j = j₀` (`overlap → 1`);
  – `cross_overlap_basis_tendsto_zero` at `j ≠ j₀` (`overlap → 0`);
  – the structural field `weight_norm_le_one` of `IsBNTCanonicalForm`
    (CPSV16 §II.C line 246) feeds into
    `norm_coeff_le_copies_of_norm_weight_le_one` (`Api.lean`) and gives
    the coefficient bound `‖P.coeff N j‖ ≤ P.copies j`.

* The RHS = `∑_k Q.coeff N k · overlap(Q.basis k, P.basis j₀) N`
  vanishes asymptotically, again by coefficient boundedness from
  `hQ.weight_norm_le_one` and the contrapositive assumption that all
  `k`-overlaps decay.

* `SameMPV₂` makes both sides equal, so `P.coeff N j₀` tends to `0`,
  contradicting `IsBNTCanonicalForm.coeff_not_tendsto_zero_at_block`
  applied to the user-supplied unit-modulus witness `hUnit` via the
  Cesàro non-decay lemma in `SectorBNT/CesaroNonDecay.lean`.

The extracted `k₀` then satisfies (i) equal bond dimensions, via the
contrapositive of
`mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP`, and (ii) cast-left
gauge-phase equivalence, via the contrapositive of
`mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left_of_irreducible_TP`.

Hypothesis disclosure: the modulus bound `weight_norm_le_one` is a
structural field of `IsBNTCanonicalForm` (CPSV16 §II.C line 246) and
need not be supplied externally.  The unit-modulus witness at the
chosen sector `j₀` is supplied externally because CPSV16 line 246 is
**global** (the unit-modulus copy can sit in any sector); the
structural field `weight_unit_exists` does not pin it to a specific
sector.  Issue #1725 Phase A retired the auxiliary dominant-block
structural field that previously fixed `j₀ = 0` and discharged the
unit-modulus witness implicitly. -/
theorem exists_block_match_of_sameMPVPos
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (j₀ : Fin P.basisCount)
    (hUnitP_at_j₀ : ∃ q : Fin (P.copies j₀), ‖P.weight j₀ q‖ = 1)
    (hP_pos : 0 < P.basisCount) (hQ_pos : 0 < Q.basisCount)
    (hEqual : SameMPV₂Pos P.toTensor Q.toTensor) :
    ∃ k₀ : Fin Q.basisCount,
      ∃ h : P.basisDim j₀ = Q.basisDim k₀,
        GaugePhaseEquiv
            (cast (congr_arg (MPSTensor d) h) (P.basis j₀))
            (Q.basis k₀) ∧
        ¬ Tendsto (fun N : ℕ =>
            mpvOverlap (d := d) (P.basis j₀) (Q.basis k₀) N)
          atTop (𝓝 0) := by
  classical
  -- The Q-side positivity hypothesis is part of the user-facing signature
  -- (witnessing that the existential `∃ k₀ : Fin Q.basisCount` is non-vacuous);
  -- the contradiction route below also forces it, so it is recorded but not
  -- used directly in the proof.
  have _hP_pos_used : 0 < P.basisCount := hP_pos
  have _hQ_pos_used : 0 < Q.basisCount := hQ_pos
  -- Derive the CPSV16 §II.C line-246 modulus bounds from the strengthened
  -- `IsBNTCanonicalForm` predicate.  The structural fields replace what
  -- used to be supplied as explicit parameters at the call site.
  have hP_weight_le := hP.weight_norm_le_one
  have hQ_weight_le := hQ.weight_norm_le_one
  -- Block coefficient non-decay derived from the externally supplied
  -- per-block unit-modulus witness via the Cesàro non-decay lemma.
  have hP_dom_coeff_not_tendsto_zero :
      ¬ Tendsto (fun N : ℕ => P.coeff N j₀) atTop (𝓝 0) :=
    hP.coeff_not_tendsto_zero_at_block j₀ hUnitP_at_j₀
  -- Step 1: extract some k₀ with non-decaying overlap to `P.basis j₀`.
  have hExists_k :
      ∃ k₀ : Fin Q.basisCount,
        ¬ Tendsto (fun N : ℕ =>
            mpvOverlap (d := d) (P.basis j₀) (Q.basis k₀) N) atTop (𝓝 0) := by
    by_contra hAll
    push Not at hAll
    -- `hAll : ∀ k, Tendsto (overlap (P.basis j₀) (Q.basis k)) → 0`.
    -- From `SameMPV₂`, both expansions of `mpv ·.toTensor σ` agree.  Take the
    -- overlap with `P.basis j₀` to obtain the column-`j₀` identity:
    --   ∑_j P.coeff N j · overlap(P.basis j, P.basis j₀) N
    --     = ∑_k Q.coeff N k · overlap(Q.basis k, P.basis j₀) N.
    -- Under `SameMPV₂Pos`, the per-`N` overlap identity is established only
    -- for `N ≥ 1`.  This eventual identity suffices because every consumer
    -- below operates on `atTop` limits.
    have hOverlap_identity :
        ∀ᶠ N : ℕ in atTop,
          (∑ j : Fin P.basisCount, P.coeff N j *
              mpvOverlap (d := d) (P.basis j) (P.basis j₀) N)
            = ∑ k : Fin Q.basisCount, Q.coeff N k *
                mpvOverlap (d := d) (Q.basis k) (P.basis j₀) N := by
      refine Filter.eventually_atTop.mpr ⟨1, fun N hN => ?_⟩
      have hLHS :=
        mpvOverlap_eq_sum_of_decomp_left (d := d) (g := P.basisCount)
          (dim := P.basisDim) (A_total := P.toTensor) (A := P.basis)
          (N := N) (c := fun j => P.coeff N j)
          (hdecomp := fun σ => P.mpv_toTensor_eq_sum_coeff (N := N) σ)
          (B := P.basis j₀)
      have hRHS :=
        mpvOverlap_eq_sum_of_decomp_left (d := d) (g := Q.basisCount)
          (dim := Q.basisDim) (A_total := Q.toTensor) (A := Q.basis)
          (N := N) (c := fun k => Q.coeff N k)
          (hdecomp := fun σ => Q.mpv_toTensor_eq_sum_coeff (N := N) σ)
          (B := P.basis j₀)
      have hPQ :
          mpvOverlap (d := d) P.toTensor (P.basis j₀) N
            = mpvOverlap (d := d) Q.toTensor (P.basis j₀) N := by
        simp only [mpvOverlap]
        refine Finset.sum_congr rfl ?_
        intro σ _
        rw [hEqual N hN σ]
      exact (hLHS.symm.trans hPQ).trans hRHS
    -- Step 2: LHS tail (j ≠ j₀) tends to 0 because each summand is
    -- `bounded · (overlap → 0)`.
    have hP_cross :
        ∀ j : Fin P.basisCount, j ≠ j₀ →
          Tendsto (fun N : ℕ =>
              P.coeff N j * mpvOverlap (d := d) (P.basis j) (P.basis j₀) N)
            atTop (𝓝 0) := by
      intro j hj
      have hOverlap :
          Tendsto (fun N : ℕ =>
              mpvOverlap (d := d) (P.basis j) (P.basis j₀) N) atTop (𝓝 0) :=
        hP.cross_overlap_basis_tendsto_zero hj
      -- bounded `P.coeff N j` × tending-to-zero overlap.
      have hBound :
          Tendsto (fun N : ℕ =>
              (P.copies j : ℝ) *
              ‖mpvOverlap (d := d) (P.basis j) (P.basis j₀) N‖)
            atTop (𝓝 0) := by
        have := hOverlap.norm.const_mul ((P.copies j : ℝ))
        simpa using this
      refine squeeze_zero_norm (fun N => ?_) hBound
      have hC :=
        P.norm_coeff_le_copies_of_norm_weight_le_one (N := N) (j := j)
          (hWeightLe := hP_weight_le j)
      calc
        ‖P.coeff N j * mpvOverlap (d := d) (P.basis j) (P.basis j₀) N‖
            = ‖P.coeff N j‖ *
              ‖mpvOverlap (d := d) (P.basis j) (P.basis j₀) N‖ := norm_mul _ _
        _ ≤ (P.copies j : ℝ) *
              ‖mpvOverlap (d := d) (P.basis j) (P.basis j₀) N‖ :=
            mul_le_mul_of_nonneg_right hC (norm_nonneg _)
    have hP_tail_tendsto_zero :
        Tendsto (fun N : ℕ =>
            ∑ j ∈ (Finset.univ : Finset (Fin P.basisCount)).erase j₀,
              P.coeff N j *
                mpvOverlap (d := d) (P.basis j) (P.basis j₀) N)
          atTop (𝓝 0) := by
      have := tendsto_finset_sum
        ((Finset.univ : Finset (Fin P.basisCount)).erase j₀)
        (fun (j : Fin P.basisCount) hj =>
          hP_cross j (Finset.ne_of_mem_erase hj))
      simpa using this
    -- Step 3: the diagonal `P.coeff N j₀ · (self_overlap N - 1)` tends to 0
    -- (bounded × tendsto 0).
    have hP_self_minus_one :
        Tendsto (fun N : ℕ =>
            mpvOverlap (d := d) (P.basis j₀) (P.basis j₀) N - 1)
          atTop (𝓝 0) := by
      have := (hP.basis_normalized_self_overlap j₀).sub_const (1 : ℂ)
      simpa using this
    have hP_diag_minus_coeff :
        Tendsto (fun N : ℕ =>
            P.coeff N j₀ *
              (mpvOverlap (d := d) (P.basis j₀) (P.basis j₀) N - 1))
          atTop (𝓝 0) := by
      have hBound :
          Tendsto (fun N : ℕ =>
              (P.copies j₀ : ℝ) *
              ‖mpvOverlap (d := d) (P.basis j₀) (P.basis j₀) N - 1‖)
            atTop (𝓝 0) := by
        have := hP_self_minus_one.norm.const_mul ((P.copies j₀ : ℝ))
        simpa using this
      refine squeeze_zero_norm (fun N => ?_) hBound
      have hC :=
        P.norm_coeff_le_copies_of_norm_weight_le_one (N := N) (j := j₀)
          (hWeightLe := hP_weight_le j₀)
      calc
        ‖P.coeff N j₀ *
            (mpvOverlap (d := d) (P.basis j₀) (P.basis j₀) N - 1)‖
            = ‖P.coeff N j₀‖ *
              ‖mpvOverlap (d := d) (P.basis j₀) (P.basis j₀) N - 1‖ :=
            norm_mul _ _
        _ ≤ (P.copies j₀ : ℝ) *
              ‖mpvOverlap (d := d) (P.basis j₀) (P.basis j₀) N - 1‖ :=
            mul_le_mul_of_nonneg_right hC (norm_nonneg _)
    -- Step 4: assemble LHS - P.coeff N j₀ → 0.
    -- Algebraic identity:
    --   ∑_j P.coeff N j · o(j,j₀) - P.coeff N j₀
    --     = P.coeff N j₀ · (o(j₀,j₀) - 1) +
    --       ∑_{j ≠ j₀} P.coeff N j · o(j,j₀).
    have hLHS_minus_coeff :
        Tendsto (fun N : ℕ =>
            (∑ j : Fin P.basisCount, P.coeff N j *
                mpvOverlap (d := d) (P.basis j) (P.basis j₀) N)
              - P.coeff N j₀)
          atTop (𝓝 0) := by
      have hCombined :
          Tendsto (fun N : ℕ =>
              P.coeff N j₀ *
                (mpvOverlap (d := d) (P.basis j₀) (P.basis j₀) N - 1)
              + ∑ j ∈ (Finset.univ : Finset (Fin P.basisCount)).erase j₀,
                  P.coeff N j *
                    mpvOverlap (d := d) (P.basis j) (P.basis j₀) N)
            atTop (𝓝 0) := by
        have h := hP_diag_minus_coeff.add hP_tail_tendsto_zero
        simpa using h
      refine hCombined.congr ?_
      intro N
      -- algebraic rewrite
      have hSplit :
          (∑ j : Fin P.basisCount, P.coeff N j *
              mpvOverlap (d := d) (P.basis j) (P.basis j₀) N)
            = P.coeff N j₀ *
                mpvOverlap (d := d) (P.basis j₀) (P.basis j₀) N
              + ∑ j ∈ (Finset.univ : Finset (Fin P.basisCount)).erase j₀,
                  P.coeff N j *
                    mpvOverlap (d := d) (P.basis j) (P.basis j₀) N := by
        rw [← Finset.add_sum_erase
          (Finset.univ : Finset (Fin P.basisCount))
          (fun j => P.coeff N j *
            mpvOverlap (d := d) (P.basis j) (P.basis j₀) N)
          (Finset.mem_univ j₀)]
      have hRw :
          P.coeff N j₀ *
              mpvOverlap (d := d) (P.basis j₀) (P.basis j₀) N
            = P.coeff N j₀ *
                (mpvOverlap (d := d) (P.basis j₀) (P.basis j₀) N - 1)
              + P.coeff N j₀ := by ring
      rw [hSplit, hRw]; ring
    -- Step 5: RHS → 0 by `hAll` (all overlaps decay) + Q.coeff boundedness.
    have hQ_term_tendsto_zero :
        ∀ k : Fin Q.basisCount,
          Tendsto (fun N : ℕ =>
              Q.coeff N k * mpvOverlap (d := d) (Q.basis k) (P.basis j₀) N)
            atTop (𝓝 0) := by
      intro k
      -- We have decay for `mpvOverlap (P.basis j₀) (Q.basis k)`; swap factors
      -- via conjugate symmetry.
      have hOverlap_swap :
          Tendsto (fun N : ℕ =>
              mpvOverlap (d := d) (Q.basis k) (P.basis j₀) N) atTop (𝓝 0) :=
        tendsto_mpvOverlap_zero_swap (d := d) (A := P.basis j₀) (B := Q.basis k)
          (N := id) (hAll k)
      have hBound :
          Tendsto (fun N : ℕ =>
              (Q.copies k : ℝ) *
              ‖mpvOverlap (d := d) (Q.basis k) (P.basis j₀) N‖)
            atTop (𝓝 0) := by
        have := hOverlap_swap.norm.const_mul ((Q.copies k : ℝ))
        simpa using this
      refine squeeze_zero_norm (fun N => ?_) hBound
      have hC :=
        Q.norm_coeff_le_copies_of_norm_weight_le_one (N := N) (j := k)
          (hWeightLe := hQ_weight_le k)
      calc
        ‖Q.coeff N k * mpvOverlap (d := d) (Q.basis k) (P.basis j₀) N‖
            = ‖Q.coeff N k‖ *
              ‖mpvOverlap (d := d) (Q.basis k) (P.basis j₀) N‖ := norm_mul _ _
        _ ≤ (Q.copies k : ℝ) *
              ‖mpvOverlap (d := d) (Q.basis k) (P.basis j₀) N‖ :=
            mul_le_mul_of_nonneg_right hC (norm_nonneg _)
    have hRHS_tendsto_zero :
        Tendsto (fun N : ℕ =>
            ∑ k : Fin Q.basisCount, Q.coeff N k *
              mpvOverlap (d := d) (Q.basis k) (P.basis j₀) N)
          atTop (𝓝 0) := by
      have :=
        tendsto_finset_sum (Finset.univ : Finset (Fin Q.basisCount))
          (fun (k : Fin Q.basisCount) _ => hQ_term_tendsto_zero k)
      simpa using this
    -- Step 6: combine.  LHS = RHS pointwise, RHS → 0, LHS - coeff → 0; hence
    --   coeff = LHS - (LHS - coeff) = RHS - (LHS - coeff) → 0 - 0 = 0.
    have hCoeff_tendsto_zero :
        Tendsto (fun N : ℕ => P.coeff N j₀) atTop (𝓝 0) := by
      have hDiff :
          Tendsto (fun N : ℕ =>
              (∑ k : Fin Q.basisCount, Q.coeff N k *
                  mpvOverlap (d := d) (Q.basis k) (P.basis j₀) N)
                - ((∑ j : Fin P.basisCount, P.coeff N j *
                      mpvOverlap (d := d) (P.basis j) (P.basis j₀) N)
                    - P.coeff N j₀))
            atTop (𝓝 (0 - 0)) :=
        hRHS_tendsto_zero.sub hLHS_minus_coeff
      have hDiff' :
          Tendsto (fun N : ℕ =>
              (∑ k : Fin Q.basisCount, Q.coeff N k *
                  mpvOverlap (d := d) (Q.basis k) (P.basis j₀) N)
                - ((∑ j : Fin P.basisCount, P.coeff N j *
                      mpvOverlap (d := d) (P.basis j) (P.basis j₀) N)
                    - P.coeff N j₀))
            atTop (𝓝 0) := by simpa using hDiff
      refine Filter.Tendsto.congr' ?_ hDiff'
      refine hOverlap_identity.mono ?_
      intro N hId
      -- coeff = RHS - (LHS - coeff)
      linear_combination -hId
    exact hP_dom_coeff_not_tendsto_zero hCoeff_tendsto_zero
  -- Step 7: from the chosen `k₀`, extract dimension equality + gauge phase.
  obtain ⟨k₀, hk₀⟩ := hExists_k
  haveI hj₀dim : NeZero (P.basisDim j₀) := ⟨(hP.basis_dim_pos j₀).ne'⟩
  haveI hk₀dim : NeZero (Q.basisDim k₀) := ⟨(hQ.basis_dim_pos k₀).ne'⟩
  -- Contrapositive of `mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP`:
  -- if overlap does not tend to 0, then dimensions must agree.
  have hDim : P.basisDim j₀ = Q.basisDim k₀ := by
    by_contra hne
    exact hk₀ <|
      mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP
        (P.basis j₀) (Q.basis k₀)
        (hP.basis_irreducible j₀) (hQ.basis_irreducible k₀)
        (hP.basis_left_canonical j₀) (hQ.basis_left_canonical k₀)
        hne
  -- Contrapositive of cast-left non-gauge-phase decay: gauge-phase must hold.
  have hGPE :
      GaugePhaseEquiv
        (cast (congr_arg (MPSTensor d) hDim) (P.basis j₀)) (Q.basis k₀) := by
    by_contra hNot
    exact hk₀ <|
      mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left_of_irreducible_TP
        (hdim := hDim) (A := P.basis j₀) (B := Q.basis k₀)
        (hA_irr := hP.basis_irreducible j₀)
        (hB_irr := hQ.basis_irreducible k₀)
        (hA_norm := hP.basis_left_canonical j₀)
        (hB_norm := hQ.basis_left_canonical k₀)
        (hNot := hNot)
  exact ⟨k₀, hDim, hGPE, hk₀⟩

/-- Reformulation for the all-length `SameMPV₂` form.  Forwards to the
positive-length core via `SameMPV₂.toSameMPV₂Pos`. -/
theorem exists_block_match_of_sameMPV
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (j₀ : Fin P.basisCount)
    (hUnitP_at_j₀ : ∃ q : Fin (P.copies j₀), ‖P.weight j₀ q‖ = 1)
    (hP_pos : 0 < P.basisCount) (hQ_pos : 0 < Q.basisCount)
    (hEqual : SameMPV₂ P.toTensor Q.toTensor) :
    ∃ k₀ : Fin Q.basisCount,
      ∃ h : P.basisDim j₀ = Q.basisDim k₀,
        GaugePhaseEquiv
            (cast (congr_arg (MPSTensor d) h) (P.basis j₀))
            (Q.basis k₀) ∧
        ¬ Tendsto (fun N : ℕ =>
            mpvOverlap (d := d) (P.basis j₀) (Q.basis k₀) N)
          atTop (𝓝 0) :=
  exists_block_match_of_sameMPVPos
    (P := P) (Q := Q) hP hQ j₀ hUnitP_at_j₀ hP_pos hQ_pos hEqual.toSameMPV₂Pos

end MPSTensor
