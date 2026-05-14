/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.PaperBNT.Api
import TNLean.MPS.FundamentalTheorem.PaperBNT.WeakExistential
import TNLean.MPS.Overlap.Basic
import TNLean.MPS.Overlap.CastDecay
import TNLean.Analysis.ConvergenceHelpers

/-!
# Dominant-pair matching on the paper-faithful BNT canonical-form surface

This module is **Phase 4b-ii** of the CPSV16/CPSV21 fundamental-theorem
clean-slate plan (issue #1688).  It produces the **gauge-phase match** for a
single dominant block of one BNT canonical form against some block of the
other, under `SameMPV₂` of the assembled tensors.

The module has three layers:

1. **Lemma 1** — package `SameMPV₂` as a special case of
   `EventuallyNonzeroProportionalMPV₂` with constant scalar `1`.
2. **Lemma 2** — specialise the Phase 3 weak existential
   (`exists_nondecaying_overlap_pair_of_eventuallyProportional`,
   `PaperBNT/WeakExistential.lean`) to the `SameMPV₂` hypothesis: some pair
   of basis blocks has a non-decaying cross-overlap.
3. **Lemma 3** — the **dominant-pair matching** statement: for the dominant
   block of `P` (index `⟨0, hP_pos⟩`), there is a block `k₀` of `Q` of equal
   bond dimension, gauge-phase equivalent (cast-left shape) to the dominant
   `P`-block, and with a non-decaying cross-overlap.

## Hypothesis disclosure (paper-faithful)

The dominant-pair matching at the **fixed** index `⟨0, hP_pos⟩` does not
follow from the core seven-field `IsBNTCanonicalForm` data alone: the core
seven fields are deliberately invariant under relabelling of sectors and do
not single out a dominant sector.  Following the CPSV16 §II.A line-246
normalization convention, `IsBNTCanonicalForm` now carries two additional
structural fields:

* `weight_norm_le_one : ∀ j q, ‖weight j q‖ ≤ 1`  — CPSV16 line 246, the
  modulus bound.  Lemma 3 below feeds this in via `hP.weight_norm_le_one`
  and `hQ.weight_norm_le_one`, replacing the prior explicit `hP_norm /
  hQ_norm` parameters.
* `weight_unit_exists : ∃ j q, ‖weight j q‖ = 1`  — CPSV16 line 246,
  the unit-modulus existential.

The remaining external hypothesis on Lemma 3,
`(hP_dom_coeff_not_tendsto_zero : ¬ Tendsto (P.coeff · ⟨0, hP_pos⟩) atTop (𝓝 0))`,
records that the **dominant sector**'s coefficient does not asymptotically
vanish.  This is the index-0 reading of the existential
`weight_unit_exists`; deriving the index-0 form from the existential would
require relabelling sectors so the unit-modulus copy sits in sector 0
together with a Bohr/Kronecker–Weyl non-decay argument for power-sums of
unit-modulus complex numbers (CPSV16 lines 1181–1188 paper-side; see also
the audit memos `extra_hypotheses_audit_2026-05-14` §Q2 and
`thermodynamic_limit_normalization_audit_2026-05-14` §Q-C).  The general
non-decay result is tracked separately and will replace this explicit
parameter once available.

These hypotheses are weaker than the legacy `IsCanonicalFormBNT` package
(which baked in `mu_strict_anti` + a single per-sector "spectral level"
weight); they are also weaker than the optional `HasEqualModulusWeightLayer`
layer of `PaperBNT/EqualModulus.lean`, which would imply both bounds via the
`spectral_level_dom_norm_one` + `spectral_level_antitone` + `phase_weight`
factorisation.

## Output for Phase 4b-iii

The matched gauge-phase data produced here will be consumed in Phase 4b-iii
(matched-sector subtraction) together with `PaperBNT/DropSector.lean`
(Phase 4a) and `PaperBNT/NewtonGirard.lean` (Phase 4b-i) to drive the
strong-induction step of the CPSV16 `II_cor2` argument.

## References

* CPSV16: Cirac–Pérez-García–Schuch–Verstraete, *Matrix Product Density
  Operators: Renormalization Fixed Points and Boundary Theories*,
  Ann. Phys. **378**, 100 (2017); arXiv:1606.00608.  Source-line tags:
  217–246 (global modulus normalization; dominant-norm-1 weight assumption),
  234–246 (the dominant block is selected by normality + modulus-1 dominant
  weight), 264–279 (gauge-phase grouping rule), 287–301 (raw two-layer BNT
  display), 1080–1091 (overlap dichotomy), 1172–1188 (`II_cor2` proof:
  dominant block projection forces non-decay; multiplicity recovery via
  power-sum coefficient comparison).
* CPSV21: Cirac–Pérez-García–Schuch–Verstraete,
  *Matrix product states and projected entangled pair states*, Rev. Mod.
  Phys. **93**, 045003 (2021); arXiv:2011.12127.  Definition 4.3
  (lines 1846–1884), Theorem 4.5 (lines 1891–1900).

## Tags

matrix product states, fundamental theorem, BNT, dominant block,
gauge-phase equivalence, non-decaying overlap, paper-faithful BNT canonical
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
eventual scope).  The conversion is purely `Filter.Eventually` packaging.

Paper anchor: CPSV16 corollary `II_cor2`, lines 1172–1192, instantiates
`thm1` with equal MPV; the proportionality scalar is `1`.
-/
theorem SameMPV₂.toEventuallyNonzeroProportionalMPV₂
    {d D₁ D₂ : ℕ} {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    (h : SameMPV₂ A B) :
    EventuallyNonzeroProportionalMPV₂ A B :=
  (h.toNonzeroProportionalMPV₂).eventually

/-! ### Lemma 2: weak non-decay existential for `SameMPV₂`

The Phase 3 weak existential
(`exists_nondecaying_overlap_pair_of_eventuallyProportional`,
`PaperBNT/WeakExistential.lean`) immediately specialises to the
`SameMPV₂` hypothesis via Lemma 1.

Paper anchor: CPSV16 lines 1121–1132 (Lem1, combined-family eventual LI),
applied along the contrapositive route of CPSV16 lines 1172–1192
(`II_cor2`).
-/
theorem exists_nondecaying_overlap_pair_of_sameMPV
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hQ_pos : 0 < Q.basisCount)
    (hEqual : SameMPV₂ P.toTensor Q.toTensor) :
    ∃ j : Fin P.basisCount, ∃ k : Fin Q.basisCount,
      ¬ Tendsto (fun N => mpvOverlap (d := d) (P.basis j) (Q.basis k) N)
          atTop (𝓝 0) :=
  exists_nondecaying_overlap_pair_of_eventuallyProportional
    (P := P) (Q := Q) hP hQ hQ_pos hEqual.toEventuallyNonzeroProportionalMPV₂

/-! ### Lemma 3: dominant-pair matching at the fixed index `0`

The main result of Phase 4b-ii: under `SameMPV₂` plus the CPSV16
lines 217–246 normalisation data (and the dominant-coefficient non-decay
hypothesis), the dominant block `P.basis ⟨0, hP_pos⟩` of `P` has a `Q`-side
match `Q.basis k₀` of equal bond dimension, gauge-phase equivalent in the
cast-left shape, and with a non-decaying cross-overlap.

The proof is a direct read of the CPSV16 lines 1172–1188 dominant-block
projection: assume by contradiction that **all** cross-overlaps
`mpvOverlap (P.basis ⟨0, _⟩) (Q.basis k)` decay; project the `SameMPV₂`
identity onto `mpvState (P.basis ⟨0, _⟩)` (taking the bilinear overlap with
the dominant `P`-block).

* The LHS = `∑_j P.coeff N j · overlap(P.basis j, P.basis ⟨0, _⟩) N`
  is `P.coeff N ⟨0, _⟩ + (small)` thanks to:
  – `basis_normalized_self_overlap` at `j = 0` (`overlap → 1`);
  – `cross_overlap_basis_tendsto_zero` at `j ≠ 0` (`overlap → 0`);
  – `norm_coeff_le_copies_of_norm_weight_le_one` (`Api.lean`) gives the
    coefficient bound `‖P.coeff N j‖ ≤ P.copies j` from `hP_norm`.

* The RHS = `∑_k Q.coeff N k · overlap(Q.basis k, P.basis ⟨0, _⟩) N`
  vanishes asymptotically, again by coefficient boundedness from
  `hQ_norm` and the contrapositive assumption that all `k`-overlaps decay.

* `SameMPV₂` makes both sides equal, so `P.coeff N ⟨0, _⟩` tends to `0`,
  contradicting `hP_dom_coeff_not_tendsto_zero`.

The extracted `k₀` then satisfies (i) equal bond dimensions, via the
contrapositive of
`mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP`, and (ii) cast-left
gauge-phase equivalence, via the contrapositive of
`mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left_of_irreducible_TP`.

Hypothesis disclosure: the extra normalisation hypotheses `hP_norm`,
`hQ_norm`, and `hP_dom_coeff_not_tendsto_zero` are NOT part of
`IsBNTCanonicalForm` (the core predicate is deliberately label-invariant).
They are the paper-faithful reading of CPSV16 lines 217–246 and 234–246;
see the module docstring above for the design rationale.
-/
theorem exists_dominant_match_of_sameMPV
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hP_pos : 0 < P.basisCount) (hQ_pos : 0 < Q.basisCount)
    (hEqual : SameMPV₂ P.toTensor Q.toTensor)
    (hP_dom_coeff_not_tendsto_zero :
      ¬ Tendsto (fun N : ℕ => P.coeff N ⟨0, hP_pos⟩) atTop (𝓝 0)) :
    ∃ k₀ : Fin Q.basisCount,
      ∃ h : P.basisDim ⟨0, hP_pos⟩ = Q.basisDim k₀,
        GaugePhaseEquiv
            (cast (congr_arg (MPSTensor d) h) (P.basis ⟨0, hP_pos⟩))
            (Q.basis k₀) ∧
        ¬ Tendsto (fun N : ℕ =>
            mpvOverlap (d := d) (P.basis ⟨0, hP_pos⟩) (Q.basis k₀) N)
          atTop (𝓝 0) := by
  classical
  -- The Q-side positivity hypothesis is part of the user-facing signature
  -- (witnessing that the existential `∃ k₀ : Fin Q.basisCount` is non-vacuous);
  -- the contradiction route below also forces it, so it is recorded but not
  -- used directly in the proof.
  have _hQ_pos_used : 0 < Q.basisCount := hQ_pos
  -- Derive the CPSV16 line-246 modulus bounds from the strengthened
  -- `IsBNTCanonicalForm` predicate; these used to be explicit parameters
  -- `hP_norm / hQ_norm` and have been folded into the structure.
  have hP_norm := hP.weight_norm_le_one
  have hQ_norm := hQ.weight_norm_le_one
  set j₀ : Fin P.basisCount := ⟨0, hP_pos⟩ with hj₀_def
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
    have hOverlap_identity :
        ∀ N : ℕ,
          (∑ j : Fin P.basisCount, P.coeff N j *
              mpvOverlap (d := d) (P.basis j) (P.basis j₀) N)
            = ∑ k : Fin Q.basisCount, Q.coeff N k *
                mpvOverlap (d := d) (Q.basis k) (P.basis j₀) N := by
      intro N
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
        rw [hEqual N σ]
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
          (hWeightLe := hP_norm j)
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
          (hWeightLe := hP_norm j₀)
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
          (hWeightLe := hQ_norm k)
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
      refine hDiff'.congr ?_
      intro N
      have hId := hOverlap_identity N
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

end MPSTensor
