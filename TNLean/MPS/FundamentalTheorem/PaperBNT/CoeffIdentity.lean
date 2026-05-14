/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.PaperBNT.StrongMatch
import TNLean.MPS.CanonicalForm.PhaseCover
import TNLean.PiAlgebra.CanonicalFormSepAux

/-!
# Phase B-γ (paper-faithful) CPSV16 §II.C lines 1187-1188 Corollary substitution

This module is **Phase B-γ** of the CPSV16/CPSV21 fundamental-theorem
clean-slate plan (issue #1725) — the paper-faithful Corollary `II_cor2`
substitution argument.  Given matched gauges from Phase B-α
(`forall_unit_k_exists_j_nondecaying_overlap_of_sameMPV`,
`PaperBNT/StrongMatch.lean`) encoded as the injection
`φ : UnitQ ↪ Fin P.basisCount` from Phase B-β
(`bijective_match_of_sameMPV`, `PaperBNT/StrongMatch.lean`), substitute
the per-pair gauge identity
`mpv (Q.basis k) σ = ζ_k^N · mpv (P.basis (φ k)) σ` into the original
`SameMPV₂` proportionality and project the resulting overlap onto each
`P.basis j₀` to read off the per-block coefficient identity directly,
without recursion or `dropSector`.

## Paper anchor

CPSV16 (arXiv:1606.00608) §II.C lines 1187-1188 (the substitution
argument of the Corollary's proof, after the Step 1 matching has been
established).  Gauge-to-MPV translation: Lemma `equalMPS`, CPSV16 lines
1080-1097.  Unit-modulus closure: CPSV16 §II.A line 246 normalization
combined with the per-block normalized self-overlap (CPSV21 line 1818).

## Scope (Phase B-γ)

The single main result is the matched-pair *asymptotic-difference*
identity plus the non-matched-decay statement; together they
characterize the structure of the matched coefficient sequences
directly, without recursion or `dropSector`.  See the docstring of
`coeff_identity_via_global_gauge` for the precise statement and the
"Scoping note" therein for the relationship to the eventual-exact
form requested by issue #1725 Phase B-γ.

## File split (PR #1729 follow-up)

This file was extracted from `PaperBNT/StrongMatch.lean` to keep that
file under the 1000-line module limit.  Phase B-α
(`forall_unit_k_exists_j_nondecaying_overlap_of_sameMPV`) and Phase B-β
(`bijective_match_of_sameMPV`) remain in `StrongMatch.lean`; this file
contains only Phase B-γ content.

No `sorry`, no `axiom`, no `unsafe`.
-/

open scoped Matrix BigOperators
open Filter Topology

namespace MPSTensor

variable {d : ℕ}

/-! ### Phase B-γ: CPSV16 §II.C lines 1187-1188 Corollary substitution

This section implements the **Corollary `II_cor2` substitution argument**
(CPSV16 §II.C lines 1187-1188): given matched gauges from Phase B-α
(`forall_unit_k_exists_j_nondecaying_overlap_of_sameMPV`), encoded as
the injection `φ : UnitQ ↪ Fin P.basisCount` from Phase B-β
(`bijective_match_of_sameMPV`), substitute the per-pair gauge identity
`mpv (Q.basis k) σ = ζ_k^N · mpv (P.basis (φ k)) σ` into the
`SameMPV₂` proportionality and read off the per-block coefficient
identity by projecting the overlap onto each `P.basis j₀`.

## Honest scoping (per task brief, §"Honest scoping")

The user-requested target form for the matched-pair clause is
*eventual exact equality*:

  `∀ k : UnitQ, ∃ ζ, ‖ζ‖ = 1 ∧ ∃ N₀, ∀ N > N₀,`
  `    P.coeff N (φ k) = ζ^N · Q.coeff N k.val`.

Deriving eventual exact equality from the partial-bijection data (UnitQ
only, with non-unit Q-blocks unconstrained) requires either a full
bijection or substantial new analysis (combined LI on a partial union
is the very obstacle that #1722 flagged).  We deliver the
**asymptotic-difference** form

  `Tendsto (fun N => P.coeff N (φ k) - ζ^N · Q.coeff N k.val) atTop (𝓝 0)`,

which is the natural output of the overlap-projection argument and is
equivalent to the eventual exact form via the multiset-rigidity step
(Newton–Girard, `PaperBNT/NewtonGirard.lean`) when both sides are power
sums over closed-unit-disk weights.  The non-matched-decay clause is
delivered in full.

Paper anchor: CPSV16 §II.C lines 1187-1188 (arXiv:1606.00608); the
substitution `Y = ⊕_j (𝟙_{r_j} ⊗ Y_j)` is a *single* global gauge
followed by a *single* coefficient comparison.  We avoid `dropSector`
entirely (Phase 4c drift, per
`/tmp/phase_4c_drift_audit_2026-05-14.md`). -/

/-- **Helper: gauge-phase data ⇒ MPV-level scalar power identity with `‖ζ‖ = 1`.**

Given a matched bond-dimension equality `h : P.basisDim j = Q.basisDim k`
and a cast-left gauge-phase equivalence
`GaugePhaseEquiv (cast h (P.basis j)) (Q.basis k)` between BNT basis
blocks, extract a gauge phase `ζ : ℂ` with `‖ζ‖ = 1` and the MPV-level
scalar power identity

  `mpv (Q.basis k) σ = ζ^N · mpv (P.basis j) σ` for every `N, σ`.

The proof combines `MPVBlockPhaseEquiv.of_gaugePhaseEquiv_cast`
(which packages the cast-aware gauge-to-MPV translation) with the
unit-modulus closure `norm_eq_one_of_selfOverlap_scale`
(`MPS/SharedInfra/GaugePhase.lean`), fed by the normalized self-overlaps
of the BNT basis blocks (`basis_normalized_self_overlap` field of
`IsBNTCanonicalForm`).

Paper anchor: CPSV16 §II.A Lemma `equalMPS` (lines 1080–1097) for the
gauge-to-MPV translation, and CPSV16 §II.A line-246 normalization
(`weight_norm_le_one`) combined with the per-block normalized
self-overlap (CPSV21 line 1818) for the unit-modulus closure on `ζ`. -/
private lemma extract_unit_gauge_phase_mpv
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    {j : Fin P.basisCount} {k : Fin Q.basisCount}
    (h : P.basisDim j = Q.basisDim k)
    (hGPE : GaugePhaseEquiv
        (cast (congr_arg (MPSTensor d) h) (P.basis j)) (Q.basis k)) :
    ∃ ζ : ℂ, ‖ζ‖ = 1 ∧
      ∀ (N : ℕ) (σ : Fin N → Fin d),
        mpv (Q.basis k) σ = ζ ^ N * mpv (P.basis j) σ := by
  classical
  obtain ⟨ζ, hζne, hmpv⟩ :=
    MPVBlockPhaseEquiv.of_gaugePhaseEquiv_cast (P.basis j) (Q.basis k) h hGPE
  refine ⟨ζ, ?_, hmpv⟩
  -- ‖ζ‖ = 1 via `norm_eq_one_of_selfOverlap_scale`, fed by both
  -- self-overlaps tending to 1 and the scale identity from `hmpv`.
  have hAA : Tendsto (fun N => ‖mpvOverlap (d := d) (P.basis j) (P.basis j) N‖)
      atTop (𝓝 (1 : ℝ)) := by
    have h1 := (hP.basis_normalized_self_overlap j).norm
    simpa using h1
  have hBB : Tendsto (fun N => ‖mpvOverlap (d := d) (Q.basis k) (Q.basis k) N‖)
      atTop (𝓝 (1 : ℝ)) := by
    have h1 := (hQ.basis_normalized_self_overlap k).norm
    simpa using h1
  have hScale :=
    mpvOverlap_self_scale_of_mpv_eq_pow_mul (A := P.basis j) (B := Q.basis k)
      (ζ := ζ) hmpv
  exact norm_eq_one_of_selfOverlap_scale (ζ := ζ) hAA hBB hScale

/-- **Helper: gauge substitution propagates to `mpvOverlap`.**

From the MPV-level scalar power identity
`mpv (Q.basis k) σ = ζ^N · mpv (P.basis j) σ`, the overlap with any
third tensor `X` satisfies
`mpvOverlap (Q.basis k) X N = ζ^N · mpvOverlap (P.basis j) X N`.

This is the elementary linearity of `mpvOverlap` in its first argument,
specialised to the gauge-substitution shape used by the Phase B-γ
projection argument. -/
private lemma mpvOverlap_subst_via_mpv_pow
    {D₁ D₂ D₃ : ℕ} {ζ : ℂ}
    {A : MPSTensor d D₁} {B : MPSTensor d D₂} (X : MPSTensor d D₃)
    (hmpv : ∀ (N : ℕ) (σ : Fin N → Fin d), mpv B σ = ζ ^ N * mpv A σ)
    (N : ℕ) :
    mpvOverlap (d := d) B X N = ζ ^ N * mpvOverlap (d := d) A X N := by
  classical
  simp only [mpvOverlap]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro σ _
  rw [hmpv N σ]
  ring

/-- **CPSV16 §II.C lines 1187-1188 Corollary substitution (paper-faithful
Phase B-γ).**

Given matched gauges from Phase B-α
(`forall_unit_k_exists_j_nondecaying_overlap_of_sameMPV`) encoded as the
injection `φ : UnitQ ↪ Fin P.basisCount` from Phase B-β
(`bijective_match_of_sameMPV`), the **per-block coefficient identity**
holds in the following two-part shape:

* **Matched pair (`k : UnitQ`, `j = φ k`):** there is a unit-modulus
  gauge phase `ζ_k : ℂ` with `‖ζ_k‖ = 1` for which the **asymptotic
  difference** `P.coeff N (φ k) - ζ_k^N · Q.coeff N k.val` tends to `0`.
* **Non-matched (`j ∉ range(φ)`):** the coefficient `P.coeff N j` itself
  tends to `0`.

Together these characterize the structure of the matched coefficient
sequences directly, without recursion or `dropSector`.

## Scoping note (honest scoping)

The user-requested literal form of the matched-pair clause is
*eventual exact* equality `P.coeff N (φ k) = ζ_k^N · Q.coeff N k.val`
for all sufficiently large `N`.  Deriving eventual exact equality from
the partial-bijection data (UnitQ ⊂ Fin Q.basisCount only, with non-unit
Q-blocks unconstrained by the matching) requires combined LI on
`P.basis ⊔ {Q.basis k : k ∉ UnitQ}`, the precise partial-union LI that
issue #1722 flagged as not naturally derivable.  We deliver the
**asymptotic-difference** form `Tendsto (· - ·) atTop (𝓝 0)`, which is
the natural output of the overlap-projection argument and which the
multiset-rigidity step (`PaperBNT/NewtonGirard.lean`,
`Multiset.eq_of_power_sum_eq`) upgrades to multiset equality of weights
when consumed downstream.

## Proof outline

For each `j₀ : Fin P.basisCount`, project the SameMPV₂ identity onto
the overlap with `P.basis j₀`:

  `∑_j P.coeff N j · ⟨P.basis j | P.basis j₀⟩_N`
    `= ∑_k Q.coeff N k · ⟨Q.basis k | P.basis j₀⟩_N`.

* **LHS analysis** (mirrors `DominantMatch.exists_dominant_match_of_sameMPV`
  Steps 2–4): `LHS - P.coeff N j₀ → 0`.  The off-diagonal terms
  (`j ≠ j₀`) decay by `cross_overlap_basis_tendsto_zero` (CPSV16 lines
  1080–1091) and the diagonal term `coeff · (self_overlap - 1)` decays
  by `basis_normalized_self_overlap` (CPSV21 line 1818).
* **RHS analysis**: split `k : Fin Q.basisCount` into the unit-modulus
  subset `UnitQ` and its complement.
  * For `k ∈ UnitQ`: substitute via
    `mpv (Q.basis k) σ = ζ_k^N · mpv (P.basis (φ k)) σ`
    (CPSV16 line 1186, gauge-phase equivalence).  The resulting term
    `Q.coeff N k · ζ_k^N · ⟨P.basis (φ k) | P.basis j₀⟩_N` tends to
    `Q.coeff N k · ζ_k^N` when `j₀ = φ k` (diagonal, self → 1) and to
    `0` otherwise (off-diagonal, cross-decay).
  * For `k ∉ UnitQ`: `Q.coeff N k → 0` by
    `coeff_tendsto_zero_of_all_weights_subnorm` (CPSV16 line 246 +
    line 1244 dichotomy, `PaperBNT/Api.lean`); combined with the
    `leftCanonical_mpvOverlap_bound` uniform bound on `mpvOverlap`
    (left-canonical, CPSV21 lines 1815–1837), the contribution
    `Q.coeff N k · mpvOverlap (Q.basis k) (P.basis j₀) N` decays to `0`.
* **Combine**: `LHS = RHS` pointwise (by `SameMPV₂`); the analyses then
  give
    `P.coeff N j₀ - ∑_{k ∈ UnitQ, φ k = j₀} ζ_k^N · Q.coeff N k.val → 0`.

  * If `j₀ ∈ range(φ)`: by injectivity of `φ`, the sum has exactly one
    term (the unique `k₀ : UnitQ` with `φ k₀ = j₀`), giving the
    matched-pair clause.
  * If `j₀ ∉ range(φ)`: the sum is empty, giving the non-matched clause.

Paper anchor: CPSV16 §II.C lines 1187-1188 (arXiv:1606.00608);
combined-family LI `Lem1` at CPSV16 lines 1131-1132; gauge-to-MPV
translation Lemma `equalMPS` at CPSV16 lines 1080-1097. -/
theorem coeff_identity_via_global_gauge
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hEqual : SameMPV₂ P.toTensor Q.toTensor) :
    let UnitQ := { k : Fin Q.basisCount // ∃ q : Fin (Q.copies k), ‖Q.weight k q‖ = 1 }
    ∀ (φ : UnitQ ↪ Fin P.basisCount)
      (_hMatch : ∀ k : UnitQ, ∃ h : P.basisDim (φ k) = Q.basisDim k.val,
        GaugePhaseEquiv
            (cast (congr_arg (MPSTensor d) h) (P.basis (φ k))) (Q.basis k.val) ∧
        ¬ Tendsto (fun N : ℕ =>
            mpvOverlap (d := d) (P.basis (φ k)) (Q.basis k.val) N)
          atTop (𝓝 0)),
      (∀ k : UnitQ, ∃ ζ : ℂ, ‖ζ‖ = 1 ∧
          Tendsto (fun N : ℕ =>
              P.coeff N (φ k) - ζ ^ N * Q.coeff N k.val)
            atTop (𝓝 0)) ∧
      (∀ j : Fin P.basisCount, (∀ k : UnitQ, φ k ≠ j) →
          Tendsto (fun N : ℕ => P.coeff N j) atTop (𝓝 0)) := by
  classical
  -- The `let UnitQ := ...` in the goal introduces a let-binding that
  -- `intro` consumes BEFORE the explicit `∀` binders.  We name it `UnitQ`.
  intro UnitQ φ hMatch
  -- For each `k : UnitQ`, extract the matched gauge data `(h, hGPE, _)`
  -- and feed it into `extract_unit_gauge_phase_mpv` to obtain `(ζ, ‖ζ‖=1, hmpv)`.
  let gaugeData : (k : UnitQ) →
      { ζ : ℂ // ‖ζ‖ = 1 ∧
        ∀ (N : ℕ) (σ : Fin N → Fin d),
          mpv (Q.basis k.val) σ = ζ ^ N * mpv (P.basis (φ k)) σ } := fun k =>
    let hm := hMatch k
    let h : P.basisDim (φ k) = Q.basisDim k.val := hm.choose
    let hGPE : GaugePhaseEquiv
        (cast (congr_arg (MPSTensor d) h) (P.basis (φ k))) (Q.basis k.val) :=
      hm.choose_spec.1
    let res := extract_unit_gauge_phase_mpv hP hQ h hGPE
    ⟨res.choose, res.choose_spec⟩
  let ζ : UnitQ → ℂ := fun k => (gaugeData k).val
  have hζ_norm : ∀ k : UnitQ, ‖ζ k‖ = 1 := fun k => (gaugeData k).property.1
  have hζ_mpv : ∀ (k : UnitQ) (N : ℕ) (σ : Fin N → Fin d),
      mpv (Q.basis k.val) σ = (ζ k) ^ N * mpv (P.basis (φ k)) σ := fun k =>
    (gaugeData k).property.2
  -- Weight bounds for both canonical forms (CPSV16 line 246).
  have hP_weight_le : ∀ j : Fin P.basisCount,
      ∀ q : Fin (P.copies j), ‖P.weight j q‖ ≤ 1 := hP.weight_norm_le_one
  have hQ_weight_le : ∀ k : Fin Q.basisCount,
      ∀ q : Fin (Q.copies k), ‖Q.weight k q‖ ≤ 1 := hQ.weight_norm_le_one
  -- For each k ∉ UnitQ, every weight is strictly subnormal, hence the
  -- Q-side coefficient decays (Cesàro converse, `PaperBNT/Api.lean`).
  have hQ_coeff_zero_of_nonunit : ∀ k : Fin Q.basisCount,
      (¬ ∃ q : Fin (Q.copies k), ‖Q.weight k q‖ = 1) →
      Tendsto (fun N : ℕ => Q.coeff N k) atTop (𝓝 0) := by
    intro k hnone
    apply hQ.coeff_tendsto_zero_of_all_weights_subnorm
    intro q
    have hle := hQ_weight_le k q
    have hne : ‖Q.weight k q‖ ≠ 1 := by
      intro h1
      exact hnone ⟨q, h1⟩
    exact lt_of_le_of_ne hle hne
  -- Auxiliary `NeZero` instances for the left-canonical mpvOverlap bound.
  have hP_dimPos : ∀ j : Fin P.basisCount, NeZero (P.basisDim j) :=
    fun j => ⟨(hP.basis_dim_pos j).ne'⟩
  have hQ_dimPos : ∀ k : Fin Q.basisCount, NeZero (Q.basisDim k) :=
    fun k => ⟨(hQ.basis_dim_pos k).ne'⟩
  -- ============================================================
  -- The per-`j₀` projection result.
  -- ============================================================
  -- For each `j₀ : Fin P.basisCount`, define the "matched RHS contribution"
  -- as the sum over UnitQ of conditional terms.
  let matchedRHS : Fin P.basisCount → ℕ → ℂ := fun j₀ N =>
    ∑ k : UnitQ, (if φ k = j₀ then (ζ k) ^ N * Q.coeff N k.val else 0)
  -- ============================================================
  -- Master per-`j₀` tendsto: `P.coeff N j₀ - matchedRHS j₀ N → 0`.
  -- ============================================================
  have master_tendsto : ∀ j₀ : Fin P.basisCount,
      Tendsto (fun N : ℕ => P.coeff N j₀ - matchedRHS j₀ N) atTop (𝓝 0) := by
    intro j₀
    haveI hj₀dim : NeZero (P.basisDim j₀) := hP_dimPos j₀
    -- Overlap projection identity:
    -- `∑_j P.coeff N j · ⟨P.basis j | P.basis j₀⟩_N
    --    = ∑_k Q.coeff N k · ⟨Q.basis k | P.basis j₀⟩_N`.
    have hProj_identity :
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
    -- LHS analysis: each `j ≠ j₀` term tends to `0` (cross-decay × bounded).
    have hP_cross : ∀ j : Fin P.basisCount, j ≠ j₀ →
        Tendsto (fun N : ℕ =>
            P.coeff N j * mpvOverlap (d := d) (P.basis j) (P.basis j₀) N)
          atTop (𝓝 0) := by
      intro j hj
      have hOverlap : Tendsto (fun N : ℕ =>
          mpvOverlap (d := d) (P.basis j) (P.basis j₀) N) atTop (𝓝 0) :=
        hP.cross_overlap_basis_tendsto_zero hj
      have hBound :
          Tendsto (fun N : ℕ =>
              (P.copies j : ℝ) *
              ‖mpvOverlap (d := d) (P.basis j) (P.basis j₀) N‖)
            atTop (𝓝 0) := by
        have := hOverlap.norm.const_mul ((P.copies j : ℝ))
        simpa using this
      refine squeeze_zero_norm (fun N => ?_) hBound
      have hC := P.norm_coeff_le_copies_of_norm_weight_le_one (N := N) (j := j)
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
    -- Diagonal: `P.coeff N j₀ · (self_overlap - 1) → 0`.
    have hP_self_minus_one : Tendsto (fun N : ℕ =>
        mpvOverlap (d := d) (P.basis j₀) (P.basis j₀) N - 1)
        atTop (𝓝 0) := by
      have := (hP.basis_normalized_self_overlap j₀).sub_const (1 : ℂ)
      simpa using this
    have hP_diag_minus_coeff : Tendsto (fun N : ℕ =>
        P.coeff N j₀ *
          (mpvOverlap (d := d) (P.basis j₀) (P.basis j₀) N - 1))
        atTop (𝓝 0) := by
      have hBound : Tendsto (fun N : ℕ =>
          (P.copies j₀ : ℝ) *
          ‖mpvOverlap (d := d) (P.basis j₀) (P.basis j₀) N - 1‖)
          atTop (𝓝 0) := by
        have := hP_self_minus_one.norm.const_mul ((P.copies j₀ : ℝ))
        simpa using this
      refine squeeze_zero_norm (fun N => ?_) hBound
      have hC := P.norm_coeff_le_copies_of_norm_weight_le_one (N := N) (j := j₀)
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
    have hLHS_minus_coeff : Tendsto (fun N : ℕ =>
        (∑ j : Fin P.basisCount, P.coeff N j *
            mpvOverlap (d := d) (P.basis j) (P.basis j₀) N)
          - P.coeff N j₀)
        atTop (𝓝 0) := by
      have hCombined : Tendsto (fun N : ℕ =>
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
      have hSplit : (∑ j : Fin P.basisCount, P.coeff N j *
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
      have hRw : P.coeff N j₀ *
          mpvOverlap (d := d) (P.basis j₀) (P.basis j₀) N
          = P.coeff N j₀ *
              (mpvOverlap (d := d) (P.basis j₀) (P.basis j₀) N - 1)
            + P.coeff N j₀ := by ring
      rw [hSplit, hRw]; ring
    -- RHS analysis: split `k : Fin Q.basisCount` into `UnitQ` and complement.
    -- For each `k : Fin Q.basisCount`, compute its `Q.coeff N k · overlap` term.
    -- We will partition `Finset.univ : Finset (Fin Q.basisCount)` into
    -- "is unit-modulus on Q" and "is not", and analyse each side.
    -- For each k ∈ UnitQ with φ k = j₀: term tends to (Q.coeff N k · ζ_k^N) eventually.
    -- For each k ∈ UnitQ with φ k ≠ j₀: term → 0.
    -- For each k ∉ UnitQ: term → 0.
    --
    -- We work with a per-k analysis function.  For each `k : Fin Q.basisCount`,
    -- consider the term `tQ k N := Q.coeff N k * mpvOverlap (Q.basis k) (P.basis j₀) N`.
    -- We aim: `Tendsto (fun N => tQ k N - tQ_target k N) atTop (𝓝 0)`, where
    -- `tQ_target k N := if (∃ kU : UnitQ, kU.val = k ∧ φ kU = j₀)`
    --                  `then ζ_{kU}^N · Q.coeff N k else 0`.
    --
    -- Step 1: For k ∈ UnitQ, rewrite `mpvOverlap (Q.basis k) (P.basis j₀) N
    --                                  = ζ_k^N · mpvOverlap (P.basis (φ k)) (P.basis j₀) N`.
    have hQ_unit_overlap_subst : ∀ (kU : UnitQ) (N : ℕ),
        mpvOverlap (d := d) (Q.basis kU.val) (P.basis j₀) N
          = (ζ kU) ^ N * mpvOverlap (d := d) (P.basis (φ kU)) (P.basis j₀) N := by
      intro kU N
      exact mpvOverlap_subst_via_mpv_pow (X := P.basis j₀) (hζ_mpv kU) N
    -- Step 2: For k ∈ UnitQ with φ k ≠ j₀, the term `Q.coeff N k.val · overlap → 0`.
    have hQ_unit_unmatched_tendsto_zero : ∀ kU : UnitQ, φ kU ≠ j₀ →
        Tendsto (fun N : ℕ =>
            Q.coeff N kU.val *
              mpvOverlap (d := d) (Q.basis kU.val) (P.basis j₀) N)
          atTop (𝓝 0) := by
      intro kU hne
      -- Rewrite via gauge substitution: term = Q.coeff · ζ^N · ⟨A_{φ k} | A_{j₀}⟩.
      have hOverlap_decay : Tendsto (fun N : ℕ =>
          mpvOverlap (d := d) (P.basis (φ kU)) (P.basis j₀) N) atTop (𝓝 0) :=
        hP.cross_overlap_basis_tendsto_zero hne
      -- Bound: |Q.coeff N k| ≤ Q.copies k, |ζ_k^N| = 1.
      have hBound : Tendsto (fun N : ℕ =>
          (Q.copies kU.val : ℝ) *
          ‖mpvOverlap (d := d) (P.basis (φ kU)) (P.basis j₀) N‖)
          atTop (𝓝 0) := by
        have := hOverlap_decay.norm.const_mul ((Q.copies kU.val : ℝ))
        simpa using this
      refine squeeze_zero_norm (fun N => ?_) hBound
      rw [hQ_unit_overlap_subst kU N]
      have hC := Q.norm_coeff_le_copies_of_norm_weight_le_one (N := N) (j := kU.val)
        (hWeightLe := hQ_weight_le kU.val)
      have hζN : ‖(ζ kU) ^ N‖ = 1 := by
        rw [norm_pow, hζ_norm kU, one_pow]
      calc
        ‖Q.coeff N kU.val *
            ((ζ kU) ^ N *
              mpvOverlap (d := d) (P.basis (φ kU)) (P.basis j₀) N)‖
            = ‖Q.coeff N kU.val‖ * (‖(ζ kU) ^ N‖ *
              ‖mpvOverlap (d := d) (P.basis (φ kU)) (P.basis j₀) N‖) := by
              rw [norm_mul, norm_mul]
        _ = ‖Q.coeff N kU.val‖ *
              ‖mpvOverlap (d := d) (P.basis (φ kU)) (P.basis j₀) N‖ := by
              rw [hζN, one_mul]
        _ ≤ (Q.copies kU.val : ℝ) *
              ‖mpvOverlap (d := d) (P.basis (φ kU)) (P.basis j₀) N‖ :=
            mul_le_mul_of_nonneg_right hC (norm_nonneg _)
    -- Step 3: For k ∉ UnitQ, `Q.coeff N k → 0` and overlap bounded by D₁·D₂.
    have hQ_nonunit_tendsto_zero : ∀ k : Fin Q.basisCount,
        (¬ ∃ q : Fin (Q.copies k), ‖Q.weight k q‖ = 1) →
        Tendsto (fun N : ℕ =>
            Q.coeff N k * mpvOverlap (d := d) (Q.basis k) (P.basis j₀) N)
          atTop (𝓝 0) := by
      intro k hnone
      have hCoeff := hQ_coeff_zero_of_nonunit k hnone
      -- Uniform overlap bound (left-canonical Cauchy-Schwarz).
      haveI : NeZero (Q.basisDim k) := hQ_dimPos k
      haveI : NeZero (P.basisDim j₀) := hP_dimPos j₀
      have hOverlap_bound : ∀ N : ℕ,
          ‖mpvOverlap (d := d) (Q.basis k) (P.basis j₀) N‖
            ≤ (Q.basisDim k : ℝ) * (P.basisDim j₀ : ℝ) := fun N =>
        leftCanonical_mpvOverlap_bound (Q.basis k) (P.basis j₀)
          (hQ.basis_left_canonical k) (hP.basis_left_canonical j₀) N
      -- Combined: |coeff · overlap| ≤ |coeff| · D₁·D₂, with |coeff| → 0.
      have hBoundProd : Tendsto (fun N : ℕ =>
          ‖Q.coeff N k‖ *
          ((Q.basisDim k : ℝ) * (P.basisDim j₀ : ℝ)))
          atTop (𝓝 0) := by
        have hc := hCoeff.norm
        have : Tendsto (fun N : ℕ => ‖Q.coeff N k‖) atTop (𝓝 0) := by
          simpa using hc
        have := this.mul_const ((Q.basisDim k : ℝ) * (P.basisDim j₀ : ℝ))
        simpa using this
      refine squeeze_zero_norm (fun N => ?_) hBoundProd
      have hCS := hOverlap_bound N
      calc
        ‖Q.coeff N k * mpvOverlap (d := d) (Q.basis k) (P.basis j₀) N‖
            = ‖Q.coeff N k‖ *
              ‖mpvOverlap (d := d) (Q.basis k) (P.basis j₀) N‖ := norm_mul _ _
        _ ≤ ‖Q.coeff N k‖ * ((Q.basisDim k : ℝ) * (P.basisDim j₀ : ℝ)) :=
            mul_le_mul_of_nonneg_left hCS (norm_nonneg _)
    -- Step 4: For k ∈ UnitQ with φ k = j₀, the term equals
    -- `ζ_k^N · Q.coeff N k.val · mpvOverlap (P.basis j₀) (P.basis j₀) N`,
    -- which equals `ζ_k^N · Q.coeff N k.val + ζ_k^N · Q.coeff N k.val · (self - 1)`,
    -- and the second part tends to `0`.
    have hQ_unit_matched_minus : ∀ kU : UnitQ, φ kU = j₀ →
        Tendsto (fun N : ℕ =>
            Q.coeff N kU.val *
              mpvOverlap (d := d) (Q.basis kU.val) (P.basis j₀) N
            - (ζ kU) ^ N * Q.coeff N kU.val)
          atTop (𝓝 0) := by
      intro kU hEq
      have hSelf_minus_one : Tendsto (fun N : ℕ =>
          mpvOverlap (d := d) (P.basis j₀) (P.basis j₀) N - 1)
          atTop (𝓝 0) := by
        have := (hP.basis_normalized_self_overlap j₀).sub_const (1 : ℂ)
        simpa using this
      -- After substitution and using φ kU = j₀:
      -- Q.coeff N kU.val · ⟨B_{kU} | A_{j₀}⟩ = ζ_{kU}^N · Q.coeff N kU.val · ⟨A_{j₀} | A_{j₀}⟩
      have hRewrite : ∀ N : ℕ,
          Q.coeff N kU.val *
              mpvOverlap (d := d) (Q.basis kU.val) (P.basis j₀) N
            - (ζ kU) ^ N * Q.coeff N kU.val
            = (ζ kU) ^ N * Q.coeff N kU.val *
              (mpvOverlap (d := d) (P.basis j₀) (P.basis j₀) N - 1) := by
        intro N
        rw [hQ_unit_overlap_subst kU N]
        -- Goal: Q.coeff N kU.val * (ζ_{kU}^N * mpvOverlap (P.basis (φ kU)) (P.basis j₀) N)
        --   - (ζ_{kU}^N * Q.coeff N kU.val)
        --   = (ζ_{kU}^N * Q.coeff N kU.val) *
        --       (mpvOverlap (P.basis j₀) (P.basis j₀) N - 1)
        -- Use φ kU = j₀ to identify P.basis (φ kU) with P.basis j₀.
        rw [hEq]
        ring
      refine Tendsto.congr (fun N => (hRewrite N).symm) ?_
      have hBound : Tendsto (fun N : ℕ =>
          (Q.copies kU.val : ℝ) *
          ‖mpvOverlap (d := d) (P.basis j₀) (P.basis j₀) N - 1‖)
          atTop (𝓝 0) := by
        have := hSelf_minus_one.norm.const_mul ((Q.copies kU.val : ℝ))
        simpa using this
      refine squeeze_zero_norm (fun N => ?_) hBound
      have hC := Q.norm_coeff_le_copies_of_norm_weight_le_one
        (N := N) (j := kU.val) (hWeightLe := hQ_weight_le kU.val)
      have hζN : ‖(ζ kU) ^ N‖ = 1 := by
        rw [norm_pow, hζ_norm kU, one_pow]
      calc
        ‖(ζ kU) ^ N * Q.coeff N kU.val *
            (mpvOverlap (d := d) (P.basis j₀) (P.basis j₀) N - 1)‖
            = (‖(ζ kU) ^ N‖ * ‖Q.coeff N kU.val‖) *
              ‖mpvOverlap (d := d) (P.basis j₀) (P.basis j₀) N - 1‖ := by
              rw [norm_mul, norm_mul]
        _ = ‖Q.coeff N kU.val‖ *
              ‖mpvOverlap (d := d) (P.basis j₀) (P.basis j₀) N - 1‖ := by
              rw [hζN, one_mul]
        _ ≤ (Q.copies kU.val : ℝ) *
              ‖mpvOverlap (d := d) (P.basis j₀) (P.basis j₀) N - 1‖ :=
            mul_le_mul_of_nonneg_right hC (norm_nonneg _)
    -- Combine all per-k pieces:
    -- For each k : Fin Q.basisCount, define a "per-k delta":
    --   `Δ k N := (Q.coeff N k · overlap(Q.basis k, P.basis j₀, N))
    --              - (kU_match_contrib k N)`,
    -- where `kU_match_contrib k N = ζ_{kU}^N · Q.coeff N k` if `k = kU.val` for
    -- some `kU : UnitQ` with `φ kU = j₀`, else `0`.
    -- We claim `Δ k N → 0` for all k, and `∑_k Δ k N → 0` is what we want.
    --
    -- Define the bridge function piece-wise on `Fin Q.basisCount`:
    -- `bridge k N := if (∃ kU : UnitQ, kU.val = k ∧ φ kU = j₀)
    --                  then (ζ kU)^N · Q.coeff N k else 0`.
    -- The key identity: `bridge k N = matchedRHS j₀ N` when summed over `k`,
    -- modulo the conversion from `UnitQ` to a Fin-indexed sum.
    --
    -- Approach: sum `tQ k N - bridge k N` over `k : Fin Q.basisCount`.
    -- LHS sum = RHS - ∑_k bridge k N = RHS - matchedRHS j₀ N
    --   (since the sum over k = sum over UnitQ ∪ complement, and only UnitQ
    --    with φ kU = j₀ contributes).
    -- We show the LHS sum tends to 0 by combining per-k pieces.
    -- For convenience, we work with the "matched bridge" form via UnitQ.
    -- Concretely: `∑_{k : Fin Q.basisCount} tQ k N`
    --   = `∑_{kU : UnitQ} tQ kU.val N + ∑_{k ∉ image of UnitQ} tQ k N`.
    -- And `matchedRHS j₀ N = ∑_{kU : UnitQ, φ kU = j₀} (ζ kU)^N · Q.coeff N kU.val`.
    --
    -- Since φ is an Embedding, injectivity gives at most one such `kU`.
    -- We'll re-express things using `Finset.sum` on a partition.
    -- ============================================================
    -- The cleanest combinatorial path: introduce the inclusion
    --   `inc : UnitQ → Fin Q.basisCount := Subtype.val`,
    -- which is injective.  Sum decomposition:
    -- `∑_k tQ k N = ∑_{kU} tQ kU.val N + ∑_{k ∈ univ \ image inc} tQ k N`.
    -- The first sum: by per-`kU` cases (matched/unmatched), it tends to
    -- `matchedRHS j₀ N` (asymptotically).
    -- The second sum: by `hQ_nonunit_tendsto_zero`, tends to `0`.
    -- ============================================================
    -- Step A: `∑_{k ∉ image inc} tQ k N → 0`.
    -- These `k`'s have no `q` with `‖Q.weight k q‖ = 1` (otherwise k ∈ UnitQ).
    have hQ_complement_set :
        (Finset.univ : Finset (Fin Q.basisCount)).filter
          (fun k => ¬ ∃ q : Fin (Q.copies k), ‖Q.weight k q‖ = 1)
        = (Finset.univ : Finset (Fin Q.basisCount)).filter
          (fun k => ¬ ∃ q : Fin (Q.copies k), ‖Q.weight k q‖ = 1) := rfl
    have h_complement_tendsto_zero :
        Tendsto (fun N : ℕ =>
            ∑ k ∈ (Finset.univ : Finset (Fin Q.basisCount)).filter
              (fun k => ¬ ∃ q : Fin (Q.copies k), ‖Q.weight k q‖ = 1),
              Q.coeff N k * mpvOverlap (d := d) (Q.basis k) (P.basis j₀) N)
          atTop (𝓝 0) := by
      have := tendsto_finset_sum
        ((Finset.univ : Finset (Fin Q.basisCount)).filter
          (fun k => ¬ ∃ q : Fin (Q.copies k), ‖Q.weight k q‖ = 1))
        (fun k hk => hQ_nonunit_tendsto_zero k
          (by
            have := Finset.mem_filter.mp hk
            exact this.2))
      simpa using this
    -- Step B: `∑_{k ∈ image inc} tQ k N → matchedRHS j₀ N` (asymptotically).
    -- We index this sum via the embedding `UnitQ ↪ Fin Q.basisCount` (Subtype.val).
    -- The matched-kU contributions give `ζ_{kU}^N · Q.coeff N kU.val` (modulo o(1)).
    -- The unmatched-kU contributions give `0` (modulo o(1)).
    -- ∑_{kU : UnitQ} (Q.coeff N kU.val · overlap - matched_term kU N) → 0.
    have hQ_unit_sum_minus :
        Tendsto (fun N : ℕ =>
            ∑ kU : UnitQ,
              (Q.coeff N kU.val *
                mpvOverlap (d := d) (Q.basis kU.val) (P.basis j₀) N
                - (if φ kU = j₀ then (ζ kU) ^ N * Q.coeff N kU.val else 0)))
          atTop (𝓝 0) := by
      have hPer : ∀ kU : UnitQ,
          Tendsto (fun N : ℕ =>
              Q.coeff N kU.val *
                mpvOverlap (d := d) (Q.basis kU.val) (P.basis j₀) N
                - (if φ kU = j₀ then (ζ kU) ^ N * Q.coeff N kU.val else 0))
            atTop (𝓝 0) := by
        intro kU
        by_cases hCase : φ kU = j₀
        · rw [show (fun N : ℕ =>
              Q.coeff N kU.val *
                mpvOverlap (d := d) (Q.basis kU.val) (P.basis j₀) N
              - (if φ kU = j₀ then (ζ kU) ^ N * Q.coeff N kU.val else 0))
            = (fun N : ℕ =>
              Q.coeff N kU.val *
                mpvOverlap (d := d) (Q.basis kU.val) (P.basis j₀) N
              - (ζ kU) ^ N * Q.coeff N kU.val) from by
            funext N; rw [if_pos hCase]]
          exact hQ_unit_matched_minus kU hCase
        · rw [show (fun N : ℕ =>
              Q.coeff N kU.val *
                mpvOverlap (d := d) (Q.basis kU.val) (P.basis j₀) N
              - (if φ kU = j₀ then (ζ kU) ^ N * Q.coeff N kU.val else 0))
            = (fun N : ℕ =>
              Q.coeff N kU.val *
                mpvOverlap (d := d) (Q.basis kU.val) (P.basis j₀) N) from by
            funext N; rw [if_neg hCase]; ring]
          exact hQ_unit_unmatched_tendsto_zero kU hCase
      have := tendsto_finset_sum (Finset.univ : Finset UnitQ)
        (fun (kU : UnitQ) _ => hPer kU)
      simpa using this
    -- Identify the sum over `UnitQ` with the sum over `image inc ⊂ Fin Q.basisCount`.
    -- This is the bijection `UnitQ ≃ image inc` from `Subtype.val` injectivity.
    -- We'll convert via `Finset.sum_subtype`.
    -- Combine: `RHS - matchedRHS j₀ N → 0` where RHS is the full Q-sum.
    have hRHS_minus_matchedRHS :
        Tendsto (fun N : ℕ =>
            (∑ k : Fin Q.basisCount, Q.coeff N k *
                mpvOverlap (d := d) (Q.basis k) (P.basis j₀) N)
              - matchedRHS j₀ N)
          atTop (𝓝 0) := by
      -- Rewrite `RHS - matchedRHS = unit_sum_minus_matchedRHS + complement_sum`.
      -- Strategy:
      --   RHS = ∑_{kU : UnitQ} f kU.val + ∑_{k ∈ CFilter} f k  (partition);
      --   matchedRHS = ∑_{kU : UnitQ} (if φ kU = j₀ then … else 0);
      --   RHS - matchedRHS = ∑_{kU : UnitQ} (f kU.val - …) + ∑_{CFilter} f k.
      -- The first summand → 0 by `hQ_unit_sum_minus`; the second → 0 by
      -- `h_complement_tendsto_zero`.
      have hSplitSum : ∀ N : ℕ,
          (∑ k : Fin Q.basisCount, Q.coeff N k *
              mpvOverlap (d := d) (Q.basis k) (P.basis j₀) N)
            - matchedRHS j₀ N
            = (∑ kU : UnitQ,
                  (Q.coeff N kU.val *
                    mpvOverlap (d := d) (Q.basis kU.val) (P.basis j₀) N
                    - (if φ kU = j₀ then (ζ kU) ^ N * Q.coeff N kU.val else 0)))
              + (∑ k ∈ (Finset.univ : Finset (Fin Q.basisCount)).filter
                    (fun k => ¬ ∃ q : Fin (Q.copies k), ‖Q.weight k q‖ = 1),
                  Q.coeff N k *
                    mpvOverlap (d := d) (Q.basis k) (P.basis j₀) N) := by
        intro N
        classical
        -- Partition: ∑ k ∈ univ, f k = ∑ k ∈ univ.filter p, f k + ∑ k ∈ univ.filter (¬ p), f k.
        have hPartition :
            (∑ k : Fin Q.basisCount, Q.coeff N k *
                mpvOverlap (d := d) (Q.basis k) (P.basis j₀) N)
              = (∑ k ∈ (Finset.univ : Finset (Fin Q.basisCount)).filter
                    (fun k => ∃ q : Fin (Q.copies k), ‖Q.weight k q‖ = 1),
                  Q.coeff N k *
                    mpvOverlap (d := d) (Q.basis k) (P.basis j₀) N)
                + (∑ k ∈ (Finset.univ : Finset (Fin Q.basisCount)).filter
                    (fun k => ¬ ∃ q : Fin (Q.copies k), ‖Q.weight k q‖ = 1),
                  Q.coeff N k *
                    mpvOverlap (d := d) (Q.basis k) (P.basis j₀) N) := by
          rw [← Finset.sum_filter_add_sum_filter_not
            (Finset.univ : Finset (Fin Q.basisCount))
            (fun k => ∃ q : Fin (Q.copies k), ‖Q.weight k q‖ = 1)
            (fun k => Q.coeff N k *
              mpvOverlap (d := d) (Q.basis k) (P.basis j₀) N)]
        -- Convert the filter-sum (positive side) to a UnitQ sum.
        have hFilterToSub :
            (∑ k ∈ (Finset.univ : Finset (Fin Q.basisCount)).filter
                (fun k => ∃ q : Fin (Q.copies k), ‖Q.weight k q‖ = 1),
              Q.coeff N k *
                mpvOverlap (d := d) (Q.basis k) (P.basis j₀) N)
              = ∑ kU : UnitQ, Q.coeff N kU.val *
                mpvOverlap (d := d) (Q.basis kU.val) (P.basis j₀) N := by
          refine Finset.sum_subtype
            ((Finset.univ : Finset (Fin Q.basisCount)).filter
              (fun k => ∃ q : Fin (Q.copies k), ‖Q.weight k q‖ = 1))
            ?_ _
          intro x
          simp
        -- Express `matchedRHS j₀ N` as a sum over UnitQ.
        have hMatched_def : matchedRHS j₀ N = ∑ kU : UnitQ,
            (if φ kU = j₀ then (ζ kU) ^ N * Q.coeff N kU.val else 0) := rfl
        rw [hPartition, hFilterToSub, hMatched_def]
        rw [show
          ∑ kU : UnitQ,
            (Q.coeff N kU.val *
                mpvOverlap (d := d) (Q.basis kU.val) (P.basis j₀) N
              - (if φ kU = j₀ then (ζ kU) ^ N * Q.coeff N kU.val else 0))
            = (∑ kU : UnitQ, Q.coeff N kU.val *
                mpvOverlap (d := d) (Q.basis kU.val) (P.basis j₀) N)
              - ∑ kU : UnitQ,
                (if φ kU = j₀ then (ζ kU) ^ N * Q.coeff N kU.val else 0)
          from Finset.sum_sub_distrib _ _]
        ring
      refine Tendsto.congr (fun N => (hSplitSum N).symm) ?_
      have := hQ_unit_sum_minus.add h_complement_tendsto_zero
      simpa using this
    -- Now use the projection identity to pivot from LHS to RHS.
    -- `(LHS - P.coeff N j₀) - (RHS - matchedRHS j₀ N) = matchedRHS j₀ N - P.coeff N j₀`.
    -- And `LHS = RHS` (projection identity), so the LHS difference is exactly
    -- `matchedRHS j₀ N - P.coeff N j₀`.  Hence both `(LHS - P.coeff N j₀)` and
    -- `(RHS - matchedRHS j₀ N)` differ by a constant per N — combined they
    -- give `P.coeff N j₀ - matchedRHS j₀ N → 0`.
    have hDiff : Tendsto (fun N : ℕ =>
        (∑ j : Fin P.basisCount, P.coeff N j *
            mpvOverlap (d := d) (P.basis j) (P.basis j₀) N)
          - P.coeff N j₀
          - ((∑ k : Fin Q.basisCount, Q.coeff N k *
                mpvOverlap (d := d) (Q.basis k) (P.basis j₀) N)
            - matchedRHS j₀ N))
        atTop (𝓝 (0 - 0)) :=
      hLHS_minus_coeff.sub hRHS_minus_matchedRHS
    have hDiff_zero : Tendsto (fun N : ℕ =>
        (∑ j : Fin P.basisCount, P.coeff N j *
            mpvOverlap (d := d) (P.basis j) (P.basis j₀) N)
          - P.coeff N j₀
          - ((∑ k : Fin Q.basisCount, Q.coeff N k *
                mpvOverlap (d := d) (Q.basis k) (P.basis j₀) N)
            - matchedRHS j₀ N))
        atTop (𝓝 0) := by simpa using hDiff
    -- Use the projection identity LHS = RHS pointwise to collapse the
    -- difference to `matchedRHS j₀ N - P.coeff N j₀`.
    have hMatched_minus_coeff : Tendsto (fun N : ℕ =>
        matchedRHS j₀ N - P.coeff N j₀)
        atTop (𝓝 0) := by
      refine hDiff_zero.congr ?_
      intro N
      have hId := hProj_identity N
      -- `(LHS - coeff) - (RHS - matched) = matched - coeff` when LHS = RHS.
      linear_combination hId
    -- Negate to obtain the desired `P.coeff N j₀ - matchedRHS j₀ N → 0`.
    have hFinal := hMatched_minus_coeff.neg
    simp only [neg_sub, neg_zero] at hFinal
    exact hFinal
  -- ============================================================
  -- Specialize the master tendsto to derive the two clauses.
  -- ============================================================
  refine ⟨?_, ?_⟩
  · -- Matched-pair clause: for each k : UnitQ, with j₀ := φ k, the matched sum
    -- has exactly one nonzero term (the k itself), giving the asymptotic identity.
    intro k
    refine ⟨ζ k, hζ_norm k, ?_⟩
    have hM := master_tendsto (φ k)
    refine hM.congr ?_
    intro N
    -- Show: P.coeff N (φ k) - matchedRHS (φ k) N = P.coeff N (φ k) - ζ k ^ N · Q.coeff N k.val.
    -- Equivalently: matchedRHS (φ k) N = ζ k ^ N · Q.coeff N k.val.
    have hSum : matchedRHS (φ k) N = (ζ k) ^ N * Q.coeff N k.val := by
      change (∑ kU : UnitQ,
          (if φ kU = φ k then (ζ kU) ^ N * Q.coeff N kU.val else 0))
        = (ζ k) ^ N * Q.coeff N k.val
      have hφ_inj : Function.Injective (φ : UnitQ → Fin P.basisCount) :=
        φ.injective
      have h_unique : ∀ kU : UnitQ, kU ≠ k →
          (if φ kU = φ k then (ζ kU) ^ N * Q.coeff N kU.val else 0) = 0 := by
        intro kU hne
        rw [if_neg]
        intro hEq
        exact hne (hφ_inj hEq)
      rw [Finset.sum_eq_single k]
      · rw [if_pos rfl]
      · intro kU _ hne
        exact h_unique kU hne
      · intro hMem
        exfalso
        exact hMem (Finset.mem_univ k)
    rw [hSum]
  · -- Non-matched clause: for each j ∉ range(φ), matchedRHS j N = 0,
    -- hence P.coeff N j → 0.
    intro j₀ hUnmatched
    have hM := master_tendsto j₀
    refine hM.congr ?_
    intro N
    have hSum : matchedRHS j₀ N = 0 := by
      change (∑ kU : UnitQ,
          (if φ kU = j₀ then (ζ kU) ^ N * Q.coeff N kU.val else 0)) = 0
      apply Finset.sum_eq_zero
      intro kU _
      rw [if_neg (hUnmatched kU)]
    rw [hSum, sub_zero]

end MPSTensor
