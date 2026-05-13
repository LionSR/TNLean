/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Algebra.UnitModulusPowerSum
import TNLean.MPS.FundamentalTheorem.SectorDecomposition.PerBlockProjection

/-!
# Discharge of the `hNoCancel` hypothesis in the per-block projection

This module discharges the load-bearing hypothesis `hNoCancel` of

  `fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_sectorDecomp`
  `fixed_left_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_sectorDecomp`

from the following four hypotheses:

* **Unit-modulus sector weights.**  Together with
  `unitModulus_power_sum_not_tendsto_zero`, this forces the BNT coefficient
  `Q.coeff N k₀ = ∑_q (Q.weight k₀ q)^N` to not tend to zero as `N → ∞`.

* **Decay of `Q`-off-diagonal cross-overlaps.**  The off-diagonal terms of
  the expansion
  `mpvOverlap Q.toTensor (Q.basis k₀) N
      = ∑_k Q.coeff N k · mpvOverlap (Q.basis k) (Q.basis k₀) N`
  vanish in the limit.

* **Nonzero self-overlap limit at `k₀`.**  The diagonal term tends to a
  nonzero limit, so the expansion is asymptotically equivalent to
  `Q.coeff N k₀ · mpvOverlap (Q.basis k₀) (Q.basis k₀) N`.

* **Lower bound on `‖c N‖`.**  The scalar witness of the eventual
  proportionality is bounded below by a positive constant.

Combining these hypotheses, the load-bearing `hNoCancel` follows, and the
per-block projection contradiction then closes as in
`PerBlockProjection.lean`.

## Main statements

* `mpvOverlap_toTensor_basis_not_tendsto_zero` (a Q-only analytic
  statement: assuming unit-modulus, off-diagonal decay, and nonzero
  self-overlap limit, the assembled-tensor-to-block overlap does not
  tend to zero).

* `hNoCancel_of_unitModulus_decay_c_norm_lower` (the universally-quantified
  hNoCancel discharge consumed by the per-block projection theorems).

* `fixed_right_all_overlaps_decay_false_paperFaithful`
  `fixed_left_all_overlaps_decay_false_paperFaithful`
  — corollaries assembling the per-block-projection skeleton with the
  analytic discharge of the non-cancellation hypothesis.

* `fixed_right_all_overlaps_decay_false_paperFaithful_twoLayer`
  `fixed_left_all_overlaps_decay_false_paperFaithful_twoLayer`
  — two-layer counterparts consuming `IsBNTCanonicalFormSD P` (resp.
  `IsBNTCanonicalFormSD Q`).  The abstract `hNoCancel` is kept in the
  signature: the analytic discharge of `hNoCancel` in the two-layer
  setting is deferred (see audit memo for the analytic content).

## References

* Cirac, Pérez-García, Schuch, Verstraete, *Matrix Product Density Operators:
  Renormalization Fixed Points and Boundary Theories*, arXiv:1606.00608
  (2017), Theorem `thm1`, lines 1170--1192.
-/

open scoped Matrix BigOperators
open Filter

namespace MPSTensor

variable {d : ℕ}

section UnitModulusNonCancellation

/-- **Assembled-tensor-to-block overlap does not vanish.**

For a sector decomposition `Q` with unit-modulus sector weights, a fixed
block index `k₀`, decaying off-diagonal cross-overlaps to `Q.basis k₀`,
and a nonzero self-overlap limit at `k₀`, the assembled-tensor-to-block
overlap `mpvOverlap Q.toTensor (Q.basis k₀) N` does not tend to zero as
`N → ∞`.

Source: arXiv:1606.00608, Theorem `thm1`, lines 1170--1192 (Q-side
non-cancellation in the per-block projection step). -/
lemma mpvOverlap_toTensor_basis_not_tendsto_zero
    (Q : SectorDecomposition d)
    (hQ_unit : ∀ k q, ‖Q.sectors.weight k q‖ = 1)
    (k₀ : Fin Q.basisCount)
    (hQ_decay_offdiag : ∀ k, k ≠ k₀ →
        Tendsto (fun N => mpvOverlap (d := d) (Q.basis k) (Q.basis k₀) N)
          atTop (nhds 0))
    {ℓ : ℂ} (hℓ_ne : ℓ ≠ 0)
    (hQ_self_limit :
        Tendsto (fun N => mpvOverlap (d := d) (Q.basis k₀) (Q.basis k₀) N)
          atTop (nhds ℓ)) :
    ¬ Tendsto (fun N => mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N)
        atTop (nhds 0) := by
  classical
  intro hZero
  -- Step 1: Expand the overlap via the basis decomposition of `Q.toTensor`.
  have hExpand : ∀ N : ℕ,
      mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N
        = ∑ k : Fin Q.basisCount,
            Q.coeff N k * mpvOverlap (d := d) (Q.basis k) (Q.basis k₀) N := by
    intro N
    refine mpvOverlap_eq_sum_of_decomp_left
      (d := d) (g := Q.basisCount) (dim := Q.basisDim)
      Q.toTensor Q.basis (N := N)
      (fun k => Q.coeff N k) ?_ (Q.basis k₀)
    intro σ
    exact Q.mpv_toTensor_eq_sum_coeff (N := N) σ
  -- Step 2: For each k ≠ k₀, `Q.coeff N k * overlap_k N → 0`.
  have hOffDiag : ∀ k : Fin Q.basisCount, k ≠ k₀ →
      Tendsto
        (fun N =>
          Q.coeff N k * mpvOverlap (d := d) (Q.basis k) (Q.basis k₀) N)
        atTop (nhds 0) := by
    intro k hk
    refine squeeze_zero_norm
      (f := fun N =>
        Q.coeff N k * mpvOverlap (d := d) (Q.basis k) (Q.basis k₀) N)
      (a := fun N => (Q.copies k : ℝ)
                      * ‖mpvOverlap (d := d) (Q.basis k) (Q.basis k₀) N‖)
      ?_ ?_
    · intro N
      simp only [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (Q.norm_coeff_le_copies hQ_unit N k) (norm_nonneg _)
    · have h0 : Tendsto
          (fun N => ‖mpvOverlap (d := d) (Q.basis k) (Q.basis k₀) N‖)
          atTop (nhds 0) :=
        (tendsto_zero_iff_norm_tendsto_zero.mp (hQ_decay_offdiag k hk))
      have := h0.const_mul (Q.copies k : ℝ)
      simpa using this
  -- Step 3: Total off-diagonal contribution tends to zero.
  have hOffDiagSum : Tendsto
      (fun N => ∑ k ∈ (Finset.univ.erase k₀),
          Q.coeff N k * mpvOverlap (d := d) (Q.basis k) (Q.basis k₀) N)
      atTop (nhds 0) := by
    have hTo : Tendsto
        (fun N => ∑ k ∈ (Finset.univ.erase k₀),
            Q.coeff N k * mpvOverlap (d := d) (Q.basis k) (Q.basis k₀) N)
        atTop
        (nhds (∑ _k ∈ (Finset.univ.erase k₀ : Finset (Fin Q.basisCount)),
                (0 : ℂ))) := by
      refine tendsto_finset_sum (Finset.univ.erase k₀) ?_
      intro k hk
      exact hOffDiag k (Finset.ne_of_mem_erase hk)
    simpa using hTo
  -- Step 4: From the assumption, the diagonal term tends to zero.
  have hDiag_tendsto : Tendsto
      (fun N =>
        Q.coeff N k₀ * mpvOverlap (d := d) (Q.basis k₀) (Q.basis k₀) N)
      atTop (nhds 0) := by
    -- diagonal = whole sum - off-diagonal sum
    have hRew : ∀ N : ℕ,
        Q.coeff N k₀ * mpvOverlap (d := d) (Q.basis k₀) (Q.basis k₀) N
          = mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N
            - ∑ k ∈ (Finset.univ.erase k₀),
                Q.coeff N k * mpvOverlap (d := d) (Q.basis k) (Q.basis k₀) N := by
      intro N
      have hcomb :
          mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N
            = Q.coeff N k₀ * mpvOverlap (d := d) (Q.basis k₀) (Q.basis k₀) N
              + ∑ k ∈ (Finset.univ.erase k₀),
                  Q.coeff N k *
                    mpvOverlap (d := d) (Q.basis k) (Q.basis k₀) N := by
        rw [hExpand N]
        exact (Finset.add_sum_erase _ _ (Finset.mem_univ k₀)).symm
      exact eq_sub_of_add_eq hcomb.symm
    have hSub := hZero.sub hOffDiagSum
    have hZero' : (0 : ℂ) - 0 = 0 := by ring
    rw [hZero'] at hSub
    refine hSub.congr' ?_
    refine Filter.Eventually.of_forall ?_
    intro N
    exact (hRew N).symm
  -- Step 5: Since self-overlap → ℓ ≠ 0, `Q.coeff N k₀ → 0`.
  have hCoeff_tendsto : Tendsto (fun N => Q.coeff N k₀) atTop (nhds 0) := by
    -- Q.coeff N k₀ = (coeff * self) / self  (eventually, self ≠ 0)
    -- Use: coeff * self → 0, self → ℓ ≠ 0  ⟹  coeff → 0/ℓ = 0
    have hQuot : Tendsto
        (fun N =>
          (Q.coeff N k₀ * mpvOverlap (d := d) (Q.basis k₀) (Q.basis k₀) N)
            / mpvOverlap (d := d) (Q.basis k₀) (Q.basis k₀) N)
        atTop (nhds (0 / ℓ)) :=
      hDiag_tendsto.div hQ_self_limit hℓ_ne
    have hRewQuot : ∀ᶠ N in atTop,
        (Q.coeff N k₀ * mpvOverlap (d := d) (Q.basis k₀) (Q.basis k₀) N)
            / mpvOverlap (d := d) (Q.basis k₀) (Q.basis k₀) N
          = Q.coeff N k₀ := by
      have hself_ne : ∀ᶠ N in atTop,
          mpvOverlap (d := d) (Q.basis k₀) (Q.basis k₀) N ≠ 0 :=
        hQ_self_limit.eventually_ne hℓ_ne
      filter_upwards [hself_ne] with N hN
      field_simp
    have := hQuot.congr' hRewQuot
    simpa using this
  -- Step 6: Contradict unit-modulus power-sum non-decay at block `k₀`.
  refine UnitModulusPowerSum.unitModulus_power_sum_not_tendsto_zero
    (r := Q.copies k₀) (Q.copies_pos k₀) (Q.weight k₀) (hQ_unit k₀) ?_
  -- Convert `Q.coeff N k₀ → 0` to `∑ q, (Q.weight k₀ q)^N → 0`.
  refine hCoeff_tendsto.congr ?_
  intro N
  change Q.coeff N k₀ = ∑ q : Fin (Q.copies k₀), (Q.weight k₀ q) ^ N
  rfl

/-- **Single-sequence `hNoCancel` discharge.**

For a sector decomposition `Q` with unit-modulus weights and a fixed
block index `k₀` admitting both decaying off-diagonal cross-overlaps and a
nonzero self-overlap limit, every scalar sequence `c : ℕ → ℂ` whose norm
is eventually bounded below by a positive constant satisfies the
non-cancellation conclusion of `hNoCancel`. -/
lemma hNoCancel_single_seq
    (Q : SectorDecomposition d)
    (hQ_unit : ∀ k q, ‖Q.sectors.weight k q‖ = 1)
    (k₀ : Fin Q.basisCount)
    (hQ_decay_offdiag : ∀ k, k ≠ k₀ →
        Tendsto (fun N => mpvOverlap (d := d) (Q.basis k) (Q.basis k₀) N)
          atTop (nhds 0))
    {ℓ : ℂ} (hℓ_ne : ℓ ≠ 0)
    (hQ_self_limit :
        Tendsto (fun N => mpvOverlap (d := d) (Q.basis k₀) (Q.basis k₀) N)
          atTop (nhds ℓ))
    (c : ℕ → ℂ)
    (hc_lower : ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N in atTop, δ ≤ ‖c N‖) :
    ¬ Tendsto (fun N => c N * mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N)
        atTop (nhds 0) := by
  classical
  intro hCancel
  -- From `c N * X N → 0` and `‖c N‖ ≥ δ`, deduce `X N → 0`.
  rcases hc_lower with ⟨δ, hδpos, hδ⟩
  have hXnorm : Tendsto
      (fun N => ‖mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N‖)
      atTop (nhds 0) := by
    -- ‖X N‖ ≤ ‖c N * X N‖ / δ
    have hCancel_norm : Tendsto
        (fun N => ‖c N * mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N‖)
        atTop (nhds 0) := by
      have := hCancel.norm
      simpa using this
    -- Upper bound function.
    set bound : ℕ → ℝ := fun N =>
      ‖c N * mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N‖ / δ with hbound_def
    have hbound_tendsto : Tendsto bound atTop (nhds 0) := by
      have := hCancel_norm.div_const δ
      simpa [bound] using this
    have hle : ∀ᶠ N in atTop,
        ‖mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N‖ ≤ bound N := by
      filter_upwards [hδ] with N hN
      have h1 : ‖c N * mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N‖
          = ‖c N‖ * ‖mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N‖ :=
        norm_mul _ _
      have hXnn : 0 ≤ ‖mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N‖ :=
        norm_nonneg _
      have h2 : δ * ‖mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N‖
          ≤ ‖c N‖ * ‖mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N‖ :=
        mul_le_mul_of_nonneg_right hN hXnn
      have h3 : ‖mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N‖
          ≤ ‖c N‖ * ‖mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N‖ / δ := by
        rw [le_div_iff₀ hδpos, mul_comm]
        exact h2
      have h4 : ‖c N‖ * ‖mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N‖ / δ
            = bound N := by
        simp only [bound]
        rw [h1]
      exact h3.trans h4.le
    exact squeeze_zero' (Filter.Eventually.of_forall (fun N => norm_nonneg _))
      hle hbound_tendsto
  have hXtendsto : Tendsto
      (fun N => mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N)
      atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hXnorm
  exact mpvOverlap_toTensor_basis_not_tendsto_zero Q hQ_unit k₀
    hQ_decay_offdiag hℓ_ne hQ_self_limit hXtendsto

/-- **Universally-quantified `hNoCancel` discharge.**

The form consumed by
`fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_sectorDecomp`.
Each scalar witness `c` of the eventual proportionality is assumed to
admit a positive lower bound (`hc_lower`), and the non-cancellation
conclusion then follows from `hNoCancel_single_seq`. -/
lemma hNoCancel_of_unitModulus_decay_c_norm_lower
    {P Q : SectorDecomposition d}
    (hQ_unit : ∀ k q, ‖Q.sectors.weight k q‖ = 1)
    (k₀ : Fin Q.basisCount)
    (hQ_decay_offdiag : ∀ k, k ≠ k₀ →
        Tendsto (fun N => mpvOverlap (d := d) (Q.basis k) (Q.basis k₀) N)
          atTop (nhds 0))
    {ℓ : ℂ} (hℓ_ne : ℓ ≠ 0)
    (hQ_self_limit :
        Tendsto (fun N => mpvOverlap (d := d) (Q.basis k₀) (Q.basis k₀) N)
          atTop (nhds ℓ))
    (hc_lower :
        ∀ c : ℕ → ℂ,
        (∀ᶠ N in atTop, ∀ σ : Fin N → Fin d,
          mpv P.toTensor σ = c N * mpv Q.toTensor σ) →
        ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N in atTop, δ ≤ ‖c N‖) :
    ∀ c : ℕ → ℂ,
        (∀ᶠ N in atTop, ∀ σ : Fin N → Fin d,
          mpv P.toTensor σ = c N * mpv Q.toTensor σ) →
        ¬ Tendsto
            (fun N => c N * mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N)
            atTop (nhds 0) := by
  intro c hProp
  exact hNoCancel_single_seq Q hQ_unit k₀ hQ_decay_offdiag hℓ_ne
    hQ_self_limit c (hc_lower c hProp)

end UnitModulusNonCancellation

section PerBlockProjectionContradiction

/-- **Right-block per-block projection contradiction.**

Source: arXiv:1606.00608, Theorem `thm1`, lines 1170--1192.

Specialization of
`fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_sectorDecomp`
with the load-bearing `hNoCancel` hypothesis discharged from four
analytic inputs: unit-modulus `Q`-sector weights, decay of `Q`
off-diagonal cross-overlaps, a nonzero `Q`-self-overlap limit, and a
lower bound on the proportionality scalar `‖c N‖`.

**Scope restriction (factored analytic discharge).**  The signature adds
four hypotheses absent from arXiv:1606.00608 Theorem `thm1`
(lines 1170--1192):

* `hP_unit`, `hQ_unit`: unit-modulus sector weights on `P` and `Q`.
  These match CPSV21 Definition 4.2, and both are explicit assumptions
  in this surface.
* `hQ_decay_offdiag`: BNT separation expressed as off-diagonal
  cross-overlap decay on `Q`.  Present in the source via the
  equal-MPV BNT structure.
* `hℓ_ne` + `hQ_self_limit`: the self-overlap on the fixed block tends
  to a nonzero limit.  Source: `HasNormalizedSelfOverlap` field of the
  canonical form.
* `hc_lower`: eventual lower bound on the proportionality scalar.
  Source: the dominant-adjusted scalar limit; in the strict-anti
  `IsCanonicalFormBNT` surface this follows from
  `exists_dominant_phase_adjusted_scalar_tendsto_one_*`, but the
  derivation is deferred to Plan C Objective B. -/
theorem fixed_right_all_overlaps_decay_false_paperFaithful
    (P Q : SectorDecomposition d)
    (hP_unit : ∀ j q, ‖P.sectors.weight j q‖ = 1)
    (hQ_unit : ∀ k q, ‖Q.sectors.weight k q‖ = 1)
    (hProp : EventuallyNonzeroProportionalMPV₂ P.toTensor Q.toTensor)
    (k₀ : Fin Q.basisCount)
    (hAllDecay_PtoQ : ∀ j : Fin P.basisCount,
        Tendsto (fun N => mpvOverlap (d := d) (P.basis j) (Q.basis k₀) N)
          atTop (nhds 0))
    (hQ_decay_offdiag : ∀ k : Fin Q.basisCount, k ≠ k₀ →
        Tendsto (fun N => mpvOverlap (d := d) (Q.basis k) (Q.basis k₀) N)
          atTop (nhds 0))
    {ℓ : ℂ} (hℓ_ne : ℓ ≠ 0)
    (hQ_self_limit :
        Tendsto (fun N => mpvOverlap (d := d) (Q.basis k₀) (Q.basis k₀) N)
          atTop (nhds ℓ))
    (hc_lower :
        ∀ c : ℕ → ℂ,
        (∀ᶠ N in atTop, ∀ σ : Fin N → Fin d,
          mpv P.toTensor σ = c N * mpv Q.toTensor σ) →
        ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N in atTop, δ ≤ ‖c N‖) :
    False :=
  fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_sectorDecomp
    P Q hP_unit hProp k₀ hAllDecay_PtoQ
    (hNoCancel_of_unitModulus_decay_c_norm_lower
      (P := P) (Q := Q) hQ_unit k₀ hQ_decay_offdiag hℓ_ne
      hQ_self_limit hc_lower)

/-- **Left-block per-block projection contradiction.**

Source: arXiv:1606.00608, Theorem `thm1`, lines 1182--1185.

Symmetric counterpart of
`fixed_right_all_overlaps_decay_false_paperFaithful`.  The proof reduces
to the right-block version after swapping the two families.

**Scope restriction (factored analytic discharge).**  The signature adds
four hypotheses absent from arXiv:1606.00608 Theorem `thm1`
(lines 1182--1185):

* `hP_unit`, `hQ_unit`: unit-modulus sector weights on `P` and `Q`.
  These match CPSV21 Definition 4.2, and both are explicit assumptions
  in this surface.
* `hP_decay_offdiag`: BNT separation expressed as off-diagonal
  cross-overlap decay on `P`.  Present in the source via the
  equal-MPV BNT structure.
* `hℓ_ne` + `hP_self_limit`: the self-overlap on the fixed block tends
  to a nonzero limit.  Source: `HasNormalizedSelfOverlap` field of the
  canonical form.
* `hc_lower`: eventual lower bound on the proportionality scalar.
  Source: the dominant-adjusted scalar limit; in the strict-anti
  `IsCanonicalFormBNT` surface this follows from
  `exists_dominant_phase_adjusted_scalar_tendsto_one_*`, but the
  derivation is deferred to Plan C Objective B. -/
theorem fixed_left_all_overlaps_decay_false_paperFaithful
    (P Q : SectorDecomposition d)
    (hP_unit : ∀ j q, ‖P.sectors.weight j q‖ = 1)
    (hQ_unit : ∀ k q, ‖Q.sectors.weight k q‖ = 1)
    (hProp : EventuallyNonzeroProportionalMPV₂ P.toTensor Q.toTensor)
    (j₀ : Fin P.basisCount)
    (hAllDecay_QtoP : ∀ k : Fin Q.basisCount,
        Tendsto (fun N => mpvOverlap (d := d) (P.basis j₀) (Q.basis k) N)
          atTop (nhds 0))
    (hP_decay_offdiag : ∀ j : Fin P.basisCount, j ≠ j₀ →
        Tendsto (fun N => mpvOverlap (d := d) (P.basis j) (P.basis j₀) N)
          atTop (nhds 0))
    {ℓ : ℂ} (hℓ_ne : ℓ ≠ 0)
    (hP_self_limit :
        Tendsto (fun N => mpvOverlap (d := d) (P.basis j₀) (P.basis j₀) N)
          atTop (nhds ℓ))
    (hc_lower :
        ∀ c : ℕ → ℂ,
        (∀ᶠ N in atTop, ∀ σ : Fin N → Fin d,
          mpv Q.toTensor σ = c N * mpv P.toTensor σ) →
        ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N in atTop, δ ≤ ‖c N‖) :
    False :=
  fixed_left_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_sectorDecomp
    P Q hQ_unit hProp j₀ hAllDecay_QtoP
    (hNoCancel_of_unitModulus_decay_c_norm_lower
      (P := Q) (Q := P) hP_unit j₀ hP_decay_offdiag hℓ_ne
      hP_self_limit hc_lower)

set_option linter.style.longLine false in
/-- **Two-layer right-block per-block projection contradiction.**

Two-layer counterpart of `fixed_right_all_overlaps_decay_false_paperFaithful`
on the `IsBNTCanonicalFormSD` surface.  The two-layer canonical-form
hypothesis on `P` supplies the uniform coefficient bound
`‖P.coeff N j‖ ≤ copies j` via
`SectorDecomposition.norm_coeff_le_copies_of_IsBNTCanonicalFormSD`;
the canonical-form hypothesis on `Q` is bundled in the signature for
the eventual analytic discharge of `hNoCancel` (currently abstract).

In contrast to `fixed_right_all_overlaps_decay_false_paperFaithful`,
the analytic non-cancellation conclusion is **not** discharged here:
the `hNoCancel` hypothesis is consumed in the same shape as in
`fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_sectorDecomp_twoLayer`.
The downstream analytic argument that produces `hNoCancel` for the
non-dominant `k₀` branch on the `IsBNTCanonicalFormSD` surface lives
outside this module. -/
theorem fixed_right_all_overlaps_decay_false_paperFaithful_twoLayer
    (P Q : SectorDecomposition d)
    (hP : IsBNTCanonicalFormSD P)
    (_hQ : IsBNTCanonicalFormSD Q)
    (hProp : EventuallyNonzeroProportionalMPV₂ P.toTensor Q.toTensor)
    (k₀ : Fin Q.basisCount)
    (hAllDecay_PtoQ : ∀ j : Fin P.basisCount,
        Tendsto (fun N => mpvOverlap (d := d) (P.basis j) (Q.basis k₀) N)
          atTop (nhds 0))
    (hNoCancel : ∀ c : ℕ → ℂ,
        (∀ᶠ N in atTop, ∀ σ : Fin N → Fin d,
          mpv P.toTensor σ = c N * mpv Q.toTensor σ) →
        ¬ Tendsto
            (fun N => c N * mpvOverlap (d := d) Q.toTensor (Q.basis k₀) N)
            atTop (nhds 0)) :
    False :=
  fixed_right_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_sectorDecomp_twoLayer
    P Q hP hProp k₀ hAllDecay_PtoQ hNoCancel

set_option linter.style.longLine false in
/-- **Two-layer left-block per-block projection contradiction.**

Symmetric counterpart of `fixed_right_all_overlaps_decay_false_paperFaithful_twoLayer`
fixing a `P`-block `j₀` instead of a `Q`-block.  Reduces to the
right-block two-layer version after swapping `P` and `Q`. -/
theorem fixed_left_all_overlaps_decay_false_paperFaithful_twoLayer
    (P Q : SectorDecomposition d)
    (_hP : IsBNTCanonicalFormSD P)
    (hQ : IsBNTCanonicalFormSD Q)
    (hProp : EventuallyNonzeroProportionalMPV₂ P.toTensor Q.toTensor)
    (j₀ : Fin P.basisCount)
    (hAllDecay_QtoP : ∀ k : Fin Q.basisCount,
        Tendsto (fun N => mpvOverlap (d := d) (P.basis j₀) (Q.basis k) N)
          atTop (nhds 0))
    (hNoCancel : ∀ c : ℕ → ℂ,
        (∀ᶠ N in atTop, ∀ σ : Fin N → Fin d,
          mpv Q.toTensor σ = c N * mpv P.toTensor σ) →
        ¬ Tendsto
            (fun N => c N * mpvOverlap (d := d) P.toTensor (P.basis j₀) N)
            atTop (nhds 0)) :
    False :=
  fixed_left_all_overlaps_decay_false_of_eventuallyNonzeroProportionalMPV₂_sectorDecomp_twoLayer
    P Q hQ hProp j₀ hAllDecay_QtoP hNoCancel

end PerBlockProjectionContradiction

end MPSTensor
