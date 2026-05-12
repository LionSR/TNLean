/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.Full.NondecayingPartnerUnique

/-!
# Leading non-decaying partners for proportional BNT families

This module records the first partner-identification step in the CPSV16
proportional fundamental theorem argument.

## References

* Cirac, Pérez-García, Schuch, Verstraete, *Matrix Product Density Operators:
  Renormalization Fixed Points and Boundary Theories*, arXiv:1606.00608 (2017),
  Theorem II.1, lines 1170--1192.
-/

open scoped Matrix BigOperators InnerProductSpace
open Filter

namespace MPSTensor

section LeadingPartner

/-- **The leading right block can only have the leading left block as non-decaying partner.**

Source context: arXiv:1606.00608, Theorem II.1, line 1182. Before peeling
the dominant pair, the source argument first identifies a non-decaying partner
of the fixed leading block. In the restricted one-copy-per-sector BNT setting,
strict ordering of the weights forces such a partner for the leading `B`-block
to be the leading `A`-block.

**Scope restriction (one-copy-per-sector):** The local hypotheses
`IsCanonicalFormBNT` are the already-grouped one-copy-per-sector canonical
forms. CPSV16 allows BNT multiplicities inside a sector. This restriction is
documented in `docs/paper-gaps/ft_one_copy_scope_restriction.tex`. -/
lemma leading_right_nondecaying_partner_eq_leading_left_of_eventuallyNonzeroProportionalMPV₂_CFBNT
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hA : IsCanonicalFormBNT μA A)
    (hB : IsCanonicalFormBNT μB B)
    (hrA : rA ≠ 0) (hrB : rB ≠ 0)
    (hProp : EventuallyNonzeroProportionalMPV₂
      (toTensorFromBlocks μA A) (toTensorFromBlocks μB B))
    (j₁ : Fin rA)
    (hnd : ¬ Tendsto
      (fun N => mpvOverlap (d := d) (A j₁) (B ⟨0, Nat.pos_of_ne_zero hrB⟩) N)
      atTop (nhds 0)) :
    j₁ = ⟨0, Nat.pos_of_ne_zero hrA⟩ := by
  classical
  let a0 : Fin rA := ⟨0, Nat.pos_of_ne_zero hrA⟩
  let b0 : Fin rB := ⟨0, Nat.pos_of_ne_zero hrB⟩
  by_contra hj₁_ne
  have hA_self : ∀ j : Fin rA,
      Tendsto (fun N => mpvOverlap (d := d) (A j) (A j) N) atTop (nhds 1) :=
    hA.toHasNormalizedSelfOverlap.overlap_tendsto_one
  have hB_self : ∀ k : Fin rB,
      Tendsto (fun N => mpvOverlap (d := d) (B k) (B k) N) atTop (nhds 1) :=
    hB.toHasNormalizedSelfOverlap.overlap_tendsto_one
  have hB_inner : ∀ k : Fin rB,
      Tendsto (fun N => mpvInner (d := d) (B k) (B k) N) atTop (nhds 1) :=
    fun k => tendsto_inner_one (B k) (hB_self k)
  have hB_cross_inner : ∀ k l : Fin rB, k ≠ l →
      Tendsto (fun N => mpvInner (d := d) (B k) (B l) N) atTop (nhds 0) :=
    fun k l hkl => tendsto_inner_zero (B k) (B l) (hB.cross_overlap_tendsto_zero k l hkl)
  have hμA_ne : μA a0 ≠ 0 := hA.toHasStrictOrderedNonzeroWeights.mu_ne_zero a0
  have hμB_ne : μB b0 ≠ 0 := hB.toHasStrictOrderedNonzeroWeights.mu_ne_zero b0
  obtain ⟨c, _hc, hState, hAdjusted⟩ :=
    exists_dominant_adjusted_scalar_tendsto_norm_one_of_eventuallyNonzeroProportionalMPV₂_CFBNT
      A B hA hB hrA hrB hProp
  have hWeightedInner :
      ∀ᶠ N in atTop,
        (∑ j : Fin rA, (μA j) ^ N * mpvInner (d := d) (B b0) (A j) N) =
          c N * (∑ k : Fin rB, (μB k) ^ N * mpvInner (d := d) (B b0) (B k) N) :=
    eventually_weighted_mpvInner_eq_mul_sequence_of_eventually_weighted_mpvState_eq_smul_sequence
      A B c hState (B b0)
  have hNormInner :
      ∀ᶠ N in atTop,
        (μA a0 ^ N)⁻¹ *
            (∑ j : Fin rA, (μA j) ^ N * mpvInner (d := d) (B b0) (A j) N) =
          (c N * (μB b0 / μA a0) ^ N) *
            ((μB b0 ^ N)⁻¹ *
              (∑ k : Fin rB, (μB k) ^ N * mpvInner (d := d) (B b0) (B k) N)) := by
    refine hWeightedInner.mono ?_
    intro N hN
    let S : ℂ := ∑ k : Fin rB, (μB k) ^ N * mpvInner (d := d) (B b0) (B k) N
    rw [hN]
    change (μA a0 ^ N)⁻¹ * (c N * S) =
      (c N * (μB b0 / μA a0) ^ N) * ((μB b0 ^ N)⁻¹ * S)
    calc
      (μA a0 ^ N)⁻¹ * (c N * S) = ((μA a0 ^ N)⁻¹ * c N) * S := by ring
      _ = ((c N * (μB b0 / μA a0) ^ N) * (μB b0 ^ N)⁻¹) * S := by
        rw [adjusted_scalar_factor_eq (c N) (μA a0) (μB b0) N hμA_ne hμB_ne]
      _ = (c N * (μB b0 / μA a0) ^ N) * ((μB b0 ^ N)⁻¹ * S) := by ring
  have huniq : ∀ j : Fin rA, j ≠ j₁ →
      Tendsto (fun N => mpvOverlap (d := d) (A j) (B b0) N) atTop (nhds 0) := by
    intro j hj
    by_contra hnot
    exact hj (unique_left_nondecaying_overlap_partner_CFBNT A B hA hB b0 j j₁ hnot hnd)
  have hLHS_zero :
      Tendsto
        (fun N : ℕ =>
          (μA a0 ^ N)⁻¹ *
            (∑ j : Fin rA, (μA j) ^ N * mpvInner (d := d) (B b0) (A j) N))
        atTop (nhds (0 : ℂ)) := by
    have hsplit : ∀ N,
        (μA a0 ^ N)⁻¹ *
            (∑ j : Fin rA, (μA j) ^ N * mpvInner (d := d) (B b0) (A j) N) =
          (μA a0 ^ N)⁻¹ *
              ((μA j₁) ^ N * mpvInner (d := d) (B b0) (A j₁) N) +
            (μA a0 ^ N)⁻¹ *
              (∑ j ∈ Finset.univ.erase j₁,
                (μA j) ^ N * mpvInner (d := d) (B b0) (A j) N) := by
      intro N
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₁), mul_add]
    simp_rw [hsplit]
    have h_j₁ :
        Tendsto
          (fun N : ℕ =>
            (μA a0 ^ N)⁻¹ *
              ((μA j₁) ^ N * mpvInner (d := d) (B b0) (A j₁) N))
          atTop (nhds (0 : ℂ)) := by
      have hRatio : ‖μA j₁ / μA a0‖ < 1 := by
        rw [norm_div]
        exact (div_lt_one (norm_pos_iff.mpr hμA_ne)).mpr
          (hA.mu_strict_anti (by
            simp only [a0, Fin.lt_def]
            exact Nat.pos_of_ne_zero (fun h => hj₁_ne (Fin.ext h))))
      convert geometric_mul_inner_tendsto_zero (μA j₁ / μA a0) (B b0) (A j₁)
        hRatio (hB_self b0) (hA_self j₁) using 1
      ext N
      rw [div_pow]
      field_simp [pow_ne_zero N hμA_ne]
    have h_rest :
        Tendsto
          (fun N : ℕ =>
            (μA a0 ^ N)⁻¹ *
              (∑ j ∈ Finset.univ.erase j₁,
                (μA j) ^ N * mpvInner (d := d) (B b0) (A j) N))
          atTop (nhds (0 : ℂ)) := by
      have hsum :
          Tendsto
            (fun N : ℕ =>
              ∑ j ∈ Finset.univ.erase j₁,
                (μA j / μA a0) ^ N * mpvInner (d := d) (B b0) (A j) N)
            atTop (nhds (0 : ℂ)) := by
        have := tendsto_finset_sum (Finset.univ.erase j₁)
          (fun (j : Fin rA) (hj : j ∈ Finset.univ.erase j₁) =>
            show Tendsto _ atTop (nhds (0 : ℂ)) from
            bounded_mul_tendsto_zero (μA j / μA a0)
              (fun N => mpvInner (d := d) (B b0) (A j) N) (by
                rw [norm_div]
                exact (div_le_one (norm_pos_iff.mpr hμA_ne)).mpr
                  (hA.toIsCanonicalForm.mu_antitone
                    (show a0 ≤ j from Fin.mk_le_mk.mpr (Nat.zero_le _))))
              (tendsto_inner_zero_swap (d := d) (A j) (B b0)
                (huniq j (Finset.ne_of_mem_erase hj))))
        simpa using this
      convert hsum using 1
      ext N
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [div_pow]
      field_simp [pow_ne_zero N hμA_ne]
    convert h_j₁.add h_rest using 1
    simp
  have hRHS_norm_one :
      Tendsto
        (fun N : ℕ =>
          ‖(c N * (μB b0 / μA a0) ^ N) *
            ((μB b0 ^ N)⁻¹ *
              (∑ k : Fin rB, (μB k) ^ N * mpvInner (d := d) (B b0) (B k) N))‖)
        atTop (nhds (1 : ℝ)) := by
    have hB_proj :
        Tendsto
          (fun N : ℕ =>
            (μB b0 ^ N)⁻¹ *
              (∑ k : Fin rB, (μB k) ^ N * mpvInner (d := d) (B b0) (B k) N))
          atTop (nhds (1 : ℂ)) := by
      have hsum :
          Tendsto
            (fun N : ℕ =>
              ∑ k : Fin rB, (μB k / μB b0) ^ N *
                mpvInner (d := d) (B b0) (B k) N)
            atTop (nhds (1 : ℂ)) :=
        sum_tendsto_one_of_diag (hμ0 := hμB_ne) (j0 := b0) rfl (hB_inner b0)
          (fun k hk => by
            rw [norm_div]
            exact (div_lt_one (norm_pos_iff.mpr hμB_ne)).mpr
              (hB.mu_strict_anti (by
                simp only [b0, Fin.lt_def]
                exact Nat.pos_of_ne_zero (fun h => hk (Fin.ext h)))))
          (fun k hk => hB_cross_inner b0 k hk.symm)
      convert hsum using 1
      ext N
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [div_pow]
      field_simp [pow_ne_zero N hμB_ne]
    simpa [norm_mul] using hAdjusted.mul hB_proj.norm
  have hLHS_norm_zero :
      Tendsto
        (fun N : ℕ =>
          ‖(μA a0 ^ N)⁻¹ *
            (∑ j : Fin rA, (μA j) ^ N * mpvInner (d := d) (B b0) (A j) N)‖)
        atTop (nhds (0 : ℝ)) := by
    simpa using hLHS_zero.norm
  have hRHS_norm_zero :
      Tendsto
        (fun N : ℕ =>
          ‖(c N * (μB b0 / μA a0) ^ N) *
            ((μB b0 ^ N)⁻¹ *
              (∑ k : Fin rB, (μB k) ^ N * mpvInner (d := d) (B b0) (B k) N))‖)
        atTop (nhds (0 : ℝ)) := by
    refine Tendsto.congr' ?_ hLHS_norm_zero
    filter_upwards [hNormInner] with N hN
    rw [hN]
  exact zero_ne_one (tendsto_nhds_unique hRHS_norm_zero hRHS_norm_one)

end LeadingPartner

end MPSTensor
