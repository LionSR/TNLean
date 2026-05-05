/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.Full.Helpers

/-!
# Dominant-weight comparison for the full BNT theorem

This module contains the dominant-weight norm comparison used by
`exists_nondecaying_overlap_of_sameMPV₂_CFBNT`.  It is split out from the main
non-decaying-overlap induction so that the induction file only carries the recursive
matching argument.

## Main statements

* `dominant_weight_norm_eq_of_sameMPV₂_CFBNT`: equality of the largest BNT weight norms
  for two equal-MPV BNT families.

## References

* Cirac, Pérez-García, Schuch, Verstraete, *Matrix product states and projected entangled
  pair states: Concepts, symmetries, theorems*, Rev. Mod. Phys. 93 (2021), arXiv:2011.12127.
* Cirac, Pérez-García, Schuch, Verstraete, *Fundamental Theorems for PEPS*,
  arXiv:1606.00608 (2017).

## Tags

matrix product states, fundamental theorem, BNT, dominant weights
-/

open scoped Matrix BigOperators
open Filter

namespace MPSTensor

section HeteroEqualCase

/-- Dominant BNT block weights have equal norms for equal total MPVs. -/
lemma dominant_weight_norm_eq_of_sameMPV₂_CFBNT
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hA : IsCanonicalFormBNT μA A)
    (hB : IsCanonicalFormBNT μB B)
    (hrA : rA ≠ 0) (hrB : rB ≠ 0)
    (hSumState : ∀ N : ℕ,
      ∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N =
        ∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N)
    (hA_self : ∀ k, Tendsto (fun N => mpvOverlap (d := d) (A k) (A k) N) atTop (nhds 1))
    (hB_self : ∀ k, Tendsto (fun N => mpvOverlap (d := d) (B k) (B k) N) atTop (nhds 1))
    (hA_cross : ∀ j k, j ≠ k →
      Tendsto (fun N => mpvOverlap (d := d) (A j) (A k) N) atTop (nhds 0))
    (hB_cross : ∀ j k, j ≠ k →
      Tendsto (fun N => mpvOverlap (d := d) (B j) (B k) N) atTop (nhds 0)) :
    ‖μA ⟨0, Nat.pos_of_ne_zero hrA⟩‖ = ‖μB ⟨0, Nat.pos_of_ne_zero hrB⟩‖ := by
  have hrA_pos : 0 < rA := Nat.pos_of_ne_zero hrA
  have hrB_pos : 0 < rB := Nat.pos_of_ne_zero hrB
  have inner_identity : ∀ {D : ℕ} (X : MPSTensor d D) (N : ℕ),
      ∑ j : Fin rA, (μA j) ^ N * mpvInner (d := d) X (A j) N =
        ∑ k : Fin rB, (μB k) ^ N * mpvInner (d := d) X (B k) N := by
    intro D X N
    simp only [mpvInner]
    have h := congr_arg (fun v => @inner ℂ _ _ (mpvState (d := d) X N) v) (hSumState N)
    simp only [inner_sum, inner_smul_right] at h
    exact h
  have hA_inner_diag : ∀ j : Fin rA,
      Tendsto (fun N => mpvInner (d := d) (A j) (A j) N) atTop (nhds 1) :=
    fun j => tendsto_inner_one (A j) (hA_self j)
  have hA_inner_off : ∀ i j : Fin rA, i ≠ j →
      Tendsto (fun N => mpvInner (d := d) (A i) (A j) N) atTop (nhds 0) :=
    fun i j hij => tendsto_inner_zero (A i) (A j) (hA_cross i j hij)
  have hB_inner_diag : ∀ k : Fin rB,
      Tendsto (fun N => mpvInner (d := d) (B k) (B k) N) atTop (nhds 1) :=
    fun k => tendsto_inner_one (B k) (hB_self k)
  have hB_inner_off : ∀ i j : Fin rB, i ≠ j →
      Tendsto (fun N => mpvInner (d := d) (B i) (B j) N) atTop (nhds 0) :=
    fun i j hij => tendsto_inner_zero (B i) (B j) (hB_cross i j hij)
  have hμA_ne : μA ⟨0, hrA_pos⟩ ≠ 0 := hA.toHasStrictOrderedNonzeroWeights.mu_ne_zero _
  have hμB_ne : μB ⟨0, hrB_pos⟩ ≠ 0 := hB.toHasStrictOrderedNonzeroWeights.mu_ne_zero _
  have normalized_identity :
      ∀ {D : ℕ} (X : MPSTensor d D) (c : ℂ) (hc : c ≠ 0) (N : ℕ),
      ∑ j : Fin rA, (μA j / c) ^ N * mpvInner (d := d) X (A j) N =
        ∑ k : Fin rB, (μB k / c) ^ N * mpvInner (d := d) X (B k) N := by
    intro D X c hc N
    have h := inner_identity X N
    have hcN : c ^ N ≠ 0 := pow_ne_zero N hc
    simp only [div_pow, div_mul_eq_mul_div]
    rw [← Finset.sum_div, ← Finset.sum_div]
    exact congr_arg (· / c ^ N) h
  have hμA_le : ∀ j : Fin rA, ‖μA j‖ ≤ ‖μA ⟨0, hrA_pos⟩‖ := by
    intro j
    exact hA.toIsCanonicalForm.mu_antitone
      (show (⟨0, hrA_pos⟩ : Fin rA) ≤ j from Fin.mk_le_mk.mpr (Nat.zero_le _))
  have hμB_le : ∀ k : Fin rB, ‖μB k‖ ≤ ‖μB ⟨0, hrB_pos⟩‖ := by
    intro k
    exact hB.toIsCanonicalForm.mu_antitone
      (show (⟨0, hrB_pos⟩ : Fin rB) ≤ k from Fin.mk_le_mk.mpr (Nat.zero_le _))
  by_contra hne
  rcases lt_or_gt_of_ne hne with h_lt | h_gt
  · have h_eq := normalized_identity (B ⟨0, hrB_pos⟩) (μB ⟨0, hrB_pos⟩) hμB_ne
    have hLHS : Tendsto (fun N => ∑ j, (μA j / μB ⟨0, hrB_pos⟩) ^ N *
        mpvInner (d := d) (B ⟨0, hrB_pos⟩) (A j) N) atTop (nhds 0) := by
      have := tendsto_finset_sum (Finset.univ : Finset (Fin rA))
        (fun (j : Fin rA) _ => show Tendsto (fun N => (μA j / μB ⟨0, hrB_pos⟩) ^ N *
          mpvInner (d := d) (B ⟨0, hrB_pos⟩) (A j) N) atTop (nhds (0 : ℂ)) from ?_)
      · simpa using this
      have hratio : ‖μA j / μB ⟨0, hrB_pos⟩‖ < 1 := by
        rw [norm_div]
        exact (div_lt_one (norm_pos_iff.mpr hμB_ne)).mpr
          (lt_of_le_of_lt (hμA_le j) h_lt)
      exact geometric_mul_inner_tendsto_zero _ _ _ hratio (hB_self _) (hA_self j)
    have hRHS : Tendsto (fun N => ∑ k, (μB k / μB ⟨0, hrB_pos⟩) ^ N *
        mpvInner (d := d) (B ⟨0, hrB_pos⟩) (B k) N) atTop (nhds 1) :=
      sum_tendsto_one_of_diag (hμ0 := hμB_ne) (j0 := ⟨0, hrB_pos⟩) rfl (hB_inner_diag _)
        (fun k hk => by
          rw [norm_div]
          exact (div_lt_one (norm_pos_iff.mpr hμB_ne)).mpr
            (hB.mu_strict_anti (by
              simp only [Fin.lt_def]
              exact Nat.pos_of_ne_zero (by
                intro h
                exact hk (Fin.ext h)))))
        (fun k hk => hB_inner_off _ _ hk.symm)
    exact zero_ne_one (tendsto_nhds_unique (hLHS.congr (fun N => h_eq N)) hRHS)
  · have h_eq := normalized_identity (A ⟨0, hrA_pos⟩) (μA ⟨0, hrA_pos⟩) hμA_ne
    have hLHS : Tendsto (fun N => ∑ j, (μA j / μA ⟨0, hrA_pos⟩) ^ N *
        mpvInner (d := d) (A ⟨0, hrA_pos⟩) (A j) N) atTop (nhds 1) :=
      sum_tendsto_one_of_diag (hμ0 := hμA_ne) (j0 := ⟨0, hrA_pos⟩) rfl (hA_inner_diag _)
        (fun j hj => by
          rw [norm_div]
          exact (div_lt_one (norm_pos_iff.mpr hμA_ne)).mpr
            (hA.mu_strict_anti (by
              simp only [Fin.lt_def]
              exact Nat.pos_of_ne_zero (by
                intro h
                exact hj (Fin.ext h)))))
        (fun j hj => hA_inner_off _ _ hj.symm)
    have hRHS : Tendsto (fun N => ∑ k : Fin rB, (μB k / μA ⟨0, hrA_pos⟩) ^ N *
        mpvInner (d := d) (A ⟨0, hrA_pos⟩) (B k) N) atTop (nhds (0 : ℂ)) := by
      have hterm : ∀ k : Fin rB,
          Tendsto (fun N => (μB k / μA ⟨0, hrA_pos⟩) ^ N *
            mpvInner (d := d) (A ⟨0, hrA_pos⟩) (B k) N) atTop (nhds (0 : ℂ)) := by
        intro k
        have hratio : ‖μB k / μA ⟨0, hrA_pos⟩‖ < 1 := by
          rw [norm_div]
          exact (div_lt_one (norm_pos_iff.mpr hμA_ne)).mpr
            (lt_of_le_of_lt (hμB_le k) h_gt)
        exact geometric_mul_inner_tendsto_zero _ _ _ hratio (hA_self _) (hB_self k)
      have := tendsto_finset_sum (Finset.univ : Finset (Fin rB))
        (fun (k : Fin rB) _ => hterm k)
      simpa using this
    exact one_ne_zero (tendsto_nhds_unique (hLHS.congr (fun N => h_eq N)) hRHS)

end HeteroEqualCase

end MPSTensor
