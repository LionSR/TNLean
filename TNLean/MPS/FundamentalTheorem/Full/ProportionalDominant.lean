/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.Full.ProportionalExpansion

/-!
# Dominant projected contradiction for proportional BNT families

This module contains the dominant-block projection contradiction used in the
proportional non-decaying-overlap step of the fundamental theorem.

## References

* Cirac, Pérez-García, Schuch, Verstraete, *Fundamental Theorems for PEPS*,
  arXiv:1606.00608 (2017), Theorem `thm1`, lines 1170--1192.
-/

open scoped Matrix BigOperators InnerProductSpace
open Filter

namespace MPSTensor

section ProportionalDominant

/-- **Dominant-block projection contradiction for proportional BNT families.**

Source: arXiv:1606.00608, Theorem `thm1`, lines 1170--1192. If the normalized
proportional projection identity has an adjusted scalar whose modulus tends to
one, then the dominant block on either side cannot have all cross-overlaps
tending to zero. This is the dominant case of the CPSV16 line 1182 argument. -/
lemma dominant_projection_contradictions_of_normalized_proportional_inner
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hA : IsCanonicalFormBNT μA A)
    (hB : IsCanonicalFormBNT μB B)
    (hrA : rA ≠ 0) (hrB : rB ≠ 0)
    (c : ℕ → ℂ)
    (hNormalizedInner :
      ∀ {D : ℕ} (X : MPSTensor d D) (μ ν : ℂ),
        μ ≠ 0 → ν ≠ 0 → ∀ N : ℕ,
          (μ ^ N)⁻¹ *
              (∑ j : Fin rA, (μA j) ^ N * mpvInner (d := d) X (A j) N) =
            (c N * (ν / μ) ^ N) *
              ((ν ^ N)⁻¹ *
                (∑ k : Fin rB, (μB k) ^ N * mpvInner (d := d) X (B k) N)))
    (hAdjustedScalar_dom :
      Tendsto
        (fun N : ℕ =>
          ‖c N * (μB ⟨0, Nat.pos_of_ne_zero hrB⟩ /
            μA ⟨0, Nat.pos_of_ne_zero hrA⟩) ^ N‖)
        atTop (nhds (1 : ℝ)))
    (hA_self : ∀ j : Fin rA,
      Tendsto (fun N => mpvOverlap (d := d) (A j) (A j) N) atTop (nhds 1))
    (hB_self : ∀ k : Fin rB,
      Tendsto (fun N => mpvOverlap (d := d) (B k) (B k) N) atTop (nhds 1))
    (hA_cross : ∀ j k : Fin rA, j ≠ k →
      Tendsto (fun N => mpvOverlap (d := d) (A j) (A k) N) atTop (nhds 0))
    (hB_cross : ∀ j k : Fin rB, j ≠ k →
      Tendsto (fun N => mpvOverlap (d := d) (B j) (B k) N) atTop (nhds 0)) :
    ((∀ j : Fin rA,
        Tendsto
          (fun N => mpvOverlap (d := d) (A j)
            (B ⟨0, Nat.pos_of_ne_zero hrB⟩) N)
          atTop (nhds 0)) → False) ∧
    ((∀ k : Fin rB,
        Tendsto
          (fun N => mpvOverlap (d := d)
            (A ⟨0, Nat.pos_of_ne_zero hrA⟩) (B k) N)
          atTop (nhds 0)) → False) := by
  let a0 : Fin rA := ⟨0, Nat.pos_of_ne_zero hrA⟩
  let b0 : Fin rB := ⟨0, Nat.pos_of_ne_zero hrB⟩
  have hμA_ne : μA a0 ≠ 0 := hA.toHasStrictOrderedNonzeroWeights.mu_ne_zero a0
  have hμB_ne : μB b0 ≠ 0 := hB.toHasStrictOrderedNonzeroWeights.mu_ne_zero b0
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
  have hAdjustedScalar :
      Tendsto (fun N : ℕ => ‖c N * (μB b0 / μA a0) ^ N‖) atTop
        (nhds (1 : ℝ)) := by
    simpa [a0, b0] using hAdjustedScalar_dom
  have hDominantB_contra :
      (∀ j : Fin rA, Tendsto (fun N => mpvOverlap (d := d) (A j) (B b0) N)
        atTop (nhds 0)) → False := by
    intro hall
    have hall_inner : ∀ j : Fin rA,
        Tendsto (fun N => mpvInner (d := d) (B b0) (A j) N) atTop (nhds 0) :=
      fun j => tendsto_inner_zero_swap (d := d) (A j) (B b0) (hall j)
    have hA_proj_sum :
        Tendsto
          (fun N : ℕ =>
            ∑ j : Fin rA, (μA j / μA a0) ^ N *
              mpvInner (d := d) (B b0) (A j) N)
          atTop (nhds 0) := by
      have := tendsto_finset_sum (Finset.univ : Finset (Fin rA))
        (fun (j : Fin rA) _ => show
          Tendsto
            (fun N : ℕ =>
              (μA j / μA a0) ^ N * mpvInner (d := d) (B b0) (A j) N)
            atTop (nhds (0 : ℂ)) from
          bounded_mul_tendsto_zero _ _ (by
            rw [norm_div]
            exact (div_le_one (norm_pos_iff.mpr hμA_ne)).mpr
              (hA.toIsCanonicalForm.mu_antitone
                (show a0 ≤ j from Fin.mk_le_mk.mpr (Nat.zero_le _))))
            (hall_inner j))
      simpa using this
    have hA_proj :
        Tendsto
          (fun N : ℕ =>
            (μA a0 ^ N)⁻¹ *
              (∑ j : Fin rA, (μA j) ^ N * mpvInner (d := d) (B b0) (A j) N))
          atTop (nhds 0) := by
      convert hA_proj_sum using 1
      ext N
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [div_pow]
      field_simp [pow_ne_zero N hμA_ne]
    have hB_proj :
        Tendsto
          (fun N : ℕ =>
            (μB b0 ^ N)⁻¹ *
              (∑ k : Fin rB, (μB k) ^ N * mpvInner (d := d) (B b0) (B k) N))
          atTop (nhds 1) := by
      have hsum :
          Tendsto
            (fun N : ℕ =>
              ∑ k : Fin rB, (μB k / μB b0) ^ N *
                mpvInner (d := d) (B b0) (B k) N)
            atTop (nhds 1) :=
        sum_tendsto_one_of_diag (hμ0 := hμB_ne) (j0 := b0) rfl (hB_inner_diag b0)
          (fun k hk => by
            rw [norm_div]
            exact (div_lt_one (norm_pos_iff.mpr hμB_ne)).mpr
              (hB.mu_strict_anti (by
                simp only [b0, Fin.lt_def]
                exact Nat.pos_of_ne_zero (fun h => hk (Fin.ext h)))))
          (fun k hk => hB_inner_off b0 k hk.symm)
      convert hsum using 1
      ext N
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [div_pow]
      field_simp [pow_ne_zero N hμB_ne]
    have hRHS_norm_one :
        Tendsto
          (fun N : ℕ =>
            ‖(c N * (μB b0 / μA a0) ^ N) *
              ((μB b0 ^ N)⁻¹ *
                (∑ k : Fin rB, (μB k) ^ N *
                  mpvInner (d := d) (B b0) (B k) N))‖)
          atTop (nhds (1 : ℝ)) := by
      have hmul := hAdjustedScalar.mul hB_proj.norm
      simpa [norm_mul] using hmul
    have hRHS_norm_zero :
        Tendsto
          (fun N : ℕ =>
            ‖(c N * (μB b0 / μA a0) ^ N) *
              ((μB b0 ^ N)⁻¹ *
                (∑ k : Fin rB, (μB k) ^ N *
                  mpvInner (d := d) (B b0) (B k) N))‖)
          atTop (nhds (0 : ℝ)) := by
      have hnorm := hA_proj.norm
      have hnorm_zero :
          Tendsto
            (fun N : ℕ =>
              ‖(μA a0 ^ N)⁻¹ *
                (∑ j : Fin rA, (μA j) ^ N *
                  mpvInner (d := d) (B b0) (A j) N)‖)
            atTop (nhds (0 : ℝ)) := by
        simpa using hnorm
      refine hnorm_zero.congr (fun N => ?_)
      rw [hNormalizedInner (B b0) (μA a0) (μB b0) hμA_ne hμB_ne N]
    exact zero_ne_one (tendsto_nhds_unique hRHS_norm_zero hRHS_norm_one)
  have hDominantA_contra :
      (∀ k : Fin rB, Tendsto (fun N => mpvOverlap (d := d) (A a0) (B k) N)
        atTop (nhds 0)) → False := by
    intro hall
    have hall_inner : ∀ k : Fin rB,
        Tendsto (fun N => mpvInner (d := d) (A a0) (B k) N) atTop (nhds 0) :=
      fun k => tendsto_inner_zero (A a0) (B k) (hall k)
    have hA_proj :
        Tendsto
          (fun N : ℕ =>
            (μA a0 ^ N)⁻¹ *
              (∑ j : Fin rA, (μA j) ^ N * mpvInner (d := d) (A a0) (A j) N))
          atTop (nhds 1) := by
      have hsum :
          Tendsto
            (fun N : ℕ =>
              ∑ j : Fin rA, (μA j / μA a0) ^ N *
                mpvInner (d := d) (A a0) (A j) N)
            atTop (nhds 1) :=
        sum_tendsto_one_of_diag (hμ0 := hμA_ne) (j0 := a0) rfl (hA_inner_diag a0)
          (fun j hj => by
            rw [norm_div]
            exact (div_lt_one (norm_pos_iff.mpr hμA_ne)).mpr
              (hA.mu_strict_anti (by
                simp only [a0, Fin.lt_def]
                exact Nat.pos_of_ne_zero (fun h => hj (Fin.ext h)))))
          (fun j hj => hA_inner_off a0 j hj.symm)
      convert hsum using 1
      ext N
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [div_pow]
      field_simp [pow_ne_zero N hμA_ne]
    have hB_proj_sum :
        Tendsto
          (fun N : ℕ =>
            ∑ k : Fin rB, (μB k / μB b0) ^ N *
              mpvInner (d := d) (A a0) (B k) N)
          atTop (nhds 0) := by
      have := tendsto_finset_sum (Finset.univ : Finset (Fin rB))
        (fun (k : Fin rB) _ => show
          Tendsto
            (fun N : ℕ =>
              (μB k / μB b0) ^ N * mpvInner (d := d) (A a0) (B k) N)
            atTop (nhds (0 : ℂ)) from
          bounded_mul_tendsto_zero _ _ (by
            rw [norm_div]
            exact (div_le_one (norm_pos_iff.mpr hμB_ne)).mpr
              (hB.toIsCanonicalForm.mu_antitone
                (show b0 ≤ k from Fin.mk_le_mk.mpr (Nat.zero_le _))))
            (hall_inner k))
      simpa using this
    have hB_proj :
        Tendsto
          (fun N : ℕ =>
            (μB b0 ^ N)⁻¹ *
              (∑ k : Fin rB, (μB k) ^ N * mpvInner (d := d) (A a0) (B k) N))
          atTop (nhds 0) := by
      convert hB_proj_sum using 1
      ext N
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [div_pow]
      field_simp [pow_ne_zero N hμB_ne]
    have hRHS_norm_zero :
        Tendsto
          (fun N : ℕ =>
            ‖(c N * (μB b0 / μA a0) ^ N) *
              ((μB b0 ^ N)⁻¹ *
                (∑ k : Fin rB, (μB k) ^ N *
                  mpvInner (d := d) (A a0) (B k) N))‖)
          atTop (nhds (0 : ℝ)) := by
      have hmul := hAdjustedScalar.mul hB_proj.norm
      simpa [norm_mul] using hmul
    have hRHS_norm_one :
        Tendsto
          (fun N : ℕ =>
            ‖(c N * (μB b0 / μA a0) ^ N) *
              ((μB b0 ^ N)⁻¹ *
                (∑ k : Fin rB, (μB k) ^ N *
                  mpvInner (d := d) (A a0) (B k) N))‖)
          atTop (nhds (1 : ℝ)) := by
      have hnorm := hA_proj.norm
      have hnorm_one :
          Tendsto
            (fun N : ℕ =>
              ‖(μA a0 ^ N)⁻¹ *
                (∑ j : Fin rA, (μA j) ^ N *
                  mpvInner (d := d) (A a0) (A j) N)‖)
            atTop (nhds (1 : ℝ)) := by
        simpa using hnorm
      refine hnorm_one.congr (fun N => ?_)
      rw [hNormalizedInner (A a0) (μA a0) (μB b0) hμA_ne hμB_ne N]
    exact zero_ne_one (tendsto_nhds_unique hRHS_norm_zero hRHS_norm_one)
  exact ⟨by simpa [b0] using hDominantB_contra, by simpa [a0] using hDominantA_contra⟩

end ProportionalDominant

end MPSTensor
