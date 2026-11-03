/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.NormalizedSequentialApproximation

/-!
# One normalized MPS with a sharper designated cut

The designated cut and the remaining cuts have different rank and mass
budgets. One actual sequential product of their leading marginal projections
retains both bounds after normalization. Boundary cuts need no projection:
their coefficient matrix has rank at most one.

This supplies the simultaneous approximation reading of ALVV,
arXiv:1602.08828v2, Theorem `thm:al-ld`, lines 1096–1105.
-/

open scoped BigOperators ComplexOrder InnerProductSpace Matrix

namespace TNLean.MPS.AreaLaw

/-- Distinct marginal-mass budgets give one normalized MPS satisfying the
sharper designated-cut rank and the global bond bound simultaneously.
The vector is the actual normalized sequential projection product.
Supporting ALVV, arXiv:1602.08828v2, Theorem `thm:al-ld`, lines 1096–1105. -/
theorem exists_unit_mps_of_designated_prefix_mass
    {L q : ℕ} (ψ : EuclideanSpace ℂ (Fin L → Fin q)) (hψ : ‖ψ‖ = 1)
    (k0 Ds Dg : ℕ) (hDs : 1 ≤ Ds) (hDsg : Ds ≤ Dg)
    (delta : ℝ) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hspecial : k0 ∈ Finset.Ico 1 L →
      1 - (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q)
        (leftBlock L k0) ψ).kyFanNorm Ds ≤ delta / 32)
    (hother : ∀ k ∈ Finset.Ico 1 L, k ≠ k0 →
      1 - (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q)
        (leftBlock L k) ψ).kyFanNorm Dg ≤ delta / (32 * ((L : ℝ) + 1))) :
    ∃ Φ : EuclideanSpace ℂ (Fin L → Fin q), ‖Φ‖ = 1 ∧
      IsOpenMPS L q Dg (fun x ↦ Φ x) ∧ (cutMatrix Φ k0).rank ≤ Ds ∧
      1 - delta < ‖⟪Φ, ψ⟫_ℂ‖ ∧ ‖Φ - ψ‖ ^ 2 ≤ delta / 2 := by
  classical
  let D : ℕ → ℕ := fun k ↦ if k = k0 then Ds else Dg
  have hsmall : 0 ≤ delta / (32 * ((L : ℝ) + 1)) := by positivity
  have hpt (k : ℕ) (hk : k ∈ Finset.Ico 1 L) :
      1 - (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q)
        (leftBlock L k) ψ).kyFanNorm (D k) ≤
        delta / (32 * ((L : ℝ) + 1)) + (if k = k0 then delta / 32 else 0) := by
    by_cases heq : k = k0
    · subst k
      simp only [D, ite_true]
      linarith only [hspecial hk, hsmall]
    · simp only [D, ite_eq_right heq, add_zero]
      exact hother k hk heq
  have hsingle : (∑ k ∈ Finset.Ico 1 L, if k = k0 then delta / 32 else 0) ≤ delta / 32 := by
    rw [Finset.sum_ite_eq']
    split_ifs <;> linarith only [hdelta]
  have hcard : ((Finset.Ico 1 L).card : ℝ) ≤ (L : ℝ) + 1 := by
    exact_mod_cast (show (Finset.Ico 1 L).card ≤ L + 1 by rw [Nat.card_Ico]; omega)
  have hconstant : (∑ _k ∈ Finset.Ico 1 L,
      delta / (32 * ((L : ℝ) + 1))) ≤ delta / 32 := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    calc
      _ ≤ ((L : ℝ) + 1) * (delta / (32 * ((L : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_right hcard hsmall
      _ = _ := by field_simp
  have hsum : (∑ k ∈ Finset.Ico 1 L,
      (1 - (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q)
        (leftBlock L k) ψ).kyFanNorm (D k))) ≤ delta / 8 := by
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [Finset.sum_add_distrib]
    linarith only [hsingle, hconstant, hdelta]
  let P : ∀ k : ℕ, LeftBlockMatrix L q k := fun k ↦
    (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q)
      (leftBlock L k) ψ).leadingEigenprojection (D k)
  let Φ0 := sequentialTruncation P (L - 1) ψ
  let Φ := (‖Φ0‖ : ℂ)⁻¹ • Φ0
  obtain ⟨_hpos, hΦ, hrank, hoverlap, hsq⟩ :=
    normalized_sequentialTruncation_of_prefix_mass ψ hψ D delta hdelta hdelta1 hsum
  refine ⟨Φ, hΦ, ?_, ?_, hoverlap, hsq⟩
  · apply isOpenMPS_of_internal_cutMatrix_rank_le Φ
    intro k hk hkL
    have hD : D k ≤ Dg := by dsimp only [D]; split_ifs <;> omega
    exact (hrank k hk hkL).trans hD
  · rcases Nat.eq_zero_or_pos k0 with rfl | hk0
    · exact (rank_cutMatrix_zero_le Φ).trans hDs
    · rcases lt_or_ge k0 L with hkL | hLk
      · simpa only [D, ite_true] using hrank k0 hk0 hkL
      · exact (rank_cutMatrix_le_one_of_le hLk Φ).trans hDs

end TNLean.MPS.AreaLaw
