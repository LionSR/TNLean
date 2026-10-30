/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AKLV.WidthPolynomial
import QICLean.Algebra.OperatorSchmidtRealignment

/-!
# The AKLV polynomial rank estimate from the original physical interactions

The middle window is shortened around the same central cut, the omitted interactions
are actually summed into the exterior operators, and the uniform polynomial estimate
is applied to this unchanged Hamiltonian. The numerical constant is universal.
Zero degree and odd window lengths are included.

**Local fix (count):** The commuting-gap coefficient uses the correction documented at
https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf.

Source: AKLV, arXiv:1301.1162v1, Lemma 4.2 (`l:agsp`), lines 586--663.
This module proves an explicit constant bound with base `q * (ell + 1)`;
no approximate-ground-projector or area-law theorem is assumed.
-/

open Matrix
open scoped BigOperators

namespace TNLean.MPS.AreaLaw

/-- A window of width `min s (2 * sqrt ell)` can be placed within the original window
with exactly the same central cut. AKLV, arXiv:1301.1162v1, Lemma 4.2, lines 658--663. -/
theorem exists_aklv_centered_short_window (s ell : ℕ) :
    ∃ b, b + min s (2 * Nat.sqrt ell) ≤ s ∧
      b + min s (2 * Nat.sqrt ell) / 2 = s / 2 := by
  by_cases h : s ≤ 2 * Nat.sqrt ell
  · rw [min_eq_left h]
    exact ⟨0, by omega, by omega⟩
  · rw [min_eq_right (by omega : 2 * Nat.sqrt ell ≤ s)]
    refine ⟨s / 2 - Nat.sqrt ell, ?_, ?_⟩ <;> omega

/-- There is a nonempty subwindow centered at the original cut whose width and rank
exponent are bounded uniformly, including degree zero. AKLV, arXiv:1301.1162v1,
Lemma 4.2, the shorter-window step in lines 658--663. -/
theorem exists_aklv_effective_window {s ell : ℕ} (hs : 1 ≤ s) :
    ∃ m b : ℕ, 1 ≤ m ∧ m ≤ ell + 1 ∧ b + m ≤ s ∧ b + m / 2 = s / 2 ∧
      3 * m + 6 * (ell / m) + 5 ≤ 16 * (ell / s + Nat.sqrt ell + 1) := by
  by_cases hell : ell = 0
  · subst ell
    refine ⟨1, s / 2, by omega, by omega, by omega, by omega, ?_⟩
    norm_num
  · obtain ⟨hm, hwidth, hexp⟩ := Nat.aklv_effective_width_bounds (by omega : 1 ≤ ell) hs
    obtain ⟨b, hsub, hcenter⟩ := exists_aklv_centered_short_window s ell
    exact ⟨min s (2 * Nat.sqrt ell), b, hm, hwidth, hsub, hcenter, hexp⟩

/-- An arbitrary degree-bounded polynomial of the original physically supported
Hamiltonian obeys a universal explicit AKLV rank bound at the original central cut.
AKLV, arXiv:1301.1162v1, Lemma 4.2 (`l:agsp`), lines 586--663. -/
theorem operatorSchmidtRank_aklv_polynomial_le {L q a s ell : ℕ}
    (hq : 1 ≤ q) (hs : 0 < s) (hspace : a + s + 1 ≤ L)
    (H : Fin s → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hH : ∀ j, Entropy.IsSupportedOn (H j) (interval L (a + j.val) (a + j.val + 2)))
    (HL HR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hL : Entropy.IsSupportedOn HL (interval L 0 (a + 1)))
    (hR : Entropy.IsSupportedOn HR (interval L (a + s) L))
    (P : Polynomial ℂ) (hP : P.natDegree ≤ ell) :
    operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q)
      (leftBlock L (a + s / 2))
      (Polynomial.aeval (HL + (∑ j, H j) + HR) P)) ≤
      (q * (ell + 1)) ^ (16 * (ell / s + Nat.sqrt ell + 1)) := by
  obtain ⟨m, b, hm, hwidth, hsub, hcenter, hexp⟩ :=
    exists_aklv_effective_window (ell := ell) (by omega : 1 ≤ s)
  let H' : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
    fun j ↦ H ⟨b + j.val, by omega⟩
  obtain ⟨HL', HR', hL', hR', hH', hG⟩ :=
    exists_aklv_subwindow_regrouping hsub H hH HL HR hL hR
  have hrank := operatorSchmidtRank_aklv_polynomial_of_width_le hq
    (by omega : 0 < m) hwidth (by omega : a + b + m + 1 ≤ L)
    H' hH' HL' HR' hL' hR' P hP
  have hcut : a + b + m / 2 = a + s / 2 := by omega
  rw [← hG, hcut] at hrank
  exact hrank.trans (Nat.pow_le_pow_right (by nlinarith : 1 ≤ q * (ell + 1)) hexp)

/-- The maximum-form AKLV exponent for positive degree, with a universal explicit
constant. AKLV, arXiv:1301.1162v1, Lemma 4.2 (`l:agsp`). -/
theorem operatorSchmidtRank_aklv_polynomial_le_max {L q a s ell : ℕ}
    (hq : 1 ≤ q) (hs : 0 < s) (hell : 1 ≤ ell) (hspace : a + s + 1 ≤ L)
    (H : Fin s → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hH : ∀ j, Entropy.IsSupportedOn (H j) (interval L (a + j.val) (a + j.val + 2)))
    (HL HR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hL : Entropy.IsSupportedOn HL (interval L 0 (a + 1)))
    (hR : Entropy.IsSupportedOn HR (interval L (a + s) L))
    (P : Polynomial ℂ) (hP : P.natDegree ≤ ell) :
    operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q)
      (leftBlock L (a + s / 2))
      (Polynomial.aeval (HL + (∑ j, H j) + HR) P)) ≤
      (q * (ell + 1)) ^ (48 * max (ell / s) (Nat.sqrt ell)) := by
  refine (operatorSchmidtRank_aklv_polynomial_le hq hs hspace H hH HL HR hL hR P hP).trans ?_
  apply Nat.pow_le_pow_right (by nlinarith : 1 ≤ q * (ell + 1))
  have hn : 1 ≤ Nat.sqrt ell := Nat.sqrt_pos.mpr (by omega)
  have h1 := le_max_left (ell / s) (Nat.sqrt ell)
  have h2 := le_max_right (ell / s) (Nat.sqrt ell)
  omega

/-- For positive degree, the base can be written exactly as in AKLV's rank estimate,
with universal exponent constant `96`. AKLV, arXiv:1301.1162v1, Lemma 4.2 (`l:agsp`).
The preceding theorem covers the smaller degrees without a degenerate base. -/
theorem operatorSchmidtRank_aklv_polynomial_le_source_base {L q a s ell : ℕ}
    (hq : 1 ≤ q) (hs : 0 < s) (hell : 1 ≤ ell) (hspace : a + s + 1 ≤ L)
    (H : Fin s → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hH : ∀ j, Entropy.IsSupportedOn (H j) (interval L (a + j.val) (a + j.val + 2)))
    (HL HR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hL : Entropy.IsSupportedOn HL (interval L 0 (a + 1)))
    (hR : Entropy.IsSupportedOn HR (interval L (a + s) L))
    (P : Polynomial ℂ) (hP : P.natDegree ≤ ell) :
    operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q)
      (leftBlock L (a + s / 2))
      (Polynomial.aeval (HL + (∑ j, H j) + HR) P)) ≤
      (q * ell) ^ (96 * max (ell / s) (Nat.sqrt ell)) := by
  by_cases hlarge : 2 ≤ q * ell
  · have hbase : q * (ell + 1) ≤ (q * ell) ^ 2 := by
      calc
        _ ≤ 2 * (q * ell) :=
          (Nat.mul_le_mul_left q (by omega : ell + 1 ≤ 2 * ell)).trans_eq (by ac_rfl)
        _ ≤ _ := by nlinarith
    refine (operatorSchmidtRank_aklv_polynomial_le_max hq hs hell hspace
      H hH HL HR hL hR P hP).trans ?_
    refine (Nat.pow_le_pow_left hbase _).trans_eq ?_
    rw [← pow_mul]
    congr 1
    omega
  · have hq1 : q = 1 := by nlinarith
    have hell1 : ell = 1 := by nlinarith
    subst q
    subst ell
    rw [operatorSchmidtRank_eq_rank_realignment]
    refine (Matrix.rank_le_card_height _).trans ?_
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, one_pow, one_mul]
    exact Nat.le_refl 1

end TNLean.MPS.AreaLaw
