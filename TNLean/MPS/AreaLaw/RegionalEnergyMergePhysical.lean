/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.RegionalEnergyMerge
import TNLean.MPS.AreaLaw.AKLV.TwoBlockTruncation
import TNLean.MPS.AreaLaw.FiveRegionHamiltonian

/-!
# Joining the actual internal Hamiltonians of adjacent intervals

The internal Hamiltonian on the union is the sum of the two child internal
Hamiltonians and at most one original bond. The attained minima therefore
satisfy the one-unit boundary bound, including empty children and endpoints.
This is auxiliary to ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, lines
1627–1632, and the energy-estimation argument at lines 1805–1807.
-/

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

open Matrix

/-- Attained minima for the actual adjacent interval Hamiltonians have boundary
error at most one. Lower child estimates of error at most three consequently
add to a lower parent estimate of error at most seven. All operators come from
the original positive nearest-neighbour contractions. Auxiliary to ALVV,
arXiv:1602.08828v2, Figure `fig:algo1`, lines 1627–1632. -/
theorem exists_adjacent_interval_energy_merge {L q l m r : ℕ}
    (hq : 0 < q) (hlm : l ≤ m) (hmr : m ≤ r) (hrL : r ≤ L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1) :
    let A := aklvRegionalHamiltonians l m h 1
    let B := aklvRegionalHamiltonians m r h 1
    let P := aklvRegionalHamiltonians l r h 1
    ∃ (eA eB eP : ℝ) (x z : (Fin L → Fin q) → ℂ),
      star x ⬝ᵥ x = 1 ∧ A *ᵥ x = (eA : ℂ) • x ∧ B *ᵥ x = (eB : ℂ) • x ∧
      (A - (eA : ℂ) • 1).PosSemidef ∧ (B - (eB : ℂ) • 1).PosSemidef ∧
      star z ⬝ᵥ z = 1 ∧ P *ᵥ z = (eP : ℂ) • z ∧
      (P - (eP : ℂ) • 1).PosSemidef ∧
      eA + eB ≤ eP ∧ eP ≤ eA + eB + 1 ∧
      ∀ pA pB : ℝ, eA - 3 ≤ pA → pA ≤ eA → eB - 3 ≤ pB → pB ≤ eB →
        eP - 7 ≤ pA + pB ∧ pA + pB ≤ eP := by
  intro A B P
  classical
  obtain ⟨_hk, hR, hregion, hbound, _⟩ :=
    five_region_original_bond_data L q l m m r hlm le_rfl hmr hrL h hs h0 h1
  let J := Finset.univ.filter (fun i : Fin (L - 1) ↦
    l ≤ i.val ∧ i.val + 1 < r ∧ i.val + 1 = m)
  let Y := ∑ i ∈ J, h i
  have hcard : J.card ≤ 1 := by
    have hc := Finset.card_le_card_of_injOn (fun i : Fin (L - 1) ↦ i.val + 1)
      (s := J) (t := {m}) (fun _ hi ↦ by simpa using (Finset.mem_filter.mp hi).2.2.2)
      (by intro i _ j _ hij; apply Fin.ext; change i.val + 1 = j.val + 1 at hij; omega)
    simpa using hc
  obtain ⟨hY, hYc⟩ := sum_posSemidef_and_le_card_of_positive_unit_terms J h
    (fun i _ ↦ h0 i) (fun i _ ↦ h1 i)
  have hY1 : Y ≤ 1 := by
    calc
      Y ≤ (J.card : ℝ) • 1 := hYc
      _ ≤ (1 : ℝ) • 1 := smul_le_smul_of_nonneg_right (by exact_mod_cast hcard) zero_le_one
      _ = 1 := one_smul ℝ _
  have hsplit : P = A + B + Y := by
    change (∑ i ∈ Finset.univ.filter (fun i : Fin (L - 1) ↦
      l ≤ i.val ∧ i.val + 1 < r), h i) =
      (∑ i ∈ Finset.univ.filter (fun i : Fin (L - 1) ↦
        l ≤ i.val ∧ i.val + 1 < m), h i) +
      (∑ i ∈ Finset.univ.filter (fun i : Fin (L - 1) ↦
        m ≤ i.val ∧ i.val + 1 < r), h i) +
      ∑ i ∈ Finset.univ.filter (fun i : Fin (L - 1) ↦
        l ≤ i.val ∧ i.val + 1 < r ∧ i.val + 1 = m), h i
    simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp_all <;> omega
  rw [hsplit]
  exact exists_disjoint_regional_energy_merge hq (interval L l m) (interval L m r)
    (hR (show (1 : Fin 5) ≠ 3 by decide)) A B Y (hregion 1) (hregion 3)
    (hbound 1).1 (hbound 3).1 hY hY1

end TNLean.MPS.AreaLaw
