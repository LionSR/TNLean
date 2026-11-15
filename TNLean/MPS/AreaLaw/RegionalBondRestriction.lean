/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.FiveRegionHamiltonian

/-!
# Original bonds restricted to a parent interval

Set the bonds outside a parent interval to zero while keeping every
internal bond unchanged. This realizes the parent's actual Hamiltonian
on the full chain, so that the existing regional soft construction can
be applied without a new Hamiltonian decomposition premise.
This is auxiliary geometry for ALVV, arXiv:1602.08828v2,
Figure `fig:generate`, lines 1348–1392.
-/

open scoped BigOperators ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw

open Matrix

/-- Keep precisely the bonds internal to the specified interval.
This is the parent Hamiltonian, extended by zero interactions outside
that interval, an auxiliary to the regional construction of ALVV,
arXiv:1602.08828v2, Figure `fig:generate`, lines 1348–1392. -/
def intervalBondRestriction {L q : ℕ} (l r : ℕ)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (i : Fin (L - 1)) : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
  if l ≤ i.val ∧ i.val + 1 < r then h i else 0

/-- Restricting the interactions preserves their designated supports.
Auxiliary to ALVV, arXiv:1602.08828v2, Figure `fig:generate`, lines 1348–1392. -/
theorem intervalBondRestriction_supported {L q : ℕ} (l r : ℕ)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2))) (i : Fin (L - 1)) :
    Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (intervalBondRestriction l r h i) (interval L i.val (i.val + 2)) := by
  unfold intervalBondRestriction
  split_ifs
  · exact hs i
  · constructor <;> simp

/-- Restricting positive unit interactions preserves both order bounds.
Auxiliary to ALVV, arXiv:1602.08828v2, Figure `fig:generate`, lines 1348–1392. -/
theorem intervalBondRestriction_bounds {L q : ℕ} (l r : ℕ)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1) (i : Fin (L - 1)) :
    0 ≤ intervalBondRestriction l r h i ∧ intervalBondRestriction l r h i ≤ 1 := by
  unfold intervalBondRestriction
  split_ifs
  · exact ⟨h0 i, h1 i⟩
  · exact ⟨le_rfl, zero_le_one⟩

/-- The sum of the restricted bonds is the literal original parent sum.
Auxiliary to ALVV, arXiv:1602.08828v2, Figure `fig:generate`, lines 1348–1392. -/
theorem sum_intervalBondRestriction {L q : ℕ} (l r : ℕ)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) :
    ∑ i, intervalBondRestriction l r h i =
      ∑ i ∈ Finset.univ.filter
        (fun i : Fin (L - 1) ↦ l ≤ i.val ∧ i.val + 1 < r), h i := by
  simp only [Finset.sum_filter, intervalBondRestriction]

/-- A subinterval of the parent retains exactly its original bonds.
Auxiliary to ALVV, arXiv:1602.08828v2, Figure `fig:generate`, lines 1348–1392. -/
theorem sum_internal_intervalBondRestriction_eq {L q : ℕ} {l a b r : ℕ}
    (hla : l ≤ a) (hbr : b ≤ r)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) :
    (∑ i ∈ Finset.univ.filter
      (fun i : Fin (L - 1) ↦ a ≤ i.val ∧ i.val + 1 < b),
        intervalBondRestriction l r h i) =
      ∑ i ∈ Finset.univ.filter
        (fun i : Fin (L - 1) ↦ a ≤ i.val ∧ i.val + 1 < b), h i := by
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := (Finset.mem_filter.mp hi).2
  exact ite_eq_left (by omega)

/-- Each exterior regional sum vanishes after restriction to the parent.
The two conclusions include empty intervals and endpoints. Auxiliary to
ALVV, arXiv:1602.08828v2, Figure `fig:generate`, lines 1348–1392. -/
theorem sum_exterior_intervalBondRestriction {L q : ℕ} (l r : ℕ)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) :
    (∑ i ∈ Finset.univ.filter
      (fun i : Fin (L - 1) ↦ 0 ≤ i.val ∧ i.val + 1 < l),
        intervalBondRestriction l r h i) = 0 ∧
    (∑ i ∈ Finset.univ.filter
      (fun i : Fin (L - 1) ↦ r ≤ i.val ∧ i.val + 1 < L),
        intervalBondRestriction l r h i) = 0 := by
  constructor <;> apply Finset.sum_eq_zero
  · intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    simp only [intervalBondRestriction]
    rw [ite_eq_right (by omega)]
  · intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    simp only [intervalBondRestriction]
    rw [ite_eq_right (by omega)]

end TNLean.MPS.AreaLaw
