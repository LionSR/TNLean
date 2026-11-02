/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import QICLean.Analysis.GroundEnergyBounds
import TNLean.Circuit.EntropySupport
import TNLean.Lattice.ZeroEntropy
import TNLean.MPS.AreaLaw.Basic

/-!
# Five consecutive regions and their original bonds

Four cuts partition the original nearest-neighbour bonds into five internal families and at
most four crossing bonds. The internal Hamiltonians retain their actual supports and positive
unit-term budgets.

These results support ALVV, arXiv:1602.08828v2,
`def:hard-trunc`, lines 873–886, and Theorem `t:ais`, lines 1010–1024.
-/

section

section

section

section

section

namespace TNLean.MPS.AreaLaw

/-- An internal nearest-neighbour bond lies within the specified site interval.
Auxiliary to ALVV, arXiv:1602.08828v2, `def:hard-trunc`, lines 873–886.
No ordering or chain-interior hypotheses are needed on the endpoints. -/
theorem internal_bond_support_subset {L lo hi : ℕ} {i : Fin (L - 1)}
    (hmem : i ∈ (Finset.univ : Finset (Fin (L - 1))).filter
      (fun j ↦ lo ≤ j.val ∧ j.val + 1 < hi)) :
    interval L i.val (i.val + 2) ⊆ interval L lo hi := by
  have hiRange := (Finset.mem_filter.mp hmem).2
  intro v hv
  simp only [mem_interval] at hv ⊢
  omega

/-- The literal internal-bond index set contains at most `hi-lo-1` bonds.
Auxiliary to the same regional Hamiltonian decomposition of ALVV,
`def:hard-trunc`, lines 873–886; empty and out-of-range intervals are included. -/
theorem card_internal_bonds_le (L lo hi : ℕ) :
    ((Finset.univ : Finset (Fin (L - 1))).filter
      (fun i ↦ lo ≤ i.val ∧ i.val + 1 < hi)).card ≤ hi - lo - 1 := by
  let I := (Finset.univ : Finset (Fin (L - 1))).filter
    (fun i ↦ lo ≤ i.val ∧ i.val + 1 < hi)
  have hmap : Set.MapsTo Fin.val (I : Set (Fin (L - 1)))
      (Finset.Ico lo (hi - 1) : Set ℕ) := by
    intro i hiI
    have hiRange := (Finset.mem_filter.mp hiI).2
    apply Finset.mem_Ico.mpr
    constructor
    · exact hiRange.1
    · omega
  have hcard : I.card ≤ (Finset.Ico lo (hi - 1)).card :=
    Finset.card_le_card_of_injOn Fin.val hmap (by
      intro i _ j _ hij
      exact Fin.ext hij)
  rw [Nat.card_Ico] at hcard
  change I.card ≤ hi - lo - 1
  omega

/-- The sum of the actual internal bonds is supported on its site interval.
Auxiliary to ALVV's regional hard truncation, `def:hard-trunc`, lines 873–886.
This is only a support statement and requires no local dimension hypothesis. -/
theorem isSupportedOn_sum_internal_bonds (L q lo hi : ℕ)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2))) :
    Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (∑ i ∈ (Finset.univ : Finset (Fin (L - 1))).filter
        (fun j ↦ lo ≤ j.val ∧ j.val + 1 < hi), h i) (interval L lo hi) := by
  exact TNLean.Lattice.isSupportedOn_sum _ fun i hiI ↦
    (hs i).mono (internal_bond_support_subset hiI)
end TNLean.MPS.AreaLaw

namespace TNLean.MPS.AreaLaw

/-- Consecutive half-open intervals with ordered endpoints are pairwise
disjoint, including empty intervals. Auxiliary geometry for ALVV,
arXiv:1602.08828v2, `def:hard-trunc`, lines 873–886. -/
private theorem pairwise_disjoint_consecutive_intervals
    {L m : ℕ} (k : Fin (m + 1) → ℕ) (hk : Monotone k) :
    Pairwise fun i j : Fin m ↦
      Disjoint (interval L (k i.castSucc) (k i.succ))
        (interval L (k j.castSucc) (k j.succ)) := by
  have hlt (i j : Fin m) (hij : i < j) :
      Disjoint (interval L (k i.castSucc) (k i.succ))
        (interval L (k j.castSucc) (k j.succ)) := by
    have hs : i.succ ≤ j.castSucc := by
      change i.val + 1 ≤ j.val
      exact hij
    have hends := hk hs
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hx' := mem_interval.mp hx
    have hy' := mem_interval.mp hy
    omega
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact hlt i j hij
  · exact (hlt j i hji).symm

/-- The original internal Hamiltonians of consecutive regions commute.
Commutation is derived from their actual nearest-neighbour supports.
Auxiliary to ALVV, arXiv:1602.08828v2, `def:hard-trunc`, lines 873–886,
and Theorem `t:ais`, lines 1010–1024. -/
theorem pairwise_commute_sum_internal_consecutive_regions
    {L q m : ℕ} (k : Fin (m + 1) → ℕ) (hk : Monotone k)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2))) :
    Pairwise fun i j : Fin m ↦
      Commute
        (∑ r ∈ (Finset.univ : Finset (Fin (L - 1))).filter
          (fun r ↦ k i.castSucc ≤ r.val ∧ r.val + 1 < k i.succ), h r)
        (∑ r ∈ (Finset.univ : Finset (Fin (L - 1))).filter
          (fun r ↦ k j.castSucc ≤ r.val ∧ r.val + 1 < k j.succ), h r) := by
  intro i j hij
  apply QuantumCircuit.commute_of_mem_supportedOperators
    (Finset.disjoint_coe.mpr (pairwise_disjoint_consecutive_intervals k hk hij))
  · exact QuantumCircuit.mem_supportedOperators_of_isSupportedOn
      (isSupportedOn_sum_internal_bonds L q (k i.castSucc) (k i.succ) h hs)
  · exact QuantumCircuit.mem_supportedOperators_of_isSupportedOn
      (isSupportedOn_sum_internal_bonds L q (k j.castSucc) (k j.succ) h hs)
end TNLean.MPS.AreaLaw
end
end

section

namespace Fin

/-- Classification of actual nearest-neighbour bond starts at four ordered
cuts. Auxiliary to ALVV, arXiv:1602.08828v2, `def:hard-trunc`,
lines 873–886, and `t:ais`, lines 1010–1024. -/
private theorem four_cut_crossing_iff_not_internal
    {L k1 k2 k3 k4 : ℕ} (h12 : k1 ≤ k2) (h23 : k2 ≤ k3)
    (h34 : k3 ≤ k4) (i : Fin (L - 1)) :
    (i.val + 1 = k1 ∨ i.val + 1 = k2 ∨ i.val + 1 = k3 ∨ i.val + 1 = k4) ↔
      ¬ ((0 ≤ i.val ∧ i.val + 1 < k1) ∨
        (k1 ≤ i.val ∧ i.val + 1 < k2) ∨
        (k2 ≤ i.val ∧ i.val + 1 < k3) ∨
        (k3 ≤ i.val ∧ i.val + 1 < k4) ∨
        (k4 ≤ i.val ∧ i.val + 1 < L)) := by
  have hi := i.isLt
  omega
end Fin

namespace Finset

/-- Four cut positions give at most four actual crossing bonds.
Auxiliary geometry for ALVV, arXiv:1602.08828v2, `def:hard-trunc`,
lines 873–886, and `t:ais`, lines 1010–1024. -/
private theorem card_four_cut_crossing_le (L k1 k2 k3 k4 : ℕ) :
    ((univ : Finset (Fin (L - 1))).filter
      (fun i ↦ i.val + 1 ∈ ({k1, k2, k3, k4} : Finset ℕ))).card ≤ 4 := by
  let J := (univ : Finset (Fin (L - 1))).filter
    (fun i ↦ i.val + 1 ∈ ({k1, k2, k3, k4} : Finset ℕ))
  have hcard : J.card ≤ ({k1, k2, k3, k4} : Finset ℕ).card := by
    apply Finset.card_le_card_of_injOn (fun i : Fin (L - 1) ↦ i.val + 1)
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · intro i _ j _ hij
      exact Fin.ext (Nat.add_right_cancel hij)
  exact hcard.trans Finset.card_le_four
end Finset

open scoped BigOperators

namespace Finset

/-- The exact nearest-neighbour sum over the five internal site intervals
and the literal crossing-bond set. All coefficients are retained once.
Auxiliary geometry for ALVV, arXiv:1602.08828v2, `def:hard-trunc`,
source lines 873–886, `c:goodagsphardtrunc`, lines 979–1005,
and Theorem `t:ais`, lines 1010–1024. -/
theorem sum_five_internal_regions_add_crossings
    {A : Type*} [AddCommMonoid A] {L k1 k2 k3 k4 : ℕ}
    (h12 : k1 ≤ k2) (h23 : k2 ≤ k3) (h34 : k3 ≤ k4)
    (h : Fin (L - 1) → A) :
    (∑ i, h i) =
      (∑ i ∈ (univ : Finset (Fin (L - 1))).filter
        (fun i ↦ 0 ≤ i.val ∧ i.val + 1 < k1), h i) +
      (∑ i ∈ (univ : Finset (Fin (L - 1))).filter
        (fun i ↦ k1 ≤ i.val ∧ i.val + 1 < k2), h i) +
      (∑ i ∈ (univ : Finset (Fin (L - 1))).filter
        (fun i ↦ k2 ≤ i.val ∧ i.val + 1 < k3), h i) +
      (∑ i ∈ (univ : Finset (Fin (L - 1))).filter
        (fun i ↦ k3 ≤ i.val ∧ i.val + 1 < k4), h i) +
      (∑ i ∈ (univ : Finset (Fin (L - 1))).filter
        (fun i ↦ k4 ≤ i.val ∧ i.val + 1 < L), h i) +
      (∑ i ∈ (univ : Finset (Fin (L - 1))).filter
        (fun i ↦ i.val + 1 ∈ ({k1, k2, k3, k4} : Finset ℕ)), h i) := by
  simp only [Finset.sum_filter, Finset.mem_insert, Finset.mem_singleton]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hi := i.isLt
  have hclass := Fin.four_cut_crossing_iff_not_internal h12 h23 h34 i
  have hcover :
      (0 ≤ i.val ∧ i.val + 1 < k1) ∨
      (k1 ≤ i.val ∧ i.val + 1 < k2) ∨
      (k2 ≤ i.val ∧ i.val + 1 < k3) ∨
      (k3 ≤ i.val ∧ i.val + 1 < k4) ∨
      (k4 ≤ i.val ∧ i.val + 1 < L) ∨
      (i.val + 1 = k1 ∨ i.val + 1 = k2 ∨ i.val + 1 = k3 ∨ i.val + 1 = k4) := by
    omega
  rcases hcover with h0 | h1 | h2 | h3 | h4 | hJ
  all_goals
    simp (disch := omega) only [ite_eq_left, ite_eq_right]
  all_goals simp
end Finset

open scoped BigOperators ComplexOrder MatrixOrder

open scoped BigOperators ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw

/-- The actual five regional Hamiltonians and their four crossing bonds
satisfy the support, positivity, budget, and exact-sum identities needed
for regional truncation. Auxiliary to ALVV, arXiv:1602.08828v2,
`def:hard-trunc`, lines 873–886, and `c:goodagsphardtrunc`, lines 979–1005.
Coincident cuts, empty regions, and empty chains are included. -/
theorem five_region_original_bond_data
    (L q k1 k2 k3 k4 : ℕ) (h12 : k1 ≤ k2) (h23 : k2 ≤ k3)
    (h34 : k3 ≤ k4) (h4L : k4 ≤ L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h i) (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1) :
    let k : Fin 6 → ℕ := ![0, k1, k2, k3, k4, L]
    let R : Fin 5 → Finset (Fin L) := fun j ↦ interval L (k j.castSucc) (k j.succ)
    let I : Fin 5 → Finset (Fin (L - 1)) := fun j ↦
      Finset.univ.filter (fun i ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ)
    let A : Fin 5 → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
      fun j ↦ ∑ i ∈ I j, h i
    let J : Finset (Fin (L - 1)) := Finset.univ.filter
      (fun i ↦ i.val + 1 ∈ ({k1, k2, k3, k4} : Finset ℕ))
    let Y : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := ∑ i ∈ J, h i
    Monotone k ∧ (Pairwise fun i j ↦ Disjoint (R i) (R j)) ∧
      (∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (A j) (R j)) ∧
      (∀ j, (A j).PosSemidef ∧
        A j ≤ ((I j).card : ℝ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)) ∧
      Y.PosSemidef ∧
      Y ≤ (J.card : ℝ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ∧
      J.card ≤ 4 ∧ (∑ i, h i) = (∑ j, A j) + Y := by
  intro k R I A J Y
  have hk : Monotone k := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    fin_cases i <;> simp [k] <;> omega
  have hRordered (i j : Fin 5) (hij : i < j) : Disjoint (R i) (R j) := by
    apply Finset.disjoint_left.mpr
    intro v hvi hvj
    have hends := hk (Fin.succ_le_castSucc_iff.mpr hij)
    change v ∈ interval L (k i.castSucc) (k i.succ) at hvi
    change v ∈ interval L (k j.castSucc) (k j.succ) at hvj
    rw [mem_interval] at hvi hvj
    omega
  have hR : Pairwise fun i j ↦ Disjoint (R i) (R j) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hij' | hji
    · exact hRordered i j hij'
    · exact (hRordered j i hji).symm
  have hAs (j : Fin 5) :
      Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (A j) (R j) :=
    isSupportedOn_sum_internal_bonds L q (k j.castSucc) (k j.succ) h hs
  have hA (j : Fin 5) : (A j).PosSemidef ∧
      A j ≤ ((I j).card : ℝ) •
        (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) :=
    Matrix.sum_posSemidef_and_le_card_of_positive_unit_terms (I j) h
      (fun i _ ↦ h0 i) (fun i _ ↦ h1 i)
  have hY : Y.PosSemidef ∧
      Y ≤ (J.card : ℝ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) :=
    Matrix.sum_posSemidef_and_le_card_of_positive_unit_terms J h
      (fun i _ ↦ h0 i) (fun i _ ↦ h1 i)
  have hJ : J.card ≤ 4 := Finset.card_four_cut_crossing_le L k1 k2 k3 k4
  refine ⟨hk, hR, hAs, hA, hY.1, hY.2, hJ, ?_⟩
  rw [Fin.sum_univ_five]
  change (∑ i : Fin (L - 1), h i) =
    (∑ i ∈ (Finset.univ : Finset (Fin (L - 1))).filter
      (fun i ↦ 0 ≤ i.val ∧ i.val + 1 < k1), h i) +
    (∑ i ∈ (Finset.univ : Finset (Fin (L - 1))).filter
      (fun i ↦ k1 ≤ i.val ∧ i.val + 1 < k2), h i) +
    (∑ i ∈ (Finset.univ : Finset (Fin (L - 1))).filter
      (fun i ↦ k2 ≤ i.val ∧ i.val + 1 < k3), h i) +
    (∑ i ∈ (Finset.univ : Finset (Fin (L - 1))).filter
      (fun i ↦ k3 ≤ i.val ∧ i.val + 1 < k4), h i) +
    (∑ i ∈ (Finset.univ : Finset (Fin (L - 1))).filter
      (fun i ↦ k4 ≤ i.val ∧ i.val + 1 < L), h i) +
    (∑ i ∈ (Finset.univ : Finset (Fin (L - 1))).filter
      (fun i ↦ i.val + 1 ∈ ({k1, k2, k3, k4} : Finset ℕ)), h i)
  exact Finset.sum_five_internal_regions_add_crossings h12 h23 h34 h
end TNLean.MPS.AreaLaw
end

section

open scoped BigOperators

namespace Real

/-- Clipping three bulks at an independent real threshold `t` and retaining
two windows with at most `2*ell-2` original internal bonds gives a total
centered norm budget at most `3*t + 4*ell`, including all crossing bonds. Auxiliary to ALVV,
arXiv:1602.08828v2, `def:hard-trunc`, lines 873–886, and the spectral
radius estimate in Theorem `t:ais`, lines 1010–1024.
No additional crossing-bond constant is added after this budget. -/
theorem five_region_final_clipping_budget_le
    (ell C : ℕ) (c : Fin 5 → ℕ) (t : ℝ) (hell : 1 ≤ ell)
    (hc1 : c 1 ≤ 2 * ell - 2) (hc3 : c 3 ≤ 2 * ell - 2) (hC : C ≤ 4) :
    (∑ i : Fin 5, if i ∈ ({0, 2, 4} : Finset (Fin 5)) then t
      else (c i : ℝ)) + (C : ℝ) ≤ 3 * t + 4 * (ell : ℝ) := by
  have hnat : c 1 + c 3 + C ≤ 4 * ell := by omega
  have hreal : (c 1 : ℝ) + (c 3 : ℝ) + (C : ℝ) ≤ 4 * (ell : ℝ) := by
    exact_mod_cast hnat
  simp only [Fin.sum_univ_five]
  norm_num
  linarith
end Real
end
end
end
end
