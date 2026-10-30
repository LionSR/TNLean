/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AKLV.LowFrequencyPower
import TNLean.Lattice.ZeroEntropy
import Mathlib.Data.Nat.Sqrt

/-!
# Regrouping an AKLV window around the same central cut

A consecutive subwindow of the actual nearest-neighbour interactions is retained.
The omitted interactions are summed into the corresponding exterior operators;
the Hamiltonian is unchanged and the required exterior supports follow from those
of the original terms. No supplied regrouping or new operator family is assumed.

Source: AKLV, arXiv:1301.1162v1, Lemma 4.2 (`l:agsp`), lines 586--603 and 658--663.
-/

open Matrix
open scoped BigOperators

namespace TNLean.MPS.AreaLaw

/-- Retaining consecutive middle interactions and summing the omitted terms into the
exterior operators preserves the actual Hamiltonian and physical supports.
AKLV, arXiv:1301.1162v1, Lemma 4.2, lines 586--603 and 658--663. -/
theorem exists_aklv_subwindow_regrouping {L q a s b m : ℕ} (hsub : b + m ≤ s)
    (H : Fin s → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hH : ∀ j, Entropy.IsSupportedOn (H j) (interval L (a + j.val) (a + j.val + 2)))
    (HL HR : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hL : Entropy.IsSupportedOn HL (interval L 0 (a + 1)))
    (hR : Entropy.IsSupportedOn HR (interval L (a + s) L)) :
    let H' : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
      fun j ↦ H ⟨b + j.val, by omega⟩
    ∃ HL' HR' : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ,
      Entropy.IsSupportedOn HL' (interval L 0 (a + b + 1)) ∧
      Entropy.IsSupportedOn HR' (interval L (a + b + m) L) ∧
      (∀ j, Entropy.IsSupportedOn (H' j)
        (interval L (a + b + j.val) (a + b + j.val + 2))) ∧
      HL + (∑ j, H j) + HR = HL' + (∑ j, H' j) + HR' := by
  classical
  intro H'
  let left : Finset (Fin s ⊕ Fin 2) := Finset.univ.filter
    (Sum.elim (fun j ↦ j.val < b) (fun t ↦ t.val = 0))
  let right : Finset (Fin s ⊕ Fin 2) := Finset.univ.filter
    (Sum.elim (fun j ↦ b + m ≤ j.val) (fun t ↦ t.val = 1))
  let HL' := ∑ t ∈ left, aklvWindowFamily H HL HR t
  let HR' := ∑ t ∈ right, aklvWindowFamily H HL HR t
  have hleft : Entropy.IsSupportedOn HL' (interval L 0 (a + b + 1)) := by
    apply TNLean.Lattice.isSupportedOn_sum
    intro t ht
    have hp := (Finset.mem_filter.mp ht).2
    cases t with
    | inl j =>
      apply (hH j).mono
      intro v hv
      rw [mem_interval] at hv ⊢
      change j.val < b at hp
      omega
    | inr t =>
      fin_cases t
      · exact hL.mono (interval_mono (by omega) (by omega))
      · simp only [Sum.elim_inr] at hp
        contradiction
  have hright : Entropy.IsSupportedOn HR' (interval L (a + b + m) L) := by
    apply TNLean.Lattice.isSupportedOn_sum
    intro t ht
    have hp := (Finset.mem_filter.mp ht).2
    cases t with
    | inl j =>
      apply (hH j).mono
      intro v hv
      rw [mem_interval] at hv ⊢
      change b + m ≤ j.val at hp
      omega
    | inr t =>
      fin_cases t
      · simp only [Sum.elim_inr] at hp
        contradiction
      · exact hR.mono (interval_mono (by omega) le_rfl)
  have hHL' : HL' = HL + ∑ j ∈ Finset.univ.filter (fun j : Fin s ↦ j.val < b), H j := by
    simp only [Finset.sum_filter, Fin.val_eq_zero_iff, Fin.isValue, aklvWindowFamily,
      Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_two, ↓reduceIte,
      cons_val_zero, one_ne_zero, add_zero, add_comm, add_right_inj, HL', left]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with hj
    · exact ite_eq_left hj
    · exact ite_eq_right hj
  have hHR' : HR' = HR + ∑ j ∈ Finset.univ.filter (fun j : Fin s ↦ b + m ≤ j.val), H j := by
    simp only [Finset.sum_filter, aklvWindowFamily, Fintype.sum_sum_type, Sum.elim_inl,
      Sum.elim_inr, Fin.sum_univ_two, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
      zero_ne_one, ↓reduceIte, Nat.mod_succ, cons_val_one, cons_val_fin_one, add_comm,
      add_zero, add_right_inj, HR', right]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with hj
    · exact ite_eq_left hj
    · exact ite_eq_right hj
  have hmiddle : (∑ j, H' j) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin s ↦ b ≤ j.val ∧ j.val < b + m), H j := by
    refine Finset.sum_bij (fun j _ ↦ (⟨b + j.val, by omega⟩ : Fin s)) ?_ ?_ ?_ ?_
    · intro j _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    · intro i _ j _ hij
      apply Fin.ext
      have hval := congrArg Fin.val hij
      change b + i.val = b + j.val at hval
      omega
    · intro j hj
      have hp := (Finset.mem_filter.mp hj).2
      refine ⟨⟨j.val - b, by omega⟩, Finset.mem_univ _, Fin.ext ?_⟩
      change b + (j.val - b) = j.val
      omega
    · intro j _
      rfl
  have hsplit : (∑ j, H j) =
      (∑ j ∈ Finset.univ.filter (fun j : Fin s ↦ j.val < b), H j) +
        (∑ j ∈ Finset.univ.filter (fun j : Fin s ↦ b ≤ j.val ∧ j.val < b + m), H j) +
        (∑ j ∈ Finset.univ.filter (fun j : Fin s ↦ b + m ≤ j.val), H j) := by
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp_all <;> omega
  refine ⟨HL', HR', hleft, hright, ?_, ?_⟩
  · intro j
    simpa only [H', Nat.add_assoc] using hH ⟨b + j.val, by omega⟩
  · rw [hHL', hHR', hmiddle, hsplit]
    abel

end TNLean.MPS.AreaLaw
