/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hamiltonian

/-!
# Counting the supports of a range-one chain

A nonempty support of diameter at most one is a singleton or a pair of adjacent sites.
Consequently a chain of `L` sites has at most `2L` such supports.
-/

open scoped Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

private theorem chainSupport_range_one_eq_interval {L : ℕ} (X : ChainSupport L 1) :
    X.1 = interval L (X.1.min' X.2.1).val ((X.1.min' X.2.1).val + X.1.card) := by
  classical
  by_cases hone : X.1.card = 1
  · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hone
    simp only [hx, Finset.min'_singleton, Finset.card_singleton]
    ext i
    simp only [Finset.mem_singleton, mem_interval]
    constructor
    · rintro rfl
      omega
    · intro hi
      exact Fin.ext (by omega)
  · have htwo : X.1.card = 2 := by
      have := X.2.card_le
      have := X.2.1.card_pos
      omega
    obtain ⟨a, ha, hXa⟩ := X.2.exists_eq_interval_of_card_eq htwo
    have haX : (⟨a, by omega⟩ : Fin L) ∈ X.1 := by
      rw [hXa]
      simp only [mem_interval]
      omega
    have hmX := X.1.min'_mem X.2.1
    have hmval : (X.1.min' X.2.1).val = a := by
      have hlow := (mem_interval.mp ((Finset.ext_iff.mp hXa _).mp hmX)).1
      have hupp := Finset.min'_le X.1 _ haX
      change (X.1.min' X.2.1).val ≤ a at hupp
      omega
    simpa only [hmval, htwo, Nat.add_assoc] using hXa

/-- A chain of `L` sites has at most `2L` nonempty supports of diameter at most one.
This is a counting consequence of the interaction convention in the one-dimensional note,
Section 1, `eq:ham`. -/
theorem card_chainSupport_range_one_le (L : ℕ) : Fintype.card (ChainSupport L 1) ≤ 2 * L := by
  classical
  let f : ChainSupport L 1 → Fin L × Fin 2 := fun X ↦
    (X.1.min' X.2.1, ⟨X.1.card - 1, by have := X.2.card_le; omega⟩)
  have hf : Function.Injective f := by
    intro X Y h
    have hm := congrArg Prod.fst h
    have hc := congrArg (fun p ↦ p.2.val) h
    change X.1.min' X.2.1 = Y.1.min' Y.2.1 at hm
    change X.1.card - 1 = Y.1.card - 1 at hc
    have hcard : X.1.card = Y.1.card := by
      have := X.2.1.card_pos
      have := Y.2.1.card_pos
      omega
    apply Subtype.ext
    rw [chainSupport_range_one_eq_interval X, chainSupport_range_one_eq_interval Y, hm, hcard]
  simpa [Nat.mul_comm] using Fintype.card_le_of_injective f hf

/-- The operator norm of a range-one chain Hamiltonian is at most `2LJ`.
This follows from the interaction convention in the one-dimensional note, Section 1,
`eq:ham`, and the support count above. -/
theorem ChainHamiltonian.norm_operator_le_of_range_one {L q : ℕ} {J : ℝ}
    (h : ChainHamiltonian L q 1 J) : ‖h.operator‖ ≤ 2 * L * J := by
  classical
  by_cases hL : L = 0
  · subst L
    have hcard : Fintype.card (ChainSupport 0 1) = 0 := by
      have := card_chainSupport_range_one_le 0
      omega
    let := Fintype.card_eq_zero_iff.mp hcard
    simp [ChainHamiltonian.operator]
  · have hJ := h.norm_bound_nonneg ⟨0, by omega⟩
    calc
      ‖h.operator‖ ≤ ∑ X, ‖h.term X‖ := norm_sum_le _ _
      _ ≤ ∑ _ : ChainSupport L 1, J := Finset.sum_le_sum fun X _ ↦ h.norm_le X
      _ = (Fintype.card (ChainSupport L 1) : ℝ) * J := by simp
      _ ≤ (2 * L : ℝ) * J :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast card_chainSupport_range_one_le L) hJ

end TNLean.MPS.AreaLaw
