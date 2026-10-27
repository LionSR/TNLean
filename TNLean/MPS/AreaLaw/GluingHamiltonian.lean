/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.RangeOneSupport
import TNLean.Lattice.ZeroEntropy

/-!
# The Hamiltonian on one side of a boundary site

At a cut after the first `k` sites, the interactions not wholly to the left act on the
boundary site and the right part of the chain. Their sum has norm at most `2L`.

This is the decomposition `H = H_L + (H_R + H_i)` used in Landau, Vazirani and Vidick,
arXiv:1307.5143v1, `algo53.tex`, lines 409–410. The native range-one model also
permits one-site terms and arbitrary Hermitian contractions.
-/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- A normalized range-one Hamiltonian splits into a left-supported part and a part
supported from the boundary site onward, whose norm is at most `2L`.
Source: LVV13, arXiv:1307.5143v1, `algo53.tex`, lines 409–410. -/
theorem ChainHamiltonian.exists_gluing_decomposition_of_range_one {L q : ℕ}
    (h : ChainHamiltonian L q 1 1) (k : ℕ) :
    ∃ HL B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ,
      h.operator = HL + B ∧
      Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) HL (interval L 0 k) ∧
      Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) B (interval L 0 (k - 1))ᶜ ∧
      ‖B‖ ≤ 2 * (L : ℝ) := by
  classical
  let A := interval L 0 k
  have hright (X : ChainSupport L 1) (hX : ¬X.1 ⊆ A) :
      X.1 ⊆ (interval L 0 (k - 1))ᶜ := by
    obtain ⟨y, hy, hyA⟩ := Finset.not_subset.mp hX
    have hyk : k ≤ y.val := by simpa [A, mem_interval, not_lt] using hyA
    intro x hx
    have hxk : k - 1 ≤ x.val := Nat.sub_le_iff_le_add.mpr (hyk.trans (X.2.2 x hx y hy))
    simpa [mem_interval, not_lt] using hxk
  let S := Finset.univ.filter fun X : ChainSupport L 1 ↦ X.1 ⊆ A
  let U := Finset.univ.filter fun X : ChainSupport L 1 ↦ ¬X.1 ⊆ A
  refine ⟨∑ X ∈ S, h.term X, ∑ X ∈ U, h.term X, ?_, ?_, ?_, ?_⟩
  · exact (Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun X : ChainSupport L 1 ↦ X.1 ⊆ A) h.term).symm
  · exact TNLean.Lattice.isSupportedOn_sum S fun X hX ↦
      (h.supported X).mono (Finset.mem_filter.mp hX).2
  · exact TNLean.Lattice.isSupportedOn_sum U fun X hX ↦
      (h.supported X).mono (hright X (Finset.mem_filter.mp hX).2)
  · have hcard : U.card ≤ 2 * L :=
      (Finset.card_le_univ U).trans (card_chainSupport_range_one_le L)
    calc
      _ ≤ ∑ _ ∈ U, (1 : ℝ) := norm_sum_le_of_le U fun X _ ↦ h.norm_le X
      _ ≤ 2 * (L : ℝ) := by
        simpa using (show (U.card : ℝ) ≤ 2 * (L : ℝ) by exact_mod_cast hcard)

end TNLean.MPS.AreaLaw
