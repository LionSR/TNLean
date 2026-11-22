/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Chain.RangeOneSupport
import QICLean.ManyBody.Entropy.ZeroEntropy

/-!
# The Hamiltonian on one side of a boundary site

At a cut after the first `k` sites, the interactions not wholly to the left act on the
boundary site and the right part of the chain. Their sum has norm at most `2L`.

This is the decomposition `H = H_L + (H_R + H_i)` used in Landau, Vazirani and Vidick,
arXiv:1307.5143v1, `algo53.tex`, lines 409–410: `H_L` is the partial Hamiltonian
`ManyBody.Interaction.partialHamiltonian` of the supports inside the first `k` sites, and
`H_R + H_i` is the partial Hamiltonian of the other supports. The native range-one model also
permits one-site terms and arbitrary Hermitian contractions.
-/

open ManyBody (ChainSupport interval mem_interval ChainInteraction)

open Matrix
open scoped Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ}

/-- The sum of the interactions not wholly inside the first `k` sites, those acting on the
boundary site `k - 1` and the right part of the chain, is supported from the boundary site
onward. Source: LVV13, arXiv:1307.5143v1, `algo53.tex`, lines 409–410, the term
`H_R + H_i`. -/
theorem _root_.ManyBody.ChainInteraction.isSupportedOn_partialHamiltonian_not_subset
    (h : ChainInteraction L q 1) (k : ℕ) :
    ManyBody.IsSupportedOn (X := fun _ ↦ Fin q)
      (h.partialHamiltonian (Finset.univ.filter fun X : ChainSupport L 1 ↦
        ¬ X.1 ⊆ interval L 0 k))
      (interval L 0 (k - 1))ᶜ := by
  change _ ∈ ManyBody.supportedOperators _ _
  refine h.partialHamiltonian_mem_supportedOperators fun X hX ↦ ?_
  have hX' := (Finset.mem_filter.mp hX).2
  obtain ⟨y, hy, hyA⟩ := Finset.not_subset.mp hX'
  have hyk : k ≤ y.val := by simpa [mem_interval, not_lt] using hyA
  intro x hx
  have hxk : k - 1 ≤ x.val := Nat.sub_le_iff_le_add.mpr (hyk.trans (X.2.2 x hx y hy))
  simpa [mem_interval, not_lt] using hxk

/-- The sum of the interactions not wholly inside the first `k` sites has norm at most `2L`
when every term has norm at most one. -/
theorem _root_.ManyBody.ChainInteraction.norm_partialHamiltonian_not_subset_le
    (h : ChainInteraction L q 1) (hhJ : ∀ X, ‖h.term X‖ ≤ 1) (k : ℕ) :
    ‖h.partialHamiltonian (Finset.univ.filter fun X : ChainSupport L 1 ↦
        ¬ X.1 ⊆ interval L 0 k)‖ ≤ 2 * (L : ℝ) := by
  classical
  set U := Finset.univ.filter (fun X : ChainSupport L 1 ↦ ¬ X.1 ⊆ interval L 0 k)
  have hcard : U.card ≤ 2 * L :=
    (Finset.card_le_univ U).trans (card_chainSupport_range_one_le L)
  calc
    _ ≤ ∑ _ ∈ U, (1 : ℝ) := norm_sum_le_of_le U fun X _ ↦ hhJ X
    _ ≤ 2 * (L : ℝ) := by
      simpa using (show (U.card : ℝ) ≤ 2 * (L : ℝ) by exact_mod_cast hcard)

/-- A normalized range-one Hamiltonian splits into a left-supported part and a part
supported from the boundary site onward, whose norm is at most `2L`: the partial
Hamiltonians of the supports inside the first `k` sites and of the other supports.
Source: LVV13, arXiv:1307.5143v1, `algo53.tex`, lines 409–410. -/
theorem _root_.ManyBody.ChainInteraction.exists_gluing_decomposition_of_range_one
    (h : ChainInteraction L q 1) (hhJ : ∀ X, ‖h.term X‖ ≤ 1) (k : ℕ) :
    ∃ HL B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ,
      h.hamiltonian = HL + B ∧
      ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) HL (interval L 0 k) ∧
      ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) B (interval L 0 (k - 1))ᶜ ∧
      ‖B‖ ≤ 2 * (L : ℝ) :=
  ⟨h.partialHamiltonian (Finset.univ.filter fun X : ChainSupport L 1 ↦ X.1 ⊆ interval L 0 k),
    h.partialHamiltonian (Finset.univ.filter fun X : ChainSupport L 1 ↦ ¬ X.1 ⊆ interval L 0 k),
    (h.partialHamiltonian_filter_add_filter_not fun X : ChainSupport L 1 ↦
      X.1 ⊆ interval L 0 k).symm,
    h.partialHamiltonian_mem_supportedOperators fun _ hX ↦ (Finset.mem_filter.mp hX).2,
    h.isSupportedOn_partialHamiltonian_not_subset k,
    h.norm_partialHamiltonian_not_subset_le hhJ k⟩

end TNLean.MPS.AreaLaw
