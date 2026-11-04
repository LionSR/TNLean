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
arXiv:1307.5143v1, `algo53.tex`, lines 409–410, given as the named parts `cutLeftPart` and
`cutBoundaryPart` of the Hamiltonian at a cut. The native range-one model also permits
one-site terms and arbitrary Hermitian contractions.
-/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ}

/-- The sum of the interactions wholly inside the first `k` sites.
Source: LVV13, arXiv:1307.5143v1, `algo53.tex`, lines 409–410, the term `H_L`. -/
noncomputable def ChainHamiltonian.cutLeftPart (h : ChainHamiltonian L q 1 1) (k : ℕ) :
    Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
  ∑ X ∈ Finset.univ.filter (fun X : ChainSupport L 1 ↦ X.1 ⊆ interval L 0 k), h.term X

/-- The sum of the interactions not wholly inside the first `k` sites: those acting on the
boundary site `k - 1` and the right part of the chain.
Source: LVV13, arXiv:1307.5143v1, `algo53.tex`, lines 409–410, the term `H_R + H_i`. -/
noncomputable def ChainHamiltonian.cutBoundaryPart (h : ChainHamiltonian L q 1 1) (k : ℕ) :
    Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
  ∑ X ∈ Finset.univ.filter (fun X : ChainSupport L 1 ↦ ¬ X.1 ⊆ interval L 0 k), h.term X

/-- The Hamiltonian is the sum of its left part and its boundary part at every cut. -/
theorem ChainHamiltonian.cutLeftPart_add_cutBoundaryPart (h : ChainHamiltonian L q 1 1) (k : ℕ) :
    h.operator = h.cutLeftPart k + h.cutBoundaryPart k :=
  (Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun X : ChainSupport L 1 ↦ X.1 ⊆ interval L 0 k) h.term).symm

/-- The left part is supported on the first `k` sites. -/
theorem ChainHamiltonian.cutLeftPart_isSupportedOn (h : ChainHamiltonian L q 1 1) (k : ℕ) :
    Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h.cutLeftPart k) (interval L 0 k) :=
  TNLean.Lattice.isSupportedOn_sum _ fun X hX ↦
    (h.supported X).mono (Finset.mem_filter.mp hX).2

/-- The boundary part is supported from the boundary site onward. -/
theorem ChainHamiltonian.cutBoundaryPart_isSupportedOn (h : ChainHamiltonian L q 1 1) (k : ℕ) :
    Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h.cutBoundaryPart k)
      (interval L 0 (k - 1))ᶜ := by
  refine TNLean.Lattice.isSupportedOn_sum _ fun X hX ↦ (h.supported X).mono ?_
  have hX' := (Finset.mem_filter.mp hX).2
  obtain ⟨y, hy, hyA⟩ := Finset.not_subset.mp hX'
  have hyk : k ≤ y.val := by simpa [mem_interval, not_lt] using hyA
  intro x hx
  have hxk : k - 1 ≤ x.val := Nat.sub_le_iff_le_add.mpr (hyk.trans (X.2.2 x hx y hy))
  simpa [mem_interval, not_lt] using hxk

/-- The boundary part has norm at most `2L`. -/
theorem ChainHamiltonian.norm_cutBoundaryPart_le (h : ChainHamiltonian L q 1 1) (k : ℕ) :
    ‖h.cutBoundaryPart k‖ ≤ 2 * (L : ℝ) := by
  classical
  set U := Finset.univ.filter (fun X : ChainSupport L 1 ↦ ¬ X.1 ⊆ interval L 0 k)
  have hcard : U.card ≤ 2 * L :=
    (Finset.card_le_univ U).trans (card_chainSupport_range_one_le L)
  calc
    _ ≤ ∑ _ ∈ U, (1 : ℝ) := norm_sum_le_of_le U fun X _ ↦ h.norm_le X
    _ ≤ 2 * (L : ℝ) := by
      simpa using (show (U.card : ℝ) ≤ 2 * (L : ℝ) by exact_mod_cast hcard)

/-- A normalized range-one Hamiltonian splits into a left-supported part and a part
supported from the boundary site onward, whose norm is at most `2L`: the existence form
of the named decomposition `cutLeftPart` plus `cutBoundaryPart`.
Source: LVV13, arXiv:1307.5143v1, `algo53.tex`, lines 409–410. -/
theorem ChainHamiltonian.exists_gluing_decomposition_of_range_one
    (h : ChainHamiltonian L q 1 1) (k : ℕ) :
    ∃ HL B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ,
      h.operator = HL + B ∧
      Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) HL (interval L 0 k) ∧
      Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) B (interval L 0 (k - 1))ᶜ ∧
      ‖B‖ ≤ 2 * (L : ℝ) :=
  ⟨h.cutLeftPart k, h.cutBoundaryPart k, h.cutLeftPart_add_cutBoundaryPart k,
    h.cutLeftPart_isSupportedOn k, h.cutBoundaryPart_isSupportedOn k,
    h.norm_cutBoundaryPart_le k⟩

end TNLean.MPS.AreaLaw
