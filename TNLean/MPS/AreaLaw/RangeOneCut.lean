/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hamiltonian
import TNLean.Lattice.ZeroEntropy

/-!
# Splitting a range-one Hamiltonian at a cut

A range-one interaction crossing the cut after the first `k` sites is supported on the
adjacent pair at that cut. Positive interactions of norm at most one therefore give a
decomposition `H = H_L + H_R + K`, with `0 ≤ K ≤ 1`.

This is the Hamiltonian decomposition used by Landau, Vazirani and Vidick,
arXiv:1307.5143v1, `References/1307.5143/algo53.tex`, lines 283 and 409–410.
-/

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw

/-- An interaction of range one meeting both sides of a cut is the adjacent pair at that
cut. Source: LVV13, `algo53.tex`, the nearest-neighbour assumption at line 283 and the cut
decomposition at lines 409–410. -/
theorem IsChainSupport.eq_interval_of_splits_of_range_one {L k : ℕ} {X : Finset (Fin L)}
    (hX : IsChainSupport L 1 X)
    (hsplit : (∃ x ∈ X, x.val < k) ∧ ∃ y ∈ X, k ≤ y.val) :
    X = interval L (k - 1) (k + 1) := by
  obtain ⟨⟨x, hx, hxk⟩, y, hy, hky⟩ := hsplit
  have htwo : X.card = 2 := by
    have hcard := hX.card_le
    have hlt : 1 < X.card := Finset.one_lt_card.mpr
      ⟨x, hx, y, hy, by rintro rfl; omega⟩
    omega
  obtain ⟨a, -, hXa⟩ := hX.exists_eq_interval_of_card_eq htwo
  have hak : k = a + 1 := by
    have hax := mem_interval.mp ((Finset.ext_iff.mp hXa x).mp hx)
    have hay := mem_interval.mp ((Finset.ext_iff.mp hXa y).mp hy)
    omega
  rw [hXa]
  congr 1 <;> omega

/-- Positive range-one interactions of norm at most one split at every cut as
`H = H_L + H_R + K`, with the two parts supported on their respective sides and
`0 ≤ K ≤ 1`. Source: LVV13, `algo53.tex`, line 283 and lines 409–410. -/
theorem ChainHamiltonian.exists_cut_decomposition_of_range_one {L q : ℕ}
    (h : ChainHamiltonian L q 1 1) (hpos : ∀ X, (h.term X).PosSemidef) (k : ℕ) :
    ∃ HL HR K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ,
      h.operator = HL + HR + K ∧
      Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) HL (interval L 0 k) ∧
      Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) HR (interval L 0 k)ᶜ ∧
      K.PosSemidef ∧ (1 - K).PosSemidef := by
  classical
  let A := interval L 0 k
  let S := Finset.univ.filter fun X : ChainSupport L 1 ↦ X.1 ⊆ A
  let U := Finset.univ.filter fun X : ChainSupport L 1 ↦ ¬X.1 ⊆ A
  let T := U.filter fun X ↦ X.1 ⊆ Aᶜ
  let C := U.filter fun X ↦ ¬X.1 ⊆ Aᶜ
  have hcross (X : ChainSupport L 1) (hXC : X ∈ C) :
      X.1 = interval L (k - 1) (k + 1) := by
    have hnotL := (Finset.mem_filter.mp (Finset.mem_filter.mp hXC).1).2
    have hnotR := (Finset.mem_filter.mp hXC).2
    apply X.2.eq_interval_of_splits_of_range_one
    constructor
    · obtain ⟨x, hx, hxA⟩ := Finset.not_subset.mp hnotR
      exact ⟨x, hx, by simpa [A, mem_interval] using hxA⟩
    · obtain ⟨y, hy, hyA⟩ := Finset.not_subset.mp hnotL
      refine ⟨y, hy, ?_⟩
      have : ¬y.val < k := by simpa [A, mem_interval] using hyA
      omega
  have hcard : C.card ≤ 1 := Finset.card_le_one.mpr fun X hX Y hY ↦
    Subtype.ext ((hcross X hX).trans (hcross Y hY).symm)
  let K := ∑ X ∈ C, h.term X
  have hK : K.PosSemidef := posSemidef_sum C fun X _ ↦ hpos X
  have hKn : ‖K‖ ≤ 1 := by
    calc
      ‖K‖ ≤ ∑ _ ∈ C, (1 : ℝ) := norm_sum_le_of_le C fun X _ ↦ h.norm_le X
      _ ≤ 1 := by simpa using (show (C.card : ℝ) ≤ 1 by exact_mod_cast hcard)
  have hK1 : (1 - K).PosSemidef :=
    Matrix.le_iff.mp ((CStarAlgebra.norm_le_one_iff_of_nonneg _ hK.nonneg).mp hKn)
  let HL := ∑ X ∈ S, h.term X
  let HR := ∑ X ∈ T, h.term X
  refine ⟨HL, HR, K, ?_, ?_, ?_, hK, hK1⟩
  · have hSU : h.operator = HL + ∑ X ∈ U, h.term X :=
      (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun X : ChainSupport L 1 ↦ X.1 ⊆ A) h.term).symm
    have hTC : (∑ X ∈ U, h.term X) = HR + K :=
      (Finset.sum_filter_add_sum_filter_not U (fun X ↦ X.1 ⊆ Aᶜ) h.term).symm
    rw [hSU, hTC, add_assoc]
  · exact TNLean.Lattice.isSupportedOn_sum S fun X hX ↦
      (h.supported X).mono (Finset.mem_filter.mp hX).2
  · exact TNLean.Lattice.isSupportedOn_sum T fun X hX ↦
      (h.supported X).mono (Finset.mem_filter.mp hX).2

end TNLean.MPS.AreaLaw
