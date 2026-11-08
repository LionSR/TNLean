/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Huang.ChainGrid
import TNLean.Circuit.EntropySupport
import TNLean.Algebra.MatrixHermitianSum

/-!
# The Hamiltonian decomposition associated with the uniform grid

For original nearest-neighbor interaction terms, sum the edges internal to each explicit
grid block and retain the omitted grid-boundary edges separately. The resulting block
Hamiltonians have disjoint supports. Their sum differs from the original Hamiltonian
by exactly the omitted edges.

This is the physical decomposition in Osborne, arXiv:quant-ph/0508031v2, Figures 1--2
and equations (2)--(3), used in Huang, arXiv:1406.6355v6, Section 5.4, Lemma 19.
-/

open Matrix QuantumCircuit
open scoped BigOperators Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

variable {L q w : ℕ}

/-- The edge immediately before an internal grid boundary. Osborne, Figure 2. -/
def chainGridBoundaryEdge (hw : 0 < w) (k : Fin ((L - 1) / w)) : Fin (L - 1) :=
  ⟨chainGridCut w k.val - 1, by
    have hc := chainGridCut_bounds hw k
    omega⟩

/-- The right endpoint of a boundary edge is its grid cut. Osborne, Figure 2. -/
theorem chainGridBoundaryEdge_val_succ (hw : 0 < w) (k : Fin ((L - 1) / w)) :
    (chainGridBoundaryEdge hw k).val + 1 = chainGridCut w k.val := by
  have hc := (chainGridCut_bounds hw k).1
  dsimp only [chainGridBoundaryEdge]
  omega

/-- Different grid boundaries give different original nearest-neighbor edges.
Osborne, Figure 2. -/
theorem chainGridBoundaryEdge_injective (hw : 0 < w) :
    Function.Injective (chainGridBoundaryEdge (L := L) hw) := by
  intro j k hjk
  have hval := congrArg Fin.val hjk
  have hj := chainGridBoundaryEdge_val_succ hw j
  have hk := chainGridBoundaryEdge_val_succ hw k
  have hprod : (j.val + 1) * w = (k.val + 1) * w := by
    change chainGridCut w j.val = chainGridCut w k.val
    omega
  have hsucc : j.val + 1 = k.val + 1 := mul_right_cancel₀ hw.ne' hprod
  exact Fin.ext (by omega)

/-- The original edge indices omitted from the within-block Hamiltonians. Osborne, Figure 2. -/
noncomputable def chainGridBoundaryEdges (hw : 0 < w) : Finset (Fin (L - 1)) :=
  Finset.univ.image (chainGridBoundaryEdge hw)

/-- The block owner of the left endpoint of an edge. Osborne, Figure 2. -/
def chainGridEdgeOwner (w : ℕ) (i : Fin (L - 1)) : Fin (L / w + 1) :=
  chainGridOwner w ⟨i.val, lt_of_lt_of_le i.isLt (Nat.sub_le L 1)⟩

/-- An edge not omitted at a grid boundary lies inside its explicitly assigned block.
Osborne, arXiv:quant-ph/0508031v2, Figure 2. -/
theorem chainGridEdge_subset_ownerBlock (hw : 0 < w) (i : Fin (L - 1))
    (hi : i ∉ chainGridBoundaryEdges hw) :
    interval L i.val (i.val + 2) ⊆ chainGridBlock L w (chainGridEdgeOwner w i).val := by
  classical
  have hnot : ¬ ∃ k : Fin ((L - 1) / w), chainGridCut w k.val = i.val + 1 := by
    rintro ⟨k, hk⟩
    have heq : chainGridBoundaryEdge hw k = i := by
      apply Fin.ext
      have h := chainGridBoundaryEdge_val_succ hw k
      omega
    exact hi (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, heq⟩)
  obtain ⟨j, hj⟩ := (chainGrid_edge_in_block_iff hw (by omega : i.val + 1 < L)).mpr hnot
  let x : Fin L := ⟨i.val, lt_of_lt_of_le i.isLt (Nat.sub_le L 1)⟩
  have hxedge : x ∈ interval L i.val (i.val + 2) :=
    mem_interval.mpr (show i.val ≤ i.val ∧ i.val < i.val + 2 by omega)
  have hxj := hj hxedge
  have hxown := mem_chainGridBlock_owner hw x
  have heq : j.val = (chainGridEdgeOwner w i).val := by
    by_contra hne
    have hdisj := pairwise_disjoint_chainGridBlock L w hne
    exact Finset.disjoint_left.mp hdisj hxj hxown
  simpa only [heq] using hj

/-- The sum of original terms internal to one explicit grid block. Osborne, Figure 2. -/
noncomputable def chainGridBlockHamiltonian (hw : 0 < w)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (j : Fin (L / w + 1)) : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
  ∑ i ∈ Finset.univ.filter (fun i ↦ i ∉ chainGridBoundaryEdges hw ∧ chainGridEdgeOwner w i = j), h i

/-- The retained interaction is the sum of the within-block Hamiltonians. Osborne, Figure 2. -/
noncomputable def chainGridRetainedHamiltonian (hw : 0 < w)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) :=
  ∑ j, chainGridBlockHamiltonian hw h j

/-- The signed omitted term gives the convention `H = A - ∑ B_k`. Osborne, equations (2)--(3). -/
noncomputable def chainGridBoundaryTerm (hw : 0 < w)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (k : Fin ((L - 1) / w)) := -h (chainGridBoundaryEdge hw k)

/-- The block sum retains exactly the edges not crossing grid boundaries. Osborne, Figure 2. -/
theorem chainGridRetainedHamiltonian_eq_sum_filter (hw : 0 < w)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) :
    chainGridRetainedHamiltonian hw h =
      ∑ i ∈ Finset.univ.filter (fun i ↦ i ∉ chainGridBoundaryEdges hw), h i := by
  classical
  unfold chainGridRetainedHamiltonian chainGridBlockHamiltonian
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ chainGridBoundaryEdges hw
  · simp [hi]
  · simp [hi, eq_comm]

/-- The original Hamiltonian is the retained block sum minus the signed omitted terms.
All terms and labels are constructed from the original nearest-neighbor interactions.
Osborne, arXiv:quant-ph/0508031v2, equations (2)--(3) and Figure 2. -/
theorem sum_eq_chainGridRetained_sub_boundary (hw : 0 < w)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) :
    (∑ i, h i) = chainGridRetainedHamiltonian hw h - ∑ k, chainGridBoundaryTerm hw h k := by
  classical
  have himage : (∑ i ∈ chainGridBoundaryEdges hw, h i) =
      ∑ k, h (chainGridBoundaryEdge hw k) := by
    rw [chainGridBoundaryEdges, Finset.sum_image]
    exact fun _ _ _ _ h ↦ chainGridBoundaryEdge_injective hw h
  have hfilter : Finset.univ.filter (fun i : Fin (L - 1) ↦ i ∈ chainGridBoundaryEdges hw) =
      chainGridBoundaryEdges hw := by ext i; simp
  have hsplit := Finset.sum_filter_not_add_sum_filter Finset.univ
    (fun i : Fin (L - 1) ↦ i ∈ chainGridBoundaryEdges hw) h
  rw [hfilter, himage] at hsplit
  rw [chainGridRetainedHamiltonian_eq_sum_filter]
  simpa only [chainGridBoundaryTerm, Finset.sum_neg_distrib, sub_neg_eq_add] using hsplit.symm

/-- A constructed block Hamiltonian is supported on its own block.
Osborne, Figure 2. -/
theorem chainGridBlockHamiltonian_mem_supported (hw : 0 < w)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h i)
      (interval L i.val (i.val + 2))) (j : Fin (L / w + 1)) :
    chainGridBlockHamiltonian hw h j ∈
      supportedOperators q (chainGridBlock L w j.val : Set (Fin L)) := by
  classical
  apply Submodule.sum_mem
  intro i hi
  obtain ⟨hinot, hiowner⟩ := (Finset.mem_filter.mp hi).2
  have hsub := chainGridEdge_subset_ownerBlock hw i hinot
  rw [hiowner] at hsub
  exact mem_supportedOperators_of_isSupportedOn ((hs i).mono hsub)

/-- Hermiticity of each original term implies Hermiticity of each retained block.
Osborne, equations (2)--(3). -/
theorem isHermitian_chainGridBlockHamiltonian (hw : 0 < w)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hHerm : ∀ i, (h i).IsHermitian) (j : Fin (L / w + 1)) :
    (chainGridBlockHamiltonian hw h j).IsHermitian :=
  Matrix.isHermitian_sum _ fun i _ ↦ hHerm i

end TNLean.MPS.AreaLaw
