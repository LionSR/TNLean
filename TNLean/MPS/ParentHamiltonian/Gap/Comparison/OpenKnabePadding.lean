/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.Combinatorics.FinSum
import TNLean.MPS.ParentHamiltonian.Gap.Comparison.CyclicWindowOpenHamiltonian
import TNLean.MPS.ParentHamiltonian.Gap.Filtration.FixedAmbient

/-!
# Zero padding of open-chain interactions into a cyclic family

The local terms of an open \(N\)-site chain can be indexed by a cyclic group
\(\mathbb Z/P\mathbb Z\), with \(P\ge N\), by setting every term beyond
the last nonwrapping start equal to zero. Their sum remains the original open
Hamiltonian. The padded terms are symmetric projections and commute at every
oriented cyclic separation of at least the interaction range.

This construction permits the cyclic finite-range Knabe inequality to be
applied to open chains. The resulting open-chain criterion is a consequence
of the finite-range coefficient derivation documented in
`docs/paper-gaps/knabe88_finite_range_coefficient.tex`; it is not the
nearest-neighbor periodic statement printed in Knabe (1988).
-/

open scoped BigOperators

namespace MPSTensor

variable {α : Type*} [Fintype α] [DecidableEq α] {D : ℕ}

/-- The Hamiltonian of the windows of the open chain that start at one position is the term of
that window, and vanishes when no window starts there. -/
theorem hamiltonian_restrict_parentChainInteraction_val_eq (A : MPTensor α (Fin D)) (R N k : ℕ) :
    ((parentChainInteraction A R N).restrict fun i ↦ i.val = k).hamiltonian =
      if h : k < N + 1 - R then (parentChainInteraction A R N).term ⟨k, h⟩ else 0 := by
  rw [ManyBody.Interaction.hamiltonian]
  split_ifs with h
  · refine (Finset.sum_eq_single_of_mem _ (Finset.mem_univ ⟨k, h⟩) fun i _ hi ↦ ?_).trans ?_
    · exact ManyBody.Interaction.restrict_term_of_neg fun hv ↦ hi (Fin.ext hv)
    · exact ManyBody.Interaction.restrict_term_of_pos rfl
  · exact Finset.sum_eq_zero fun i _ ↦
      ManyBody.Interaction.restrict_term_of_neg fun hv ↦ h (hv ▸ i.isLt)

/-- Every member of the zero-padded cyclic family of an open chain, the Hamiltonian of the
windows starting at one position, is an orthogonal projection, including the zero members. -/
theorem isStarProjection_hamiltonian_restrict_parentChainInteraction_val_eq
    (A : MPTensor α (Fin D)) (R N k : ℕ) :
    IsStarProjection ((parentChainInteraction A R N).restrict fun i ↦ i.val = k).hamiltonian := by
  rw [hamiltonian_restrict_parentChainInteraction_val_eq]
  split_ifs
  · exact isStarProjection_parentChainInteraction_term A R N _
  · exact .zero _

/-- The members of the zero-padded cyclic family of an open chain commute at every oriented
cyclic separation between \(R\) and \(P-R\), as required by the cyclic Knabe inequality. -/
theorem commute_hamiltonian_restrict_parentChainInteraction_of_oriented_separation
    {N P R e : ℕ} [NeZero P] (A : MPTensor α (Fin D))
    (hR : 0 < R) (heR : R ≤ e) (heP : e + R ≤ P) (s : ZMod P) :
    Commute ((parentChainInteraction A R N).restrict fun i ↦ i.val = s.val).hamiltonian
      ((parentChainInteraction A R N).restrict fun i ↦
        i.val = (s + (e : ZMod P)).val).hamiltonian := by
  have he : e < P := by omega
  have hval : (e : ZMod P).val = e := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt he]
  have hsep : s.val + R ≤ (s + (e : ZMod P)).val ∨
      (s + (e : ZMod P)).val + R ≤ s.val := by
    by_cases hwrap : s.val + e < P
    · left
      rw [ZMod.val_add, hval, Nat.mod_eq_of_lt hwrap]
      omega
    · right
      have h := ZMod.val_add_val_of_le (a := s) (b := (e : ZMod P)) (by omega)
      rw [hval] at h
      omega
  refine ManyBody.Interaction.commute_hamiltonian_restrict _ _ fun i j hi hj ↦ ?_
  rcases hsep with hsep | hsep
  · exact commute_parentChainInteraction_term_of_add_le A (by omega)
  · exact (commute_parentChainInteraction_term_of_add_le A (by omega)).symm

/-- If the cyclic period is at least the physical volume, summing the zero-padded cyclic family
gives the Hamiltonian of the parent interaction on the open chain. -/
theorem sum_hamiltonian_restrict_parentChainInteraction_val_eq
    {N P R : ℕ} [NeZero P] (A : MPTensor α (Fin D)) (hR : 0 < R) (hNP : N ≤ P) :
    ∑ s : ZMod P, ((parentChainInteraction A R N).restrict fun i ↦ i.val = s.val).hamiltonian =
      (parentChainInteraction A R N).hamiltonian := by
  rw [ManyBody.Interaction.sum_hamiltonian_restrict_eq_hamiltonian_restrict Finset.univ _
    (fun _ ↦ True) (fun i ↦ (i.val : ZMod P)) (fun _ _ ↦ Finset.mem_univ _) fun i n _ ↦ ?_]
  · exact Finset.sum_congr rfl fun i _ ↦ ManyBody.Interaction.restrict_term_of_pos trivial
  · have hi : i.val < P := by have := i.isLt; omega
    refine ⟨fun h ↦ ⟨trivial, ?_⟩, fun h ↦ ?_⟩
    · rw [h, ZMod.natCast_zmod_val]
    · rw [h.2, ZMod.val_natCast, Nat.mod_eq_of_lt hi]

end MPSTensor
