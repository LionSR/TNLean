/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularRegionGram
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Sym.Sym2.Order

/-!
# The cycle exponent in a connected regular region

The internal edges of a region are the edges of its induced graph. A nonempty
connected induced graph with `v` vertices and `i` internal edges has `v ≤ i + 1`.
Consequently the ratio of group-order powers in its regular-bond Gram scalar is
`|G| ^ (i + 1 - v)`, with no truncation of a negative integer exponent. For a tree
the exponent is zero.

These are auxiliary graph-counting facts for the finite-region contraction in
Schuch, Cirac, and Pérez-García, arXiv:1001.3807, lines 1935–1957. They do not
assert the full physical entropy theorem.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators

namespace TNLean.PEPS

variable {V : Type*} [LinearOrder V] {Γ : SimpleGraph V}

private theorem adj_inf_sup_of_mem_edgeSet (e : Sym2 V) (he : e ∈ Γ.edgeSet) :
    Γ.Adj e.inf e.sup := by
  cases e using Sym2.ind with
  | _ u v =>
    change Γ.Adj u v at he
    rcases le_total u v with h | h
    · simpa [h] using he
    · simpa [h] using he.symm

/-- Ordered endpoint pairs and Mathlib's unordered graph edges describe the
same edges. The inverse sorts the two endpoints. -/
def orderedEdgeEquivEdgeSet : Edge Γ ≃ Γ.edgeSet where
  toFun e := ⟨s(e.1.1, e.1.2), e.2.2⟩
  invFun e := ⟨(e.1.inf, e.1.sup),
    lt_of_le_of_ne (Sym2.inf_le_sup e.1)
      (Γ.ne_of_adj (adj_inf_sup_of_mem_edgeSet e.1 e.2)),
    adj_inf_sup_of_mem_edgeSet e.1 e.2⟩
  left_inv e := by
    apply Subtype.ext
    simp [e.2.1.le]
  right_inv e := Subtype.ext (Sym2.sortEquiv.left_inv e.1)

/-- An edge of the induced region graph is exactly an edge of the ambient
graph with both endpoints in the region. -/
def inducedRegionEdgeEquiv (R : Finset V) :
    Edge (Γ.induce (R : Set V)) ≃ {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R} where
  toFun e := ⟨⟨(e.1.1.1, e.1.2.1), e.2.1, e.2.2⟩, e.1.1.2, e.1.2.2⟩
  invFun e := ⟨(⟨e.1.1.1, e.2.1⟩, ⟨e.1.1.2, e.2.2⟩), e.1.2.1, e.1.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable [Fintype V] [DecidableRel Γ.Adj]

/-- The internal-edge count agrees with the edge count of the induced graph. -/
theorem card_inducedRegion_edgeSet (R : Finset V) :
    Nat.card (Γ.induce (R : Set V)).edgeSet =
      Fintype.card {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R} := by
  rw [← Nat.card_congr (orderedEdgeEquivEdgeSet (Γ := Γ.induce (R : Set V))),
    Nat.card_congr (inducedRegionEdgeEquiv (Γ := Γ) R), Nat.card_eq_fintype_card]

/-- Source: SCP10, finite-region contraction, lines 1935–1957. A nonempty
connected region has at least its number of vertices minus one internal edges. -/
theorem region_card_le_internalEdge_card_add_one (R : Finset V)
    (hR : (Γ.induce (R : Set V)).Connected) :
    R.card ≤ Fintype.card {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R} + 1 := by
  have h := hR.card_vert_le_card_edgeSet_add_one
  rw [card_inducedRegion_edgeSet] at h
  simpa [Nat.card_eq_fintype_card] using h

/-- In a tree region the number of internal edges is exactly one less than
the number of vertices. -/
theorem internalEdge_card_add_one_eq_card_of_isTree (R : Finset V)
    (hR : (Γ.induce (R : Set V)).IsTree) :
    Fintype.card {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R} + 1 = R.card := by
  have h := (SimpleGraph.isTree_iff_connected_and_card.mp hR).2
  rw [card_inducedRegion_edgeSet] at h
  simpa [Nat.card_eq_fintype_card] using h

variable {G : Type*} [Group G] [Fintype G]

/-- Source: SCP10, connected regular-region contraction, lines 1935–1957.
The group-order ratio is the group order raised to the cycle exponent.
Connectedness ensures that the natural subtraction represents a nonnegative
integer difference. -/
theorem regionGroupOrder_pow_div_pow_eq_cycleRank (R : Finset V)
    (hR : (Γ.induce (R : Set V)).Connected) :
    (Fintype.card G : ℂ) ^
        (Fintype.card {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R} + 1) /
        (Fintype.card G : ℂ) ^ R.card =
      (Fintype.card G : ℂ) ^
        (Fintype.card {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R} + 1 - R.card) := by
  exact (pow_sub₀ (Fintype.card G : ℂ) (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    (region_card_le_internalEdge_card_add_one R hR)).symm

/-- Including the site factors gives the cycle-exponent expression for the
regular-region Gram scalar. Source: SCP10, finite-region contraction,
lines 1935–1957. -/
theorem regularRegionGramScalar_eq_cycleRank (c : V → ℂ) (R : Finset V)
    (hR : (Γ.induce (R : Set V)).Connected) :
    regularRegionGramScalar (Γ := Γ) (G := G) c R =
      (∏ v : {v : V // v ∈ R}, c v.1) * (Fintype.card G : ℂ) ^
        (Fintype.card {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R} + 1 - R.card) := by
  rw [regularRegionGramScalar, mul_div_assoc, regionGroupOrder_pow_div_pow_eq_cycleRank R hR]

/-- Tree regions introduce no additional group-order factor. -/
theorem regularRegionGramScalar_eq_prod_of_isTree (c : V → ℂ) (R : Finset V)
    (hR : (Γ.induce (R : Set V)).IsTree) :
    regularRegionGramScalar (Γ := Γ) (G := G) c R =
      ∏ v : {v : V // v ∈ R}, c v.1 := by
  rw [regularRegionGramScalar, internalEdge_card_add_one_eq_card_of_isTree R hR, mul_div_assoc,
    div_self (pow_ne_zero _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)), mul_one]

end TNLean.PEPS
