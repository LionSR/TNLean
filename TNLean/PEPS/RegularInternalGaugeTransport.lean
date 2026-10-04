/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularWalkHolonomy
import TNLean.PEPS.RegularTwoCycleGlobalFluxMove

/-!
# Directed transport of reconstructed internal operators

Reconstruction by vertex labels changes a directed operator by left
multiplication at its target and inverse right multiplication at its source.
This elementary group identity is auxiliary to the accessible-coordinate
construction of SCP10, arXiv:1001.3807, lines 1765–1920.
-/

namespace TNLean.PEPS
variable {V : Type*} [LinearOrder V] {Γ : SimpleGraph V}
variable {G : Type*} [Group G]

/-- An internal reconstruction determines transport in either traversal
orientation. This is an auxiliary algebraic identity for SCP10, lines 1765–1920. -/
theorem regularDirectedTransport_eq_of_internal_reconstruction (R : Finset V)
    (k : {v : V // v ∈ R} → G) (u w : Edge Γ → G)
    (hw : ∀ (e : Edge Γ) (he : e.1.1 ∈ R ∧ e.1.2 ∈ R),
      w e = k ⟨e.1.2, he.2⟩ * u e * (k ⟨e.1.1, he.1⟩)⁻¹)
    {x y : V} (hadj : Γ.Adj x y) (hx : x ∈ R) (hy : y ∈ R) :
    regularDirectedTransport w hadj =
      k ⟨y, hy⟩ * regularDirectedTransport u hadj * (k ⟨x, hx⟩)⁻¹ := by
  rcases lt_or_gt_of_ne hadj.ne with hxy | hyx
  · rw [regularDirectedTransport_of_lt w hadj hxy,
      regularDirectedTransport_of_lt u hadj hxy, hw _ ⟨hx, hy⟩]
  · rw [regularDirectedTransport_of_gt w hadj hyx,
      regularDirectedTransport_of_gt u hadj hyx, hw _ ⟨hy, hx⟩]
    group

/-- Equality of directed transports equates the actual coefficient of their
shared edge. This elementary identity is auxiliary to SCP10, lines 1765–1920. -/
theorem regularDirectedTransport_injective_on_edge {x y : V} (hadj : Γ.Adj x y)
    (u w : Edge Γ → G)
    (he : regularDirectedTransport u hadj = regularDirectedTransport w hadj) :
    u (Edge.ofAdj hadj) = w (Edge.ofAdj hadj) := by
  by_cases hxy : x < y
  · simpa only [regularDirectedTransport, ite_eq_left hxy] using he
  · simpa only [regularDirectedTransport, ite_eq_right hxy, inv_inj] using he

/-- Directed transport depends only on the endpoints, not on the proof of adjacency. -/
theorem regularDirectedTransport_eq_of_endpoints {a b c d : V}
    (u : Edge Γ → G) (h : Γ.Adj a b) (h' : Γ.Adj c d)
    (ha : a = c) (hb : b = d) :
    regularDirectedTransport u h = regularDirectedTransport u h' := by
  subst c d
  rfl

omit [Group G] in
/-- Equality of internal ordered coefficients preserves a common ambient extension. -/
theorem regularRegionBondExtension_congr_of_internal (R : Finset V)
    (a b u : Edge Γ → G)
    (h : ∀ (e : Edge Γ) (_he : e.1.1 ∈ R ∧ e.1.2 ∈ R), a e = b e) :
    regularRegionBondExtension R a u = regularRegionBondExtension R b u := by
  classical
  funext e
  simp only [regularRegionBondExtension]
  split_ifs with he
  · exact h e he
  · rfl

omit [Group G] in
/-- An internal assignment equal to the ambient one leaves its region extension unchanged. -/
theorem regularRegionBondExtension_eq_of_internal (R : Finset V)
    (u w : Edge Γ → G)
    (h : ∀ (e : Edge Γ) (_he : e.1.1 ∈ R ∧ e.1.2 ∈ R), u e = w e) :
    regularRegionBondExtension R u w = w := by
  rw [regularRegionBondExtension_congr_of_internal R u w w h]
  classical
  funext e
  simp [regularRegionBondExtension]

end TNLean.PEPS
