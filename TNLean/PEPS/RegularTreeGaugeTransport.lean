/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularBoundaryRoute

/-!
# Directed tree transport and actual cycle vacancy

The normalized tree gauge is derived from the original bond assignment.
Its gradient describes transport in either direction. An ordered internal
residual is trivial precisely when its actual transport agrees with that
endpoint gradient. These are auxiliary coordinate identities for SCP10,
arXiv:1001.3807, lines 1765–1920 and Theorem 6.16, lines 2271–2305.
They make no assertion about parent Hamiltonians or a prescribed braid.
-/

namespace TNLean.PEPS
variable {V : Type*} [LinearOrder V] {Γ : SimpleGraph V}
variable {G : Type*} [Group G] [Fintype G]
variable (R : Finset V) (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
variable (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v // v ∈ R})

/-- Tree-edge transport is the actual normalized gauge gradient. The proof
uses uniqueness of tree paths. Source: SCP10, lines 1765–1920. -/
theorem regularRegionTreeGauge_directedTransport (u : Edge Γ → G)
    {v w : {x : V // x ∈ R}} (h : T.Adj v w) (hΓ : Γ.Adj v.1 w.1) :
    regularDirectedTransport u hΓ =
      (regularRegionTreeGauge R T hT htree o u).1 w *
        ((regularRegionTreeGauge R T hT htree o u).1 v)⁻¹ := by
  have heq : h.toWalk = Classical.choose (htree.connected.exists_isPath v w) :=
    (htree.existsUnique_path v w).unique (.of_adj h)
      (Classical.choose_spec (htree.connected.exists_isPath v w))
  have H := regularRegionTreeWalk_holonomy R T hT htree o u v w
  unfold regularRegionTreeWalk at H
  rw [← heq] at H
  change 1 * regularDirectedTransport u hΓ = _ at H
  simpa only [one_mul] using H

/-- An actual residual is trivial exactly when its directed operator is the
normalized endpoint gradient. Source: SCP10, lines 1765–1920. -/
theorem regularRegionGaugeResidual_eq_one_iff_directedTransport
    (u : Edge Γ → G) {v w : V} (hΓ : Γ.Adj v w) (hv : v ∈ R) (hw : w ∈ R) :
    regularRegionGaugeResidual R (regularRegionTreeGauge R T hT htree o u).1 u
      ⟨Edge.ofAdj hΓ, by
        rcases lt_or_gt_of_ne hΓ.ne with hlt | hgt
        · simpa only [Edge.ofAdj_of_lt hΓ hlt] using And.intro hv hw
        · simpa only [Edge.ofAdj_of_gt hΓ hgt] using And.intro hw hv⟩ = 1 ↔
      regularDirectedTransport u hΓ =
        (regularRegionTreeGauge R T hT htree o u).1 ⟨w, hw⟩ *
          ((regularRegionTreeGauge R T hT htree o u).1 ⟨v, hv⟩)⁻¹ := by
  let k := (regularRegionTreeGauge R T hT htree o u).1
  have hbase (a b c : G) : a⁻¹ * b * c = 1 ↔ b = a * c⁻¹ := by
    constructor
    · intro h
      calc
        b = a * (a⁻¹ * b * c) * c⁻¹ := by group
        _ = a * c⁻¹ := by rw [h]; group
    · intro h
      rw [h]
      group
  rcases lt_or_gt_of_ne hΓ.ne with hlt | hgt
  · simpa only [regularRegionGaugeResidual, Edge.ofAdj_of_lt hΓ hlt,
      regularDirectedTransport_of_lt u hΓ hlt] using hbase (k ⟨w, hw⟩) _ (k ⟨v, hv⟩)
  · simp only [regularRegionGaugeResidual, Edge.ofAdj_of_gt hΓ hgt,
      regularDirectedTransport_of_gt u hΓ hgt]
    rw [hbase]
    exact ⟨fun h => by rw [h, mul_inv_rev, inv_inv],
      fun h => by rw [← inv_inv (u _), h, mul_inv_rev, inv_inv]⟩

/-- Vacancy of the loop formed by three tree steps is equivalent to the
fourth transport being the tree gradient. Source: SCP10, Theorem 6.16,
lines 2271–2305, together with the coordinate construction, lines 1765–1920. -/
theorem regularRegionTreeGauge_fourStep_holonomy_eq_one_iff
    (u : Edge Γ → G) (v₁ v₂ v₃ v₄ : {v : V // v ∈ R})
    (h₁₂ : T.Adj v₁ v₂) (h₂₃ : T.Adj v₂ v₃) (h₃₄ : T.Adj v₃ v₄)
    (h₁₄ : Γ.Adj v₁.1 v₄.1) :
    regularWalkHolonomy u
      (.cons (SimpleGraph.induce_adj.mp (hT h₁₂))
        (.cons (SimpleGraph.induce_adj.mp (hT h₂₃))
          (.cons (SimpleGraph.induce_adj.mp (hT h₃₄)) (.cons h₁₄.symm .nil)))) = 1 ↔
    regularDirectedTransport u h₁₄ =
      (regularRegionTreeGauge R T hT htree o u).1 v₄ *
        ((regularRegionTreeGauge R T hT htree o u).1 v₁)⁻¹ := by
  rw [regularWalkHolonomy_cons, regularWalkHolonomy_cons, regularWalkHolonomy_cons,
    regularWalkHolonomy_cons, regularWalkHolonomy_nil, one_mul,
    regularDirectedTransport_symm u h₁₄,
    regularRegionTreeGauge_directedTransport R T hT htree o u h₁₂
      (SimpleGraph.induce_adj.mp (hT h₁₂)),
    regularRegionTreeGauge_directedTransport R T hT htree o u h₂₃
      (SimpleGraph.induce_adj.mp (hT h₂₃)),
    regularRegionTreeGauge_directedTransport R T hT htree o u h₃₄
      (SimpleGraph.induce_adj.mp (hT h₃₄))]
  let k := (regularRegionTreeGauge R T hT htree o u).1
  change ((regularDirectedTransport u h₁₄)⁻¹ * (k v₄ * (k v₃)⁻¹) *
    (k v₃ * (k v₂)⁻¹) * (k v₂ * (k v₁)⁻¹) = 1) ↔ _
  have hs : (regularDirectedTransport u h₁₄)⁻¹ * (k v₄ * (k v₃)⁻¹) *
      (k v₃ * (k v₂)⁻¹) * (k v₂ * (k v₁)⁻¹) =
      (regularDirectedTransport u h₁₄)⁻¹ * (k v₄ * (k v₁)⁻¹) := by group
  rw [hs, inv_mul_eq_one]

end TNLean.PEPS
