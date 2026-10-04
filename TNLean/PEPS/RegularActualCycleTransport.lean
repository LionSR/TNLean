/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularActualCycleBidirectionalPermutation
import TNLean.PEPS.RegularInternalGaugeTransport

/-!
# Transport in actual derived cycle coordinates

The original bond assignment determines its normalized tree gauge and cycle
residuals. Directed transport of either the original assignment or a physically
permuted assignment is obtained by endpoint reconstruction. These identities
are auxiliary to SCP10, arXiv:1001.3807, lines 1765–1920 and Theorem 6.16,
lines 2271–2305. No coefficient, state or Gram identity is assumed.
-/
noncomputable section
namespace TNLean.PEPS
variable {V : Type*} [LinearOrder V]
variable {Γ : SimpleGraph V}
variable {G : Type*} [Group G] [Fintype G]
variable (R : Finset V) (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
variable (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v // v ∈ R})

/-- The actual original transport is reconstructed from its derived coordinates.
Source: SCP10, lines 1765–1920. -/
theorem regularDirectedTransport_treeGauge_cycleResidual (u : Edge Γ → G)
    (v w : {x : V // x ∈ R}) (h : Γ.Adj v.1 w.1) :
    regularDirectedTransport u h =
      (regularRegionTreeGauge R T hT htree o u).1 w *
        regularDirectedTransport
          (regularTreeCycleAssignment R T (regularRegionTreeCycleResidual R T hT htree o u)) h *
        ((regularRegionTreeGauge R T hT htree o u).1 v)⁻¹ := by
  apply regularDirectedTransport_eq_of_internal_reconstruction R
    (regularRegionTreeGauge R T hT htree o u).1 _ u _ h v.2 w.2
  intro e he
  have H := regularGaugedTreeCycleAssignment_treeGauge_of_internal R T hT htree o u e he
  simpa only [regularGaugedTreeCycleAssignment, dite_eq_left he] using H.symm

/-- A forward or inverse actual cycle operation has its derived directed transport.
Source: SCP10, Theorem 6.16, lines 2271–2305. -/
theorem regularActualCycleDirectionalPermutation_directedTransport
    (φ : Equiv.Perm (RegionCycleEdge (Γ := Γ) R T → G))
    (reverse : Bool) (u : Edge Γ → G) (v w : {x : V // x ∈ R}) (h : Γ.Adj v.1 w.1) :
    regularDirectedTransport
      (regularActualCycleDirectionalPermutation R T hT htree o φ reverse u) h =
      (regularRegionTreeGauge R T hT htree o u).1 w *
        regularDirectedTransport
          (regularTreeCycleAssignment R T
            ((if reverse then φ.symm else φ) (regularRegionTreeCycleResidual R T hT htree o u))) h *
        ((regularRegionTreeGauge R T hT htree o u).1 v)⁻¹ := by
  apply regularDirectedTransport_eq_of_internal_reconstruction R
    (regularRegionTreeGauge R T hT htree o u).1 _ _ _ h v.2 w.2
  intro e he
  simp only [regularActualCycleDirectionalPermutation, regularActualCyclePermutation,
    regularRegionBondExtension, ite_eq_left he, regularGaugedTreeCycleAssignment, dite_eq_left he]

omit [Fintype G] in
/-- A selected native cycle coordinate gives the corresponding directed operator,
with inversion precisely in the reverse ordered orientation.
Source: SCP10, lines 1765–1920. -/
theorem regularTreeCycleAssignment_directedTransport
    (z : RegionCycleEdge (Γ := Γ) R T → G) (e : RegionCycleEdge (Γ := Γ) R T)
    {v w : V} (h : Γ.Adj v w) (he : Edge.ofAdj h = e.1.1) :
    regularDirectedTransport (regularTreeCycleAssignment R T z) h =
      if v < w then z e else (z e)⁻¹ := by
  simp only [regularDirectedTransport, he]
  have H : regularTreeCycleAssignment R T z e.1.1 = z e := by
    simp only [regularTreeCycleAssignment, dite_eq_left e.1.2.1,
      dite_eq_left e.1.2.2, dite_eq_left e.2]
  rw [H]

/-- A controlled two-chord operation or its inverse retains every other
literal ordered bond coefficient. Source: SCP10, Theorem 6.16, lines 2271–2305. -/
theorem regularActualTwoChordPermutation_eq_of_ne
    (e₀ e₁ : RegionCycleEdge (Γ := Γ) R T) (hne : e₀ ≠ e₁)
    (reverse : Bool) (u : Edge Γ → G) (e : Edge Γ) (he₁ : e ≠ e₁.1.1) :
    regularActualCycleDirectionalPermutation R T hT htree o
      (regularTwoCycleMove e₀ e₁ hne) reverse u e = u e := by
  classical
  let k := (regularRegionTreeGauge R T hT htree o u).1
  let ω := regularRegionTreeCycleResidual R T hT htree o u
  let φ : Equiv.Perm (RegionCycleEdge (Γ := Γ) R T → G) :=
    if reverse then (regularTwoCycleMove e₀ e₁ hne).symm else regularTwoCycleMove e₀ e₁ hne
  have hcycle : regularTreeCycleAssignment R T (φ ω) e =
      regularTreeCycleAssignment R T ω e := by
    simp only [regularTreeCycleAssignment]
    split_ifs with ht hh hn
    · rfl
    · have hf : (⟨⟨e, ht, hh⟩, hn⟩ : RegionCycleEdge (Γ := Γ) R T) ≠ e₁ := by
        intro h
        exact he₁ (congrArg (fun f => f.1.1) h)
      cases reverse <;> simp [φ, regularTwoCycleMove, hf]
    all_goals rfl
  by_cases he : e.1.1 ∈ R ∧ e.1.2 ∈ R
  · have H := regularGaugedTreeCycleAssignment_treeGauge_of_internal R T hT htree o u e he
    change regularRegionBondExtension R
      (regularGaugedTreeCycleAssignment R T k (φ ω)) u e = u e
    rw [regularRegionBondExtension, ite_eq_left he,
      regularGaugedTreeCycleAssignment, dite_eq_left he, hcycle]
    simpa only [regularGaugedTreeCycleAssignment, dite_eq_left he] using H
  · simp only [regularActualCycleDirectionalPermutation, regularActualCyclePermutation,
      regularRegionBondExtension, ite_eq_right he]

end TNLean.PEPS
