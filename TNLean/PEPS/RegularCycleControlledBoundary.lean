/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.PermutationMatrixUnitary
import TNLean.PEPS.RegularTwistedRegionProjectorCoordinates
import TNLean.PEPS.RegularBoundaryRoute

/-!
# Boundary permutations controlled by actual cycle coordinates

A boundary translation depending on the cycle labels is a reversible permutation
of the original spanning-tree physical coordinates. Its native permutation matrix
is unitary. Applying it to an actual twisted canonical block gives the exact
coefficient sum below, derived from the original contraction.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807,
`Papers/1001.3807/paper_v3.tex`, lines 1935–1990.
This algebraic operation does not assert the geometric relative-word identity
or the unrestricted conclusion of Theorem 6.9.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V : Type*} [LinearOrder V] {Γ : SimpleGraph V}
variable {G : Type*} [Group G]

/-- Translate the boundary by the inverse of a function of the cycle labels,
leaving all internal, rooted-vertex, and cycle coordinates fixed.
Source: SCP10, controlled disentangling, lines 1935–1990. -/
def regularCycleControlledBoundary (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) (o : {v : V // v ∈ R})
    (W : ({e : {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R} //
      ¬ T.Adj ⟨e.1.1.1, e.2.1⟩ ⟨e.1.1.2, e.2.2⟩} → G) →
        {e : Edge Γ // IsRegionBoundaryEdge R e} → G) :
    Equiv.Perm (RegularRegionCoordinates (Γ := Γ) (G := G) R T o) where
  toFun c := (fun f => (W c.2.2.2 f)⁻¹ * c.1 f, c.2)
  invFun c := (fun f => W c.2.2.2 f * c.1 f, c.2)
  left_inv c := by simp only [mul_inv_cancel_left]
  right_inv c := by simp only [inv_mul_cancel_left]

/-- The controlled boundary permutation on the original half-edge physical basis.
Its matrix convention sends each basis vector to its permuted basis vector. -/
noncomputable def regularCycleControlledBoundaryMatrix [Fintype V]
    [DecidableRel Γ.Adj] [Fintype G] [DecidableEq G] (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v : V // v ∈ R})
    (W : ({e : {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R} //
      ¬ T.Adj ⟨e.1.1.1, e.2.1⟩ ⟨e.1.1.2, e.2.2⟩} → G) →
        {e : Edge Γ // IsRegionBoundaryEdge R e} → G) :
    Matrix (RegionHalfEdgeConfig (Γ := Γ) G R) (RegionHalfEdgeConfig (Γ := Γ) G R) ℂ :=
  Matrix.permMatrixHom (R := ℂ)
    ((regularRegionCoordinatesEquiv R T hT htree o).trans
      ((regularCycleControlledBoundary R T o W).trans
        (regularRegionCoordinatesEquiv R T hT htree o).symm))

variable [Fintype V] [DecidableRel Γ.Adj] [Fintype G] [DecidableEq G]

/-- The cycle-controlled boundary operation is unitary on the original physical
half-edge space. Source: SCP10, controlled disentangling, lines 1935–1990. -/
theorem regularCycleControlledBoundaryMatrix_mem_unitaryGroup (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v : V // v ∈ R})
    (W : ({e : {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R} //
      ¬ T.Adj ⟨e.1.1.1, e.2.1⟩ ⟨e.1.1.2, e.2.2⟩} → G) →
        {e : Edge Γ // IsRegionBoundaryEdge R e} → G) :
    regularCycleControlledBoundaryMatrix R T hT htree o W ∈
      Matrix.unitaryGroup (RegionHalfEdgeConfig (Γ := Γ) G R) ℂ := by
  let E := regularRegionCoordinatesEquiv (G := G) R T hT htree o
  let σ : Equiv.Perm (RegionHalfEdgeConfig (Γ := Γ) G R) :=
    E.trans ((regularCycleControlledBoundary R T o W).trans E.symm)
  change (σ⁻¹).permMatrix ℂ ∈ _
  exact (σ⁻¹).permMatrix_mem_unitaryGroup

/-- Exact action of the controlled permutation on an actual twisted canonical
block. The cycle tuple is unchanged, and only its boundary indicator is
translated. Source: SCP10, lines 1935–1990. No relative-word identity is assumed. -/
theorem regularCycleControlledBoundaryMatrix_mul_coordinates (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v : V // v ∈ R})
    (W : ({e : {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R} //
      ¬ T.Adj ⟨e.1.1.1, e.2.1⟩ ⟨e.1.1.2, e.2.2⟩} → G) →
        {e : Edge Γ // IsRegionBoundaryEdge R e} → G)
    (u : Edge Γ → G) (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o)
    (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G) :
    (regularCycleControlledBoundaryMatrix R T hT htree o W *
      regularProjectorTwistedRegionMatrix R u)
        ((regularRegionCoordinatesEquiv R T hT htree o).symm c) θ =
      (Fintype.card G : ℂ)⁻¹ ^ R.card * ∑ x : G,
        if c.1 = (fun f => (W c.2.2.2 f)⁻¹ * x *
            regularRegionBoundaryTransport R
              (regularRegionTreeGauge R T hT htree o u).1 u θ f) ∧
          c.2.2.2 = (fun e => x * regularRegionTreeCycleResidual R T hT htree o u e * x⁻¹)
        then 1 else 0 := by
  classical
  let E := regularRegionCoordinatesEquiv (G := G) R T hT htree o
  let σ : Equiv.Perm (RegionHalfEdgeConfig (Γ := Γ) G R) :=
    E.trans ((regularCycleControlledBoundary R T o W).trans E.symm)
  have hmul : (regularCycleControlledBoundaryMatrix R T hT htree o W *
      regularProjectorTwistedRegionMatrix R u) (E.symm c) θ =
    regularProjectorTwistedRegionMatrix R u
      (E.symm ((regularCycleControlledBoundary R T o W).symm c)) θ := by
    change (((σ⁻¹).permMatrix ℂ) * regularProjectorTwistedRegionMatrix R u) (E.symm c) θ = _
    change ((σ⁻¹).permMatrix ℂ *ᵥ
      (fun a => regularProjectorTwistedRegionMatrix R u a θ)) (E.symm c) = _
    rw [Matrix.permMatrix_mulVec]
    simp only [Function.comp_apply, σ, Equiv.Perm.inv_def, Equiv.symm_trans_apply,
      Equiv.symm_symm, E.apply_symm_apply]
  rw [hmul, regularProjectorTwistedRegionMatrix_coordinates]
  apply congrArg ((Fintype.card G : ℂ)⁻¹ ^ R.card * ·)
  apply Finset.sum_congr rfl
  intro x _
  have hb : (fun f => W c.2.2.2 f * c.1 f) =
      x • regularRegionBoundaryTransport R
        (regularRegionTreeGauge R T hT htree o u).1 u θ ↔
    c.1 = (fun f => (W c.2.2.2 f)⁻¹ * x * regularRegionBoundaryTransport R
      (regularRegionTreeGauge R T hT htree o u).1 u θ f) := by
    simp only [funext_iff, Pi.smul_apply, smul_eq_mul, mul_assoc,
      eq_inv_mul_iff_mul_eq]
  change (if (fun f => W c.2.2.2 f * c.1 f) =
      x • regularRegionBoundaryTransport R
        (regularRegionTreeGauge R T hT htree o u).1 u θ ∧
      c.2.2.2 = (fun e => x * regularRegionTreeCycleResidual R T hT htree o u e * x⁻¹)
    then (1 : ℂ) else 0) = _
  simp only [hb]

/-- The physical control constructed from fixed actual complement walks.
The walks and their cycle words are chosen before any bond assignment or closure
sector. Source: SCP10, accessible complement control, lines 1935–1990. -/
noncomputable def regularComplementWalkControlMatrix (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ Finset.univ \ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce ((Finset.univ \ R : Finset V) : Set V)) (htree : T.IsTree)
    (o : {v : V // v ∈ Finset.univ \ R})
    (v w : {e : Edge Γ // IsRegionBoundaryEdge R e} → {v : V // v ∈ Finset.univ \ R})
    (p : (f : {e : Edge Γ // IsRegionBoundaryEdge R e}) →
      (Γ.induce ((Finset.univ \ R : Finset V) : Set V)).Walk (v f) (w f)) :
    Matrix (RegionHalfEdgeConfig (Γ := Γ) G (Finset.univ \ R))
      (RegionHalfEdgeConfig (Γ := Γ) G (Finset.univ \ R)) ℂ :=
  regularCycleControlledBoundaryMatrix (G := G) (Finset.univ \ R) T hT htree o
    (fun z f => FreeGroup.lift z (regularRegionCycleWord (Finset.univ \ R) T
      (p ((regionBoundaryEdgeComplEquiv (G := Γ) R).symm f))))

/-- The fixed complement-walk control is unitary on the original physical
half-edge basis. Source: SCP10, lines 1935–1990. -/
theorem regularComplementWalkControlMatrix_mem_unitaryGroup (R : Finset V)
    (T : SimpleGraph {v : V // v ∈ Finset.univ \ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce ((Finset.univ \ R : Finset V) : Set V)) (htree : T.IsTree)
    (o : {v : V // v ∈ Finset.univ \ R})
    (v w : {e : Edge Γ // IsRegionBoundaryEdge R e} → {v : V // v ∈ Finset.univ \ R})
    (p : (f : {e : Edge Γ // IsRegionBoundaryEdge R e}) →
      (Γ.induce ((Finset.univ \ R : Finset V) : Set V)).Walk (v f) (w f)) :
    regularComplementWalkControlMatrix (G := G) R T hT htree o v w p ∈
      Matrix.unitaryGroup (RegionHalfEdgeConfig (Γ := Γ) G (Finset.univ \ R)) ℂ :=
  regularCycleControlledBoundaryMatrix_mem_unitaryGroup (Finset.univ \ R) T hT htree o _

/-- Actual complement walk words remove the combined region/complement
boundary transport at the input reindexed by the inverse region transport.
The actual conjugated cycle constraint is retained. Source: SCP10,
lines 1935–1990.

**Scope restriction (conditional relative words):** This auxiliary statement
assumes the identity relating the constructed complement walk words to the
combined crossing transport. Its geometric derivation is still required in
the unrestricted Theorem 6.9, as recorded in
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`. -/
theorem regularCycleControlledBoundaryMatrix_mul_coordinates_of_combined_relative_walk_words
    (R : Finset V) (kR : {v : V // v ∈ R} → G)
    (T : SimpleGraph {v : V // v ∈ Finset.univ \ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce ((Finset.univ \ R : Finset V) : Set V)) (htree : T.IsTree)
    (o : {v : V // v ∈ Finset.univ \ R})
    (v w : {e : Edge Γ // IsRegionBoundaryEdge R e} → {v : V // v ∈ Finset.univ \ R})
    (p : (f : {e : Edge Γ // IsRegionBoundaryEdge R e}) →
      (Γ.induce ((Finset.univ \ R : Finset V) : Set V)).Walk (v f) (w f))
    (u : Edge Γ → G) (f₀ : {e : Edge Γ // IsRegionBoundaryEdge R e})
    (hrelative : ∀ f, FreeGroup.lift
        (regularRegionTreeCycleResidual (Finset.univ \ R) T hT htree o u)
        (regularRegionCycleWord (Finset.univ \ R) T (p f)) =
      regularCombinedBoundaryTransport R kR
          (regularRegionTreeGauge (Finset.univ \ R) T hT htree o u).1 u 1 f *
        (regularCombinedBoundaryTransport R kR
          (regularRegionTreeGauge (Finset.univ \ R) T hT htree o u).1 u 1 f₀)⁻¹)
    (c : RegularRegionCoordinates (Γ := Γ) (G := G) (Finset.univ \ R) T o)
    (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G) :
    (regularComplementWalkControlMatrix (G := G) R T hT htree o v w p *
      regularProjectorTwistedRegionMatrix (Finset.univ \ R) u)
        ((regularRegionCoordinatesEquiv (Finset.univ \ R) T hT htree o).symm c)
        (fun f => (regularRegionBoundaryTransport R kR u).symm θ
          ((regionBoundaryEdgeComplEquiv (G := Γ) R).symm f)) =
      (Fintype.card G : ℂ)⁻¹ ^ (Finset.univ \ R).card * ∑ x : G,
        if c.1 = (fun f => x * regularCombinedBoundaryTransport R kR
            (regularRegionTreeGauge (Finset.univ \ R) T hT htree o u).1 u 1 f₀ *
              θ ((regionBoundaryEdgeComplEquiv (G := Γ) R).symm f)) ∧
          c.2.2.2 = (fun e => x *
            regularRegionTreeCycleResidual (Finset.univ \ R) T hT htree o u e * x⁻¹)
        then 1 else 0 := by
  classical
  let S := Finset.univ \ R
  let kS := (regularRegionTreeGauge S T hT htree o u).1
  let E := regionBoundaryEdgeComplEquiv (G := Γ) R
  let η := fun f => (regularRegionBoundaryTransport R kR u).symm θ (E.symm f)
  have hcomp (f : {e : Edge Γ // IsRegionBoundaryEdge S e}) :
      regularRegionBoundaryTransport S kS u η f =
        regularCombinedBoundaryTransport R kR kS u θ (E.symm f) := by
    change regularRegionBoundaryTransport S kS u η f =
      regularRegionBoundaryTransport S kS u η (E (E.symm f))
    rw [E.apply_symm_apply]
  rw [regularComplementWalkControlMatrix, regularCycleControlledBoundaryMatrix_mul_coordinates]
  apply congrArg ((Fintype.card G : ℂ)⁻¹ ^ S.card * ·)
  apply Finset.sum_congr rfl
  intro x _
  by_cases hz : c.2.2.2 =
      (fun e => x * regularRegionTreeCycleResidual S T hT htree o u e * x⁻¹)
  · have hb : (fun f =>
        (FreeGroup.lift c.2.2.2 (regularRegionCycleWord S T (p (E.symm f))))⁻¹ * x *
          regularRegionBoundaryTransport S kS u η f) =
      (fun f => x * regularCombinedBoundaryTransport R kR kS u 1 f₀ * θ (E.symm f)) := by
      funext f
      rw [hz, regularRegionCycleWord_eval_conj, hrelative (E.symm f), hcomp,
        regularCombinedBoundaryTransport_apply R kR kS u θ (E.symm f)]
      dsimp only [S, kS]
      group
    rw [hb]
  · dsimp only [S] at hz
    simp only [hz, and_false, ↓reduceIte]

end TNLean.PEPS
