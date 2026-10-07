/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularTwistedRegionProjectorCoordinates
import TNLean.PEPS.RegularCycleControlledSupport
/-!
# Charge parameter transport in actual accessible block coordinates

A selected reference register is multiplied by a selected cycle register.
Independent vertex translations commute with this permutation. On the literal
character-weighted contraction the charge parameter changes by right
multiplication with the inverse flux label, while the character is retained.
Source: SCP10, arXiv:1001.3807, lines 2569–2581, using the accessible coordinates
of lines 1765–1920.

**Scope restriction (chosen finite block):** A spanning tree, one internal
charge bond and one non-tree flux bond are chosen. These auxiliary identities
are not the full geometric charge–flux braid; see
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/
noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
private abbrev RV (R : Finset V) := {v : V // v ∈ R}
private abbrev RI (R : Finset V) := {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R}
private abbrev RC (R : Finset V) (T : SimpleGraph (RV R)) :=
  {e : RI (Γ := Γ) R // ¬ T.Adj ⟨e.1.1.1, e.2.1⟩ ⟨e.1.1.2, e.2.2⟩}
variable (R : Finset V) (T : SimpleGraph (RV R)) [DecidableRel T.Adj]
/-- Multiply one reference coordinate by the selected cycle coordinate.
Source: SCP10, charge–flux action, lines 2569–2581. -/
def regularChargeFluxCoordinatePermutation (o : RV R) (e : RI (Γ := Γ) R)
    (b : RC (Γ := Γ) R T) :
    Equiv.Perm (RegularRegionCoordinates (Γ := Γ) (G := G) R T o) where
  toFun c := (c.1, (fun f => if f = e then c.2.2.2 b * c.2.1 f else c.2.1 f), c.2.2)
  invFun c := (c.1, (fun f => if f = e then (c.2.2.2 b)⁻¹ * c.2.1 f else c.2.1 f), c.2.2)
  left_inv c := by
    dsimp only
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext f
        by_cases h : f = e <;> simp [h]
      · rfl
  right_inv c := by
    dsimp only
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext f
        by_cases h : f = e <;> simp [h]
      · rfl
/-- Transport the charge–flux permutation to original incident physical labels.
Source: SCP10, lines 1765–1920 and 2569–2581. -/
def regularChargeFluxPhysicalPermutation
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (e : RI (Γ := Γ) R) (b : RC (Γ := Γ) R T) :
    Equiv.Perm (RegionHalfEdgeConfig (Γ := Γ) G R) :=
  regularRegionCoordinatePhysicalPermutation R T hT htree o
    (regularChargeFluxCoordinatePermutation R T o e b)
omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] [DecidableEq G] [DecidableRel T.Adj] in
private theorem coordinate_boundary (o : RV R) (e : RI (Γ := Γ) R)
    (b : RC (Γ := Γ) R T) (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o) :
    (regularChargeFluxCoordinatePermutation R T o e b c).1 = c.1 := rfl
omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] [DecidableEq G] [DecidableRel T.Adj] in
private theorem coordinate_cycle (o : RV R) (e : RI (Γ := Γ) R)
    (b : RC (Γ := Γ) R T) (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o) :
    (regularChargeFluxCoordinatePermutation R T o e b c).2.2.2 = c.2.2.2 := rfl
omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] [DecidableEq G] [DecidableRel T.Adj] in
private theorem coordinate_reference (o : RV R) (e : RI (Γ := Γ) R)
    (b : RC (Γ := Γ) R T) (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o) :
    (regularChargeFluxCoordinatePermutation R T o e b c).2.1 e = c.2.2.2 b * c.2.1 e := by
  exact ite_eq_left rfl
omit [Fintype G] [DecidableEq G] in
private theorem charge_cancel (χ : G → ℂ) (p z x a t k : G) (hz : z = x * t * x⁻¹) :
    χ ((p * k * t⁻¹ * k⁻¹) * (k * x⁻¹ * (z * a))) =
      χ (p * (k * x⁻¹ * a)) := by
  subst z
  congr 1
  group

/-- The transported flux at the selected charge endpoint, obtained from the
actual tree gauge and cycle residual. Source: SCP10, lines 2569–2581. -/
def regularChargeFluxParameter
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (e : RI (Γ := Γ) R) (b : RC (Γ := Γ) R T) (u : Edge Γ → G) (p : G) : G :=
  let k := (regularRegionTreeGauge R T hT htree o u).1
  p * k ⟨e.1.1.1, e.2.1⟩ *
    (regularRegionTreeCycleResidual R T hT htree o u b)⁻¹ * (k ⟨e.1.1.1, e.2.1⟩)⁻¹

/-- A literal internal diagonal weight is evaluated on the reconstructed tail
label, including its actual tree background. Source: SCP10, lines 1765–1920
and charge–flux transport, lines 2569–2581. -/
theorem regularProjectorWeightedTwistedRegionMatrix_internalCharge_coordinates
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (u : Edge Γ → G) (χ : G → ℂ) (p : G) (e : RI (Γ := Γ) R)
    (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o)
    (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G) :
    let k := (regularRegionTreeGauge R T hT htree o u).1
    regularProjectorWeightedTwistedRegionMatrix R u
        (fun η => χ (p * η ⟨e.1, Or.inl e.2.1⟩))
        ((regularRegionCoordinatesEquiv R T hT htree o).symm c) θ =
      (Fintype.card G : ℂ)⁻¹ ^ R.card * ∑ x : G,
        if c.1 = x • regularRegionBoundaryTransport R k u θ ∧
          c.2.2.2 = (fun f => x * regularRegionTreeCycleResidual R T hT htree o u f * x⁻¹)
        then χ (p * (k ⟨e.1.1.1, e.2.1⟩ * x⁻¹ * c.2.1 e)) else 0 := by
  dsimp only
  rw [regularProjectorWeightedTwistedRegionMatrix_coordinates]
  simp only [regularRegionTreeReferenceLabels, dite_eq_left e.2.1, dite_eq_left e.2.2]

/-- The literal weighted canonical contraction changes its parameter by the
actual transported residual, retaining every operator and boundary column.
Source: SCP10, charge–flux transport, lines 2569–2581. -/
theorem regularProjectorWeightedTwistedRegionMatrix_chargeFlux_coordinates
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (e : RI (Γ := Γ) R) (b : RC (Γ := Γ) R T)
    (u : Edge Γ → G) (χ : G → ℂ) (p : G)
    (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o)
    (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G) :
    regularProjectorWeightedTwistedRegionMatrix R u
        (fun η => χ (regularChargeFluxParameter R T hT htree o e b u p *
          η ⟨e.1, Or.inl e.2.1⟩))
        ((regularRegionCoordinatesEquiv R T hT htree o).symm
          (regularChargeFluxCoordinatePermutation R T o e b c)) θ =
      regularProjectorWeightedTwistedRegionMatrix R u
        (fun η => χ (p * η ⟨e.1, Or.inl e.2.1⟩))
        ((regularRegionCoordinatesEquiv R T hT htree o).symm c) θ := by
  rw [regularProjectorWeightedTwistedRegionMatrix_internalCharge_coordinates,
    regularProjectorWeightedTwistedRegionMatrix_internalCharge_coordinates]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  simp only [coordinate_boundary, coordinate_cycle, coordinate_reference]
  by_cases h : c.1 = x • regularRegionBoundaryTransport R
      (regularRegionTreeGauge R T hT htree o u).1 u θ ∧
      c.2.2.2 = (fun f => x * regularRegionTreeCycleResidual R T hT htree o u f * x⁻¹)
  · simp only [h, regularChargeFluxParameter]
    exact charge_cancel χ p _ x _ _ _ rfl
  · simp only [h, ↓reduceIte]

/-- The native permutation acts on the actual weighted projector columns.
Source: SCP10, lines 2569–2581, with actual coordinates from lines 1765–1920. -/
theorem regularProjectorWeightedTwistedRegionMatrix_chargeFlux_mulVec
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (e : RI (Γ := Γ) R) (b : RC (Γ := Γ) R T)
    (u : Edge Γ → G) (χ : G → ℂ) (p : G)
    (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G) :
    Matrix.permMatrixHom (R := ℂ)
        (regularChargeFluxPhysicalPermutation R T hT htree o e b) *ᵥ
      (fun α => regularProjectorWeightedTwistedRegionMatrix R u
        (fun η => χ (p * η ⟨e.1, Or.inl e.2.1⟩)) α θ) =
      (fun α => regularProjectorWeightedTwistedRegionMatrix R u
        (fun η => χ (regularChargeFluxParameter R T hT htree o e b u p *
          η ⟨e.1, Or.inl e.2.1⟩)) α θ) := by
  funext α
  rw [Matrix.permMatrixHom_apply, Matrix.permMatrix_mulVec]
  have h := regularProjectorWeightedTwistedRegionMatrix_chargeFlux_coordinates
    R T hT htree o e b u χ p
    ((regularChargeFluxCoordinatePermutation R T o e b).symm
      ((regularRegionCoordinatesEquiv R T hT htree o) α)) θ
  simpa only [regularChargeFluxPhysicalPermutation, regularRegionCoordinatePhysicalPermutation,
    Equiv.trans_apply, Equiv.symm_trans_apply, Equiv.Perm.inv_def, Function.comp_apply,
    Equiv.apply_symm_apply, Equiv.symm_apply_apply, Equiv.symm_symm] using h.symm

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] [DecidableEq G] [DecidableRel T.Adj] in
/-- Independent vertex translations commute with the reference-cycle operation.
Source: SCP10, accessible coordinates, lines 1765–1920 and 2569–2581. -/
theorem regularChargeFluxCoordinatePermutation_coordinateTranslation (o : RV R)
    (e : RI (Γ := Γ) R) (b : RC (Γ := Γ) R T) (ℓ : RV R → G)
    (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o) :
    regularChargeFluxCoordinatePermutation R T o e b
        (regularRegionCoordinateTranslation R T o ℓ c) =
      regularRegionCoordinateTranslation R T o ℓ
        (regularChargeFluxCoordinatePermutation R T o e b c) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext f
      change (if f = e then (ℓ o * c.2.2.2 b * (ℓ o)⁻¹) * (ℓ o * c.2.1 f)
        else ℓ o * c.2.1 f) = ℓ o * (if f = e then c.2.2.2 b * c.2.1 f else c.2.1 f)
      split_ifs <;> group
    · rfl
/-- The transported permutation preserves the actual local invariant projector.
Source: SCP10, accessible physical coordinates, lines 1765–1820. -/
theorem regularChargeFluxPhysicalPermutation_commute_localProjector
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (e : RI (Γ := Γ) R) (b : RC (Γ := Γ) R T) :
    Commute (Matrix.permMatrixHom (R := ℂ)
      (regularChargeFluxPhysicalPermutation R T hT htree o e b))
      (regionPhysicalProductMatrix R
        (fun v => regularLegProjector (G := G) (IncidentEdge Γ v))) := by
  exact regularRegionCoordinatePhysicalPermutation_commute_localProjector R T hT htree o
    (regularChargeFluxCoordinatePermutation R T o e b)
    (fun ℓ c => regularChargeFluxCoordinatePermutation_coordinateTranslation R T o e b ℓ c)

end TNLean.PEPS
