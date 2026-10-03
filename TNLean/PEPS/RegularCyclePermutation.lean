/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularTwoCycleFluxMove
import TNLean.PEPS.RegularCycleControlledSupport

/-!
# Conjugation-equivariant permutations of accessible cycle coordinates

In spanning-tree coordinates, independent vertex translations act on all cycle
labels by the same conjugation. A permutation of the cycle labels which commutes
with this conjugation therefore preserves the actual regular invariant support.
It also transports the actual contraction with inserted non-tree bond operators,
while retaining every boundary column. These facts give a physical unitary on
arbitrary original G-isometric site tensors, fixed before the inserted operators
and the boundary configuration are chosen.

Source: SCP10, arXiv:1001.3807, accessible-coordinate construction,
lines 1765–1920. This is an auxiliary criterion for physical operations; it does
not identify a permutation with a particular string deformation or braid.
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

/-- Apply a permutation to the cycle coordinates and retain the other three
coordinate families. Source: SCP10, accessible coordinates, lines 1765–1920. -/
def regularRegionCyclePermutation (o : RV R) (φ : Equiv.Perm (RC (Γ := Γ) R T → G)) :
    Equiv.Perm (RegularRegionCoordinates (Γ := Γ) (G := G) R T o) :=
  Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _)
    (Equiv.prodCongr (Equiv.refl _) φ))

/-- Transport a cycle permutation to the original physical half-edge labels.
Source: SCP10, accessible-coordinate construction, lines 1765–1920. -/
def regularRegionCyclePhysicalPermutation
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (φ : Equiv.Perm (RC (Γ := Γ) R T → G)) :
    Equiv.Perm (RegionHalfEdgeConfig (Γ := Γ) G R) :=
  (regularRegionCoordinatesEquiv R T hT htree o).trans
    ((regularRegionCyclePermutation R T o φ).trans
      (regularRegionCoordinatesEquiv R T hT htree o).symm)

/-- A conjugation-equivariant cycle permutation transports the actual canonical
contraction, retaining every boundary column. Source: SCP10, lines 1765–1920. -/
theorem regularProjectorTwistedRegionMatrix_cyclePermutation
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (φ : Equiv.Perm (RC (Γ := Γ) R T → G))
    (hφ : ∀ z x, φ (fun e => x * z e * x⁻¹) = fun e => x * φ z e * x⁻¹)
    (ω : RC (Γ := Γ) R T → G) (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o)
    (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G) :
    regularProjectorTwistedRegionMatrix R (regularTreeCycleAssignment R T (φ ω))
      ((regularRegionCoordinatesEquiv R T hT htree o).symm
        (regularRegionCyclePermutation R T o φ c)) θ =
    regularProjectorTwistedRegionMatrix R (regularTreeCycleAssignment R T ω)
      ((regularRegionCoordinatesEquiv R T hT htree o).symm c) θ := by
  rw [regularProjectorTwistedRegionMatrix_treeCycleAssignment_coordinates,
    regularProjectorTwistedRegionMatrix_treeCycleAssignment_coordinates]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  change (if c.1 = (fun e => x * θ e) ∧
      φ c.2.2.2 = (fun e => x * φ ω e * x⁻¹) then 1 else 0) = _
  rw [← hφ]
  simp only [Equiv.apply_eq_iff_eq]

/-- The canonical physical permutation matrix transports all actual inserted
cycle assignments and boundary columns. Source: SCP10, lines 1765–1920. -/
theorem regularProjectorTwistedRegionMatrix_cyclePhysicalPermutation
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (φ : Equiv.Perm (RC (Γ := Γ) R T → G))
    (hφ : ∀ z x, φ (fun e => x * z e * x⁻¹) = fun e => x * φ z e * x⁻¹)
    (ω : RC (Γ := Γ) R T → G)
    (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G) :
    Matrix.permMatrixHom (R := ℂ)
        (regularRegionCyclePhysicalPermutation R T hT htree o φ) *ᵥ
      (fun α => regularProjectorTwistedRegionMatrix R
        (regularTreeCycleAssignment R T ω) α θ) =
    (fun α => regularProjectorTwistedRegionMatrix R
      (regularTreeCycleAssignment R T (φ ω)) α θ) := by
  funext α
  rw [Matrix.permMatrixHom_apply, Matrix.permMatrix_mulVec]
  have h := regularProjectorTwistedRegionMatrix_cyclePermutation R T hT htree o φ hφ ω
    ((regularRegionCyclePermutation R T o φ).symm
      ((regularRegionCoordinatesEquiv R T hT htree o) α)) θ
  simpa only [regularRegionCyclePhysicalPermutation, Equiv.trans_apply,
    Equiv.symm_trans_apply, Equiv.Perm.inv_def, Function.comp_apply,
    Equiv.apply_symm_apply, Equiv.symm_apply_apply, Equiv.symm_symm] using h.symm

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] [DecidableEq G] [DecidableRel T.Adj] in
/-- A conjugation-equivariant cycle permutation commutes with independent vertex
translations in the actual coordinates. Source: SCP10, lines 1765–1920. -/
theorem regularRegionCyclePermutation_coordinateTranslation (o : RV R)
    (φ : Equiv.Perm (RC (Γ := Γ) R T → G))
    (hφ : ∀ z x, φ (fun e => x * z e * x⁻¹) = fun e => x * φ z e * x⁻¹)
    (ℓ : RV R → G) (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o) :
    regularRegionCyclePermutation R T o φ (regularRegionCoordinateTranslation R T o ℓ c) =
      regularRegionCoordinateTranslation R T o ℓ (regularRegionCyclePermutation R T o φ c) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · exact hφ c.2.2.2 (ℓ o)

/-- The transported physical permutation commutes with each actual vertex
translation. Source: SCP10, accessible physical systems, lines 1765–1920. -/
theorem regularRegionCyclePhysicalPermutation_commute_vertexTranslation
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (φ : Equiv.Perm (RC (Γ := Γ) R T → G))
    (hφ : ∀ z x, φ (fun e => x * z e * x⁻¹) = fun e => x * φ z e * x⁻¹)
    (ℓ : RV R → G) :
    Commute (Matrix.permMatrixHom (R := ℂ)
      (regularRegionCyclePhysicalPermutation R T hT htree o φ))
      (regularRegionVertexTranslationMatrix (Γ := Γ) R ℓ) := by
  exact regularRegionCoordinatePhysicalPermutation_commute_vertexTranslation R T hT htree o
    (regularRegionCyclePermutation R T o φ)
    (fun ℓ c => regularRegionCyclePermutation_coordinateTranslation R T o φ hφ ℓ c) ℓ

/-- The actual regular invariant projector commutes with the transported cycle
permutation. Source: SCP10, accessible physical systems, lines 1765–1920. -/
theorem regularRegionCyclePhysicalPermutation_commute_localProjector
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (φ : Equiv.Perm (RC (Γ := Γ) R T → G))
    (hφ : ∀ z x, φ (fun e => x * z e * x⁻¹) = fun e => x * φ z e * x⁻¹) :
    Commute (Matrix.permMatrixHom (R := ℂ)
      (regularRegionCyclePhysicalPermutation R T hT htree o φ))
      (regionPhysicalProductMatrix R
        (fun v => regularLegProjector (G := G) (IncidentEdge Γ v))) :=
  commute_regionLocalProjector_of_vertexTranslation R _ (fun ℓ =>
    regularRegionCyclePhysicalPermutation_commute_vertexTranslation R T hT htree o φ hφ ℓ)

omit [DecidableEq G] in
/-- One original physical unitary implements a conjugation-equivariant cycle
permutation for every inserted assignment and boundary column. The unitary is
chosen before either datum. Source: SCP10, lines 1765–1920. -/
theorem exists_unitary_regularCyclePhysicalPermutation {d : ℕ}
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v)))
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (φ : Equiv.Perm (RC (Γ := Γ) R T → G))
    (hφ : ∀ z x, φ (fun e => x * z e * x⁻¹) = fun e => x * φ z e * x⁻¹) :
    ∃ W : Matrix (RV R → Fin d) (RV R → Fin d) ℂ,
      W ∈ Matrix.unitaryGroup (RV R → Fin d) ℂ ∧
      ∀ (ω : RC (Γ := Γ) R T → G)
        (θ : {e : Edge Γ // IsRegionBoundaryEdge R e} → G),
        W *ᵥ openRegionWeight (groupBondTensor (regularTwistedSite a
          (regularTreeCycleAssignment R T ω))) R
          (fun f => Fintype.equivFin G (θ f)) =
        openRegionWeight (groupBondTensor (regularTwistedSite a
          (regularTreeCycleAssignment R T (φ ω)))) R
          (fun f => Fintype.equivFin G (θ f)) := by
  classical
  let Q := Matrix.permMatrixHom (R := ℂ)
    (regularRegionCyclePhysicalPermutation (G := G) R T hT htree o φ)
  have hQ : Q ∈ Matrix.unitaryGroup (RegionHalfEdgeConfig (Γ := Γ) G R) ℂ :=
    (regularRegionCyclePhysicalPermutation (G := G) R T hT htree o φ)⁻¹
      |>.permMatrix_mem_unitaryGroup
  obtain ⟨W, hW, hWA⟩ := exists_unitary_regionPhysicalProductMatrix_mul_of_projector_commute
    a ha R Q hQ
    (regularRegionCyclePhysicalPermutation_commute_localProjector R T hT htree o φ hφ).eq
  refine ⟨W, hW, ?_⟩
  intro ω θ
  have hcan := regularProjectorTwistedRegionMatrix_cyclePhysicalPermutation
    R T hT htree o φ hφ ω θ
  rw [← regionPhysicalMap_regularProjectorTwistedRegionMatrix a (fun v => (ha v).toIsGInjective),
    ← regionPhysicalMap_regularProjectorTwistedRegionMatrix a (fun v => (ha v).toIsGInjective)]
  change W *ᵥ (_ *ᵥ _) = _ *ᵥ _
  rw [Matrix.mulVec_mulVec, hWA, ← Matrix.mulVec_mulVec, hcan]

end TNLean.PEPS
