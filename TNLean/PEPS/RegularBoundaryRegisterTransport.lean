/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularCycleControlledSupport
import TNLean.PEPS.RegularRegionProjectorCoordinates

/-!
# Independent physical transport of accessible boundary registers

Permuting the accessible boundary registers of a connected untwisted block
commutes with every independent vertex translation. It therefore preserves the
full Gram form of the original product physical map and has an original-spin
unitary implementation, uniformly over all actual boundary configurations.

Source: SCP10, arXiv:1001.3807, accessible coordinates, lines 1765–1920,
and the independent two-column swaps in `eq:anyons:chargeon-move-setting`,
lines 2489–2507. This is the local transport step; no gluing identity or
factorization of the four-spin charge-motion operation is asserted here.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
private abbrev RV (R : Finset V) := {v : V // v ∈ R}
private abbrev RB (R : Finset V) := {e : Edge Γ // IsRegionBoundaryEdge R e}

/-- Permute only the accessible boundary registers.
Source: SCP10, the independent column swaps, lines 2489–2507. -/
def regularBoundaryRegisterPermutation (R : Finset V)
    (T : SimpleGraph (RV R)) (o : RV R) (τ : Equiv.Perm (RB (Γ := Γ) R)) :
    Equiv.Perm (RegularRegionCoordinates (Γ := Γ) (G := G) R T o) where
  toFun c := (fun b => c.1 (τ b), c.2)
  invFun c := (fun b => c.1 (τ.symm b), c.2)
  left_inv c := by
    apply Prod.ext
    · funext b; exact congrArg c.1 (τ.apply_symm_apply b)
    · rfl
  right_inv c := by
    apply Prod.ext
    · funext b; exact congrArg c.1 (τ.symm_apply_apply b)
    · rfl

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] [DecidableEq G] in
/-- Boundary register permutations commute with all independent translations.
Source: SCP10, accessible invariant coordinates, lines 1765–1920. -/
theorem regularBoundaryRegisterPermutation_coordinateTranslation (R : Finset V)
    (T : SimpleGraph (RV R)) (o : RV R) (τ : Equiv.Perm (RB (Γ := Γ) R))
    (ℓ : RV R → G) (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o) :
    regularBoundaryRegisterPermutation R T o τ
        (regularRegionCoordinateTranslation R T o ℓ c) =
      regularRegionCoordinateTranslation R T o ℓ
        (regularBoundaryRegisterPermutation R T o τ c) := rfl

private theorem canonical_boundaryPermutation (R : Finset V)
    (T : SimpleGraph (RV R)) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : RV R)
    (τ : Equiv.Perm (RB (Γ := Γ) R))
    (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o) (θ : RB (Γ := Γ) R → G) :
    regularProjectorOpenRegionMatrix R
        ((regularRegionCoordinatesEquiv R T hT htree o).symm
          (regularBoundaryRegisterPermutation R T o τ c)) (fun b => θ (τ b)) =
      regularProjectorOpenRegionMatrix R
        ((regularRegionCoordinatesEquiv R T hT htree o).symm c) θ := by
  have hp : regularLegProjector (RB (Γ := Γ) R) (fun b => c.1 (τ b))
      (fun b => θ (τ b)) = regularLegProjector (RB (Γ := Γ) R) c.1 θ := by
    rw [regularLegProjector_apply, regularLegProjector_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    have hy : (fun b => c.1 (τ b)) = x • (fun b => θ (τ b)) ↔ c.1 = x • θ := by
      constructor
      · intro h
        funext b
        have h' := congrFun h (τ.symm b)
        simpa only [Equiv.apply_symm_apply, Pi.smul_apply] using h'
      · intro h
        funext b
        exact congrFun h (τ b)
    simp only [hy]
  rw [regularProjectorOpenRegionMatrix_coordinates,
    regularProjectorOpenRegionMatrix_coordinates]
  simp only [regularBoundaryRegisterPermutation, Equiv.coe_fn_mk, hp]
  rfl

omit [DecidableEq G] in
/-- An original-spin unitary implements an arbitrary accessible boundary
permutation on every actual untwisted open-region column. Its Gram preservation
is derived from local G-isometry. Source: SCP10, lines 2489–2507. -/
theorem exists_unitary_regularBoundaryRegisterTransport {d : ℕ}
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGIsometric (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (R : Finset V)
    (hR : (Γ.induce (R : Set V)).Connected)
    (τ : Equiv.Perm (RB (Γ := Γ) R)) :
    ∃ W : Matrix (RV R → Fin d) (RV R → Fin d) ℂ,
      W ∈ Matrix.unitaryGroup (RV R → Fin d) ℂ ∧
      ∀ θ : RB (Γ := Γ) R → G,
        W *ᵥ openRegionWeight (groupBondTensor a) R
          (fun b => Fintype.equivFin G (θ b)) =
        openRegionWeight (groupBondTensor a) R
          (fun b => Fintype.equivFin G (θ (τ b))) := by
  classical
  obtain ⟨T,hT,htree⟩ := hR.exists_isTree_le
  let : DecidableRel T.Adj := Classical.decRel _
  let o := hR.nonempty.some
  let C := regularBoundaryRegisterPermutation (G := G) R T o τ
  let Q := Matrix.permMatrixHom (R := ℂ)
    (regularRegionCoordinatePhysicalPermutation R T hT htree o C)
  have hQ : Q ∈ Matrix.unitaryGroup (RegionHalfEdgeConfig (Γ := Γ) G R) ℂ :=
    (regularRegionCoordinatePhysicalPermutation R T hT htree o C)⁻¹
      |>.permMatrix_mem_unitaryGroup
  have hcomm := regularRegionCoordinatePhysicalPermutation_commute_localProjector
    R T hT htree o C
    (fun ℓ c => regularBoundaryRegisterPermutation_coordinateTranslation R T o τ ℓ c)
  obtain ⟨W,hW,hWA⟩ := exists_unitary_regionPhysicalProductMatrix_mul_of_projector_commute
    a ha R Q hQ hcomm.eq
  refine ⟨W,hW,?_⟩
  intro θ
  have hcan : Q *ᵥ (fun α => regularProjectorOpenRegionMatrix R α θ) =
      (fun α => regularProjectorOpenRegionMatrix R α (fun b => θ (τ b))) := by
    funext α
    dsimp only [Q]
    rw [Matrix.permMatrixHom_apply, Matrix.permMatrix_mulVec]
    have h := canonical_boundaryPermutation R T hT htree o τ
      (C.symm ((regularRegionCoordinatesEquiv R T hT htree o) α)) θ
    simpa only [Q, C, regularRegionCoordinatePhysicalPermutation, Equiv.trans_apply,
      Equiv.symm_trans_apply, Equiv.Perm.inv_def, Function.comp_apply,
      Equiv.apply_symm_apply, Equiv.symm_apply_apply, Equiv.symm_symm] using h.symm
  rw [← regionPhysicalMap_regularProjectorOpenRegionMatrix a
      (fun v => (ha v).toIsGInjective),
    ← regionPhysicalMap_regularProjectorOpenRegionMatrix a
      (fun v => (ha v).toIsGInjective)]
  change W *ᵥ (_ *ᵥ _) = _ *ᵥ _
  rw [Matrix.mulVec_mulVec, hWA, ← Matrix.mulVec_mulVec, hcan]
end TNLean.PEPS
