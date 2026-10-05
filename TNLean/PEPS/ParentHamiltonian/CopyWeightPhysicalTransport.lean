/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.CopyCanonicalLocalTransport
import TNLean.PEPS.ParentHamiltonian.RegionPhysicalGroundSpaceTransport

/-!
# Physical equivalence of positive copy weights

Every fourth-root copy weight can be moved from a virtual endpoint to the
physical endpoint of its irreducible block. The resulting sitewise diagonal
map is invertible for positive multiplicities, so it transports the genuine
regional parent constraints for every region family.

Source: SCP10, arXiv:1001.3807, Section 4.1 and Section 7.
-/

noncomputable section
open scoped Matrix BigOperators
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G I : Type*} [Group G] [Fintype G] [Fintype I] [DecidableEq I]

/-- The diagonal physical coefficient supplied by the copy weights at one site. -/
def graphCopyWeight (d m : I → ℕ) (v : V)
    (σ : IncidentEdge Γ v → Σ i, Fin (d i)) : ℂ :=
  ∏ f, (Real.sqrt (Real.sqrt (m (σ f).1 : ℝ)) : ℂ)

/-- Virtual copy weights move exactly to physical endpoints, for every virtual column. -/
theorem graphDressedAveragingSite_copy_weight (d m : I → ℕ)
    (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ) (v : V)
    (η σ : IncidentEdge Γ v → Σ i, Fin (d i)) :
    graphDressedAveragingSite (blockMatrixRepresentation d D)
      (blockMultiplicityRootWeight d m) v η σ =
      graphCopyWeight d m v σ * graphAveragingSite (blockMatrixRepresentation d D) v η σ := by
  unfold graphDressedAveragingSite
  rw [graphDress_averagingSite]
  have hf (g : G) (f : IncidentEdge Γ v) :
      (if f.1.1.1 = v then
        (blockMultiplicityRootWeight d m * blockMatrixRepresentation d D g⁻¹) (η f) (σ f)
      else (blockMatrixRepresentation d D g * blockMultiplicityRootWeight d m) (σ f) (η f)) =
      (Real.sqrt (Real.sqrt (m (σ f).1 : ℝ)) : ℂ) *
        (if f.1.1.1 = v then blockMatrixRepresentation d D g⁻¹ (η f) (σ f)
        else blockMatrixRepresentation d D g (σ f) (η f)) := by
    split_ifs
    · rw [blockMultiplicityRootWeight_mul, blockDiagonal_weight_column]
      rfl
    · rw [mul_blockMultiplicityRootWeight, blockDiagonal_weight_row]
      rfl
  simp only [hf, Finset.prod_mul_distrib, graphCopyWeight, graphAveragingSite,
    ← Finset.mul_sum]
  ring

omit [Group G] [Fintype G] [Fintype I] [DecidableEq I] in
/-- Positive multiplicities make every physical copy-weight coefficient nonzero. -/
theorem graphCopyWeight_ne_zero (d m : I → ℕ) (hm : ∀ i, 0 < m i) (v : V)
    (σ : IncidentEdge Γ v → Σ i, Fin (d i)) : graphCopyWeight d m v σ ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro f _
  exact_mod_cast (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr
    (Nat.cast_pos.mpr (hm (σ f).1)))).ne'

/-- Positive copy weights give an invertible physical diagonal map at each vertex. -/
def graphCopyWeightPhysicalEquiv (d m : I → ℕ) (hm : ∀ i, 0 < m i) {p : ℕ}
    (e : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p) (v : V) :
    (Fin p → ℂ) ≃ₗ[ℂ] (Fin p → ℂ) :=
  LinearEquiv.piCongrRight fun s => LinearEquiv.smulOfNeZero ℂ ℂ
    (graphCopyWeight d m v ((e v).symm s)) (graphCopyWeight_ne_zero d m hm v _)

omit [Fintype I] [DecidableEq I] in
/-- The matrix of the physical copy filter is the literal diagonal weight matrix. -/
theorem toMatrix_graphCopyWeightPhysicalEquiv (d m : I → ℕ) (hm : ∀ i, 0 < m i) {p : ℕ}
    (e : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p) (v : V) :
    LinearMap.toMatrix' (graphCopyWeightPhysicalEquiv d m hm e v).toLinearMap =
      Matrix.diagonal (fun s => graphCopyWeight d m v ((e v).symm s)) := by
  ext s t
  simp [LinearMap.toMatrix'_apply, graphCopyWeightPhysicalEquiv, Matrix.diagonal_apply,
    Pi.single_apply, mul_ite]

/-- The actual tensor with copy weights is an invertible physical deformation
of the unweighted tensor, with the original virtual indices unchanged. -/
theorem numberedGraphDressedAveragingTensor_copy_weight (d m : I → ℕ)
    (hm : ∀ i, 0 < m i) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ) {p : ℕ}
    (e : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p) :
    physicalDeform (numberedGraphDressedAveragingTensor (blockMatrixRepresentation d D) 1 e)
      (fun v => LinearMap.toMatrix' (graphCopyWeightPhysicalEquiv d m hm e v).toLinearMap) =
      numberedGraphDressedAveragingTensor (blockMatrixRepresentation d D)
        (blockMultiplicityRootWeight d m) e := by
  unfold numberedGraphDressedAveragingTensor physicalDeform groupBondTensor
  congr 1
  funext v η s
  simp only [toMatrix_graphCopyWeightPhysicalEquiv, Matrix.diagonal_apply]
  simp only [ite_mul, zero_mul]
  rw [graphDressedAveragingSite_copy_weight]
  simp [graphDressedAveragingSite, graphDress_one]

/-- Every canonical parent constraint is transported by the physical copy filter. -/
theorem map_regionParentGroundSpace_copy_weight (d m : I → ℕ)
    (hm : ∀ i, 0 < m i) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ) {p : ℕ}
    (e : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    {ι : Type*} (R : ι → Finset V) :
    (regionParentGroundSpace
      (numberedGraphDressedAveragingTensor (blockMatrixRepresentation d D) 1 e) R).map
        (globalPhysicalEquiv (graphCopyWeightPhysicalEquiv d m hm e)).toLinearMap =
    regionParentGroundSpace (numberedGraphDressedAveragingTensor
      (blockMatrixRepresentation d D) (blockMultiplicityRootWeight d m) e) R := by
  rw [map_regionParentGroundSpace_physicalDeform,
    numberedGraphDressedAveragingTensor_copy_weight]

/-- Positive multiplicities do not alter the canonical parent space after
an invertible sitewise physical change of coordinates. -/
def canonicalCopyWeightParentEquiv (d m : I → ℕ)
    (hm : ∀ i, 0 < m i) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ) {p : ℕ}
    (e : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    {ι : Type*} (R : ι → Finset V) :
    regionParentGroundSpace
      (numberedGraphDressedAveragingTensor (blockMatrixRepresentation d D) 1 e) R ≃ₗ[ℂ]
    regionParentGroundSpace (numberedGraphDressedAveragingTensor
      (blockMatrixRepresentation d D) (blockMultiplicityRootWeight d m) e) R :=
  (globalPhysicalEquiv (graphCopyWeightPhysicalEquiv d m hm e)).ofSubmodules _ _
    (map_regionParentGroundSpace_copy_weight d m hm D e R)

end TNLean.PEPS
