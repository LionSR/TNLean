/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.SemiRegular.CopyWeightPhysicalTransport
import TNLean.PEPS.ParentHamiltonian.SemiRegular.GraphOrientedAveragingBondState
import TNLean.PEPS.ParentHamiltonian.SemiRegular.OrientedCopyParentTransport

/-!
# Physical copy weights with arbitrary edge orientation

Block-scalar copy weights can move to the physical index independently of
which endpoint is the native tail. Positive multiplicities give an invertible
physical filter and exact transport of every actual regional parent range.
Source: SCP10, Section 4.1 and Section 7.

## Positive multiplicity changes with arbitrary native edge orientation

Every map acts on genuine regional contraction ranges and the full parent
space. Source: SCP10, Definition 5.1 and Section 7.
-/

section

open ManyBody (Edge)

noncomputable section
open scoped Matrix BigOperators
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G I : Type*} [Group G] [Fintype G] [Fintype I] [DecidableEq I]

/-- Virtual copy weights move exactly to physical endpoints, for every virtual column. -/
theorem graphOrientedAveragingSite_copy_weight (d m : I → ℕ) (o : Edge Γ → Bool)
    (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ) (v : V)
    (η σ : IncidentEdge Γ v → Σ i, Fin (d i)) :
    graphOrientedAveragingSite (blockMatrixRepresentation d D)
      (blockMultiplicityRootWeight d m) o v η σ =
      graphCopyWeight d m v σ *
        graphOrientedAveragingSite (blockMatrixRepresentation d D) 1 o v η σ := by
  unfold graphOrientedAveragingSite
  have hf (g : G) (f : IncidentEdge Γ v) :
      (if graphNativeTail o v f then
        (blockMultiplicityRootWeight d m * blockMatrixRepresentation d D g⁻¹) (η f) (σ f)
      else (blockMatrixRepresentation d D g * blockMultiplicityRootWeight d m) (σ f) (η f)) =
      (Real.sqrt (Real.sqrt (m (σ f).1 : ℝ)) : ℂ) *
        (if graphNativeTail o v f then blockMatrixRepresentation d D g⁻¹ (η f) (σ f)
        else blockMatrixRepresentation d D g (σ f) (η f)) := by
    split_ifs
    · rw [blockMultiplicityRootWeight_mul, blockDiagonal_weight_column]
      rfl
    · rw [mul_blockMultiplicityRootWeight, blockDiagonal_weight_row]
      rfl
  simp only [hf, Finset.prod_mul_distrib, graphCopyWeight, Matrix.one_mul, Matrix.mul_one,
    ← Finset.mul_sum]
  ring

/-- The actual tensor with copy weights is an invertible physical deformation
of the unweighted tensor, with the original virtual indices unchanged. -/
theorem numberedGraphOrientedAveragingTensor_copy_weight (d m : I → ℕ) (o : Edge Γ → Bool)
    (hm : ∀ i, 0 < m i) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ) {p : ℕ}
    (e : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p) :
    physicalDeform (numberedGraphOrientedAveragingTensor (blockMatrixRepresentation d D) 1 o e)
      (fun v => LinearMap.toMatrix' (graphCopyWeightPhysicalEquiv d m hm e v).toLinearMap) =
      numberedGraphOrientedAveragingTensor (blockMatrixRepresentation d D)
        (blockMultiplicityRootWeight d m) o e := by
  unfold numberedGraphOrientedAveragingTensor physicalDeform groupBondTensor
  congr 1
  funext v η s
  simp only [toMatrix_graphCopyWeightPhysicalEquiv, Matrix.diagonal_apply]
  simp only [ite_mul, zero_mul]
  rw [graphOrientedAveragingSite_copy_weight]
  simp

/-- Every canonical parent constraint is transported by the physical copy filter. -/
theorem map_regionParentGroundSpace_orientedCopy_weight (d m : I → ℕ) (o : Edge Γ → Bool)
    (hm : ∀ i, 0 < m i) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ) {p : ℕ}
    (e : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    {ι : Type*} (R : ι → Finset V) :
    (regionParentGroundSpace
      (numberedGraphOrientedAveragingTensor (blockMatrixRepresentation d D) 1 o e) R).map
        (globalPhysicalEquiv (graphCopyWeightPhysicalEquiv d m hm e)).toLinearMap =
    regionParentGroundSpace (numberedGraphOrientedAveragingTensor
      (blockMatrixRepresentation d D) (blockMultiplicityRootWeight d m) o e) R := by
  rw [map_regionParentGroundSpace_physicalDeform,
    numberedGraphOrientedAveragingTensor_copy_weight]

/-- Positive multiplicities do not alter the canonical parent space after
an invertible sitewise physical change of coordinates. -/
def canonicalOrientedCopyWeightParentEquiv (d m : I → ℕ) (o : Edge Γ → Bool)
    (hm : ∀ i, 0 < m i) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ) {p : ℕ}
    (e : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    {ι : Type*} (R : ι → Finset V) :
    regionParentGroundSpace
      (numberedGraphOrientedAveragingTensor (blockMatrixRepresentation d D) 1 o e) R ≃ₗ[ℂ]
    regionParentGroundSpace (numberedGraphOrientedAveragingTensor
      (blockMatrixRepresentation d D) (blockMultiplicityRootWeight d m) o e) R :=
  (globalPhysicalEquiv (graphCopyWeightPhysicalEquiv d m hm e)).ofSubmodules _ _
    (map_regionParentGroundSpace_orientedCopy_weight d m o hm D e R)

end TNLean.PEPS
end

end

section

open ManyBody (Edge)

noncomputable section
open scoped Matrix
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G I : Type*} [Group G] [Fintype G] [Fintype I] [DecidableEq I]

/-- The canonical parent space is independent of any positive copy multiplicity,
after the explicitly constructed physical filtering and supported bond map. -/
def canonicalOrientedPositiveMultiplicityParentEquiv
    (d m : I → ℕ) (o : Edge Γ → Bool) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i) {p q : ℕ}
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (m i)) ≃ Fin q)
    {ι : Type*} (R : ι → Finset V)
    (hcover : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i) :
    regionParentGroundSpace (numberedGraphOrientedAveragingTensor
      (blockMatrixRepresentation d D) 1 o eX) R ≃ₗ[ℂ]
      regionParentGroundSpace (numberedGraphOrientedAveragingTensor
        (blockMultiplicityRepresentation d m D) 1 o eY) R :=
  (canonicalOrientedCopyWeightParentEquiv d m o hm D eX R).trans
    (canonicalOrientedCopyParentEquiv o d m D hm eX eY R hcover)

/-- Two arbitrary positive multiplicity families have equivalent full canonical
parent spaces. No prescribed relation between multiplicities and dimensions is assumed. -/
def canonicalOrientedMultiplicityChangeParentEquiv
    (d m n : I → ℕ) (o : Edge Γ → Bool) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) {p q r : ℕ}
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (eM : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (m i)) ≃ Fin q)
    (eN : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (n i)) ≃ Fin r)
    {ι : Type*} (R : ι → Finset V)
    (hcover : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i) :
    regionParentGroundSpace (numberedGraphOrientedAveragingTensor
      (blockMultiplicityRepresentation d m D) 1 o eM) R ≃ₗ[ℂ]
      regionParentGroundSpace (numberedGraphOrientedAveragingTensor
        (blockMultiplicityRepresentation d n D) 1 o eN) R :=
  (canonicalOrientedPositiveMultiplicityParentEquiv d m o D hm eX eM R hcover).symm.trans
    (canonicalOrientedPositiveMultiplicityParentEquiv d n o D hn eX eN R hcover)

end TNLean.PEPS
end

end
