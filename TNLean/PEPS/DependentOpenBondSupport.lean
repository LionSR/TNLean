/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.DependentCutBondSupport

/-!
# Coherent bond support with unrestricted exterior coordinates

A chosen set of exterior bonds retains its entire matrix space. All remaining
bonds carry representation-matrix support. The dependent product-range criterion
then gives one coherent expansion, with no factorization of the exterior data.
This is the open-boundary support step for SCP10, Theorem 5.4.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS.DependentBondNetwork

variable {Vertex Edge G : Type*} [Group G] [Fintype G]
variable [Fintype Vertex] [Fintype Edge] [DecidableEq Vertex] [DecidableEq Edge]
variable (tail head : Edge → Vertex) (D : Edge → Type*)
variable [∀ e, Fintype (D e)] [∀ e, DecidableEq (D e)]

/-- Group labels for constrained bonds and matrix-unit labels for exterior bonds. -/
abbrev OpenBondLabel (e : Edge) := G ⊕ (D e × D e)

/-- A spanning family that leaves the matrices on exterior bonds unrestricted. -/
def openBondGenerator (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (C : Finset Edge) (e : Edge) (p : OpenBondLabel (G := G) D e) :
    Matrix (D e) (D e) ℂ :=
  if e ∈ C then p.elim (fun _ ↦ 0) (fun ij ↦ Matrix.single ij.1 ij.2 1)
  else U e (p.elim id (fun _ ↦ 1))

/-- The product-range matrix with free exterior columns. -/
def openBondMatrix (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (C : Finset Edge) (e : Edge) : Matrix (D e × D e) (OpenBondLabel (G := G) D e) ℂ :=
  fun ij p ↦ openBondGenerator D U C e p ij.1 ij.2

omit [Fintype Edge] in
/-- On an interior bond every representation column is among the chosen columns. -/
theorem bondMatrix_range_le_openBondMatrix_range
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (C : Finset Edge) (e : Edge) (he : e ∉ C) :
    (Matrix.mulVecLin (bondMatrix D U e)).range ≤
      (Matrix.mulVecLin (openBondMatrix D U C e)).range := by
  rintro _ ⟨c, rfl⟩
  refine ⟨Sum.elim c (fun _ ↦ 0), ?_⟩
  ext ij
  simp [Matrix.mulVec, dotProduct, openBondMatrix, openBondGenerator, he, bondMatrix,
    Fintype.sum_sum_type]

omit [Fintype Edge] in
/-- An exterior bond has its full matrix space, including arbitrary correlations. -/
theorem openBondMatrix_range_eq_top
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ)
    (C : Finset Edge) (e : Edge) (he : e ∈ C) :
    (Matrix.mulVecLin (openBondMatrix D U C e)).range = ⊤ := by
  apply top_unique
  intro x _
  refine ⟨Sum.elim (fun _ ↦ 0) x, ?_⟩
  ext ij
  simp [Matrix.mulVec, dotProduct, openBondMatrix, openBondGenerator, he,
    Fintype.sum_sum_type, Fintype.sum_prod_type, Matrix.single_apply, ite_and]

omit [Fintype Vertex] [DecidableEq Vertex] in
/-- Representation support on internal bonds implies one coherent expansion,
while the exterior coordinates remain completely free. -/
theorem exists_openBondCoefficients_of_slices
    (U : (e : Edge) → G →* Matrix (D e) (D e) ℂ) (C : Finset Edge)
    {ψ : ((v : Vertex) → LocalConfig tail head D v) → ℂ}
    (hψ : ∀ e, e ∉ C → ∀ τ, physicalBondSlice tail head D e τ ψ ∈
      (Matrix.mulVecLin (bondMatrix D U e)).range) :
    ∃ c : ((e : Edge) → OpenBondLabel (G := G) D e) → ℂ,
      ψ = ∑ p, c p • matrixBondProduct tail head D (fun e ↦ openBondGenerator D U C e (p e)) := by
  have hsupport : bondRegrouping tail head D ψ ∈
      (dependentPhysicalProductFamilyMap (openBondMatrix D U C)).range := by
    apply (mem_range_dependentPhysicalProductFamilyMap_iff _ _).mpr
    intro e τ
    by_cases he : e ∈ C
    · rw [openBondMatrix_range_eq_top D U C e he]
      trivial
    · exact bondMatrix_range_le_openBondMatrix_range D U C e he (hψ e he τ)
  obtain ⟨c, hc⟩ := hsupport
  refine ⟨c, ?_⟩
  apply (bondRegrouping tail head D).injective
  rw [map_sum]
  simp_rw [map_smul]
  rw [← hc]
  funext β
  simp only [dependentPhysicalProductFamilyMap_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, bondRegrouping_matrixBondProduct, openBondMatrix]
  exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _

end TNLean.PEPS.DependentBondNetwork
