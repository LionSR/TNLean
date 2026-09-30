/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.Injectivity
import TNLean.Algebra.MatrixSingleSpan
import TNLean.MPS.Symmetry.Defs
import TNLean.MPS.Symmetry.ProjectiveAdjointAction
import TNLean.Algebra.TwistedRegularProjective

/-!
# Matrix-unit fixed-point tensor

The isometric representative used by Schuch, Pérez-García, and Cirac has a
maximally entangled pair on each bond. In matrix coordinates its local tensor
has the matrix units as physical letters. Consequently it is injective at one
site, independently of the chosen virtual symmetry.

Source: arXiv:1010.3732, Section II.D.2, lines 697–707, and Section II.F.2,
lines 875–929.

**Scope restriction (finite-group fixed-point realization):** The realization
theorem below assumes a finite group and chooses the physical representation
from the cocycle class. It does not prove the symmetric gapped-path
classification of arbitrary injective endpoints. See
`docs/paper-gaps/spc11_spt_finite_group_realizability.tex`.
-/

open scoped Matrix
open TNLean.Algebra

namespace MPSTensor

/-- The matrix-unit tensor with physical index `(i,j)`, encoded as
`Fin (D * D)`. Its letter is `|i⟩⟨j|`. Schuch–Pérez-García–Cirac,
arXiv:1010.3732, Section II.D.2, lines 697–707. -/
def matrixUnitFixedPoint (D : ℕ) : MPSTensor (D * D) D :=
  fun p => Matrix.single (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2 (1 : ℂ)

@[simp]
theorem matrixUnitFixedPoint_apply (D : ℕ) (i j : Fin D) :
    matrixUnitFixedPoint D (finProdFinEquiv (i, j)) = Matrix.single i j (1 : ℂ) := by
  simp [matrixUnitFixedPoint]

/-- The matrix-unit fixed point is injective at one site because its letters
span the full bond matrix algebra. Schuch–Pérez-García–Cirac,
arXiv:1010.3732, Section II.D.2, lines 697–707. -/
theorem matrixUnitFixedPoint_isInjective (D : ℕ) :
    Kraus.IsInjective (matrixUnitFixedPoint D) := by
  apply Submodule.eq_top_of_forall_single_mem
  intro i j
  exact Submodule.subset_span ⟨finProdFinEquiv (i, j), by
    rw [matrixUnitFixedPoint_apply]⟩

/-- The matrix-unit basis used to express the physical adjoint action is
exactly the local tensor. -/
theorem matrixUnitBasis_eq_fixedPoint (D : ℕ) (p : Fin (D * D)) :
    matrixUnitBasis D p = matrixUnitFixedPoint D p := by
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective p
  simp [matrixUnitBasis, matrixUnitFixedPoint,
    Matrix.stdBasis_eq_single, Module.Basis.reindex_apply]

/-- The physical adjoint representation twists each matrix-unit letter by
the virtual conjugation. Schuch–Pérez-García–Cirac, arXiv:1010.3732,
Section II.F.2, equation (sym:proj-sym). -/
theorem twistedTensor_matrixUnitFixedPoint
    {G : Type*} [Group G] {D : ℕ} {ω : ScalarCocycle G}
    (ρ : ProjectiveRepresentation (D := D) ω) (g : G) (i : Fin (D * D)) :
    twistedTensor (matrixUnitFixedPoint D) ρ.onSiteMatrix g i =
      ρ.adjoint g⁻¹ (matrixUnitFixedPoint D i) := by
  simpa only [twistedTensor, matrixUnitBasis_eq_fixedPoint] using
    ρ.onSiteMatrix_sum_basis g i

/-- The fixed-point tensor is symmetric under the physical representation
induced by any virtual projective representation. -/
theorem matrixUnitFixedPoint_isOnSiteSymmetric
    {G : Type*} [Group G] {D : ℕ} {ω : ScalarCocycle G}
    (ρ : ProjectiveRepresentation (D := D) ω) :
    IsOnSiteSymmetric (matrixUnitFixedPoint D) ρ.onSiteMatrix := by
  intro g
  apply GaugeEquiv.sameMPV
  exact ⟨ρ.X g⁻¹, fun i => twistedTensor_matrixUnitFixedPoint ρ g i⟩

/-- **Finite-group realization of every virtual cocycle class by an injective
fixed-point MPS.** For each genuine scalar two-cocycle, the twisted regular
representation supplies a unitary virtual action. The matrix-unit tensor is
injective and symmetric under its induced unitary physical action, and its
virtual factor system lies in the requested cohomology class.

The physical space and its on-site representation are allowed to depend on
the class. This is the fixed-point realization ingredient of
Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.F.2, lines 875–929.
It does not assert a symmetric gapped path between arbitrary endpoints. -/
theorem exists_unitary_injective_fixedPoint_for_cocycle
    {G : Type*} [Group G] [Fintype G]
    (ω : ScalarCocycle G) (hω : ω.IsCocycle) :
    let D := Fintype.card G
    let A := matrixUnitFixedPoint D
    0 < D ∧ Kraus.IsInjective A ∧
    ∃ (U : G →* Matrix (Fin (D * D)) (Fin (D * D)) ℂ)
      (η : ScalarCocycle G) (ρ : ProjectiveRepresentation (D := D) η),
      IsOnSiteSymmetric A U ∧
      (∀ g : G, U g ∈ Matrix.unitaryGroup (Fin (D * D)) ℂ) ∧
      (∀ g : G, (ρ.X g : Matrix (Fin D) (Fin D) ℂ) ∈
        Matrix.unitaryGroup (Fin D) ℂ) ∧
      (∀ g i, twistedTensor A U g i = ρ.adjoint g⁻¹ (A i)) ∧
      η.CohomologousTo ω := by
  classical
  let ρ := ω.regularProjectiveForClass hω
  dsimp
  refine ⟨?_, ?_, ρ.onSiteMatrix, ω.circlePhaseInclusion, ρ, ?_, ?_, ?_, ?_, ?_⟩
  · exact Fintype.card_pos_iff.mpr ⟨(1 : G)⟩
  · exact matrixUnitFixedPoint_isInjective _
  · exact matrixUnitFixedPoint_isOnSiteSymmetric ρ
  · exact ρ.onSiteMatrix_mem_unitaryGroup
      (fun g => ω.regularProjectiveForClass_mem_unitaryGroup hω g)
  · exact fun g => ω.regularProjectiveForClass_mem_unitaryGroup hω g
  · exact fun g i => twistedTensor_matrixUnitFixedPoint ρ g i
  · exact ScalarCocycle.CohomologousTo.symm
      (ScalarCocycle.cohomologousTo_circlePhaseInclusion hω)

end MPSTensor
