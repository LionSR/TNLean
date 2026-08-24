/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.DependentBlockDiagonal
import TNLean.MPS.MPDO.PhysicalSectorActiveSupportData
import TNLean.MPS.MPDO.PhysicalSupportRestriction

/-!
# Active physical-sector support coordinates

This file assembles the chosen factor-support coordinates in each physical
sector into dependent block diagonal inclusions and support projections.
Inactive sectors have zero-dimensional coordinate spaces, so no complementary
summand is introduced.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, equations AppUkU=rl and Appetakhetc, lines 1381--1450.

**Scope restriction (active physical support compression):** this support
coordinate construction is auxiliary to the cited factorization. Its status
is recorded in
docs/paper-gaps/cpsv16_active_physical_support_compression.tex.
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D}

/-- The retained physical index within one sector.  This type is empty in an
inactive sector. -/
abbrev SupportedSectorIndex (F : PhysicalSectorFactorization K)
    (A : ActiveFactorSupportData F) (k : Fin F.sectorCount) :=
  Fin (A.sector k).leftDim × Fin (A.sector k).rightDim

/-- The product of the two factor-support inclusions in one sector.

Source: arXiv:1606.00608, Appendix C.2, equation `AppUkU=rl`, lines
1381--1388. -/
noncomputable def sectorSupportInclusion (F : PhysicalSectorFactorization K)
    (A : ActiveFactorSupportData F) (k : Fin F.sectorCount) :
    Matrix (SectorIndex F k) (SupportedSectorIndex F A k) ℂ :=
  (A.sector k).leftInclusion ⊗ₖ (A.sector k).rightInclusion

/-- The product inclusion in each sector is an isometry. -/
theorem sectorSupportInclusion_isometry
    (F : PhysicalSectorFactorization K) (A : ActiveFactorSupportData F)
    (k : Fin F.sectorCount) :
    (F.sectorSupportInclusion A k)ᴴ * F.sectorSupportInclusion A k = 1 := by
  rw [sectorSupportInclusion, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, (A.sector k).leftInclusion_isometry,
    (A.sector k).rightInclusion_isometry]
  exact Matrix.one_kronecker_one

/-- The range of the product inclusion is the joint support of the sector
product family. -/
theorem sectorSupportInclusion_range
    (F : PhysicalSectorFactorization K) (A : ActiveFactorSupportData F)
    (k : Fin F.sectorCount) :
    F.sectorSupportInclusion A k * (F.sectorSupportInclusion A k)ᴴ =
      Matrix.familySupportProj (F.sectorProductFamily k) := by
  rw [sectorSupportInclusion, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul]
  exact (A.sector k).product_range

/-- The dependent direct sum of all retained sector coordinates.  Its fibers
over inactive sectors are empty. -/
abbrev SupportedPhysicalIndex (F : PhysicalSectorFactorization K)
    (A : ActiveFactorSupportData F) :=
  Σ k : Fin F.sectorCount, SupportedSectorIndex F A k

/-- The blockwise inclusion of all active factor supports in sector
coordinates.  Inactive blocks have empty domains and add no complement.

Source: arXiv:1606.00608, Appendix C.2, equation `AppUkU=rl`, lines
1381--1388. -/
noncomputable def dependentSupportInclusion
    (F : PhysicalSectorFactorization K) (A : ActiveFactorSupportData F) :
    Matrix (Σ k : Fin F.sectorCount, SectorIndex F k)
      (SupportedPhysicalIndex F A) ℂ :=
  Matrix.blockDiagonal' fun k ↦ F.sectorSupportInclusion A k

/-- The blockwise active-factor inclusion is an isometry, including when its
domain is empty. -/
theorem dependentSupportInclusion_isometry
    (F : PhysicalSectorFactorization K) (A : ActiveFactorSupportData F) :
    (F.dependentSupportInclusion A)ᴴ * F.dependentSupportInclusion A = 1 := by
  rw [dependentSupportInclusion, Matrix.blockDiagonal'_conjTranspose,
    ← Matrix.blockDiagonal'_mul]
  simp_rw [F.sectorSupportInclusion_isometry A]
  exact Matrix.blockDiagonal'_one

/-- The blockwise range projection is the direct sum of the joint supports of
the sector product families. -/
theorem dependentSupportInclusion_range
    (F : PhysicalSectorFactorization K) (A : ActiveFactorSupportData F) :
    F.dependentSupportInclusion A * (F.dependentSupportInclusion A)ᴴ =
      Matrix.blockDiagonal' fun k ↦
        Matrix.familySupportProj (F.sectorProductFamily k) := by
  rw [dependentSupportInclusion, Matrix.blockDiagonal'_conjTranspose,
    ← Matrix.blockDiagonal'_mul]
  congr 1
  funext k
  exact F.sectorSupportInclusion_range A k

/-- The direct sum of the joint product-family supports in sector
coordinates. -/
noncomputable def dependentPhysicalSupportProj
    (F : PhysicalSectorFactorization K) :
    Matrix (Σ k : Fin F.sectorCount, SectorIndex F k)
      (Σ k : Fin F.sectorCount, SectorIndex F k) ℂ :=
  Matrix.blockDiagonal' fun k ↦
    Matrix.familySupportProj (F.sectorProductFamily k)

/-- The range of the active-factor inclusion is the dependent physical
support projection. -/
theorem dependentSupportInclusion_range_eq_dependentPhysicalSupportProj
    (F : PhysicalSectorFactorization K) (A : ActiveFactorSupportData F) :
    F.dependentSupportInclusion A * (F.dependentSupportInclusion A)ᴴ =
      F.dependentPhysicalSupportProj := by
  exact F.dependentSupportInclusion_range A

/-- The dependent physical support fixes every transformed physical slice on
the left. -/
theorem dependentPhysicalSupportProj_mul_transformedPhysicalSlice
    (F : PhysicalSectorFactorization K) (β α : Fin D) :
    F.dependentPhysicalSupportProj * F.transformedPhysicalSlice β α =
      F.transformedPhysicalSlice β α := by
  rw [dependentPhysicalSupportProj, F.transformedPhysicalSlice_eq,
    ← Matrix.blockDiagonal'_mul]
  congr 1
  funext k
  exact Matrix.familySupportProj_mul (F.sectorProductFamily k) (β, α)

/-- Under the positivity hypotheses of `Appetakhetc`, the dependent physical
support also fixes every transformed physical slice on the right.

Source: arXiv:1606.00608, Appendix C.2, equations `AppUkU=rl` and
`Appetakhetc`, lines 1381--1450. -/
theorem transformedPhysicalSlice_mul_dependentPhysicalSupportProj
    (F : PhysicalSectorFactorization K)
    (hK : Kraus.IsInjective K.toMPSTensor)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef)
    (β α : Fin D) :
    F.transformedPhysicalSlice β α * F.dependentPhysicalSupportProj =
      F.transformedPhysicalSlice β α := by
  rw [dependentPhysicalSupportProj, F.transformedPhysicalSlice_eq,
    ← Matrix.blockDiagonal'_mul]
  congr 1
  funext k
  exact Matrix.mul_familySupportProj_of_conjTranspose_mem_span
    (F.sectorProductFamily k)
    (F.sectorProductFamily_conjTranspose_mem_span hK hpos k) (β, α)

/-- Every matrix fixing all transformed physical slices on the left also
fixes the direct sum of their sector-family supports. -/
theorem mul_dependentPhysicalSupportProj_eq_self_of_forall_mul_transformedPhysicalSlice_eq
    (F : PhysicalSectorFactorization K)
    (P : Matrix (Σ k : Fin F.sectorCount, SectorIndex F k)
      (Σ k : Fin F.sectorCount, SectorIndex F k) ℂ)
    (hP : ∀ β α, P * F.transformedPhysicalSlice β α =
      F.transformedPhysicalSlice β α) :
    P * F.dependentPhysicalSupportProj = F.dependentPhysicalSupportProj := by
  classical
  let E := fun k ↦ Matrix.sigmaBlockInclusion (SectorIndex F) k
  have hPE (k : Fin F.sectorCount) (q : Fin D × Fin D) :
      P * E k * F.sectorProductFamily k q =
        E k * F.sectorProductFamily k q := by
    dsimp only [E]
    calc
      P * Matrix.sigmaBlockInclusion (SectorIndex F) k *
            F.sectorProductFamily k q =
          P * (F.transformedPhysicalSlice q.1 q.2 *
            Matrix.sigmaBlockInclusion (SectorIndex F) k) := by
        rw [F.transformedPhysicalSlice_eq,
          Matrix.blockDiagonal'_mul_sigmaBlockInclusion]
        simp only [sectorProductFamily, Matrix.familyKronecker, Matrix.mul_assoc]
      _ = (P * F.transformedPhysicalSlice q.1 q.2) *
          Matrix.sigmaBlockInclusion (SectorIndex F) k := by
        simp only [Matrix.mul_assoc]
      _ = F.transformedPhysicalSlice q.1 q.2 *
          Matrix.sigmaBlockInclusion (SectorIndex F) k := by
        rw [hP]
      _ = Matrix.sigmaBlockInclusion (SectorIndex F) k *
          F.sectorProductFamily k q := by
        rw [F.transformedPhysicalSlice_eq,
          Matrix.blockDiagonal'_mul_sigmaBlockInclusion]
        rfl
  have hPSupport (k : Fin F.sectorCount) :
      P * E k * Matrix.familySupportProj (F.sectorProductFamily k) =
        E k * Matrix.familySupportProj (F.sectorProductFamily k) := by
    have hGram :
        P * E k * Matrix.familyColumnGram (F.sectorProductFamily k) =
          E k * Matrix.familyColumnGram (F.sectorProductFamily k) := by
      rw [Matrix.familyColumnGram_eq_sum, Matrix.mul_sum, Matrix.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      simp only [← Matrix.mul_assoc]
      rw [hPE]
    obtain ⟨W, hW⟩ :=
      (Matrix.familyColumnGram_posSemidef
        (F.sectorProductFamily k)).exists_supportProj_eq_mul
    change P * E k *
        (Matrix.familyColumnGram_posSemidef
          (F.sectorProductFamily k)).supportProj =
      E k * (Matrix.familyColumnGram_posSemidef
        (F.sectorProductFamily k)).supportProj
    rw [hW]
    calc
      P * E k *
          (Matrix.familyColumnGram (F.sectorProductFamily k) * W) =
          (P * E k * Matrix.familyColumnGram
            (F.sectorProductFamily k)) * W := by
        simp only [Matrix.mul_assoc]
      _ = (E k * Matrix.familyColumnGram
          (F.sectorProductFamily k)) * W := by rw [hGram]
      _ = E k *
          (Matrix.familyColumnGram (F.sectorProductFamily k) * W) := by
        simp only [Matrix.mul_assoc]
  rw [dependentPhysicalSupportProj,
    Matrix.blockDiagonal'_eq_sum_sigmaBlockInclusion, Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simpa only [Matrix.mul_assoc] using congrArg
    (fun X ↦ X * (E k)ᴴ) (hPSupport k)

end MPOTensor.PhysicalSectorFactorization
