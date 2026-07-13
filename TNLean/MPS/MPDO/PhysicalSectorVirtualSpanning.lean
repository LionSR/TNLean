/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalSectorCoordinateTransport
import TNLean.MPS.MPDO.PhysicalSectorSupportRecurrence

/-!
# Spanning by physical-sector virtual matrices

An isometric change of physical coordinates preserves the span of the virtual
matrices of an MPO tensor. For a physical-sector factorization, the entries in
the new coordinates are either zero or the virtual matrices obtained from one
sector. Consequently, injectivity of the original tensor implies that all
sector virtual matrices span the full virtual matrix algebra.

## References

- [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, equations `AppUkU=rl` and `formK`, lines 1383--1387 and
  1434--1439
-/

open scoped Matrix BigOperators

namespace MPOTensor.PhysicalSectorFactorization

variable {d e D : ℕ}

/-- An isometric change of physical coordinates can be inverted entrywise by
the adjoint change of coordinates. -/
theorem changePhysicalBasis_inverse_apply_eq_sum
    (V : Matrix (Fin e) (Fin d) ℂ) (M : MPOTensor d D)
    (hV : Vᴴ * V = 1) (i j : Fin d) :
    M i j = ∑ x : Fin e, ∑ y : Fin e,
      (star (V x i) * V y j) • changePhysicalBasis V M x y := by
  ext beta alpha
  have hmatrix :
      Vᴴ * (V * physicalSlice M beta alpha * Vᴴ) * V =
        physicalSlice M beta alpha := by
    calc
      Vᴴ * (V * physicalSlice M beta alpha * Vᴴ) * V =
          (Vᴴ * V) * physicalSlice M beta alpha * (Vᴴ * V) := by
            simp only [Matrix.mul_assoc]
      _ = physicalSlice M beta alpha := by rw [hV]; simp
  have hentry := congrFun (congrFun hmatrix i) j
  change physicalSlice M beta alpha i j =
    (∑ x : Fin e, ∑ y : Fin e,
      (star (V x i) * V y j) • changePhysicalBasis V M x y) beta alpha
  rw [← hentry]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, physicalSlice,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, changePhysicalBasis]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro p _
  ring

variable {K : MPOTensor d D}

/-- The family of virtual matrices obtained from all pairs of physical
indices in sector coordinates. -/
noncomputable def sectorCoordinateMatrixFamily (F : PhysicalSectorFactorization K)
    (q : Fin (Fintype.card (Σ k : Fin F.sectorCount, F.SectorIndex k)) ×
      Fin (Fintype.card (Σ k : Fin F.sectorCount, F.SectorIndex k))) :
    Matrix (Fin D) (Fin D) ℂ :=
  F.sectorCoordinateTensor q.1 q.2

/-- If the original MPO tensor is injective, its matrices in sector
coordinates still span the full virtual matrix algebra. -/
theorem sectorCoordinateMatrixFamily_span_eq_top
    (F : PhysicalSectorFactorization K) (hK : K.IsInjective) :
    Submodule.span ℂ (Set.range F.sectorCoordinateMatrixFamily) = ⊤ := by
  classical
  let S := Submodule.span ℂ (Set.range F.sectorCoordinateMatrixFamily)
  have hKmem (i j : Fin d) : K i j ∈ S := by
    have hrepr := changePhysicalBasis_inverse_apply_eq_sum
      F.physicalCoordinateMatrix K F.physicalCoordinateMatrix_isometry i j
    rw [← F.sectorCoordinateTensor_eq_changePhysicalBasis] at hrepr
    rw [hrepr]
    apply Submodule.sum_mem
    intro x _
    apply Submodule.sum_mem
    intro y _
    apply Submodule.smul_mem
    exact Submodule.subset_span (Set.mem_range_self (x, y))
  rw [Submodule.eq_top_iff']
  intro Y
  have hY : Y ∈ Submodule.span ℂ (Set.range K.toMPSTensor) := by
    rw [hK]
    exact Submodule.mem_top
  induction hY using Submodule.span_induction with
  | mem X hX =>
      obtain ⟨p, rfl⟩ := hX
      simpa [MPOTensor.toMPSTensor] using hKmem p.divNat p.modNat
  | zero => exact Submodule.zero_mem S
  | add X Y _ _ hX hY => exact Submodule.add_mem S hX hY
  | smul c X _ hX => exact Submodule.smul_mem S c hX

/-- Every physical matrix entry in sector coordinates belongs to the span of
the within-sector virtual matrices. Off-diagonal sector entries vanish. -/
theorem sectorCoordinateTensor_mem_span_sectorVirtualMatrixFamily
    (F : PhysicalSectorFactorization K)
    (i j : Fin (Fintype.card (Σ k : Fin F.sectorCount, F.SectorIndex k))) :
    F.sectorCoordinateTensor i j ∈
      Submodule.span ℂ (Set.range F.sectorVirtualMatrixFamily) := by
  classical
  generalize hi : F.sectorFinEquiv i = si
  generalize hj : F.sectorFinEquiv j = sj
  obtain ⟨k, x⟩ := si
  obtain ⟨h, y⟩ := sj
  have hi' : i = F.sectorFinEquiv.symm ⟨k, x⟩ := by
    apply F.sectorFinEquiv.injective
    rw [Equiv.apply_symm_apply, hi]
  have hj' : j = F.sectorFinEquiv.symm ⟨h, y⟩ := by
    apply F.sectorFinEquiv.injective
    rw [Equiv.apply_symm_apply, hj]
  subst i
  subst j
  by_cases hkh : k = h
  · subst h
    have heq : F.sectorCoordinateTensor
        (F.sectorFinEquiv.symm ⟨k, x⟩) (F.sectorFinEquiv.symm ⟨k, y⟩) =
        F.sectorVirtualMatrix k x y := by
      ext beta alpha
      simp [sectorVirtualMatrix]
    rw [heq]
    apply Submodule.subset_span
    exact ⟨⟨k, (x, y)⟩, rfl⟩
  · have heq : F.sectorCoordinateTensor
        (F.sectorFinEquiv.symm ⟨k, x⟩) (F.sectorFinEquiv.symm ⟨h, y⟩) = 0 := by
      ext beta alpha
      simpa using F.sectorCoordinateTensor_apply_ne hkh x y beta alpha
    rw [heq]
    exact Submodule.zero_mem _

/-- The virtual matrices obtained from all entries within all physical sectors
span the full virtual matrix algebra whenever the original MPO tensor is
injective.

Source: arXiv:1606.00608, Appendix C.2, equations `AppUkU=rl` and `formK`,
lines 1383--1387 and 1434--1439. -/
theorem sectorVirtualMatrixFamily_span_eq_top
    (F : PhysicalSectorFactorization K) (hK : K.IsInjective) :
    Submodule.span ℂ (Set.range F.sectorVirtualMatrixFamily) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro Y
  have hY : Y ∈ Submodule.span ℂ (Set.range F.sectorCoordinateMatrixFamily) := by
    rw [F.sectorCoordinateMatrixFamily_span_eq_top hK]
    exact Submodule.mem_top
  induction hY using Submodule.span_induction with
  | mem X hX =>
      obtain ⟨q, rfl⟩ := hX
      exact F.sectorCoordinateTensor_mem_span_sectorVirtualMatrixFamily q.1 q.2
  | zero => exact Submodule.zero_mem _
  | add X Y _ _ hX hY => exact Submodule.add_mem _ hX hY
  | smul c X _ hX => exact Submodule.smul_mem _ c hX

end MPOTensor.PhysicalSectorFactorization

