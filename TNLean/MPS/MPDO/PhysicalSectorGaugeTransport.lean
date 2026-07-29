/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalSectorFactorization

/-!
# Virtual-gauge transport of physical-sector factorizations

A virtual similarity mixes the left and right virtual indices by inverse
matrices.  These changes can be absorbed separately into the two tensor
factors of a physical-sector factorization.  Their contraction cancels the
gauge, so the neighboring operators are unchanged.
-/

open scoped ComplexOrder Matrix

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K L : MPOTensor d D}

/-- Transport a physical-sector factorization through an invertible virtual
gauge.

The physical-sector decomposition and physical isometry are unchanged.  The
gauge and its inverse are absorbed into the left and right virtual tensor
families, respectively.

Source context: arXiv:1606.00608, Appendix C.2, equation `AppUkU=rl`, lines
1381--1388. -/
noncomputable def ofGaugeEquiv (F : PhysicalSectorFactorization K)
    (hGauge : MPSTensor.GaugeEquiv K.toMPSTensor L.toMPSTensor) :
    PhysicalSectorFactorization L := by
  classical
  let X : GL (Fin D) ℂ := Classical.choose hGauge
  have hX : ∀ i : Fin (d * d),
      L.toMPSTensor i = X * K.toMPSTensor i * X⁻¹ :=
    Classical.choose_spec hGauge
  let x : Matrix (Fin D) (Fin D) ℂ := X
  let y : Matrix (Fin D) (Fin D) ℂ :=
    ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)
  refine
    { sectorCount := F.sectorCount
      leftDim := F.leftDim
      rightDim := F.rightDim
      leftDim_pos := F.leftDim_pos
      rightDim_pos := F.rightDim_pos
      sectorEquiv := F.sectorEquiv
      physicalIsometry := F.physicalIsometry
      physicalIsometry_isometry := F.physicalIsometry_isometry
      leftTensor := fun k beta ↦
        ∑ gamma, x beta gamma • F.leftTensor k gamma
      rightTensor := fun k alpha ↦
        ∑ delta, y delta alpha • F.rightTensor k delta
      factorization := ?_ }
  intro beta alpha
  ext ⟨k, a⟩ ⟨h, b⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  have hLetter (i j : Fin d) :
      L i j = x * K i j * y := by
    simpa only [MPOTensor.toMPSTensor, MPSTensor.finProdFinEquiv_divNat,
      MPSTensor.finProdFinEquiv_modNat, x, y] using
      hX (finProdFinEquiv (i, j))
  have hSlice :
      physicalSlice L beta alpha =
        ∑ gamma, ∑ delta,
          (x beta gamma * y delta alpha) • physicalSlice K gamma delta := by
    ext i j
    simp only [physicalSlice, hLetter, Matrix.mul_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro gamma _
    apply Finset.sum_congr rfl
    intro delta _
    ring
  have hConj :
      F.physicalIsometry * physicalSlice L beta alpha *
          F.physicalIsometryᴴ =
        ∑ gamma, ∑ delta, (x beta gamma * y delta alpha) •
          (F.physicalIsometry * physicalSlice K gamma delta *
            F.physicalIsometryᴴ) := by
    rw [hSlice]
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
      Matrix.smul_mul]
  rw [hConj]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases hkh : k = h
  · subst h
    rw [Matrix.blockDiagonal'_apply_eq]
    simp only [Matrix.kroneckerMap_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul]
    have hF (gamma delta : Fin D) :=
      congrFun (congrFun (F.factorization gamma delta) ⟨k, a⟩) ⟨k, b⟩
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.blockDiagonal'_apply_eq, Matrix.kroneckerMap_apply] at hF
    simp_rw [hF]
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro gamma _
    apply Finset.sum_congr rfl
    intro delta _
    ring
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hkh]
    have hF (gamma delta : Fin D) :=
      congrFun (congrFun (F.factorization gamma delta) ⟨k, a⟩) ⟨h, b⟩
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.blockDiagonal'_apply_ne _ _ _ hkh] at hF
    simp_rw [hF]
    simp

/-- Virtual-gauge transport leaves every neighboring operator unchanged. -/
@[simp] theorem ofGaugeEquiv_neighboringOperator
    (F : PhysicalSectorFactorization K)
    (hGauge : MPSTensor.GaugeEquiv K.toMPSTensor L.toMPSTensor)
    (k h : Fin F.sectorCount) :
    (F.ofGaugeEquiv hGauge).neighboringOperator k h =
      F.neighboringOperator k h := by
  classical
  let X : GL (Fin D) ℂ := Classical.choose hGauge
  let x : Matrix (Fin D) (Fin D) ℂ := X
  let y : Matrix (Fin D) (Fin D) ℂ :=
    ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)
  have hyx : y * x = 1 := by
    change
      (((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) *
        (X : Matrix (Fin D) (Fin D) ℂ)) = 1
    rw [← Units.val_mul]
    simp
  ext a b
  simp only [neighboringOperator_apply, ofGaugeEquiv, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro delta _
  rw [Finset.sum_comm]
  calc
    (∑ gamma, ∑ beta,
        ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) delta beta *
            F.rightTensor k delta a.1 b.1 *
          ((X : Matrix (Fin D) (Fin D) ℂ) beta gamma *
            F.leftTensor h gamma a.2 b.2)) =
        ∑ gamma, if delta = gamma then
          F.rightTensor k delta a.1 b.1 *
            F.leftTensor h gamma a.2 b.2
        else 0 := by
      apply Finset.sum_congr rfl
      intro gamma _
      calc
        (∑ beta,
            ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) delta beta *
                F.rightTensor k delta a.1 b.1 *
              ((X : Matrix (Fin D) (Fin D) ℂ) beta gamma *
                F.leftTensor h gamma a.2 b.2)) =
            (y * x) delta gamma *
              F.rightTensor k delta a.1 b.1 *
              F.leftTensor h gamma a.2 b.2 := by
          rw [Matrix.mul_apply]
          simp only [y, x]
          rw [Finset.sum_mul, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro beta _
          ring
        _ = if delta = gamma then
              F.rightTensor k delta a.1 b.1 *
                F.leftTensor h gamma a.2 b.2
            else 0 := by
          rw [hyx, Matrix.one_apply]
          split
          · simp_all
          · simp_all
    _ = F.rightTensor k delta a.1 b.1 *
        F.leftTensor h delta a.2 b.2 := by
      simp [Finset.sum_ite_eq, Finset.mem_univ]

/-- Positivity of the neighboring operators is preserved by virtual-gauge
transport. -/
theorem ofGaugeEquiv_neighboringOperator_posSemidef
    (F : PhysicalSectorFactorization K)
    (hGauge : MPSTensor.GaugeEquiv K.toMPSTensor L.toMPSTensor)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef) :
    ∀ k h,
      ((F.ofGaugeEquiv hGauge).neighboringOperator k h).PosSemidef := by
  intro k h
  rw [F.ofGaugeEquiv_neighboringOperator hGauge k h]
  exact hpos k h

end MPOTensor.PhysicalSectorFactorization
