/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalSectorVirtualTransport

/-!
# Virtual-gauge transport of physical-sector factorizations

A virtual similarity mixes the left and right virtual indices by inverse
matrices.  These changes can be absorbed separately into the two tensor
factors of a physical-sector factorization.  Their contraction cancels the
gauge, so the neighboring operators are unchanged.

## Background

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608, Appendix C.2,
  equation `AppUkU=rl`, lines 1381--1388, for the physical-sector
  factorization transported here.
-/

open scoped ComplexOrder Matrix

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K L : MPOTensor d D}

/-- Transport a physical-sector factorization through an invertible virtual
gauge.

The physical-sector decomposition and physical isometry are unchanged.  The
gauge and its inverse are absorbed into the left and right virtual tensor
families, respectively.

Background for the factorization: arXiv:1606.00608, Appendix C.2, equation
`AppUkU=rl`, lines 1381--1388. That passage does not state the virtual-gauge
transport; the present construction is the direct algebraic transport of its
two virtual factors. -/
noncomputable def ofGaugeEquiv (F : PhysicalSectorFactorization K)
    (hGauge : MPSTensor.GaugeEquiv K.toMPSTensor L.toMPSTensor) :
    PhysicalSectorFactorization L :=
  F.ofVirtualMatrices
    ((Classical.choose hGauge : GL (Fin D) ℂ) :
      Matrix (Fin D) (Fin D) ℂ)
    (((Classical.choose hGauge : GL (Fin D) ℂ)⁻¹ : GL (Fin D) ℂ) :
      Matrix (Fin D) (Fin D) ℂ)
    (Classical.choose_spec hGauge)

/-- Virtual-gauge transport is virtual-matrix transport by a gauge and its
inverse. -/
theorem ofGaugeEquiv_eq_ofVirtualMatrices
    (F : PhysicalSectorFactorization K)
    (hGauge : MPSTensor.GaugeEquiv K.toMPSTensor L.toMPSTensor) :
    F.ofGaugeEquiv hGauge =
      F.ofVirtualMatrices
        ((Classical.choose hGauge : GL (Fin D) ℂ) :
          Matrix (Fin D) (Fin D) ℂ)
        (((Classical.choose hGauge : GL (Fin D) ℂ)⁻¹ : GL (Fin D) ℂ) :
          Matrix (Fin D) (Fin D) ℂ)
        (Classical.choose_spec hGauge) :=
  rfl

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
  have hX : ∀ i : Fin (d * d),
      L.toMPSTensor i = X * K.toMPSTensor i * X⁻¹ :=
    Classical.choose_spec hGauge
  have hyx : y * x = 1 := by
    change
      (((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) *
        (X : Matrix (Fin D) (Fin D) ℂ)) = 1
    rw [← Units.val_mul]
    simp
  calc
    (F.ofGaugeEquiv hGauge).neighboringOperator k h =
        F.neighboringOperatorWithMatrix k h (y * x) := by
      simpa only [ofGaugeEquiv_eq_ofVirtualMatrices, X, x, y] using
        F.ofVirtualMatrices_neighboringOperator x y hX k h
    _ = F.neighboringOperator k h := by
      rw [hyx]
      exact F.neighboringOperatorWithMatrix_one k h

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
