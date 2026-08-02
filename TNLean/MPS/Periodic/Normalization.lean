/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Irreducible.SpectralRadius
import TNLean.MPS.CanonicalForm.NormalTensorGauge
import TNLean.MPS.Periodic.Defs

/-!
# Perron normalization of spectral periodic blocks

This file passes from an irreducible periodic block of spectral radius one to a
left-canonical periodic block by a pure Perron similarity.  No scalar rescales
the tensor, so the similarity preserves every matrix-product vector and leaves
the multiplicity matrices of a block-diagonal irreducible form unchanged.

## Main result

* `IsSpectrallyPeriodic.exists_isPeriodic_tpGauge`: a spectrally periodic block
  has a gauge-equivalent trace-preserving representative with the same period.

## Reference

De las Cuevas--Cirac--Schuch--Pérez-García, arXiv:1708.00029, lines 313--332.
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.Operator

namespace MPSTensor

variable {d D m : ℕ}

/-- A spectrally periodic block has a gauge-equivalent left-canonical periodic
representative obtained without scalar rescaling.

The positive-definite adjoint Perron fixed point gives the trace-preserving
gauge.  The transfer map changes by similarity, so irreducibility and the
prescribed roots-of-unity peripheral spectrum are unchanged.

Source: arXiv:1708.00029, lines 313--332. -/
theorem IsSpectrallyPeriodic.exists_isPeriodic_tpGauge
    {A : MPSTensor d D} (hA : IsSpectrallyPeriodic m A) :
    ∃ σ : Matrix (Fin D) (Fin D) ℂ,
      σ.PosDef ∧
      transferMap (d := d) (D := D) (fun i ↦ (A i)ᴴ) σ = σ ∧
      GaugeEquiv A (tpGauge (d := d) (D := D) A σ) ∧
      IsPeriodic m (tpGauge (d := d) (D := D) A σ) := by
  obtain ⟨σ, hσ, hσfix, hLeft, hGauge, hIrr⟩ :=
    exists_tpGauge_of_irreducible_spectralRadius_one
      hA.irreducible hA.spectral_radius_one
  have hSdet : (CFC.sqrt σ).det ≠ 0 :=
    (isUnit_det_cfc_sqrt_of_posDef σ hσ).ne_zero
  have hSinvDet : ((CFC.sqrt σ)⁻¹).det ≠ 0 := by
    simpa [Matrix.det_nonsing_inv] using inv_ne_zero hSdet
  have hPeripheral :
      peripheralEigenvalues
          (transferMap (d := d) (D := D) (tpGauge (d := d) (D := D) A σ)) =
        peripheralEigenvalues (transferMap (d := d) (D := D) A) := by
    rw [transferMap_tpGauge_eq_similarityMap A σ hσ]
    exact peripheralEigenvalues_similarityMap_eq
      (CFC.sqrt σ)⁻¹ hSinvDet (transferMap (d := d) (D := D) A)
  refine ⟨σ, hσ, hσfix, hGauge, ?_⟩
  exact ⟨hIrr, hLeft, hA.period_pos, hPeripheral.trans hA.peripheral_eq⟩

end MPSTensor
