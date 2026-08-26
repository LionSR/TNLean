/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.KrausGauge
import TNLean.MPS.Defs

/-!
# MPS bridges for Kraus gauges

This file records the genuine `GaugeEquiv` and `SameMPV` consequences of the
generic TP and unital gauge constructions.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- The TP-gauged family is gauge-equivalent to the original tensor. -/
theorem gaugeEquiv_tpGauge
    (A : MPSTensor d D) (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    GaugeEquiv A (Kraus.tpGauge A ρ) := by
  classical
  let X : GL (Fin D) ℂ :=
    Matrix.GeneralLinearGroup.mk'' (CFC.sqrt ρ) (by
      simpa using Matrix.PosDef.isUnit_det_cfc_sqrt hρ)
  refine ⟨X, ?_⟩
  intro i
  simp [Kraus.tpGauge, X]

/-- TP gauging preserves finite-ring MPV coefficients. -/
theorem sameMPV_tpGauge
    (A : MPSTensor d D) (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    SameMPV A (Kraus.tpGauge A ρ) :=
  GaugeEquiv.sameMPV (gaugeEquiv_tpGauge A ρ hρ)

/-- The unital-gauged family is gauge-equivalent to the original tensor. -/
theorem gaugeEquiv_unitalGauge
    (A : MPSTensor d D) (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    GaugeEquiv A (Kraus.unitalGauge A ρ) := by
  classical
  let X : GL (Fin D) ℂ :=
    Matrix.GeneralLinearGroup.mk'' (CFC.sqrt ρ) (by
      simpa using Matrix.PosDef.isUnit_det_cfc_sqrt hρ)
  refine ⟨X⁻¹, ?_⟩
  intro i
  simp [Kraus.unitalGauge, X]

/-- Unital gauging preserves finite-ring MPV coefficients. -/
theorem sameMPV_unitalGauge
    (A : MPSTensor d D) (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    SameMPV A (Kraus.unitalGauge A ρ) :=
  GaugeEquiv.sameMPV (gaugeEquiv_unitalGauge A ρ hρ)

end MPSTensor
