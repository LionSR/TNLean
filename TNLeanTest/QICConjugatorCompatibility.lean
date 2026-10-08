/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.DifferentiableInnerAction
import TNLean.MPS.Symmetry.GlobalVirtualGauge

/-!
# QICLean matrix-unit conjugator compatibility

The generic differentiable action and tensor-specific continuous gauge must
coexist in one import closure. Keeping a second matrix-unit implementation in
TNLean causes this import to fail with a duplicate declaration, even when each
module compiles separately.
-/

open scoped Matrix

variable {D : ℕ}

example
    (α : Matrix (Fin D) (Fin D) ℂ → Matrix (Fin D) (Fin D) ℂ)
    (X₀ : Matrix (Fin D) (Fin D) ℂ) (a : Fin D) (i j : Fin D) :
    Matrix.matrixUnitConjugator α X₀ a i j = (α (Matrix.single j a 1) * X₀) i a := rfl

example
    (α : Matrix (Fin D) (Fin D) ℂ → Matrix (Fin D) (Fin D) ℂ)
    (X₀ : Matrix (Fin D) (Fin D) ℂ) (a : Fin D) (Y : GL (Fin D) ℂ)
    (hα : ∀ M, α M = Y * M * Y⁻¹) :
    Matrix.matrixUnitConjugator α X₀ a =
      ((((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * X₀) a a) •
        (Y : Matrix (Fin D) (Fin D) ℂ) :=
  Matrix.matrixUnitConjugator_eq_smul α X₀ a Y hα

example
    (α : Matrix (Fin D) (Fin D) ℂ → Matrix (Fin D) (Fin D) ℂ)
    (X₀ : Matrix (Fin D) (Fin D) ℂ) (a : Fin D) (Y : GL (Fin D) ℂ)
    (hα : ∀ M, α M = Y * M * Y⁻¹) (M : Matrix (Fin D) (Fin D) ℂ) :
    α M * Matrix.matrixUnitConjugator α X₀ a =
      Matrix.matrixUnitConjugator α X₀ a * M :=
  Matrix.matrixUnitConjugator_intertwines α X₀ a Y hα M

example
    {T : Type*} [TopologicalSpace T] (hD : 0 < D)
    (α : T → Matrix (Fin D) (Fin D) ℂ → Matrix (Fin D) (Fin D) ℂ)
    (hα : ∀ M, Continuous fun t => α t M)
    (hinner : ∀ t, ∃ Y : GL (Fin D) ℂ, ∀ M, α t M = Y * M * Y⁻¹)
    (t₀ : T) (X₀ : GL (Fin D) ℂ)
    (hbase : ∀ M, α t₀ M = X₀ * M * X₀⁻¹) :
    ∃ X : T → Matrix (Fin D) (Fin D) ℂ,
      Continuous X ∧ X t₀ = X₀ ∧
      (∀ᶠ t in nhds t₀, (X t).det ≠ 0) ∧
      ∀ t M, α t M * X t = X t * M :=
  Matrix.exists_continuous_local_matrixConjugator hD α hα hinner t₀ X₀ hbase
