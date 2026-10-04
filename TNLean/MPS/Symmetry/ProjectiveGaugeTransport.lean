/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.CocycleCoboundary

/-!
# Transporting virtual projective representations through a gauge

A change of bond basis conjugates every virtual symmetry matrix and retains
its factor system. A nonzero scalar rescaling of the tensor also retains
virtual covariance. Thus the virtual cohomology class is unchanged by the
gauge preparation preceding the polar deformation.

Source: arXiv:1010.3732, Sections II.C and II.F.2.
-/

open scoped Matrix

namespace TNLean.Algebra.ProjectiveRepresentation

variable {G : Type} [Group G] {D : ℕ} {ω : ScalarCocycle G}

/-- Conjugating the virtual matrices retains the factor system. Source:
arXiv:1010.3732, Section II.C, virtual gauge preparation. -/
def conjugate (ρ : ProjectiveRepresentation (D := D) ω) (Y : GL (Fin D) ℂ) :
    ProjectiveRepresentation (D := D) ω where
  X g := Y * ρ.X g * Y⁻¹
  map_mul' := by
    intro g h
    have hY : ((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) *
        (Y : Matrix (Fin D) (Fin D) ℂ) = 1 := by simp
    simp only [Matrix.GeneralLinearGroup.coe_mul]
    calc
      _ = (Y : Matrix (Fin D) (Fin D) ℂ) *
          ((ρ.X g : Matrix (Fin D) (Fin D) ℂ) * (ρ.X h : Matrix (Fin D) (Fin D) ℂ)) *
          ((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
            simp only [Matrix.mul_assoc, ← Matrix.mul_assoc
              ((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ), hY, Matrix.one_mul]
      _ = _ := by rw [ρ.map_mul, Matrix.mul_smul, Matrix.smul_mul]

end TNLean.Algebra.ProjectiveRepresentation

namespace MPSTensor

open TNLean.Algebra

/-- Virtual covariance survives a nonzero rescaling and a bond gauge,
with the virtual matrices conjugated by that gauge. Source:
arXiv:1010.3732, Section II.C, standard-form preparation. -/
theorem twistedTensor_covariance_of_smul_gauge
    {G : Type} [Group G] {d D : ℕ} {A B : MPSTensor d D}
    (U : G →* Matrix (Fin d) (Fin d) ℂ) {ω : ScalarCocycle G}
    (ρ : ProjectiveRepresentation (D := D) ω)
    (hρ : ∀ g i, twistedTensor A U g i =
      (ρ.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * A i *
        (((ρ.X (g⁻¹))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))
    (c : ℂ) (Y : GL (Fin D) ℂ)
    (hB : ∀ i, B i = (Y : Matrix (Fin D) (Fin D) ℂ) * (c • A i) *
      ((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) :
    ∀ g i, twistedTensor B U g i =
      ((ρ.conjugate Y).X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * B i *
        ((((ρ.conjugate Y).X (g⁻¹))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
  intro g i
  have hY : ((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) *
      (Y : Matrix (Fin D) (Fin D) ℂ) = 1 := by simp
  have hTw : twistedTensor B U g i = (Y : Matrix (Fin D) (Fin D) ℂ) *
      (c • twistedTensor A U g i) *
      ((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
    simp only [twistedTensor, hB, Finset.mul_sum, Finset.sum_mul,
      Finset.smul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm]
  rw [hTw, hρ, hB]
  simp only [ProjectiveRepresentation.conjugate, mul_inv_rev, inv_inv,
    Matrix.GeneralLinearGroup.coe_mul]
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc
    ((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ), hY,
    Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul]

/-- Nonzero rescaling and virtual gauge preserve the cohomology class of
any chosen virtual representations. Source: arXiv:1010.3732, Sections II.C
and II.F.2, gauge independence of the phase label. -/
theorem cohomologousTo_of_smul_gaugeEquiv
    {G : Type} [Group G] {d D : ℕ} [NeZero D] {A B : MPSTensor d D}
    (hB : Kraus.IsInjective B) (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (c : ℂ) (hGauge : GaugeEquiv (c • A) B)
    {ω₀ ω₁ : ScalarCocycle G}
    (ρ₀ : ProjectiveRepresentation (D := D) ω₀)
    (ρ₁ : ProjectiveRepresentation (D := D) ω₁)
    (hρ₀ : ∀ g i, twistedTensor A U g i =
      (ρ₀.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * A i *
        (((ρ₀.X (g⁻¹))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))
    (hρ₁ : ∀ g i, twistedTensor B U g i =
      (ρ₁.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * B i *
        (((ρ₁.X (g⁻¹))⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) :
    ω₁.CohomologousTo ω₀ := by
  obtain ⟨Y, hY⟩ := hGauge
  exact cohomologousTo_of_isInjective B hB U (NeZero.pos D)
    (twistedTensor_covariance_of_smul_gauge U ρ₀ hρ₀ c Y hY) hρ₁

end MPSTensor
