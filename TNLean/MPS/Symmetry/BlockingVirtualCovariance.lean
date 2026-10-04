/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.Blocking
import TNLean.Algebra.UnitaryGeneralLinearInverse
import TNLean.MPS.Symmetry.EntanglementSpectrum

/-!
# Exact virtual covariance under common physical blocking

A common physical blocking replaces the on-site action by its tensor power.
The virtual representation itself is unchanged, so its factor system is
unchanged. The statements allow any block length; a positive length is needed
only in later applications to periodic coefficients and injectivity.

Source context: arXiv:1010.3732, Appendix C, lines 2653–2717, and
arXiv:1606.00608, lines 318–344.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open scoped Matrix
open TNLean.Algebra

namespace MPSTensor

/-- The tensor-power on-site unitary representation in the blocked physical
coordinates. Source context: arXiv:1606.00608, lines 318–344. -/
noncomputable def blockUnitaryPhysicalAction
    {G : Type*} [Monoid G] {d : ℕ}
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ) (L : ℕ) :
    G →* Matrix.unitaryGroup (Fin (blockPhysDim d L)) ℂ where
  toFun g := ⟨blockKron L (U g), Matrix.mem_unitaryGroup_iff.mpr
    (blockKron_mul_conjTranspose L _ (Matrix.mem_unitaryGroup_iff.mp (U g).property))⟩
  map_one' := by
    apply Subtype.ext
    change blockKron L (U 1 : Matrix (Fin d) (Fin d) ℂ) = 1
    rw [map_one]
    exact blockKron_one L
  map_mul' g h := by
    apply Subtype.ext
    change blockKron L (U (g * h) : Matrix (Fin d) (Fin d) ℂ) =
      blockKron L (U g) * blockKron L (U h)
    rw [map_mul]
    exact blockKron_mul L _ _

/-- A unitary projective virtual action implements the blocked on-site
symmetry with exactly the same factor system. Source context:
arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem rotatePhysical_blockTensor_of_unitary_virtual_covariance
    {G : Type} [Group G] {d D : ℕ} (A : MPSTensor d D)
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ) {ω : ScalarCocycle G}
    (ρ : ProjectiveRepresentation (D := D) ω)
    (hρ : ∀ g, (ρ.X g : Matrix (Fin D) (Fin D) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (hCov : ∀ g, rotatePhysical (U g) A = fun i =>
      (ρ.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * A i *
        (ρ.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ)ᴴ) (L : ℕ) :
    ∀ g, rotatePhysical (blockUnitaryPhysicalAction U L g) (blockTensor A L) =
      fun i => (ρ.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ) * blockTensor A L i *
        (ρ.X (g⁻¹) : Matrix (Fin D) (Fin D) ℂ)ᴴ := by
  intro g
  funext i
  have h := twistedTensor_blockTensor_eq_gauge
    (U := (Matrix.unitaryGroup (Fin d) ℂ).subtype.comp U) (g := g) (R := ρ.X g⁻¹)
    (fun i => by
      rw [Matrix.coe_gl_inv_eq_conjTranspose_of_mem_unitaryGroup _ (hρ g⁻¹)]
      exact congrFun (hCov g) i) L i
  rw [Matrix.coe_gl_inv_eq_conjTranspose_of_mem_unitaryGroup _ (hρ g⁻¹)] at h
  exact h

end MPSTensor
