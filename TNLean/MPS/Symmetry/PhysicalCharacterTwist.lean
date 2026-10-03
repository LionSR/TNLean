/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.Defs
import TNLean.MPS.Core.ScaledNormality
import Mathlib.Analysis.Complex.Basic

/-!
# Scalar character changes of physical symmetry

Multiplication by a unit-modulus character gives another unitary on-site
representation. This is the endpoint phase-gauge freedom allowed in
Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.C.2,
lines 440–453, and Appendix B, lines 2614–2632.
-/

open scoped Matrix

namespace MPSTensor

/-- A unit-modulus scalar is unitary. -/
private theorem scalar_mem_unitary_of_norm_eq_one (z : ℂ) (hz : ‖z‖ = 1) :
    z ∈ unitary ℂ := by
  simp only [Unitary.mem_iff, Complex.star_def, Complex.mul_conj', Complex.conj_mul', hz]
  norm_num

/-- Multiplying an on-site unitary action by a unit-modulus character is
again an on-site unitary action. Source: arXiv:1010.3732, Section II.C.2,
lines 440–453, and Appendix B, lines 2614–2632. -/
noncomputable def physicalCharacterTwist {G : Type} [Group G] {d : ℕ}
    (χ : G →* ℂ) (hχ : ∀ g, ‖χ g‖ = 1)
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ) :
    G →* Matrix.unitaryGroup (Fin d) ℂ := by
  refine {
    toFun := fun g => ⟨χ g • (U g : Matrix (Fin d) (Fin d) ℂ),
      Unitary.smul_mem_of_mem (scalar_mem_unitary_of_norm_eq_one _ (hχ g))
        (SetLike.coe_mem (U g))⟩
    map_one' := ?_
    map_mul' := ?_
  }
  · exact Subtype.ext (by simp)
  · intro g h
    apply Subtype.ext
    simp [smul_smul, mul_comm]

/-- Matrix formula for the physical character twist; source context:
arXiv:1010.3732, Section II.C.2, lines 440–453. -/
@[simp] theorem physicalCharacterTwist_apply {G : Type} [Group G] {d : ℕ}
    (χ : G →* ℂ) (hχ : ∀ g, ‖χ g‖ = 1)
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ) (g : G) :
    (physicalCharacterTwist χ hχ U g : Matrix (Fin d) (Fin d) ℂ) =
      χ g • (U g : Matrix (Fin d) (Fin d) ℂ) := rfl

/-- The inverse character changes the physical phase gauge so as to remove
the scalar symmetry of a ground-state family. Source: arXiv:1010.3732,
Section II.C.2, lines 440–453, and Appendix B, lines 2614–2632. -/
noncomputable def physicalCharacterUntwist {G : Type} [Group G] {d : ℕ}
    (χ : G →* ℂ) (hχ : ∀ g, ‖χ g‖ = 1)
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ) :
    G →* Matrix.unitaryGroup (Fin d) ℂ :=
  physicalCharacterTwist (invMonoidHom.comp χ)
    (fun g => by simp only [MonoidHom.comp_apply, invMonoidHom_apply, norm_inv, hχ, inv_one]) U

/-- Physical scalar twisting commutes with the tensor twist, by pulling the
scalar outside the finite physical sum. Source context: arXiv:1010.3732,
Section II.C.2, lines 440–453. -/
theorem twistedTensor_physicalCharacterTwist {G : Type} [Group G] {d D : ℕ}
    (χ : G →* ℂ) (hχ : ∀ g, ‖χ g‖ = 1)
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ) (A : MPSTensor d D) (g : G) :
    twistedTensor A ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp
      (physicalCharacterTwist χ hχ U)) g =
      χ g • twistedTensor A ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp U) g := by
  funext i
  simp [twistedTensor, Finset.smul_sum, smul_smul]

/-- Matrix formula for removing a physical character; source context:
arXiv:1010.3732, Section II.C.2, lines 440–453. -/
@[simp] theorem physicalCharacterUntwist_apply {G : Type} [Group G] {d : ℕ}
    (χ : G →* ℂ) (hχ : ∀ g, ‖χ g‖ = 1)
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ) (g : G) :
    (physicalCharacterUntwist χ hχ U g : Matrix (Fin d) (Fin d) ℂ) =
      (χ g)⁻¹ • (U g : Matrix (Fin d) (Fin d) ℂ) := rfl

/-- Removing the physical character scales the twisted tensor by the
inverse character. Source context: arXiv:1010.3732, Appendix B,
lines 2614–2632. -/
theorem twistedTensor_physicalCharacterUntwist {G : Type} [Group G] {d D : ℕ}
    (χ : G →* ℂ) (hχ : ∀ g, ‖χ g‖ = 1)
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ) (A : MPSTensor d D) (g : G) :
    twistedTensor A ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp
      (physicalCharacterUntwist χ hχ U)) g =
      (χ g)⁻¹ • twistedTensor A ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp U) g :=
  twistedTensor_physicalCharacterTwist (invMonoidHom.comp χ) _ U A g

/-- Scalar MPV symmetry becomes exact tensor symmetry after the permitted
physical phase-gauge change. Source: arXiv:1010.3732, Section II.C.2,
lines 440–453, and Appendix B, lines 2614–2632. -/
theorem isOnSiteSymmetric_physicalCharacterUntwist {G : Type} [Group G] {d D : ℕ}
    (χ : G →* ℂ) (hχ : ∀ g, ‖χ g‖ = 1)
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ) (A : MPSTensor d D)
    (hSym : ∀ g, SameMPV (χ g • A)
      (twistedTensor A ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp U) g)) :
    IsOnSiteSymmetric A ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp
      (physicalCharacterUntwist χ hχ U)) := by
  intro g N σ
  simp only [twistedTensor_physicalCharacterUntwist, Pi.smul_def, mpv_smul]
  simp only [← hSym g N σ, Pi.smul_def, mpv_smul]
  have hχne : χ g ≠ 0 := norm_ne_zero_iff.mp (by rw [hχ g]; exact one_ne_zero)
  rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hχne, one_pow, one_mul]

end MPSTensor
