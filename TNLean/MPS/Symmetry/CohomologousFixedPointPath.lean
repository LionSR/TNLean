/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.FixedPointGappedPathWitness
import TNLean.MPS.Symmetry.ProjectiveRephasing
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Fixed-point paths for cohomologous virtual factor systems

Unitary virtual representations have unit-modulus factor systems. If two
such systems are cohomologous, a unit-circle rephasing makes them equal.
The normalized bond interpolation then gives a symmetric gapped path with
one common physical action. This is the fixed-point construction in
Schuch--Pérez-García--Cirac, arXiv:1010.3732, Section II.F.2,
`eq:1d-sym:jointsym` and `eq:sym:omega-gamma`.

**Local fix (second-block range):** The normalized bond interpolation uses
`D₀ + D₁` as the upper limit of the second block, correcting the printed
limit `D₁`. See `docs/paper-gaps/spc11_spt_interpolation_upper_range.tex`.

## References

- [arXiv:1010.3732](https://arxiv.org/abs/1010.3732) -- Schuch,
  Pérez-García, Cirac, *Classifying quantum phases using matrix product
  states and projected entangled pair states*, Section II.F.2
-/

open scoped Matrix Matrix.Norms.L2Operator

namespace TNLean.Algebra

/-- A factor system of a unitary projective representation has unit modulus.
Source: arXiv:1010.3732, Section II.F.2, lines 886--896, the unitary virtual
representations in the fixed-point symmetry. -/
theorem ProjectiveRepresentation.norm_factorSystem
    {G : Type} [Group G] {D : ℕ} [NeZero D] {ω : ScalarCocycle G}
    (ρ : ProjectiveRepresentation (D := D) ω)
    (hρ : ∀ g, (ρ.X g : Matrix (Fin D) (Fin D) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (g h : G) : ‖(ω g h : ℂ)‖ = 1 := by
  have hp := CStarRing.norm_of_mem_unitary
    ((Matrix.unitaryGroup (Fin D) ℂ).mul_mem (hρ g) (hρ h))
  rwa [ρ.map_mul, norm_smul, CStarRing.norm_of_mem_unitary (hρ (g * h)),
    mul_one] at hp

/-- The factor system of a unitary virtual action equals its pointwise unit
phase. Source: arXiv:1010.3732, Section II.F.2, lines 886--896. -/
theorem ProjectiveRepresentation.circlePhaseInclusion_eq
    {G : Type} [Group G] {D : ℕ} [NeZero D] {ω : ScalarCocycle G}
    (ρ : ProjectiveRepresentation (D := D) ω)
    (hρ : ∀ g, (ρ.X g : Matrix (Fin D) (Fin D) ℂ) ∈ Matrix.unitaryGroup _ ℂ) :
    ω.circlePhaseInclusion = ω := by
  funext g h
  apply Units.ext
  change (ω g h : ℂ) / ‖(ω g h : ℂ)‖ = (ω g h : ℂ)
  simp only [ρ.norm_factorSystem hρ, Complex.ofReal_one, div_one]

/-- Unitary virtual actions with cohomologous factor systems can be rephased
so that their factor systems agree exactly. Source: arXiv:1010.3732,
Section II.F.2, lines 886--921. -/
theorem ProjectiveRepresentation.exists_unitary_rephase_with_factorSystem
    {G : Type} [Group G] {D₀ D₁ : ℕ} [NeZero D₀] [NeZero D₁]
    {ω₀ ω₁ : ScalarCocycle G}
    (ρ₀ : ProjectiveRepresentation (D := D₀) ω₀)
    (ρ₁ : ProjectiveRepresentation (D := D₁) ω₁)
    (h : ω₁.CohomologousTo ω₀)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ) :
    ∃ (ρ₀' : ProjectiveRepresentation (D := D₀) ω₁) (φ : G → Circle),
      (∀ g, (ρ₀'.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ) ∧
      (∀ g, ρ₀'.X g = Matrix.GeneralLinearGroup.scalar (Fin D₀)
        (Circle.toUnits (φ g)) * ρ₀.X g) := by
  have hRephase := @ProjectiveRepresentation.exists_unitary_rephase_of_cohomologous
    G _ D₀ ω₀ ω₁
  rw [ρ₀.circlePhaseInclusion_eq h₀, ρ₁.circlePhaseInclusion_eq h₁] at hRephase
  exact hRephase ρ₀ h h₀

end TNLean.Algebra

namespace MPSTensor

/-- Pointwise scalar rephasing of a virtual action preserves its fixed-point
physical action. Source: arXiv:1010.3732, Section II.F.2, lines 880--896,
where the scalar cancels between the two virtual factors. -/
theorem sptFixedPointAction_eq_of_forall_eq_smul
    {G : Type} [Group G] {D : ℕ} {ω₀ ω₁ : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D) ω₀)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D) ω₁)
    (c : G → ℂ)
    (h : ∀ g, (ρ₁.X g : Matrix (Fin D) (Fin D) ℂ) =
      c g • (ρ₀.X g : Matrix (Fin D) (Fin D) ℂ))
    (κ : G →* ℂ) :
    sptFixedPointAction ρ₁ κ = sptFixedPointAction ρ₀ κ := by
  ext g : 1
  exact congrArg (fun K => κ g • Matrix.reindexAlgEquiv ℂ ℂ finProdFinEquiv K)
    (sptKron_eq_of_eq_smul (h g⁻¹))

/-- Cohomologous unitary virtual actions admit the common-factor fixed-point
bond path. The first action is rephased to the second factor system, while
its physical fixed-point action is preserved. Source: arXiv:1010.3732,
Section II.F.2, `eq:1d-sym:jointsym` and `eq:sym:omega-gamma`. -/
theorem exists_symmetricGappedInteractionPath_of_cohomologous_fixedPoint
    {G : Type} [Group G] {D₀ D₁ : ℕ} [NeZero D₀] [NeZero D₁]
    {ω₀ ω₁ : TNLean.Algebra.ScalarCocycle G}
    (ρ₀ : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω₀)
    (ρ₁ : TNLean.Algebra.ProjectiveRepresentation (D := D₁) ω₁)
    (h : ω₁.CohomologousTo ω₀)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ) :
    ∃ (ρ₀' : TNLean.Algebra.ProjectiveRepresentation (D := D₀) ω₁)
      (h₀' : ∀ g, (ρ₀'.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈
        Matrix.unitaryGroup _ ℂ),
      sptFixedPointAction ρ₀' 1 = sptFixedPointAction ρ₀ 1 ∧
      Nonempty (SymmetricGappedInteractionPath
        (sptFixedPointUnitaryAction (ρ₀'.directSum ρ₁)
          (fun g => ρ₀'.directSum_mem_unitaryGroup ρ₁ g (h₀' g) (h₁ g)))
        (normalizedBondInteraction D₀ D₁ 0)
        (normalizedBondInteraction D₀ D₁ 1)) := by
  obtain ⟨ρ₀', φ, h₀', hX⟩ :=
    ρ₀.exists_unitary_rephase_with_factorSystem ρ₁ h h₀ h₁
  refine ⟨ρ₀', h₀', ?_, ⟨normalizedBondFixedPointGappedPath ρ₀' ρ₁
    (Nat.pos_of_ne_zero (NeZero.ne D₀)) (Nat.pos_of_ne_zero (NeZero.ne D₁)) h₀' h₁⟩⟩
  apply sptFixedPointAction_eq_of_forall_eq_smul ρ₀ ρ₀'
    (fun g => (Circle.toUnits (φ g) : ℂ))
  intro g
  simpa only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul] using
    congrArg (fun W : GL (Fin D₀) ℂ => (W : Matrix (Fin D₀) (Fin D₀) ℂ)) (hX g)

end MPSTensor
