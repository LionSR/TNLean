/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.InjectiveParentGappedPath
import TNLean.MPS.Symmetry.PhysicalCoefficientCovariance
import TNLean.MPS.Symmetry.NormalizedSymmetricRepresentative

/-!
# Gapped symmetric polar deformation of an injective MPS

An injective tensor with unitary projective virtual covariance admits a
continuous symmetric gapped canonical-parent path to its isometric physical
coefficient map. This is the polar-deformation step of
Schuch--Pérez-García--Cirac, arXiv:1010.3732, Sections II.D.2 and II.F.2.

Canonical normalization supplies unitary virtual covariance for every
exactly symmetric injective tensor and preserves its parent interactions.
-/

open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace MPSTensor

/-- The equivariant polar deformation of a one-site injective tensor has a
uniformly gapped symmetric canonical parent path. The endpoint isometric
tensor has coefficient matrix (W). Source: arXiv:1010.3732, Sections
II.D.2 and II.F.2. -/
theorem exists_projective_equivariant_polar_parent_gapped_path
    {G : Type*} [Group G] {d D : ℕ} [NeZero D]
    {ω : TNLean.Algebra.ScalarCocycle G}
    (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (ρ : TNLean.Algebra.ProjectiveRepresentation (D := D) ω)
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ)
    (hρ : ∀ g : G, (ρ.X g : Matrix (Fin D) (Fin D) ℂ) ∈
      Matrix.unitaryGroup (Fin D) ℂ)
    (hCov : ∀ g, rotatePhysical (U g : Matrix (Fin d) (Fin d) ℂ) A =
      fun i ↦ (ρ.X g⁻¹ : Matrix (Fin D) (Fin D) ℂ) * A i *
        (((ρ.X g⁻¹)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) :
    ∃ (Q : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)
      (W : Matrix (Fin d) (Fin D × Fin D) ℂ),
      Q.PosDef ∧ Wᴴ * W = 1 ∧
      A = tensorOfPhysicalCoefficientMatrix (W * Matrix.polarInterpolant Q 1) ∧
      Nonempty (SymmetricGappedInteractionPath U
        (canonicalParentMatrix A)
        (canonicalParentMatrix (tensorOfPhysicalCoefficientMatrix W))) := by
  obtain ⟨Q, W, hQ, hW, hAend, hInj, hCont, hCovPath⟩ :=
    exists_projective_equivariant_polar_tensor_path A hA ρ
      (fun g => (U g : Matrix (Fin d) (Fin d) ℂ))
      (fun g => (U g).property) hρ hCov
  let Apath : Set.Icc (0 : ℝ) 1 → MPSTensor d D :=
    fun γ => tensorOfPhysicalCoefficientMatrix
      (W * Matrix.polarInterpolant Q γ)
  have hContPath : Continuous Apath := hCont.comp continuous_subtype_val
  have hInjPath (γ : Set.Icc (0 : ℝ) 1) : Kraus.IsInjective (Apath γ) :=
    hInj γ γ.property.1 γ.property.2
  have hCovPath' (γ : Set.Icc (0 : ℝ) 1) (g : G) :
      GaugeEquiv (Apath γ)
        (rotatePhysical (U g : Matrix (Fin d) (Fin d) ℂ) (Apath γ)) :=
    hCovPath γ g
  have P := injectiveParentGappedPath U Apath hContPath hInjPath hCovPath'
  refine ⟨Q, W, hQ, hW, hAend, ?_⟩
  refine ⟨?_⟩
  convert P.reverse using 1
  · simp [Apath, hAend]
  · simp [Apath, Matrix.polarInterpolant_zero]

/-- Every one-site injective tensor with exact unitary on-site symmetry has
a symmetric uniformly gapped parent-Hamiltonian path to a tensor with an
isometric physical coefficient map. Source: arXiv:1010.3732,
Sections II.D.2 and II.F.2. -/
theorem exists_symmetric_injective_parent_path_to_isometry
    {G : Type*} [Group G] {d D : ℕ} [NeZero D]
    (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (U : G →* Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp U)) :
    ∃ W : Matrix (Fin d) (Fin D × Fin D) ℂ, Wᴴ * W = 1 ∧
      Nonempty (SymmetricGappedInteractionPath U
        (canonicalParentMatrix A)
        (canonicalParentMatrix (tensorOfPhysicalCoefficientMatrix W))) := by
  obtain ⟨B, ω, ρ, hB, _, hρ, hCov, hParent⟩ :=
    exists_unitary_virtual_rep_representative_of_symmetric_injective A hA
      ((Matrix.unitaryGroup (Fin d) ℂ).subtype.comp U)
      (fun g => (U g).property) hSymm
  have hCov' : ∀ g, rotatePhysical (U g : Matrix (Fin d) (Fin d) ℂ) B =
      fun i ↦ (ρ.X g⁻¹ : Matrix (Fin D) (Fin D) ℂ) * B i *
        (((ρ.X g⁻¹)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) :=
    fun g => funext (hCov g)
  obtain ⟨Q, W, _, hW, _, hPath⟩ :=
    exists_projective_equivariant_polar_parent_gapped_path B hB ρ U hρ hCov'
  refine ⟨W, hW, ?_⟩
  have hMatrix : canonicalParentMatrix A = canonicalParentMatrix B :=
    congrArg LinearMap.toMatrix' (hParent 2)
  rw [hMatrix]
  exact hPath

end MPSTensor
