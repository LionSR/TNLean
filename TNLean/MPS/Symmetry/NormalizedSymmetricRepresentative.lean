/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.UnitaryVirtualRepresentation
import TNLean.MPS.Symmetry.SymmetricMPS
import TNLean.MPS.ParentHamiltonian.PrimitiveGaugeExistence

/-!
# Canonical symmetric representatives with unchanged parent interactions

A nonzero scalar normalization and a virtual gauge put an injective tensor
in left-canonical form. These operations preserve its physical symmetry
and every canonical parent interaction. The virtual symmetry can then be
chosen unitary. This justifies the canonical normalization preceding the
symmetric polar deformation in arXiv:1010.3732, Sections II.D.2 and II.F.
-/

namespace MPSTensor

open TNLean.Algebra
open scoped Matrix

/-- Every injective tensor with exact unitary on-site symmetry has an
injective representative with unitary virtual projective symmetry and
identical canonical parent interactions at every range. Source:
arXiv:1010.3732, Sections II.D.2 and II.F.1; arXiv:quant-ph/0608197,
Theorem 4, canonical normalization in its proof. -/
theorem exists_unitary_virtual_rep_representative_of_symmetric_injective
    {G : Type*} [Group G] {d D : ℕ} [NeZero D]
    (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A U) :
    ∃ B : MPSTensor d D, ∃ ω : ScalarCocycle G,
      ∃ ρ : ProjectiveRepresentation (D := D) ω,
        Kraus.IsInjective B ∧ IsLeftCanonical B ∧
        (∀ g, (ρ.X g : Matrix (Fin D) (Fin D) ℂ) ∈
          Matrix.unitaryGroup (Fin D) ℂ) ∧
        (∀ g i, twistedTensor B U g i =
          (ρ.X g⁻¹ : Matrix (Fin D) (Fin D) ℂ) * B i *
            (((ρ.X g⁻¹)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) ∧
        (∀ L, parentInteraction A L = parentInteraction B L) := by
  obtain ⟨B, ζ, σ, hζ, hGauge, _, hPrim, _, _, hParent, _⟩ :=
    exists_isPrimitiveMPS_gauge_of_isNormal hA.isNormal
  have hB : Kraus.IsInjective B := isInjective_of_gaugeEquiv (hA.smul hζ) hGauge
  have hBSymm : IsOnSiteSymmetric B U :=
    (hSymm.smul ζ).of_gaugeEquiv hGauge
  obtain ⟨ω, ρ, hρ, hCov⟩ :=
    exists_unitary_virtual_rep_of_symmetric_injective_leftCanonical
      B hB hPrim.norm U hU hBSymm
  exact ⟨B, ω, ρ, hB, hPrim.norm, hρ, hCov, hParent⟩

end MPSTensor
