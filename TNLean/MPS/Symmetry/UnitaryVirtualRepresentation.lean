/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.VirtualRepresentation
import TNLean.MPS.Periodic.Applications
import TNLean.MPS.FundamentalTheorem.UnitaryGauge

/-!
# Unitary virtual symmetry in canonical form

An injective left-canonical tensor with unitary physical symmetry admits
unitary virtual gauges. Choosing these gauges first and then assembling
their projective multiplication law gives a unitary projective
representation. Source: Schuch–Pérez-García–Cirac, arXiv:1010.3732,
Section II.F.1; CPSV16, Corollary A.6.
-/

namespace MPSTensor

open TNLean.Algebra
open scoped Matrix

/-- Exact physical symmetry of an injective left-canonical tensor is
implemented by a unitary virtual gauge. Source: arXiv:1010.3732,
Section II.F.1, and arXiv:1606.00608, Corollary A.6. -/
theorem exists_unitary_gauge_of_symmetric_injective_leftCanonical
    {G : Type*} [Group G] {d D : ℕ} [NeZero D]
    (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (hleft : IsLeftCanonical A)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A U) (g : G) :
    ∃ V : Matrix.unitaryGroup (Fin D) ℂ,
      ∀ i, twistedTensor A U g i =
        (V : Matrix (Fin D) (Fin D) ℂ) * A i *
          (V : Matrix (Fin D) (Fin D) ℂ)ᴴ := by
  obtain ⟨X, hX⟩ := gaugeEquiv_twistedTensor_of_injective A hA U hSymm g
  have hBleft : IsLeftCanonical (twistedTensor A U g) :=
    isLeftCanonical_rotatePhysical A (U g)
      (by simpa only [Matrix.star_eq_conjTranspose] using
        Matrix.mem_unitaryGroup_iff.mp (hU g)) hleft
  have hIrr : ∀ B : MPSTensor d D, Kraus.IsInjective B → Kraus.IsIrreducibleFamily B :=
    fun B hB => Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM B
      (Kraus.injective_implies_irreducibleCP B hB)
  obtain ⟨V, _, hV⟩ :=
    exists_unitaryConj_of_gaugePhase_data_of_leftCanonical_irreducible
      X 1 one_ne_zero (by simpa using hX) hleft hBleft
      (hIrr A hA) (hIrr _ (isInjective_of_gaugeEquiv hA ⟨X, hX⟩))
  exact ⟨V, by simpa using hV⟩

/-- An injective left-canonical tensor with exact unitary on-site symmetry
admits a unitary virtual projective representation. Unitarity is derived
from canonical normalization rather than imposed on the virtual data.
Source: arXiv:1010.3732, Section II.F.1, and CPSV16, Corollary A.6. -/
theorem exists_unitary_virtual_rep_of_symmetric_injective_leftCanonical
    {G : Type*} [Group G] {d D : ℕ} [NeZero D]
    (A : MPSTensor d D) (hA : Kraus.IsInjective A)
    (hleft : IsLeftCanonical A)
    (U : G →* Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSymm : IsOnSiteSymmetric A U) :
    ∃ ω : ScalarCocycle G, ∃ ρ : ProjectiveRepresentation (D := D) ω,
      (∀ g, (ρ.X g : Matrix (Fin D) (Fin D) ℂ) ∈
        Matrix.unitaryGroup (Fin D) ℂ) ∧
      (∀ g i, twistedTensor A U g i =
        (ρ.X g⁻¹ : Matrix (Fin D) (Fin D) ℂ) * A i *
          (((ρ.X g⁻¹)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) := by
  choose V hV using exists_unitary_gauge_of_symmetric_injective_leftCanonical
    A hA hleft U hU hSymm
  let X : G → GL (Fin D) ℂ := fun g => Unitary.toUnits (V g)
  have hX : ∀ g i, twistedTensor A U g i =
      (X g : Matrix (Fin D) (Fin D) ℂ) * A i *
        (((X g)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := hV
  obtain ⟨ω, ρ, hρ⟩ := exists_virtual_rep_of_gauges A hA U X hX
  refine ⟨ω, ρ, ?_, ?_⟩
  · intro g
    rw [hρ]
    exact (V g⁻¹).property
  · intro g i
    simpa only [hρ, inv_inv] using hX g i

end MPSTensor
