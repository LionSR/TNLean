/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Operator.Boundary.WeakHopfRepresentation
import TNLean.MPS.Symmetry.MPOSymmetry.MixedPath.MPO.ArbitraryPhysicalMixedMPO

/-!
# An obstruction to a unital weak-Hopf realization on the enlarged physical space

The common mixed MPO is extended by zero on the two unused physical summands.
It cannot be the tensor of `WeakHopfRepresentation` when either summand is
nonempty: faithfulness of the dual representation and unitality of the physical
representation force every diagonal physical letter to be nonzero.

This obstructs a literal enlarged-space realization, independently
of fusion, action, injectivity, or adjoint closure. Averaging must instead be
performed on the active physical space, followed by ambient completion, or use
a different representation notion allowing a nonunital physical action.
Source context: arXiv:2203.12563v3, Section 5 and Appendix B. See
`docs/paper-gaps/glm23_mixed_weak_hopf_realization.tex`.
-/

open scoped Matrix
open MPOTensor.PhysicalSectorFactorization

namespace MPOTensor.WeakHopfRepresentation

variable {H : Type*} [Ring H] [Algebra ℂ H] [Coalgebra ℂ H]
  [StarRing H] [StarModule ℂ H] {d D : ℕ}

/-- Faithfulness of the convolution-dual action and physical unitality forbid
zero diagonal physical letters. No integral identity is needed. -/
theorem tensor_diag_ne_zero (W : WeakHopfRepresentation H d D) (i : Fin d) :
    W.tensor i i ≠ 0 := by
  intro hi
  have hc : dualCoefficient W.phys.toLinearMap i i = 0 :=
    W.virt_injective (hi.trans (map_zero W.virt).symm)
  have he := congrArg (fun f => f.ofConv (1 : H)) hc
  simp [dualCoefficient] at he

end MPOTensor.WeakHopfRepresentation

namespace MPSTensor.MPOSymmetry

variable {d₀ d₁ D₀ D₁ χ₀ χ₁ m : ℕ}

/-- A row in the last unused physical summand is zero in the common inclusion. -/
theorem commonFixedPointInclusion_last_row (k : Fin d₁) (j : Fin m) :
    commonFixedPointInclusion m d₀ d₁ (Fin.natAdd (m + d₀) k) j = 0 := by
  simp [commonFixedPointInclusion, physicalSumInclusion, Matrix.mul_apply]

/-- A row in the middle unused physical summand is zero in the common inclusion. -/
theorem commonFixedPointInclusion_middle_row (k : Fin d₀) (j : Fin m) :
    commonFixedPointInclusion m d₀ d₁ (Fin.castAdd d₁ (Fin.natAdd m k)) j = 0 := by
  simp [commonFixedPointInclusion, physicalSumInclusion, Matrix.mul_apply,
    Matrix.one_apply]

/-- Zero rows of an inclusion give zero physical letters after extension. -/
theorem changePhysicalBasis_eq_zero_of_row {a b χ : ℕ}
    (J : Matrix (Fin b) (Fin a) ℂ) (T : MPOTensor a χ)
    {i : Fin b} (hi : ∀ j, J i j = 0) (j : Fin b) :
    changePhysicalBasis J T i j = 0 := by
  ext β α
  simp [changePhysicalBasis, Matrix.mul_apply, hi]

/-- The common enlarged MPO has no faithful convolution-dual realization with
unital physical representation if either unused summand is nonempty. -/
theorem arbitraryPhysicalMixedMPO_ne_weakHopfTensor
    {H : Type*} [Ring H] [Algebra ℂ H] [Coalgebra ℂ H]
    [StarRing H] [StarModule ℂ H]
    (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁)
    (T₀ : MPOTensor d₀ χ₀) (T₁ : MPOTensor d₁ χ₁)
    (V₀ : Fin m → Matrix (Fin D₀) (Fin (χ₀ * D₀)) ℂ)
    (V₁ : Fin m → Matrix (Fin D₁) (Fin (χ₁ * D₁)) ℂ)
    (W₀ : Fin m → Matrix (Fin (χ₀ * D₀)) (Fin D₀) ℂ)
    (W₁ : Fin m → Matrix (Fin (χ₁ * D₁)) (Fin D₁) ℂ)
    (W : MPOTensor.WeakHopfRepresentation H
      ((((D₀ + D₁) * (D₀ + D₁)) + d₀) + d₁) (χ₀ + χ₁))
    (h : 0 < d₀ ∨ 0 < d₁) :
    arbitraryPhysicalMixedMPO A₀ A₁ T₀ T₁ V₀ V₁ W₀ W₁ ≠ W.tensor := by
  intro he
  obtain h | h := h
  · let i := Fin.castAdd d₁ (Fin.natAdd ((D₀ + D₁) * (D₀ + D₁)) ⟨0, h⟩)
    apply W.tensor_diag_ne_zero i
    rw [← he, arbitraryPhysicalMixedMPO]
    exact changePhysicalBasis_eq_zero_of_row _ _
      (fun j => commonFixedPointInclusion_middle_row ⟨0, h⟩ j) i
  · let i := Fin.natAdd (((D₀ + D₁) * (D₀ + D₁)) + d₀) ⟨0, h⟩
    apply W.tensor_diag_ne_zero i
    rw [← he, arbitraryPhysicalMixedMPO]
    exact changePhysicalBasis_eq_zero_of_row _ _
      (fun j => commonFixedPointInclusion_last_row ⟨0, h⟩ j) i

end MPSTensor.MPOSymmetry
