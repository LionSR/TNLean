/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.MixedEndpointBoundaryFactors
import TNLean.MPS.Core.SquarePhysicalCoordinates

/-!
# Physical coordinates for the two endpoint boundary letters

The exact rectangular boundary factors of the zero-parameter mixed chain
contain `A₀` in their first outer sector and raw matrix units in their
second outer sector. On the first sector, the inverse physical coordinate
matrix of the injective endpoint replaces `A₀` by the same raw units.
This is a change at the boundary physical site only. In particular, it
does not replace the arbitrary injective tensor throughout the bulk.

Source: arXiv:2203.12563, Section 5, lines 1690–1692. These local algebraic
identities do not themselves assert a global Hamiltonian comparison or a
uniform spectral gap.
-/

open scoped Matrix BigOperators

namespace MPSTensor
namespace MPOSymmetry

variable {D₀ D₁ : ℕ}

/-- The invertible square physical coordinate change turns the diagonal
first rectangular boundary letters into raw units. The other outer sector
already consists of raw units and requires no change.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem inv_squarePhysicalCoordinates_firstBoundaryLetter
    (A₀ : MPSTensor (D₀ * D₀) D₀) (hA₀ : Kraus.IsInjective A₀)
    (p : Fin (D₀ * D₀)) :
    (∑ q : Fin (D₀ * D₀), (squarePhysicalCoordinates A₀)⁻¹ p q •
      mixedEndpointFirstBoundaryLetter A₀
        (.inl (finProdFinEquiv.symm q).1) (.inl (finProdFinEquiv.symm q).2)) =
      (Matrix.single (.inl (finProdFinEquiv.symm p).1)
        (finProdFinEquiv.symm p).2 1 : Matrix (Fin D₀ ⊕ Fin D₁) (Fin D₀) ℂ) := by
  have h := congrArg (fun A : MPSTensor (D₀ * D₀) D₀ => A p)
    (rotatePhysical_inv_squarePhysicalCoordinates A₀ hA₀)
  ext i j
  cases i with
  | inl i =>
      simpa only [rotatePhysical, mixedEndpointFirstBoundaryLetter, matrixUnitPhysicalTensor,
        Matrix.sum_apply, Matrix.smul_apply, Matrix.fromRows_apply_inl, Prod.mk.eta,
        Equiv.apply_symm_apply, Matrix.single_apply, Sum.inl.injEq] using
        congrArg (fun M : Matrix (Fin D₀) (Fin D₀) ℂ => M i j) h
  | inr i =>
      simp only [mixedEndpointFirstBoundaryLetter, Matrix.sum_apply, Matrix.smul_apply,
        Matrix.fromRows_apply_inr, Matrix.zero_apply, smul_zero, Finset.sum_const_zero,
        Matrix.single_apply, Sum.inl_ne_inr, false_and, ite_false]

/-- The same invertible physical coordinate change turns the diagonal
last rectangular boundary letters into raw units. The exterior column
remains a spectator throughout the change.
Source: arXiv:2203.12563, Section 5, lines 1690–1692. -/
theorem inv_squarePhysicalCoordinates_lastBoundaryLetter
    (A₀ : MPSTensor (D₀ * D₀) D₀) (hA₀ : Kraus.IsInjective A₀)
    (p : Fin (D₀ * D₀)) :
    (∑ q : Fin (D₀ * D₀), (squarePhysicalCoordinates A₀)⁻¹ p q •
      mixedEndpointLastBoundaryLetter A₀
        (.inl (finProdFinEquiv.symm q).1) (.inl (finProdFinEquiv.symm q).2)) =
      (Matrix.single (finProdFinEquiv.symm p).1
        (.inl (finProdFinEquiv.symm p).2) 1 : Matrix (Fin D₀) (Fin D₀ ⊕ Fin D₁) ℂ) := by
  have h := congrArg (fun A : MPSTensor (D₀ * D₀) D₀ => A p)
    (rotatePhysical_inv_squarePhysicalCoordinates A₀ hA₀)
  ext i j
  cases j with
  | inl j =>
      simpa only [rotatePhysical, mixedEndpointLastBoundaryLetter, matrixUnitPhysicalTensor,
        Matrix.sum_apply, Matrix.smul_apply, Matrix.fromCols_apply_inl, Prod.mk.eta,
        Equiv.apply_symm_apply, Matrix.single_apply, Sum.inl.injEq] using
        congrArg (fun M : Matrix (Fin D₀) (Fin D₀) ℂ => M i j) h
  | inr j =>
      simp only [mixedEndpointLastBoundaryLetter, Matrix.sum_apply, Matrix.smul_apply,
        Matrix.fromCols_apply_inr, Matrix.zero_apply, smul_zero, Finset.sum_const_zero,
        Matrix.single_apply, Sum.inl_ne_inr, and_false, ite_false]

end MPOSymmetry
end MPSTensor
