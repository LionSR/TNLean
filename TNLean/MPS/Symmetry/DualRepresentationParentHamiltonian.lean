/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.DualRepresentationAdjointBoundary
import TNLean.MPS.Symmetry.BoundaryParentHamiltonian

/-!
# Canonical parent symmetry from star-compatible dual representations

The star-compatible coalgebra representation supplies arbitrary-boundary
adjoint closure. Compatibility with an MPS therefore gives commutation of its
canonical local parent with every boundary operator, and commutation of its
periodic parent with boundaries in the tensor-letter centralizer.

The centralizer condition is retained for periodic windows that wrap around
the chain. No integral-averaging formula, reconstruction of a C*-weak Hopf
algebra, or realization of a given mixed tensor is asserted.

## References

* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, Section 5, lines 1236--1320.
* Molnár et al., arXiv:2204.05940v1, Section 4 and Section 5.5.
-/

open scoped Matrix

namespace MPOTensor

variable {H : Type*} [AddCommGroup H] [Module ℂ H] [Coalgebra ℂ H]
  [StarAddMonoid H] [StarModule ℂ H]
variable {d D Dₐ L N : ℕ}

/-- The canonical local interaction commutes with every boundary operator of
a compatible star-coalgebra dual representation. Its adjoint closure is
derived from the representation, not supplied as a premise. -/
theorem IsBoundaryCompatible.parentInteractionES_commute_of_dualRepresentation
    (hcomul : ∀ x : H,
      Coalgebra.comul (R := ℂ) (star x) = star (Coalgebra.comul (R := ℂ) x))
    (φ : H →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hφ : ∀ x, φ (star x) = (φ x)ᴴ)
    (ψ : WithConv (H →ₗ[ℂ] ℂ) →ₐ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hψ : Function.Injective ψ) {A : MPSTensor d Dₐ}
    (h : IsBoundaryCompatible (ofDualRepresentation φ ψ) A)
    (hL : 0 < L) (X : Matrix (Fin D) (Fin D) ℂ) :
    Commute (MPSTensor.parentInteractionES A L)
      (Matrix.toEuclideanLin (mpoWithBoundary (ofDualRepresentation φ ψ) X L)) := by
  apply h.parentInteractionES_commute_mpoWithBoundary hL ?_ X
  intro Y
  obtain ⟨Z, hZ⟩ := exists_adjointBoundary_of_dualRepresentation hcomul φ hφ ψ hψ Y
  exact ⟨Z, hZ L⟩

/-- The periodic canonical parent commutes with every represented boundary
that commutes with the tensor letters. This includes wrapping interaction
windows and retains their necessary centralizer condition. -/
theorem IsBoundaryCompatible.parentHamiltonianES_commute_of_dualRepresentation
    (hcomul : ∀ x : H,
      Coalgebra.comul (R := ℂ) (star x) = star (Coalgebra.comul (R := ℂ) x))
    (φ : H →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hφ : ∀ x, φ (star x) = (φ x)ᴴ)
    (ψ : WithConv (H →ₗ[ℂ] ℂ) →ₐ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hψ : Function.Injective ψ) {A : MPSTensor d Dₐ}
    (h : IsBoundaryCompatible (ofDualRepresentation φ ψ) A)
    (hL : 0 < L) (hLN : L ≤ N) {X : Matrix (Fin D) (Fin D) ℂ}
    (hX : X ∈ commutingBoundaryAlgebra (ofDualRepresentation φ ψ)) :
    Commute (MPSTensor.parentHamiltonianES A L N)
      (Matrix.toEuclideanLin (mpoWithBoundary (ofDualRepresentation φ ψ) X N)) := by
  apply h.parentHamiltonianES_commute_mpoWithBoundary hL hLN ?_ hX
  intro Y
  obtain ⟨Z, hZ⟩ := exists_adjointBoundary_of_dualRepresentation hcomul φ hφ ψ hψ Y
  exact ⟨Z, hZ L⟩

end MPOTensor
