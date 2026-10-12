/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.DualRepresentationParentHamiltonian

/-!
# Star-coalgebra representation adjoint and parent-symmetry regressions

These signatures use only standard coalgebra data, a star-preserving physical
map, and a faithful convolution-dual representation. In particular, neither
normality nor an adjoint-closure conclusion is among the premises.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.hashCommand false

open scoped Matrix

namespace DualRepresentationAdjointBoundaryTest

variable {H : Type*} [AddCommGroup H] [Module ℂ H] [Coalgebra ℂ H]
  [StarAddMonoid H] [StarModule ℂ H]
variable {d D Dₐ L N : ℕ}
variable (hcomul : ∀ x : H,
    Coalgebra.comul (R := ℂ) (star x) = star (Coalgebra.comul (R := ℂ) x))
  (φ : H →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
  (hφ : ∀ x, φ (star x) = (φ x)ᴴ)
  (ψ : WithConv (H →ₗ[ℂ] ℂ) →ₐ[ℂ] Matrix (Fin D) (Fin D) ℂ)
  (hψ : Function.Injective ψ)

-- The convolution order is unchanged, even without cocommutativity.
example (f g : WithConv (H →ₗ[ℂ] ℂ)) :
    star (f * g) = star f * star g := Coalgebra.dualStar_mul hcomul f g

-- Unit compatibility is a conclusion, not an extra counit-star premise.
example : star (1 : WithConv (H →ₗ[ℂ] ℂ)) = 1 := Coalgebra.dualStar_one hcomul

-- The same boundary works at all lengths, including the empty chain.
example (X : Matrix (Fin D) (Fin D) ℂ) :
    ∃ Y : Matrix (Fin D) (Fin D) ℂ, ∀ n : ℕ,
      (MPOTensor.mpoWithBoundary (MPOTensor.ofDualRepresentation φ ψ) X n)ᴴ =
        MPOTensor.mpoWithBoundary (MPOTensor.ofDualRepresentation φ ψ) Y n :=
  MPOTensor.exists_adjointBoundary_of_dualRepresentation hcomul φ hφ ψ hψ X

example : MPOTensor.IsBoundaryAdjointClosed (MPOTensor.ofDualRepresentation φ ψ) :=
  MPOTensor.isBoundaryAdjointClosed_of_dualRepresentation hcomul φ hφ ψ hψ

-- The empty-chain identity gives the correct conjugated boundary trace.
example (X : Matrix (Fin D) (Fin D) ℂ) :
    ∃ Y : Matrix (Fin D) (Fin D) ℂ, Matrix.trace Y = star (Matrix.trace X) := by
  obtain ⟨Y, hY⟩ := MPOTensor.exists_boundary_trace_dualStar ψ hψ X
  refine ⟨Y, ?_⟩
  simpa only [Coalgebra.dualStar_one hcomul, map_one, Matrix.mul_one] using hY 1

-- Two letters are swapped physically without a spatial reversal.
example (i j k l : Fin d) :
    star (MPOTensor.dualCoefficient φ i j * MPOTensor.dualCoefficient φ k l) =
      MPOTensor.dualCoefficient φ j i * MPOTensor.dualCoefficient φ l k := by
  rw [Coalgebra.dualStar_mul hcomul,
    MPOTensor.star_dualCoefficient φ hφ, MPOTensor.star_dualCoefficient φ hφ]

example (A : MPSTensor d Dₐ)
    (h : MPOTensor.IsBoundaryCompatible (MPOTensor.ofDualRepresentation φ ψ) A)
    (hL : 0 < L) (X : Matrix (Fin D) (Fin D) ℂ) :
    Commute (MPSTensor.parentInteractionES A L)
      (Matrix.toEuclideanLin
        (MPOTensor.mpoWithBoundary (MPOTensor.ofDualRepresentation φ ψ) X L)) :=
  MPOTensor.IsBoundaryCompatible.parentInteractionES_commute_of_dualRepresentation
    hcomul φ hφ ψ hψ h hL X

-- Periodic wrapping retains the tensor-letter centralizer condition.
example (A : MPSTensor d Dₐ)
    (h : MPOTensor.IsBoundaryCompatible (MPOTensor.ofDualRepresentation φ ψ) A)
    (hL : 0 < L) (hLN : L ≤ N) (X : Matrix (Fin D) (Fin D) ℂ)
    (hX : X ∈ MPOTensor.commutingBoundaryAlgebra (MPOTensor.ofDualRepresentation φ ψ)) :
    Commute (MPSTensor.parentHamiltonianES A L N)
      (Matrix.toEuclideanLin
        (MPOTensor.mpoWithBoundary (MPOTensor.ofDualRepresentation φ ψ) X N)) :=
  MPOTensor.IsBoundaryCompatible.parentHamiltonianES_commute_of_dualRepresentation
    hcomul φ hφ ψ hψ h hL hLN hX

/--
info: 'Coalgebra.dualStar_mul' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Coalgebra.dualStar_mul

/--
info: 'Coalgebra.dualStar_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Coalgebra.dualStar_one

/--
info: 'MPOTensor.exists_adjointBoundary_of_dualRepresentation'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.exists_adjointBoundary_of_dualRepresentation

/--
info: 'MPOTensor.isBoundaryAdjointClosed_of_dualRepresentation'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.isBoundaryAdjointClosed_of_dualRepresentation

/--
info: 'MPOTensor.IsBoundaryCompatible.parentHamiltonianES_commute_of_dualRepresentation'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPOTensor.IsBoundaryCompatible.parentHamiltonianES_commute_of_dualRepresentation

end DualRepresentationAdjointBoundaryTest
