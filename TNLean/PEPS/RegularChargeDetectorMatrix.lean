/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularChargeSubspace
import TNLean.PEPS.RegularTorusSite
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Matrix form of the accessible charge detector

The orthogonal charge detector is represented in the actual group-pair basis.
It is a positive Hermitian projection and commutes with the matrix of every
independent endpoint translation. Its action on literal charge coefficients
retains the selected label and removes every inequivalent irreducible label.

Source: SCP10, arXiv:1001.3807, charge detection, lines 2470–2486.
These are auxiliary accessible-coordinate statements, before transport to the
original physical spins.
-/

noncomputable section
open scoped Matrix ComplexOrder
namespace TNLean.PEPS
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The charge detector in the actual group-pair basis.
Source: SCP10, charge detection, lines 2470–2486. -/
def regularChargeDetectorMatrix (χ : G → ℂ) : Matrix (G × G) (G × G) ℂ :=
  LinearMap.toMatrixAlgEquiv (EuclideanSpace.basisFun (G × G) ℂ).toBasis
    (regularChargeDetector χ).toLinearMap

/-- Independent endpoint translation in the actual group-pair basis.
Source: SCP10, the unknown translations in charge detection, lines 2470–2486. -/
def regularChargeTranslationMatrix (z w : G) : Matrix (G × G) (G × G) ℂ :=
  LinearMap.toMatrixAlgEquiv (EuclideanSpace.basisFun (G × G) ℂ).toBasis
    (regularChargeTranslation z w).toLinearEquiv.toLinearMap

/-- The literal endpoint-translation matrix is the product of the two regular permutations.
Source: SCP10, the unknown translations in charge detection, lines 2470–2486. -/
theorem regularChargeTranslationMatrix_eq_kronecker (z w : G) :
    regularChargeTranslationMatrix z w =
      (leftRegularMatrix G z).kronecker (leftRegularMatrix G w) := by
  ext ⟨r, s⟩ ⟨a, b⟩
  simp [regularChargeTranslationMatrix, LinearMap.toMatrixAlgEquiv_apply,
    EuclideanSpace.basisFun_toBasis, regularChargeTranslation,
    Equiv.prodCongr_apply, leftRegularMatrix_apply, ite_and]
  split_ifs <;> rfl

/-- The detector matrix is positive, Hermitian and idempotent.
Source: SCP10, charge detection, lines 2474–2486. -/
theorem regularChargeDetectorMatrix_properties (χ : G → ℂ) :
    (regularChargeDetectorMatrix χ).IsHermitian ∧
      (regularChargeDetectorMatrix χ).PosSemidef ∧
      regularChargeDetectorMatrix χ * regularChargeDetectorMatrix χ =
        regularChargeDetectorMatrix χ := by
  let b := EuclideanSpace.basisFun (G × G) ℂ
  have hp := regularChargeDetector_isSymmetricProjection χ
  have hi : regularChargeDetectorMatrix χ * regularChargeDetectorMatrix χ =
      regularChargeDetectorMatrix χ :=
    (hp.isIdempotentElem.map (LinearMap.toMatrixAlgEquiv b.toBasis)).eq
  have hh : (regularChargeDetectorMatrix χ).IsHermitian := by
    have h := congrArg (LinearMap.toMatrix b.toBasis b.toBasis) hp.isSymmetric.adjoint_eq
    rw [LinearMap.toMatrix_adjoint b b] at h
    exact h
  refine ⟨hh, ?_, hi⟩
  simpa only [hh.eq, hi] using
    Matrix.posSemidef_self_mul_conjTranspose (regularChargeDetectorMatrix χ)

/-- Applying the matrix gives the literal coordinates of the Hilbert-space detector.
Source: SCP10, charge detection, lines 2474–2486. -/
theorem regularChargeDetectorMatrix_mulVec (χ : G → ℂ)
    (v : EuclideanSpace ℂ (G × G)) :
    regularChargeDetectorMatrix χ *ᵥ (fun rs => v rs) =
      fun rs => regularChargeDetector χ v rs := by
  let b := (EuclideanSpace.basisFun (G × G) ℂ).toBasis
  exact LinearMap.toMatrix_mulVec_repr b b (regularChargeDetector χ).toLinearMap v

/-- The matrix detector commutes with every independent endpoint translation.
Source: SCP10, the unknown translations in charge detection, lines 2470–2486. -/
theorem regularChargeDetectorMatrix_commute_translation (χ : G → ℂ) (z w : G) :
    Commute (regularChargeTranslationMatrix z w) (regularChargeDetectorMatrix χ) := by
  have h : Commute (regularChargeTranslation z w).toLinearEquiv.toLinearMap
      (regularChargeDetector χ).toLinearMap := by
    apply LinearMap.ext
    intro v
    exact regularChargeDetector_commute_translation χ z w v
  exact h.map (LinearMap.toMatrixAlgEquiv
    (EuclideanSpace.basisFun (G × G) ℂ).toBasis)

/-- Every literal selected-charge coefficient vector has detector eigenvalue one.
Source: SCP10, charge detection, lines 2474–2486. -/
theorem regularChargeDetectorMatrix_chargeVector (χ : G → ℂ) (p x y : G) :
    regularChargeDetectorMatrix χ *ᵥ
        (fun rs => regularChargeMatrix χ p x y rs.1 rs.2) =
      fun rs => regularChargeMatrix χ p x y rs.1 rs.2 := by
  have h := regularChargeDetectorMatrix_mulVec χ (regularChargeVector χ p x y)
  rw [regularChargeDetector_vector] at h
  exact h

/-- The charge projector has invariant matrix entries under independent endpoint
translations. Auxiliary to SCP10, charge detection, lines 2464–2486. -/
theorem regularChargeDetectorMatrix_translate_entries (χ : G → ℂ) (x y r s a b : G) :
    regularChargeDetectorMatrix χ (x * r, y * s) (x * a, y * b) =
      regularChargeDetectorMatrix χ (r, s) (a, b) := by
  have h := congrFun (congrFun
    (regularChargeDetectorMatrix_commute_translation χ x y).eq (x * r, y * s)) (a, b)
  rw [regularChargeTranslationMatrix_eq_kronecker] at h
  dsimp only [Matrix.kronecker] at h
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker_apply,
    leftRegularMatrix_apply, mul_left_cancel_iff, ite_mul, mul_ite,
    one_mul, mul_one, zero_mul, mul_zero] at h
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.sum_ite_eq] at h
  exact h.symm

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- Every inequivalent irreducible charge coefficient vector has detector eigenvalue zero.
Source: SCP10, charge detection, lines 2474–2486. -/
theorem regularChargeDetectorMatrix_other_chargeVector
    (σ : Representation ℂ G E) (τ : Representation ℂ G F)
    [σ.IsIrreducible] [τ.IsIrreducible]
    (hσ : ∀ g, LinearMap.adjoint (σ g) = σ g⁻¹)
    (hne : σ.character ≠ τ.character) (p x y : G) :
    regularChargeDetectorMatrix σ.character *ᵥ
        (fun rs => regularChargeMatrix τ.character p x y rs.1 rs.2) = 0 := by
  have h := regularChargeDetectorMatrix_mulVec σ.character
    (regularChargeVector τ.character p x y)
  rw [regularChargeDetector_other_vector σ τ hσ hne] at h
  exact h

end TNLean.PEPS
