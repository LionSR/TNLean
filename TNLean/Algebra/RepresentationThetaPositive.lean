/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.RepresentationTheta
import TNLean.Algebra.RepresentationDeltaPositive

/-!
# Positive fourth-root representation weights

The operator \(\Theta\) has fourth power \(|G|\Delta\), so it is invertible
for every finite-dimensional complex representation of a finite group. When the
representation is unitary, its character projectors are orthogonal and its
fourth-root coefficients are nonnegative. It follows that \(\Theta\) is positive,
and invertibility strengthens this to positive definiteness.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, §7,
`Papers/1001.3807/paper_v3.tex`, lines 3000–3006, together with the normalization
of \(\Delta\) in Lemma 4.4, lines 970–976. The exact identity used here retains
the group-order factor. No contraction or parent-Hamiltonian assertion is made.
-/

open Module LinearMap
open scoped ComplexOrder

namespace Representation
variable {G V : Type*} [Group G] [Fintype G]
variable [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
/-- The fourth-root weight is invertible, with no unitarity assumption.
Source: SCP10, §7, lines 3000–3006, and Lemma 4.4, lines 970–976. -/
theorem isUnit_thetaOperator (ρ : Representation ℂ G V) : IsUnit (thetaOperator ρ) := by
  apply (isUnit_pow_iff (by norm_num : (4 : ℕ) ≠ 0)).mp
  rw [thetaOperator_pow_four, Algebra.smul_def]
  exact ((isUnit_iff_ne_zero.mpr (natCard_ne_zero_complex (G := G))).map
    (algebraMap ℂ (Module.End ℂ V))).mul (isUnit_deltaOperator ρ)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]
/-- The fourth-root weight of a unitary representation is positive.
Source: the positive coefficients in SCP10, §7, lines 3000–3006. -/
theorem isPositive_thetaOperator_of_unitary (ρ : Representation ℂ G E)
    (hρ : ∀ g, LinearMap.adjoint (ρ g) = ρ g⁻¹) :
    (thetaOperator ρ).IsPositive := by
  classical
  rw [thetaOperator]
  apply isPositive_sum_smul_charProjector_of_nonneg ρ _ hρ
  intro χ hχ
  positivity

/-- In every orthonormal basis, the fourth-root weight is positive definite.
Source: the positive occurring block weights in SCP10, §7, lines 3000–3006. -/
theorem posDef_toMatrix_thetaOperator_of_unitary (ρ : Representation ℂ G E)
    (hρ : ∀ g, LinearMap.adjoint (ρ g) = ρ g⁻¹)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℂ E) :
    (LinearMap.toMatrix b.toBasis b.toBasis (thetaOperator ρ)).PosDef := by
  have hp := (LinearMap.posSemidef_toMatrix_iff b).mpr
    (isPositive_thetaOperator_of_unitary ρ hρ)
  apply hp.posDef_iff_isUnit.mpr
  exact (isUnit_thetaOperator ρ).map (LinearMap.toMatrixAlgEquiv b.toBasis).toMonoidHom
end Representation
