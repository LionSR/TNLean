/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularChargeCoordinates
import TNLean.PEPS.GraphInsertedBondState

/-!
# Literal character-weighted bond contraction

A diagonal character insertion gives the actual accessible charge matrix after
independent translations at its two endpoints. Substitution into the original
closed graph contraction yields one such matrix per bond, with the same vertex
average as before.

Source: SCP10, arXiv:1001.3807, charge definition and detection,
lines 2449–2486. These are auxiliary regular-coordinate identities; no physical
measurement or general semiregular isometry for character insertions is asserted.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- Independent endpoint translations turn the diagonal character insertion into
its literal two-site charge matrix. Source: SCP10, lines 2449–2486. -/
theorem regularChargeMatrix_eq_leftRegular_diagonal (χ : G → ℂ) (p x y : G) :
    regularChargeMatrix χ p x y =
      leftRegularMatrix G x * Matrix.diagonal (fun g => χ (p * g)) *
        leftRegularMatrix G y⁻¹ := by
  ext r s
  have hrow (k : G) : r = x * k ↔ k = x⁻¹ * r := by
    constructor
    · intro h
      rw [h]
      group
    · rintro rfl
      group
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, leftRegularMatrix_apply, hrow]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [regularChargeMatrix, eq_inv_mul_iff_mul_eq, mul_ite, mul_one, mul_zero]
  split_ifs <;> rfl

/-- The literal regular conjugation changes the internal parameter by k⁻¹.
Source: SCP10, charge–flux braiding, lines 2569–2581. -/
theorem leftRegular_diagonal_character_conjugate (χ : G → ℂ) (p k : G) :
    leftRegularMatrix G k * Matrix.diagonal (fun g => χ (p * g)) *
        leftRegularMatrix G k⁻¹ =
      Matrix.diagonal (fun g => χ (p * k⁻¹ * g)) := by
  rw [← regularChargeMatrix_eq_leftRegular_diagonal]
  ext r s
  simp [regularChargeMatrix, Matrix.diagonal_apply, mul_assoc]


variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

/-- The actual closed averaging contraction with diagonal charge insertions is
an average of products of the translated charge matrices.
Source: SCP10, charge definition and detection, lines 2449–2486;
finite-graph coefficient form. -/
theorem graphInsertedBondNetwork_averagingSite_charge
    (χ : Edge Γ → G → ℂ) (p : Edge Γ → G) (β : Edge Γ → G × G) :
    graphBondRegrouping
      (graphInsertedBondNetwork (fun e => Matrix.diagonal (fun g => χ e (p e * g)))
        (graphAveragingSite (leftRegularMatrix G))) β =
      ∑ q : V → G, (Fintype.card G : ℂ)⁻¹ ^ Fintype.card V *
        ∏ e : Edge Γ, regularChargeMatrix (χ e) (p e) (q e.1.2) (q e.1.1)
          (β e).1 (β e).2 := by
  have hs : graphDressedAveragingSite (Γ := Γ) (leftRegularMatrix G) 1 =
      graphAveragingSite (leftRegularMatrix G) :=
    funext fun v => funext fun η => funext fun σ =>
      graphDress_one v (fun ξ => graphAveragingSite (leftRegularMatrix G) v ξ σ) η
  rw [← hs, graphInsertedBondNetwork_dressedAveragingSite]
  simp only [Matrix.mul_one]
  simp_rw [← regularChargeMatrix_eq_leftRegular_diagonal]

end TNLean.PEPS
