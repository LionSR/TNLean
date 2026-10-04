/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.ExactMPSGappedPhase
import TNLean.MPS.Symmetry.PhysicalCharacterTwist

/-!
# Physical character changes preserve symmetric interaction paths

A character change multiplies the physical action on an N-site chain by
one scalar. It therefore preserves Hamiltonian commutation, without changing
the interaction or its spectral gap.

Source: Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.C.2,
lines 440–453, and Appendix B, lines 2614–2632.
-/

open scoped Matrix

namespace Matrix

/-- Scaling every factor scales its finite Kronecker power by the product
of the scalars. Source context: arXiv:1010.3732, Appendix B, lines 2614–2632. -/
theorem finKronecker_const_smul {d N : ℕ}
    (z : ℂ) (A : Matrix (Fin d) (Fin d) ℂ) :
    (finKronecker fun _ : Fin N => z • A) =
      z ^ N • (finKronecker fun _ : Fin N => A) := by
  ext σ τ
  simp [finKronecker_apply, Finset.prod_mul_distrib]

end Matrix

namespace MPSTensor

/-- A physical character change preserves the same symmetric interaction
path and the same uniform spectral gap. Source: arXiv:1010.3732,
Section II.C.2, lines 440–453, and Appendix B, lines 2614–2632. -/
def SymmetricGappedInteractionPath.physicalCharacterTwist
    {G : Type} [Group G] {d : ℕ}
    {U : G →* Matrix.unitaryGroup (Fin d) ℂ}
    {h₀ h₁ : MPOTensor.ChainOperator d 2}
    (P : SymmetricGappedInteractionPath U h₀ h₁)
    (χ : G →* ℂ) (hχ : ∀ g, ‖χ g‖ = 1) :
    SymmetricGappedInteractionPath (MPSTensor.physicalCharacterTwist χ hχ U) h₀ h₁ where
  interaction := P.interaction
  interaction_zero := P.interaction_zero
  interaction_one := P.interaction_one
  hermitian := P.hermitian
  norm_le_one := P.norm_le_one
  continuous := P.continuous
  gap := P.gap
  symmetric γ hγ g N hN := by
    simp only [MPSTensor.physicalCharacterTwist_apply, Matrix.finKronecker_const_smul]
    exact (P.symmetric γ hγ g N hN).smul_right (χ g ^ N)

/-- The exact MPS ground realization is preserved by changing the physical
character: the Hamiltonians and their ground lines are the same.
Source: arXiv:1010.3732, Section II.C.2, lines 440–453,
and Appendix B, lines 2614–2632. -/
def ExactMPSGroundPath.physicalCharacterTwist
    {G : Type} [Group G] {d : ℕ}
    {U : G →* Matrix.unitaryGroup (Fin d) ℂ}
    {h₀ h₁ : MPOTensor.ChainOperator d 2}
    {P : SymmetricGappedInteractionPath U h₀ h₁}
    (Q : ExactMPSGroundPath P) (χ : G →* ℂ) (hχ : ∀ g, ‖χ g‖ = 1) :
    ExactMPSGroundPath (P.physicalCharacterTwist χ hχ) where
  bondDimension := Q.bondDimension
  bondDimension_pos := Q.bondDimension_pos
  tensor := Q.tensor
  continuous := Q.continuous
  injective_representative := Q.injective_representative
  nonzero := Q.nonzero
  ground_line := Q.ground_line

end MPSTensor
