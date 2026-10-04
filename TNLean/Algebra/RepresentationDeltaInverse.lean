/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.RepresentationDelta

/-!
# The inverse of the weighted trace operator

The operator \(\Delta\) acts by \(d_i/(m_i|G|)\) on each occurring irreducible
summand. All these coefficients are nonzero, so its inverse is the character-projector
sum with reciprocal weights \(|G|m_i/d_i\). Both operators commute with the group action.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Lemma 4.4,
equation `eq:noninj:deltadef`, `Papers/1001.3807/paper_v3.tex`, lines 970–976.
The argument applies to every finite-dimensional complex representation of a finite
group, without semi-regularity or unitarity. It establishes invertibility and the
explicit reciprocal weights; it does not assert positivity for an arbitrary inner product.
-/

open Module LinearMap
open scoped BigOperators

namespace Representation

variable {G V : Type*} [Group G] [Fintype G]
variable [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
/-- The reciprocal isotypic weights of the source's trace-dual operator.
Source: SCP10, Lemma 4.4, equation `eq:noninj:deltadef`, lines 970–976. -/
noncomputable def deltaOperatorInverse (ρ : Representation ℂ G V) : Module.End ℂ V :=
  ∑ χ ∈ irreducibleCharacterFinset ρ,
    (characterMultiplicity ρ χ * Nat.card G / χ 1) • charProjector ρ χ

/-- On an irreducible summand, the inverse weight is \(|G|m_i/d_i\).
Source: reciprocal of the block coefficient in SCP10, Lemma 4.4, lines 970–976. -/
theorem deltaOperatorInverse_apply_of_mem (ρ : Representation ℂ G V)
    (S : Subrepresentation ρ) [S.toRepresentation.IsIrreducible] {v : V} (hv : v ∈ S) :
    deltaOperatorInverse ρ v =
      (characterMultiplicity ρ S.toRepresentation.character * Nat.card G /
        S.toRepresentation.character 1) • v :=
  sum_smul_charProjector_apply_of_mem ρ _ S hv

/-- The reciprocal weighted operator is a left inverse of the trace-dual operator.
Source: SCP10, Lemma 4.4, equation `eq:noninj:deltadef`, lines 970–976. -/
theorem deltaOperatorInverse_mul (ρ : Representation ℂ G V) :
    deltaOperatorInverse ρ * deltaOperator ρ = 1 := by
  classical
  apply linearMap_ext_on_irreducible ρ
  intro S hS v hv
  let := hS
  rw [Module.End.mul_apply, deltaOperator_apply_of_mem ρ S hv, map_smul,
    deltaOperatorInverse_apply_of_mem ρ S hv, smul_smul, Module.End.one_apply]
  have hd : S.toRepresentation.character 1 ≠ 0 := by
    rw [char_one, Nat.cast_ne_zero]
    exact (finrank_pos_of_isIrreducible S.toRepresentation).ne'
  have hm := characterMultiplicity_ne_zero ρ
    (show S.toRepresentation.character ∈ irreducibleCharacters ρ from
      ⟨S, inferInstance, rfl⟩)
  have hG := natCard_ne_zero_complex (G := G)
  rw [div_mul_div_comm,
    mul_comm (characterMultiplicity ρ S.toRepresentation.character * (Nat.card G : ℂ))
      (S.toRepresentation.character 1), div_self (mul_ne_zero hd (mul_ne_zero hm hG)), one_smul]

/-- The reciprocal weighted operator is also a right inverse.
Source: SCP10, Lemma 4.4, equation `eq:noninj:deltadef`, lines 970–976. -/
theorem deltaOperator_mul_inverse (ρ : Representation ℂ G V) :
    deltaOperator ρ * deltaOperatorInverse ρ = 1 :=
  mul_eq_one_comm.mp (deltaOperatorInverse_mul ρ)

/-- The trace-dual operator is invertible on the whole representation space.
Source: SCP10, Lemma 4.4, equation `eq:noninj:deltadef`, lines 970–976. -/
theorem isUnit_deltaOperator (ρ : Representation ℂ G V) : IsUnit (deltaOperator ρ) :=
  ⟨⟨deltaOperator ρ, deltaOperatorInverse ρ,
    deltaOperator_mul_inverse ρ, deltaOperatorInverse_mul ρ⟩, rfl⟩

/-- The inverse trace-dual operator commutes with the group action.
Source: SCP10, the simultaneous block decomposition of Lemma 4.4, lines 970–976. -/
theorem deltaOperatorInverse_commute (ρ : Representation ℂ G V) (g : G) :
    Commute (deltaOperatorInverse ρ) (ρ g) :=
  sum_smul_charProjector_commute ρ _ g

/-- The trace-dual operator commutes with the group action.
Source: SCP10, the simultaneous block decomposition of Lemma 4.4, lines 970–976. -/
theorem deltaOperator_commute (ρ : Representation ℂ G V) (g : G) :
    Commute (deltaOperator ρ) (ρ g) := by
  change deltaOperator ρ * ρ g = ρ g * deltaOperator ρ
  rw [deltaOperator, smul_mul_assoc, mul_smul_comm,
    (sum_smul_charProjector_commute ρ (fun χ => χ 1 / characterMultiplicity ρ χ) g).eq]
end Representation
