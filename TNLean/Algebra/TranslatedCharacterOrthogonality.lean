/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CharacterProjector
import TNLean.Algebra.RepresentationDeltaPositive

/-!
# Translated irreducible characters

The convolution of two translated irreducible characters vanishes when the
representations are inequivalent. For equivalent representations it is the
character of their relative translation, multiplied by the group order and
divided by the irreducible dimension. These are auxiliary finite-group
identities for the charge-detection argument of Schuch, Cirac, and
Pérez-García, arXiv:1001.3807, lines 2464–2486.
-/

open scoped BigOperators
open Module LinearMap
namespace Representation

variable {G V W : Type*} [Group G] [Fintype G]
variable [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
variable [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

open Classical in
/-- Translated character convolution follows from the actual Schur projector.
Source: SCP10, charge detection, lines 2464–2486; auxiliary group identity. -/
theorem sum_character_inv_mul_character_translate
    (σ : Representation ℂ G V) (τ : Representation ℂ G W)
    [σ.IsIrreducible] [τ.IsIrreducible] (a b : G) :
    ∑ g, σ.character (a * g)⁻¹ * τ.character (b * g) =
      if Nonempty (σ.Equiv τ) then
        ((Nat.card G : ℂ) / finrank ℂ V) * τ.character (b * a⁻¹) else 0 := by
  classical
  have hsum := congrArg
    (fun F : Module.End ℂ W => LinearMap.trace ℂ W (τ (b * a⁻¹) * F))
    (sum_character_inv_smul_eq σ τ)
  simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, mul_one,
    mul_zero, apply_ite, map_zero, smul_eq_mul] at hsum
  have htrace (g : G) :
      LinearMap.trace ℂ W (τ (b * a⁻¹) * τ g) =
        τ.character (b * a⁻¹ * g) := by
    rw [← map_mul]
    rfl
  simp only [htrace] at hsum
  calc
    _ = ∑ g, σ.character g⁻¹ * τ.character (b * a⁻¹ * g) := by
      refine Fintype.sum_equiv (Equiv.mulLeft a) _ _ fun g => ?_
      change σ.character (a * g)⁻¹ * τ.character (b * g) =
        σ.character (a * g)⁻¹ * τ.character (b * a⁻¹ * (a * g))
      congr 2
      group
    _ = _ := by
      by_cases h : Nonempty (σ.Equiv τ) <;>
        simpa only [h, ↓reduceIte, character] using hsum

/-- The character-inversion pairing vanishes for distinct irreducible characters.
Source: SCP10, charge detection, lines 2464–2486; auxiliary character identity. -/
theorem sum_character_inv_mul_character_translate_eq_zero
    (σ : Representation ℂ G V) (τ : Representation ℂ G W)
    [σ.IsIrreducible] [τ.IsIrreducible]
    (hne : σ.character ≠ τ.character) (a b : G) :
    ∑ g, σ.character (a * g)⁻¹ * τ.character (b * g) = 0 := by
  rw [sum_character_inv_mul_character_translate,
    ite_eq_right (fun h => hne ((nonempty_equiv_iff_character_eq σ τ).mp h))]

end Representation

namespace Representation
variable {G E F : Type*} [Group G] [Fintype G]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

open Classical in
/-- The actual Hilbert-space pairing of translated unitary characters.
Source: SCP10, charge detection, lines 2464–2486; auxiliary finite-group identity. -/
theorem sum_star_character_mul_character_translate
    (σ : Representation ℂ G E) (τ : Representation ℂ G F)
    [σ.IsIrreducible] [τ.IsIrreducible]
    (hσ : ∀ g, LinearMap.adjoint (σ g) = σ g⁻¹) (a b : G) :
    ∑ g, star (σ.character (a * g)) * τ.character (b * g) =
      if Nonempty (σ.Equiv τ) then
        ((Nat.card G : ℂ) / finrank ℂ E) * τ.character (b * a⁻¹) else 0 := by
  simpa only [character_inv_of_unitary σ hσ] using
    sum_character_inv_mul_character_translate σ τ a b

/-- Different irreducible characters have orthogonal translated charge vectors.
Source: SCP10, charge detection, lines 2464–2486. -/
theorem sum_star_character_mul_character_translate_eq_zero
    (σ : Representation ℂ G E) (τ : Representation ℂ G F)
    [σ.IsIrreducible] [τ.IsIrreducible]
    (hσ : ∀ g, LinearMap.adjoint (σ g) = σ g⁻¹)
    (hne : σ.character ≠ τ.character) (a b : G) :
    ∑ g, star (σ.character (a * g)) * τ.character (b * g) = 0 := by
  simpa only [character_inv_of_unitary σ hσ] using
    sum_character_inv_mul_character_translate_eq_zero σ τ hne a b

/-- Each translated irreducible charge vector has squared norm equal to the group order.
Source: SCP10, charge detection, lines 2464–2486; explicit normalization. -/
theorem sum_star_character_mul_character_self
    (σ : Representation ℂ G E) [σ.IsIrreducible]
    (hσ : ∀ g, LinearMap.adjoint (σ g) = σ g⁻¹) (a : G) :
    ∑ g, star (σ.character (a * g)) * σ.character (a * g) = (Nat.card G : ℂ) := by
  classical
  rw [sum_star_character_mul_character_translate σ σ hσ,
    ite_eq_left ⟨Representation.Equiv.refl σ⟩, mul_inv_cancel, char_one]
  exact div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (finrank_pos_of_isIrreducible σ).ne')

end Representation
