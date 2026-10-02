/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CharacterProjector

/-!
# Weighted character projectors

A sum of character projectors acts on each irreducible summand by the weight of
its character. Such an operator commutes with the group representation.
These formulas give the scalar calculus for the source's isotypic decomposition,
including the weighted trace operator and its inverse.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Lemma 4.4,
`Papers/1001.3807/paper_v3.tex`, lines 970–1005.
-/

open Module LinearMap
open scoped BigOperators
namespace Representation

variable {G V : Type*} [Group G] [Fintype G]
variable [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
/-- An isotypic sum acts on an irreducible summand by its recorded weight.
Source: SCP10, the character-projector decomposition in Lemma 4.4, lines 983–1005. -/
theorem sum_smul_charProjector_apply_of_mem (ρ : Representation ℂ G V) (f : (G → ℂ) → ℂ)
    (S : Subrepresentation ρ) [S.toRepresentation.IsIrreducible] {v : V} (hv : v ∈ S) :
    (∑ χ ∈ irreducibleCharacterFinset ρ, f χ • charProjector ρ χ) v =
      f S.toRepresentation.character • v := by
  classical
  rw [LinearMap.sum_apply]
  have hχ : ∀ χ ∈ irreducibleCharacterFinset ρ,
      (f χ • charProjector ρ χ) v =
        if S.toRepresentation.character = χ then f χ • v else 0 := by
    intro χ hχ
    obtain ⟨S', hS', rfl⟩ := (mem_irreducibleCharacterFinset ρ).mp hχ
    simp only [LinearMap.smul_apply, charProjector_apply_of_mem ρ S'.toRepresentation S hv,
      smul_ite, smul_zero]
  rw [Finset.sum_congr rfl hχ, Finset.sum_ite_eq,
    ite_eq_left ((mem_irreducibleCharacterFinset ρ).mpr ⟨S, inferInstance, rfl⟩)]

/-- Isotypic scalar operators commute with every group action.
Source: SCP10, the block decomposition of Lemma 4.4, lines 970–976 and 983–1005. -/
theorem sum_smul_charProjector_commute (ρ : Representation ℂ G V)
    (f : (G → ℂ) → ℂ) (g : G) :
    Commute (∑ χ ∈ irreducibleCharacterFinset ρ, f χ • charProjector ρ χ) (ρ g) := by
  classical
  change _ * ρ g = ρ g * _
  apply linearMap_ext_on_irreducible ρ
  intro S hS v hv
  let := hS
  rw [Module.End.mul_apply, Module.End.mul_apply,
    sum_smul_charProjector_apply_of_mem ρ f S (S.apply_mem_toSubmodule g hv),
    sum_smul_charProjector_apply_of_mem ρ f S hv, map_smul]
/-- The character projector for an irreducible representation is idempotent.
Source: the isotypic block decomposition in SCP10, Lemma 4.4, lines 970–976. -/
theorem charProjector_mul_self (ρ : Representation ℂ G V)
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ G W) [σ.IsIrreducible] :
    charProjector ρ σ.character * charProjector ρ σ.character =
      charProjector ρ σ.character := by
  classical
  apply linearMap_ext_on_irreducible ρ
  intro S hS v hv
  let := hS
  rw [Module.End.mul_apply, charProjector_apply_of_mem ρ σ S hv]
  split_ifs with h
  · rw [charProjector_apply_of_mem ρ σ S hv, ite_eq_left h]
  · exact map_zero _

end Representation

