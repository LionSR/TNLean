/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.RepresentationDelta
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Dimension bounds from distinct irreducible characters

A semi-regular representation contains every irreducible representation of the
finite group. Consequently, any finite family of irreducibles with distinct
characters occupies at least the sum of their dimensions. The proof chooses
one atom of a Maschke decomposition for each character and compares dimensions.
Neither an inner product nor a unitarity assumption is required.

Source: SCP10, Definition 4.5, lines 1010–1013, and the smallest semi-regular
representation in Section 7, lines 2947–3019.
-/

open Module
namespace Representation
universe u v w z
variable {G : Type u} [Group G] [Finite G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- A semi-regular representation has dimension at least the sum of the dimensions
of any finite family of irreducible representations with distinct characters.
Source: SCP10, Definition 4.5 and Section 7, lines 1010–1013 and 2947–3019. -/
theorem sum_finrank_le_of_distinct_irreducibles_of_isSemiRegular
    (σ : Representation ℂ G V) (hσ : σ.IsSemiRegular)
    {I : Type w} [Fintype I] (W : I → Type z)
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    [∀ i, FiniteDimensional ℂ (W i)]
    (τ : ∀ i, Representation ℂ G (W i)) (hirr : ∀ i, (τ i).IsIrreducible)
    (hchar : Function.Injective (fun i => (τ i).character)) :
    ∑ i, finrank ℂ (W i) ≤ finrank ℂ V := by
  classical
  let _ := Fintype.ofFinite G
  obtain ⟨s, hsA, hs⟩ := exists_isInternal_isAtom σ
  have hocc : ∀ i, ∃ S ∈ s, S.toRepresentation.character = (τ i).character := by
    intro i
    have := hirr i
    obtain ⟨f, hf⟩ := exists_intertwiningMap_leftRegular_ne_zero (τ i)
    have hχ := character_mem_irreducibleCharacters_of_ne_zero
      (leftRegular ℂ G) (τ i) f hf
    rw [← irreducibleCharacters_eq_leftRegular_of_isSemiRegular σ hσ] at hχ
    exact exists_mem_character_eq_of_mem_irreducibleCharacters σ hsA hs hχ
  choose S hS hχ using hocc
  let e : I → s := fun i => ⟨S i, hS i⟩
  have he : Function.Injective e := by
    intro i j hij
    apply hchar
    change (τ i).character = (τ j).character
    rw [← hχ i, ← hχ j]
    exact congrArg (fun T : s => T.1.toRepresentation.character) hij
  have hdim : ∀ i, finrank ℂ (W i) = finrank ℂ (e i).1.toSubmodule := by
    intro i
    have := hirr i
    have := Subrepresentation.isIrreducible_toRepresentation_of_isAtom (hsA (S i) (hS i))
    obtain ⟨f⟩ := (nonempty_equiv_iff_character_eq (τ i) (S i).toRepresentation).mpr
      (hχ i).symm
    exact f.toLinearEquiv.finrank_eq
  have hsum : ∑ T : s, finrank ℂ T.1.toSubmodule = finrank ℂ V := by
    have h := character_eq_sum_of_isInternal σ hs 1
    simp only [char_one] at h
    exact_mod_cast h.symm
  rw [← hsum]
  exact Finset.sum_le_sum_of_injOn e he.injOn (Finset.subset_univ _)
    (fun i _ => (hdim i).le) (fun _ _ _ => Nat.zero_le _)
end Representation
