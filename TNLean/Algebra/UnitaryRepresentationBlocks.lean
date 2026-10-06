/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.UnitaryRepresentationAlgebra
import TNLean.Algebra.RepresentationDelta
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Character multiplicities in unitary matrix blocks

The adapted orthonormal basis supplied by the generated star algebra gives an actual
irreducible decomposition of the group representation. The trace of the character
projector of a row is its dimension times the number of multiplicity rows; comparison
with the character trace formula identifies that number with the character multiplicity.
Source: SCP10, Section 4.1 and Lemma 4.4.
-/

open scoped Matrix InnerProductSpace
open Module
namespace Representation
variable {G n : Type*} [Group G] [Fintype n] [DecidableEq n]

private theorem equiv_of_same_basis_action
    {V W ι : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [Fintype ι] (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (b : Basis ι ℂ V) (c : Basis ι ℂ W)
    (hact : ∀ g, ∃ B : Matrix ι ι ℂ,
      (∀ j, ρ g (b j) = ∑ j', B j' j • b j') ∧
      (∀ j, σ g (c j) = ∑ j', B j' j • c j')) : Nonempty (ρ.Equiv σ) := by
  classical
  let e := b.equivFun.trans c.equivFun.symm
  refine ⟨Equiv.mk e fun g => b.ext fun j => ?_⟩
  obtain ⟨B, hb, hc⟩ := hact g
  change e (ρ g (b j)) = σ g (e (b j))
  have he : ∀ j, e (b j) = c j := by
    intro j
    apply c.equivFun.injective
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
      Basis.equivFun_apply, Basis.repr_self]
  rw [hb, he, hc, map_sum]
  simp only [map_smul, he]

private theorem multiplicity_of_unitary_rows [Fintype G]
    (U : G →* Matrix n n ℂ) (K : ℕ) (d m : Fin K → ℕ)
    (b : OrthonormalBasis ((k : Fin K) × (Fin (m k) × Fin (d k))) ℂ
      (EuclideanSpace ℂ n))
    (S : ∀ k, Fin (m k) → Subrepresentation (euclideanMatrixRepresentation U))
    (hd : ∀ k, 0 < d k)
    (hspan : ∀ k i, (S k i).toSubmodule =
      Submodule.span ℂ (Set.range fun j => b ⟨k, (i, j)⟩))
    (hirr : ∀ k i, (S k i).toRepresentation.IsIrreducible)
    (hcross : ∀ k k', k ≠ k' → ∀ i i',
      (S k i).toRepresentation.character ≠ (S k' i').toRepresentation.character)
    (hact : ∀ g, ∃ B : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ,
      ∀ k i j, euclideanMatrixRepresentation U g (b ⟨k, (i, j)⟩) =
        ∑ j', B k j' j • b ⟨k, (i, j')⟩) :
    ∀ k i, characterMultiplicity (euclideanMatrixRepresentation U)
      (S k i).toRepresentation.character = (m k : ℂ) := by
  classical
  have hlin : ∀ k i, LinearIndependent ℂ (fun j => b ⟨k, (i, j)⟩) :=
    fun k i => b.orthonormal.linearIndependent.comp (fun j => ⟨k, (i, j)⟩)
      (by intro j j' h; simpa using h)
  let rb : ∀ k i, Basis (Fin (d k)) ℂ (S k i).toSubmodule := fun k i =>
    (Basis.span (hlin k i)).map (LinearEquiv.ofEq _ _ (hspan k i).symm)
  have hrb : ∀ k i j, (rb k i j : EuclideanSpace ℂ n) = b ⟨k, (i, j)⟩ := by
    intro k i j
    dsimp only [rb]
    rw [Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.coe_span_apply]
  have hdim : ∀ k i, Module.finrank ℂ (S k i).toSubmodule = d k := by
    intro k i
    simpa using Module.finrank_eq_card_basis (rb k i)
  have hrowact : ∀ g, ∃ B : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ,
      ∀ k i j, (S k i).toRepresentation g (rb k i j) =
        ∑ j', B k j' j • rb k i j' := by
    intro g
    obtain ⟨B, hB⟩ := hact g
    refine ⟨B, fun k i j => Subtype.ext ?_⟩
    change euclideanMatrixRepresentation U g (rb k i j : EuclideanSpace ℂ n) =
      (∑ j', B k j' j • rb k i j' : (S k i).toSubmodule)
    simpa only [Submodule.coe_sum, Submodule.coe_smul, hrb] using hB k i j
  have hsame : ∀ k i i', (S k i).toRepresentation.character =
      (S k i').toRepresentation.character := by
    intro k i i'
    obtain ⟨e⟩ := equiv_of_same_basis_action (S k i).toRepresentation
      (S k i').toRepresentation (rb k i) (rb k i') fun g => by
        obtain ⟨B, hB⟩ := hrowact g
        exact ⟨B k, hB k i, hB k i'⟩
    exact char_iso e
  intro k i
  have := hirr k i
  have htrace := trace_comp_charProjector (euclideanMatrixRepresentation U)
    (S k i).toRepresentation (1 : G)
  simp only [map_one, Module.End.one_eq_id, LinearMap.id_comp, char_one, hdim] at htrace
  have htrace' : LinearMap.trace ℂ (EuclideanSpace ℂ n)
      (charProjector (euclideanMatrixRepresentation U) (S k i).toRepresentation.character) =
      (m k : ℂ) * (d k : ℂ) := by
    rw [LinearMap.trace_eq_sum_inner _ b, Fintype.sum_sigma]
    have hinner : ∀ k' i' j',
        ⟪b ⟨k', (i', j')⟩, charProjector (euclideanMatrixRepresentation U)
          (S k i).toRepresentation.character (b ⟨k', (i', j')⟩)⟫_ℂ =
          if k' = k then 1 else 0 := by
      intro k' i' j'
      have := hirr k' i'
      have hmem : b ⟨k', (i', j')⟩ ∈ S k' i' := by
        change b ⟨k', (i', j')⟩ ∈ (S k' i').toSubmodule
        rw [hspan k' i']
        exact Submodule.subset_span (Set.mem_range_self j')
      rw [charProjector_apply_of_mem _ (S k i).toRepresentation (S k' i') hmem]
      by_cases hk : k' = k
      · subst k'
        rw [ite_eq_left (hsame k i' i), ite_eq_left rfl]
        exact (orthonormal_iff_ite.mp b.orthonormal _ _).trans (ite_eq_left rfl)
      · rw [ite_eq_right (hcross k' k hk i' i), ite_eq_right hk]
        simp
    simp only [Fintype.sum_prod_type, hinner]
    simp
  exact mul_right_cancel₀ (Nat.cast_ne_zero.mpr (hd k).ne') (htrace.symm.trans htrace')

/-- The orthonormal irreducible block decomposition with its actual character multiplicities.
Source: SCP10, Section 4.1, and Lemma 4.4, lines 970–976. Each row has dimension `d k`,
and the multiplicity of its character in the full representation is exactly `m k`. -/
theorem exists_unitary_character_matrix_blocks [Fintype G]
    (U : G →* Matrix n n ℂ) (hU : ∀ g, U g ∈ Matrix.unitaryGroup n ℂ) :
    ∃ (K : ℕ) (d m : Fin K → ℕ)
      (b : OrthonormalBasis ((k : Fin K) × (Fin (m k) × Fin (d k))) ℂ
        (EuclideanSpace ℂ n))
      (S : ∀ k, Fin (m k) → Subrepresentation (euclideanMatrixRepresentation U)),
      (∀ k, 0 < d k) ∧ (∀ k, 0 < m k) ∧
      (∀ k i, (S k i).toSubmodule =
        Submodule.span ℂ (Set.range fun j => b ⟨k, (i, j)⟩)) ∧
      (∀ k i, (S k i).toRepresentation.IsIrreducible) ∧
      (∀ k k', k ≠ k' → ∀ i i',
        (S k i).toRepresentation.character ≠ (S k' i').toRepresentation.character) ∧
      (∀ k i, Module.finrank ℂ (S k i).toSubmodule = d k) ∧
      (∀ k i, characterMultiplicity (euclideanMatrixRepresentation U)
        (S k i).toRepresentation.character = (m k : ℂ)) ∧
      ∀ g, ∃ B : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ,
        ∀ k i j, euclideanMatrixRepresentation U g (b ⟨k, (i, j)⟩) =
          ∑ j', B k j' j • b ⟨k, (i, j')⟩ := by
  classical
  obtain ⟨K, d, m, b, S, hd, hm, hspan, hirr, hcross, hact⟩ :=
    exists_unitary_irreducible_matrix_blocks U hU
  refine ⟨K, d, m, b, S, hd, hm, hspan, hirr, hcross, ?_,
    multiplicity_of_unitary_rows U K d m b S hd hspan hirr hcross hact, hact⟩
  intro k i
  rw [hspan k i]
  have hlin : LinearIndependent ℂ (fun j => b ⟨k, (i, j)⟩) :=
    b.orthonormal.linearIndependent.comp (fun j => ⟨k, (i, j)⟩)
      (by intro j j' h; simpa using h)
  simpa only [Fintype.card_fin] using finrank_span_eq_card hlin
end Representation
