/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Algebra.StarSubalgebraSpatial
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Orthogonal irreducible decomposition for a star-subalgebra of complex matrices

Building on orthogonal reducibility (every invariant subspace of a star-subalgebra has
an invariant orthogonal complement), this file shows that the whole representation space
splits as an orthogonal direct sum of irreducible invariant subspaces. This is the
spatial input to the structure theory of Wolf Ch. 6, towards Thm 6.14: a
finite-dimensional star-subalgebra of matrices, acting on Euclidean space, reduces the
space into mutually orthogonal pieces on each of which it acts irreducibly.

The argument is a finite induction on dimension. If the space carries no proper nonzero
invariant subspace it is already irreducible; otherwise a proper nonzero invariant
subspace splits off its orthogonal complement, both pieces are invariant and strictly
smaller, and the inductive decompositions of the two pieces are orthogonal to each other
because the two pieces are.

## Main definitions

* `StarSubalgebra.IsInvariantSubspace` -- a subspace mapped into itself by every member of
  the subalgebra, viewed as an operator on Euclidean space.
* `StarSubalgebra.IsIrreducibleSubspace` -- a nonzero invariant subspace whose only
  invariant subspaces are the zero subspace and itself.

## Main results

* `StarSubalgebra.exists_orthogonal_irreducible_of_invariant` -- every invariant subspace
  is the supremum of a finite, pairwise orthogonal family of irreducible invariant
  subspaces contained in it.
* `StarSubalgebra.exists_orthogonal_irreducible_decomposition` -- the whole representation
  space is the supremum of a finite, pairwise orthogonal family of irreducible invariant
  subspaces.

## Remaining gap towards Wolf Thm 6.14

The orthogonal decomposition into irreducible pieces is obtained here. The full theorem
additionally groups the irreducible pieces into isotypic components, equips each component
with a tensor identification of the form "matrix block on the multiplicity space", and
assembles a single unitary change of basis. Those steps are not formalized here.
-/

namespace StarSubalgebra

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (S : StarSubalgebra ℂ (Matrix n n ℂ))

/-- A subspace of Euclidean space is invariant under a star-subalgebra `S` of complex
matrices when every member of `S`, viewed as an operator on Euclidean space, maps the
subspace into itself. Wolf Ch. 6, towards Thm 6.14. -/
def IsInvariantSubspace (p : Submodule ℂ (EuclideanSpace ℂ n)) : Prop :=
  ∀ A ∈ S, p ∈ Module.End.invtSubmodule (Matrix.toEuclideanLin A)

/-- An invariant subspace is irreducible under a star-subalgebra `S` when it is nonzero and
its only invariant subspaces are the zero subspace and itself. Wolf Ch. 6, towards
Thm 6.14. -/
def IsIrreducibleSubspace (p : Submodule ℂ (EuclideanSpace ℂ n)) : Prop :=
  S.IsInvariantSubspace p ∧ p ≠ ⊥ ∧
    ∀ q : Submodule ℂ (EuclideanSpace ℂ n), S.IsInvariantSubspace q → q ≤ p → q = ⊥ ∨ q = p

/-- The whole representation space is invariant under the subalgebra. -/
theorem isInvariantSubspace_top : S.IsInvariantSubspace ⊤ :=
  fun A _ ↦ Module.End.invtSubmodule.top_mem (Matrix.toEuclideanLin A)

/-- The orthogonal complement of an invariant subspace is invariant, restated in terms of
invariant subspaces of the subalgebra. Wolf Ch. 6, towards Thm 6.14. -/
theorem isInvariantSubspace_orthogonal {p : Submodule ℂ (EuclideanSpace ℂ n)}
    (hp : S.IsInvariantSubspace p) : S.IsInvariantSubspace pᗮ :=
  S.orthogonal_mem_invtSubmodule hp

/-- Dimension-bounded form of the decomposition, used as the induction hypothesis. Every
invariant subspace of dimension `k` is the supremum of a finite, pairwise orthogonal family
of irreducible invariant subspaces contained in it. -/
private theorem exists_orthogonal_irreducible_aux :
    ∀ (k : ℕ) (p : Submodule ℂ (EuclideanSpace ℂ n)),
      S.IsInvariantSubspace p → Module.finrank ℂ p = k →
      ∃ D : Set (Submodule ℂ (EuclideanSpace ℂ n)), D.Finite ∧
        (∀ pc ∈ D, S.IsIrreducibleSubspace pc) ∧ (∀ pc ∈ D, pc ≤ p) ∧
        D.Pairwise (· ⟂ ·) ∧ sSup D = p := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro p hp hk
    by_cases hpbot : p = ⊥
    · refine ⟨∅, Set.finite_empty, by simp, by simp, Set.pairwise_empty _, ?_⟩
      rw [hpbot]; exact sSup_empty
    · by_cases hirr : S.IsIrreducibleSubspace p
      · refine ⟨{p}, Set.finite_singleton _, ?_, ?_, Set.pairwise_singleton _ _, sSup_singleton⟩
        · intro pc hpc; rw [Set.mem_singleton_iff] at hpc; exact hpc ▸ hirr
        · intro pc hpc; rw [Set.mem_singleton_iff] at hpc; exact hpc ▸ le_refl _
      · have hnall : ¬ ∀ q : Submodule ℂ (EuclideanSpace ℂ n),
            S.IsInvariantSubspace q → q ≤ p → q = ⊥ ∨ q = p :=
          fun hall ↦ hirr ⟨hp, hpbot, hall⟩
        push Not at hnall
        obtain ⟨q, hq_inv, hq_le, hq_bot, hq_ne⟩ := hnall
        have hq'_inv : S.IsInvariantSubspace (qᗮ ⊓ p) := fun A hA ↦
          Module.End.invtSubmodule.inf_mem (S.orthogonal_mem_invtSubmodule hq_inv A hA) (hp A hA)
        have hq_lt : q < p := lt_of_le_of_ne hq_le hq_ne
        have hq'_lt : qᗮ ⊓ p < p := by
          refine lt_of_le_of_ne inf_le_right ?_
          intro hcontra
          apply hq_bot
          have hple : p ≤ qᗮ := by rw [← hcontra]; exact inf_le_left
          have hqle' : q ≤ q ⊓ qᗮ := le_inf le_rfl (hq_le.trans hple)
          rwa [Submodule.inf_orthogonal_eq_bot, le_bot_iff] at hqle'
        obtain ⟨D1, hD1fin, hD1irr, hD1le, hD1pair, hD1sup⟩ :=
          ih (Module.finrank ℂ q) (hk ▸ Submodule.finrank_lt_finrank_of_lt hq_lt) q hq_inv rfl
        obtain ⟨D2, hD2fin, hD2irr, hD2le, hD2pair, hD2sup⟩ :=
          ih (Module.finrank ℂ (qᗮ ⊓ p : Submodule ℂ (EuclideanSpace ℂ n)))
            (hk ▸ Submodule.finrank_lt_finrank_of_lt hq'_lt) (qᗮ ⊓ p) hq'_inv rfl
        have hortho : q ⟂ qᗮ ⊓ p :=
          (Submodule.isOrtho_orthogonal_right q).mono_right inf_le_left
        refine ⟨D1 ∪ D2, hD1fin.union hD2fin, ?_, ?_, ?_, ?_⟩
        · rintro pc (h | h)
          · exact hD1irr pc h
          · exact hD2irr pc h
        · rintro pc (h | h)
          · exact (hD1le pc h).trans hq_le
          · exact (hD2le pc h).trans inf_le_right
        · rw [Set.pairwise_union]
          refine ⟨hD1pair, hD2pair, fun a ha b hb _ ↦ ⟨?_, ?_⟩⟩
          · exact hortho.mono (hD1le a ha) (hD2le b hb)
          · exact (hortho.mono (hD1le a ha) (hD2le b hb)).symm
        · rw [sSup_union, hD1sup, hD2sup]
          exact Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hq_le

/-- Every invariant subspace of a finite-dimensional star-subalgebra of complex matrices is
the supremum of a finite, pairwise orthogonal family of irreducible invariant subspaces
contained in it. Wolf Ch. 6, towards Thm 6.14. -/
theorem exists_orthogonal_irreducible_of_invariant
    (p : Submodule ℂ (EuclideanSpace ℂ n)) (hp : S.IsInvariantSubspace p) :
    ∃ D : Set (Submodule ℂ (EuclideanSpace ℂ n)), D.Finite ∧
      (∀ pc ∈ D, S.IsIrreducibleSubspace pc) ∧ (∀ pc ∈ D, pc ≤ p) ∧
      D.Pairwise (· ⟂ ·) ∧ sSup D = p :=
  S.exists_orthogonal_irreducible_aux (Module.finrank ℂ p) p hp rfl

/-- The whole representation space of a finite-dimensional star-subalgebra of complex
matrices is the supremum of a finite, pairwise orthogonal family of irreducible invariant
subspaces. This is the spatial semisimplicity of the representation in its decomposed form.
Wolf Ch. 6, towards Thm 6.14. -/
theorem exists_orthogonal_irreducible_decomposition :
    ∃ D : Set (Submodule ℂ (EuclideanSpace ℂ n)), D.Finite ∧
      (∀ pc ∈ D, S.IsIrreducibleSubspace pc) ∧
      D.Pairwise (· ⟂ ·) ∧ sSup D = ⊤ := by
  obtain ⟨D, hfin, hirr, -, hpair, hsup⟩ :=
    S.exists_orthogonal_irreducible_of_invariant ⊤ S.isInvariantSubspace_top
  exact ⟨D, hfin, hirr, hpair, hsup⟩

end StarSubalgebra
