/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.StarSubalgebraIsotypic

/-!
# Isotypic-component decomposition for a star-subalgebra of complex matrices

Building on the orthogonal decomposition into irreducible pieces and the same-type relation
on those pieces, this file collects the pieces of a single type into one isotypic component
and shows that the whole representation space is the orthogonal direct sum of the isotypic
components. This is the isotypic-grouping step in the structure theory of
*Quantum Channels & Operations* (Wolf 2012), Chapter 6, towards Theorem 6.14.

Given the finite, pairwise orthogonal family of irreducible pieces produced by the orthogonal
decomposition, the same-type relation partitions the family into finitely many classes. Each
isotypic component is the supremum of one class. Two pieces drawn from different classes are
orthogonal, because pieces that are not of the same type are orthogonal; lifting this across
the suprema makes distinct isotypic components orthogonal. Since the classes cover the whole
family, the components span the whole space.

## Main results

* `StarSubalgebra.isOrtho_sSup_of_not_sameIsotype` -- if no piece of one same-type class is of
  the same type as any piece of another class, then the suprema of the two classes are
  orthogonal.
* `StarSubalgebra.exists_sameIsotype_of_le_sSup` -- an irreducible subspace contained in the
  supremum of a family of irreducible pieces has the same type as one of the pieces.
* `StarSubalgebra.exists_orthogonal_isotypic_decomposition` -- the whole representation space
  is the supremum of a finite, pairwise orthogonal family of isotypic components, each of
  which is the supremum of a finite, nonempty same-type class of pairwise orthogonal
  irreducible pieces; irreducible subspaces contained in distinct components are never of the
  same type.
-/

namespace StarSubalgebra

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (S : StarSubalgebra ℂ (Matrix n n ℂ))

/-- If every piece of one set is irreducible, every piece of another set is irreducible, and no
piece of the first set is of the same type as any piece of the second set, then the supremum of
the first set is orthogonal to the supremum of the second set. Pieces of different type are
orthogonal, and orthogonality lifts across suprema. See *Quantum Channels & Operations*
(Wolf 2012), Chapter 6, towards Theorem 6.14. -/
theorem isOrtho_sSup_of_not_sameIsotype
    {D₁ D₂ : Set (Submodule ℂ (EuclideanSpace ℂ n))}
    (h₁ : ∀ p ∈ D₁, S.IsIrreducibleSubspace p) (h₂ : ∀ q ∈ D₂, S.IsIrreducibleSubspace q)
    (h : ∀ p ∈ D₁, ∀ q ∈ D₂, ¬ S.SameIsotype p q) : sSup D₁ ⟂ sSup D₂ := by
  rw [Submodule.isOrtho_sSup_left]
  intro p hp
  rw [Submodule.isOrtho_sSup_right]
  intro q hq
  exact S.isOrtho_of_not_sameIsotype (h₁ p hp) (h₂ q hq) (h p hp q hq)

/-- An irreducible subspace contained in the supremum of a family of irreducible pieces has
the same type as one of the pieces. Were it of a different type than every piece, it would be
orthogonal to every piece, hence to their supremum, hence to itself, forcing it to vanish.
See *Quantum Channels & Operations* (Wolf 2012), Chapter 6, towards Theorem 6.14. -/
theorem exists_sameIsotype_of_le_sSup {D : Set (Submodule ℂ (EuclideanSpace ℂ n))}
    (hD : ∀ q ∈ D, S.IsIrreducibleSubspace q) {p : Submodule ℂ (EuclideanSpace ℂ n)}
    (hp : S.IsIrreducibleSubspace p) (hle : p ≤ sSup D) :
    ∃ q ∈ D, S.SameIsotype p q := by
  by_contra hnone
  push Not at hnone
  have hortho : p ⟂ sSup D := Submodule.isOrtho_sSup_right.mpr fun q hq =>
    S.isOrtho_of_not_sameIsotype hp (hD q hq) (hnone q hq)
  exact hp.2.1 (Submodule.isOrtho_self.mp (hortho.mono_right hle))

/-- The whole representation space of a finite-dimensional star-subalgebra of complex matrices
is the supremum of a finite, pairwise orthogonal family of isotypic components. Each component
is the supremum of a finite, nonempty same-type class of pairwise orthogonal irreducible
pieces, and irreducible subspaces contained in distinct components are never of the same type.
The orthogonal decomposition into irreducible pieces supplies the family; the same-type
relation groups it into classes, which inherit the pairwise orthogonality; and pieces of
different type are orthogonal, so distinct components are orthogonal. An irreducible subspace
of a component has the same type as the pieces of its class, so two such subspaces in distinct
components cannot have the same type. See *Quantum Channels & Operations* (Wolf 2012),
Chapter 6, towards Theorem 6.14. -/
theorem exists_orthogonal_isotypic_decomposition :
    ∃ C : Set (Submodule ℂ (EuclideanSpace ℂ n)), C.Finite ∧
      C.Pairwise (· ⟂ ·) ∧ sSup C = ⊤ ∧
      (∀ c ∈ C, ∃ Dc : Set (Submodule ℂ (EuclideanSpace ℂ n)),
        Dc.Nonempty ∧ Dc.Finite ∧ (∀ p ∈ Dc, S.IsIrreducibleSubspace p) ∧ c = sSup Dc ∧
          Dc.Pairwise (· ⟂ ·) ∧ Dc.Pairwise fun p q => S.SameIsotype p q) ∧
      ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' →
        ∀ p, S.IsIrreducibleSubspace p → p ≤ c →
          ∀ q, S.IsIrreducibleSubspace q → q ≤ c' → ¬ S.SameIsotype p q := by
  classical
  obtain ⟨D, hDfin, hDirr, hDpair, hDsup⟩ := S.exists_orthogonal_irreducible_decomposition
  -- The same-type class of a piece `p`, taken within the family `D`.
  set cls : Submodule ℂ (EuclideanSpace ℂ n) → Set (Submodule ℂ (EuclideanSpace ℂ n)) :=
    fun p => {q ∈ D | S.SameIsotype p q} with hcls
  -- Each class is a finite set of irreducible pieces of one type, and a piece lies in its own
  -- class by reflexivity of the same-type relation.
  have hcls_fin : ∀ p, (cls p).Finite := fun p => hDfin.sep _
  have hcls_irr : ∀ p, ∀ q ∈ cls p, S.IsIrreducibleSubspace q := fun _ q hq => hDirr q hq.1
  have hcls_self : ∀ p ∈ D, p ∈ cls p := fun p hp => ⟨hp, S.sameIsotype_refl (hDirr p hp)⟩
  -- Pieces inside one class are of the same type with each other (through the representative).
  have hcls_same : ∀ p ∈ D, (cls p).Pairwise fun a b => S.SameIsotype a b := by
    intro p hp a ha b hb _
    exact S.sameIsotype_trans (hDirr a ha.1) (hDirr p hp) (hDirr b hb.1)
      (S.sameIsotype_symm (hDirr p hp) (hDirr a ha.1) ha.2) hb.2
  -- If two representatives are of the same type, they generate the same class, hence the same
  -- isotypic component.
  have hcls_eq : ∀ p ∈ D, ∀ p' ∈ D, S.SameIsotype p p' → cls p = cls p' := by
    intro p hp p' hp' hsame
    ext q
    simp only [hcls, Set.mem_setOf_eq]
    refine and_congr_right fun hqD => ⟨fun hpq => ?_, fun hp'q => ?_⟩
    · exact S.sameIsotype_trans (hDirr p' hp') (hDirr p hp) (hDirr q hqD)
        (S.sameIsotype_symm (hDirr p hp) (hDirr p' hp') hsame) hpq
    · exact S.sameIsotype_trans (hDirr p hp) (hDirr p' hp') (hDirr q hqD) hsame hp'q
  -- The isotypic components are the suprema of the classes.
  refine ⟨(fun p => sSup (cls p)) '' D, hDfin.image _, ?_, ?_, ?_, ?_⟩
  · -- Distinct components come from representatives of different type, so they are orthogonal.
    rintro _ ⟨p, hp, rfl⟩ _ ⟨p', hp', rfl⟩ hne
    have hnot : ¬ S.SameIsotype p p' :=
      fun hsame => hne (congrArg sSup (hcls_eq p hp p' hp' hsame))
    -- Cross-class pieces are not of the same type, by transitivity through the representatives.
    refine S.isOrtho_sSup_of_not_sameIsotype (hcls_irr p) (hcls_irr p') ?_
    intro a ha b hb hsame
    refine hnot ?_
    have hpb : S.SameIsotype p b := S.sameIsotype_trans (hDirr p hp) (hDirr a ha.1) (hDirr b hb.1)
      ha.2 hsame
    exact S.sameIsotype_trans (hDirr p hp) (hDirr b hb.1) (hDirr p' hp') hpb
      (S.sameIsotype_symm (hDirr p' hp') (hDirr b hb.1) hb.2)
  · -- The classes cover the whole family, so the components span the whole space.
    rw [← hDsup]
    refine le_antisymm (sSup_le ?_) (sSup_le fun p hp => ?_)
    · rintro c ⟨p, _, rfl⟩
      exact sSup_le fun q hq => le_sSup hq.1
    · -- Each piece sits inside the supremum of its own class, hence inside that component.
      exact le_trans (le_sSup (hcls_self p hp)) (le_sSup ⟨p, hp, rfl⟩)
  · -- Each component carries its class as the requested witness; the class inherits the
    -- pairwise orthogonality of the family.
    rintro c ⟨p, hp, rfl⟩
    exact ⟨cls p, ⟨p, hcls_self p hp⟩, hcls_fin p, hcls_irr p, rfl,
      hDpair.mono (Set.sep_subset _ _), hcls_same p hp⟩
  · -- Irreducible subspaces of distinct components are of different types: each has the type
    -- of its component's representative, and distinct components have representatives of
    -- different types.
    rintro _ ⟨p, hp, rfl⟩ _ ⟨p', hp', rfl⟩ hne w hw hwle w' hw' hw'le hsame
    have hnot : ¬ S.SameIsotype p p' :=
      fun hsame' => hne (congrArg sSup (hcls_eq p hp p' hp' hsame'))
    obtain ⟨a, ha, hwa⟩ := S.exists_sameIsotype_of_le_sSup (hcls_irr p) hw hwle
    obtain ⟨a', ha', hw'a'⟩ := S.exists_sameIsotype_of_le_sSup (hcls_irr p') hw' hw'le
    -- Chain the types: `p ~ a ~ w ~ w' ~ a' ~ p'`.
    have hpw : S.SameIsotype p w :=
      S.sameIsotype_trans (hDirr p hp) (hcls_irr p a ha) hw ha.2
        (S.sameIsotype_symm hw (hcls_irr p a ha) hwa)
    have hw'p' : S.SameIsotype w' p' :=
      S.sameIsotype_trans hw' (hcls_irr p' a' ha') (hDirr p' hp') hw'a'
        (S.sameIsotype_symm (hDirr p' hp') (hcls_irr p' a' ha') ha'.2)
    have hpw' : S.SameIsotype p w' := S.sameIsotype_trans (hDirr p hp) hw hw' hpw hsame
    exact hnot (S.sameIsotype_trans (hDirr p hp) hw' (hDirr p' hp') hpw' hw'p')

end StarSubalgebra

