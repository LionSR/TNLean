/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.StarSubalgebraIrreducibleDecomp
import TNLean.Algebra.StarSubalgebraSemisimple

/-!
# Irreducible invariant subspaces as simple modules over the subalgebra

A star-subalgebra `S` of complex matrices acts on Euclidean space, each member acting as the
operator its matrix represents. Mathlib already provides this action as a module structure:
matrices act on `n → ℂ`, the action restricts to the subalgebra, and it transports to
`EuclideanSpace ℂ n`. This file identifies the invariant-subspace notions used in the
structure theory of Wolf Ch. 6 (towards Thm 6.14) with their module-theoretic counterparts:
the submodules over the subalgebra are exactly the invariant subspaces, and the irreducible
invariant subspaces are exactly the simple submodules.

Through this identification the isotypic grouping behind Wolf Thm 6.14 can draw on the
general theory of simple and semisimple modules (`IsSimpleModule`, `IsSemisimpleModule` and
the isotypic decomposition built on them) instead of re-deriving it for the spatial
predicates.

## Main definitions

* `StarSubalgebra.IsInvariantSubspace.toSubmodule` -- an invariant subspace regarded as a
  submodule over the subalgebra.

## Main results

* `StarSubalgebra.isScalarTower_pi` -- the matrix action of the subalgebra on `n → ℂ` is
  complex-linear in the subalgebra member; from this the corresponding statement on
  `EuclideanSpace ℂ n` follows by the general `WithLp` instance.
* `StarSubalgebra.isInvariantSubspace_iff_exists_restrictScalars` -- the invariant subspaces
  are exactly the complex subspaces underlying submodules over the subalgebra.
* `StarSubalgebra.isIrreducibleSubspace_restrictScalars_iff` -- a submodule over the
  subalgebra is simple precisely when its underlying subspace is irreducible.
* `StarSubalgebra.isSemisimpleModule_euclideanSpace` -- Euclidean space is a semisimple
  module over the subalgebra.
-/

namespace StarSubalgebra

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (S : StarSubalgebra ℂ (Matrix n n ℂ))

/-- Scaling a member of a star-subalgebra of complex matrices scales its action on `n → ℂ`:
the restriction to the subalgebra of the corresponding property of the full matrix action.
Together with the general `WithLp` instance this yields
`IsScalarTower ℂ ↥S (EuclideanSpace ℂ n)`. Wolf Ch. 6, towards Thm 6.14. -/
instance isScalarTower_pi : IsScalarTower ℂ ↥S ((i : n) → ℂ) where
  smul_assoc c s v := by
    have h := smul_assoc c (s : Matrix n n ℂ) v
    rwa [← SetLike.val_smul] at h

/-- The module action of a member of the subalgebra on Euclidean space is the operator its
matrix represents; membership statements about the action can be rewritten to the
`Matrix.toEuclideanLin` form used by `StarSubalgebra.IsInvariantSubspace`. -/
theorem euclideanSpace_smul_def (s : ↥S) (v : EuclideanSpace ℂ n) :
    s • v = Matrix.toEuclideanLin (s : Matrix n n ℂ) v :=
  rfl

variable {S}

/-- An invariant subspace of a star-subalgebra of complex matrices, regarded as a submodule
over the subalgebra. Wolf Ch. 6, towards Thm 6.14. -/
def IsInvariantSubspace.toSubmodule {p : Submodule ℂ (EuclideanSpace ℂ n)}
    (hp : S.IsInvariantSubspace p) : Submodule ↥S (EuclideanSpace ℂ n) where
  carrier := p
  add_mem' := p.add_mem
  zero_mem' := p.zero_mem
  smul_mem' s {_} hv := hp s.1 s.2 hv

@[simp]
theorem IsInvariantSubspace.mem_toSubmodule {p : Submodule ℂ (EuclideanSpace ℂ n)}
    (hp : S.IsInvariantSubspace p) {x : EuclideanSpace ℂ n} : x ∈ hp.toSubmodule ↔ x ∈ p :=
  Iff.rfl

/-- Restricting the scalars of the submodule attached to an invariant subspace recovers the
subspace. -/
@[simp]
theorem IsInvariantSubspace.restrictScalars_toSubmodule {p : Submodule ℂ (EuclideanSpace ℂ n)}
    (hp : S.IsInvariantSubspace p) : hp.toSubmodule.restrictScalars ℂ = p := by
  ext x
  exact Iff.rfl

variable (S)

/-- The complex subspace underlying a submodule over the subalgebra is invariant under every
member of the subalgebra. Wolf Ch. 6, towards Thm 6.14. -/
theorem isInvariantSubspace_restrictScalars (q : Submodule ↥S (EuclideanSpace ℂ n)) :
    S.IsInvariantSubspace (q.restrictScalars ℂ) := by
  intro A hA
  rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
  intro x hx
  rw [Submodule.restrictScalars_mem] at hx ⊢
  rw [← euclideanSpace_smul_def S ⟨A, hA⟩ x]
  exact q.smul_mem _ hx

/-- The invariant subspaces of a star-subalgebra of complex matrices are exactly the complex
subspaces underlying submodules over the subalgebra. Wolf Ch. 6, towards Thm 6.14. -/
theorem isInvariantSubspace_iff_exists_restrictScalars (p : Submodule ℂ (EuclideanSpace ℂ n)) :
    S.IsInvariantSubspace p ↔
      ∃ q : Submodule ↥S (EuclideanSpace ℂ n), q.restrictScalars ℂ = p :=
  ⟨fun hp ↦ ⟨hp.toSubmodule, hp.restrictScalars_toSubmodule⟩,
    fun ⟨q, hq⟩ ↦ hq ▸ S.isInvariantSubspace_restrictScalars q⟩

/-- A submodule of Euclidean space over a star-subalgebra of complex matrices is simple
precisely when its underlying complex subspace is an irreducible invariant subspace. This
identifies the spatial irreducibility notion of the structure theory with simplicity of
modules, so the isotypic grouping behind Wolf Thm 6.14 can draw on the general theory of
semisimple modules. Wolf Ch. 6, towards Thm 6.14. -/
theorem isIrreducibleSubspace_restrictScalars_iff (q : Submodule ↥S (EuclideanSpace ℂ n)) :
    S.IsIrreducibleSubspace (q.restrictScalars ℂ) ↔ IsSimpleModule ↥S q := by
  rw [isSimpleModule_iff_isAtom]
  constructor
  · rintro ⟨-, hne, hmin⟩
    refine ⟨fun h ↦ hne (by rw [h, Submodule.restrictScalars_bot]), fun q' hq' ↦ ?_⟩
    rcases hmin (q'.restrictScalars ℂ) (S.isInvariantSubspace_restrictScalars q')
        (Submodule.restrictScalars_mono ℂ hq'.le) with h | h
    · rwa [Submodule.restrictScalars_eq_bot_iff] at h
    · exact absurd (Submodule.restrictScalars_injective ℂ ↥S (EuclideanSpace ℂ n) h) hq'.ne
  · intro hq
    refine ⟨S.isInvariantSubspace_restrictScalars q, ?_, fun r hr hle ↦ ?_⟩
    · rw [Ne, Submodule.restrictScalars_eq_bot_iff]
      exact hq.1
    · have hle' : hr.toSubmodule ≤ q := fun x hx ↦ hle hx
      rcases hq.le_iff.mp hle' with h | h
      · left
        have hr' := congrArg (Submodule.restrictScalars ℂ) h
        rwa [hr.restrictScalars_toSubmodule, Submodule.restrictScalars_bot] at hr'
      · right
        have hr' := congrArg (Submodule.restrictScalars ℂ) h
        rwa [hr.restrictScalars_toSubmodule] at hr'

/-- Euclidean space is a semisimple module over a star-subalgebra of complex matrices: every
submodule over the subalgebra admits a complementary submodule. This is the module-theoretic
form of the orthogonal irreducible decomposition, obtained here from semisimplicity of the
subalgebra as a ring (`StarSubalgebra.isSemisimpleRing`). Wolf Ch. 6, towards Thm 6.14. -/
theorem isSemisimpleModule_euclideanSpace : IsSemisimpleModule ↥S (EuclideanSpace ℂ n) :=
  inferInstance

end StarSubalgebra
