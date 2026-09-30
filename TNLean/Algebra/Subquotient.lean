/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.Module.Submodule.Range

/-!
# Subquotients of nested submodules

The subquotient `B ⧸ A` of two submodules `A ≤ B` of a module, used for the composition
factors of an invariant flag in the multi-block asymmetric compression theorem.

## Main definitions

* `Submodule.subquot A B`: the quotient of `B` by the preimage of `A` under the inclusion.

## Main results

* `Submodule.subquotCongr`: rewriting the two submodules.
* `Submodule.subquotMapEquiv`: subquotients are transported along the inclusion of a submodule.
* `Submodule.subquotTopEquiv`: the subquotient `⊤ ⧸ A` is the quotient `M ⧸ A`.
-/

namespace Submodule

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- The subquotient `B ⧸ A` of two submodules; only meaningful when `A ≤ B`. -/
abbrev subquot (A B : Submodule R M) : Type _ := ↥B ⧸ A.comap B.subtype

/-- The map induced on a subquotient by an endomorphism preserving both submodules. -/
def subquotMap (A B : Submodule R M) (f : M →ₗ[R] M) (hA : ∀ x ∈ A, f x ∈ A)
    (hB : ∀ x ∈ B, f x ∈ B) : subquot A B →ₗ[R] subquot A B :=
  (A.comap B.subtype).mapQ (A.comap B.subtype) (f.restrict hB) fun x hx => by
    simpa [Submodule.mem_comap] using hA x hx

@[simp] lemma subquotMap_mk (A B : Submodule R M) (f : M →ₗ[R] M) (hA : ∀ x ∈ A, f x ∈ A)
    (hB : ∀ x ∈ B, f x ∈ B) (x : B) :
    subquotMap A B f hA hB (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨f x, hB x x.2⟩ := rfl

/-- Rewriting the two submodules of a subquotient. -/
def subquotCongr {A A' B B' : Submodule R M} (hA : A = A') (hB : B = B') :
    subquot A B ≃ₗ[R] subquot A' B' := by
  subst hA; subst hB; exact LinearEquiv.refl R _

/-- Transport of a subquotient along the inclusion of a submodule `K`: the subquotient inside
`K` is the subquotient of the images in the ambient module. -/
noncomputable def subquotMapEquiv (K : Submodule R M) (A B : Submodule R K) :
    subquot A B ≃ₗ[R] subquot (A.map K.subtype) (B.map K.subtype) :=
  Submodule.Quotient.equiv _ _ (Submodule.equivMapOfInjective K.subtype K.subtype_injective B) (by
    ext ⟨y, hy⟩
    simp only [Submodule.mem_map, Submodule.mem_comap, LinearEquiv.coe_coe,
      Submodule.subtype_apply, Subtype.ext_iff, Submodule.coe_equivMapOfInjective_apply]
    constructor
    · rintro ⟨x, hxA, hxe⟩
      exact ⟨x, hxA, hxe⟩
    · rintro ⟨a, haA, hay⟩
      obtain ⟨b, hbB, hby⟩ := hy
      have hab : a = b := Subtype.coe_injective (hay.trans hby.symm)
      subst hab
      exact ⟨⟨a, hbB⟩, haA, hay⟩)

/-- The subquotient `⊤ ⧸ A` is the quotient by `A`. -/
noncomputable def subquotTopEquiv (A : Submodule R M) : subquot A ⊤ ≃ₗ[R] (M ⧸ A) :=
  Submodule.Quotient.equiv _ _ (Submodule.topEquiv (R := R) (M := M)) (by
    ext x
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, trivial⟩, hx, rfl⟩)

end Submodule
