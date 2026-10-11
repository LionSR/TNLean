/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.LayoutOwnerMap

/-!
# Memory spaces under changes of owner labels

Changing owner labels preserves the ordered tensor factors. Consequently its
canonical memory isometry acts as the identity after identifying the two memory
spaces. These identities concern arbitrary owner maps, including maps into an
empty type whenever such a map exists.

## References

* *Polynomial PEPS approximation of gapped square-grid ground states*, Theorem 5.2,
  September 24, 2026; `04-compression.tex`, lines 383–427 and 565–588.
-/

noncomputable section
open scoped TensorProduct
namespace TNLean.PEPS.PairEffect.Layout
variable {P Q : Type}

/-- Selecting registers after an owner map is the owner map of the selected
original registers. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 342–364 and 409–450. -/
theorem restrict_mapOwner (f : P → Q) (g : Q → Bool) (a : Layout P) :
    restrict g (mapOwner f a) = mapOwner f (restrict (fun p ↦ g (f p)) a) := by
  simp [restrict, mapOwner, List.filter_map, Function.comp_def]

/-- The canonical isometry of the selected memories before and after relabelling.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–450. -/
def restrictMapOwnerIso (f : P → Q) (g : Q → Bool) (a : Layout P) :
    Mem (restrict (fun p ↦ g (f p)) a) ≃ₗᵢ[ℂ] Mem (restrict g (mapOwner f a)) :=
  (mapOwnerIso f _).trans (memCongr (restrict_mapOwner f g a).symm)

/-- Owner labels do not affect the memory space of the ordered registers. -/
theorem mem_mapOwner (f : P → Q) (a : Layout P) :
    Mem (mapOwner f a) = Mem a := by
  induction a with
  | nil => rfl
  | cons r a ih =>
      exact congrArg (fun H : HSpace => HSpace.of (r.space ⊗[ℂ] H)) ih

private theorem lTensor_apply_heq_refl {A B : HSpace} (h : B = A)
    (e : A ≃ₗᵢ[ℂ] B) (he : ∀ x, HEq (e x) x) (C : HSpace)
    (z : C ⊗[ℂ] A) : HEq (e.lTensor C z) z := by
  subst B
  have he' : e = LinearIsometryEquiv.refl ℂ A := by
    ext x
    exact eq_of_heq (he x)
  rw [he']
  apply heq_of_eq
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => rfl

/-- The canonical owner identification preserves every memory vector, under
the equality of the underlying tensor-product spaces. -/
theorem mapOwnerIso_apply_heq (f : P → Q) (a : Layout P) (x : Mem a) :
    HEq (mapOwnerIso f a x) x := by
  induction a with
  | nil => rfl
  | cons r a ih =>
      exact lTensor_apply_heq_refl (mem_mapOwner f a) (mapOwnerIso f a)
        ih r.space x

end TNLean.PEPS.PairEffect.Layout
