/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.PartyCircuit.WordOwnerMap
import TNLean.Lattice.Compression.OwnerMemoryTransport

/-! # Evaluation under relabelling of owners

Owner labels do not change the ordered memory spaces. Their canonical
isometries act as the identity under these space identifications, so an
intertwining identity identifies the two continuous linear maps themselves.
This identity applies to a word after any restriction has already been formed;
it does not infer equality of restricted words from equality of full operators.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 383–434 and 565–588.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect.Word

private theorem clm_heq_of_identity_intertwining {A B A' B' : HSpace}
    (ha : A' = A) (hb : B' = B)
    (e : A ≃ₗᵢ[ℂ] A') (d : B ≃ₗᵢ[ℂ] B')
    (F : A →L[ℂ] B) (G : A' →L[ℂ] B')
    (he : ∀ x, HEq (e x) x) (hd : ∀ y, HEq (d y) y)
    (h : ∀ x, G (e x) = d (F x)) : HEq G F := by
  subst A'
  subst B'
  apply heq_of_eq
  ext x
  have hi : e x = x := eq_of_heq (he x)
  have ho : d (F x) = F x := eq_of_heq (hd (F x))
  simpa only [hi, ho] using h x

/-- Changing arbitrary owner labels preserves the actual continuous linear
map under the equality of the ordered memory spaces. Pair sources whose
owners merge are retained as internal local preparations.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 383–434
and 565–588. -/
theorem eval_mapOwner_heq {P Q : Type} (f : P → Q) {a b : Layout P}
    (w : Word a b) : HEq (w.mapOwner f).eval w.eval := by
  exact clm_heq_of_identity_intertwining
    (Layout.mem_mapOwner f a) (Layout.mem_mapOwner f b)
    (Layout.mapOwnerIso f a) (Layout.mapOwnerIso f b)
    w.eval (w.mapOwner f).eval
    (Layout.mapOwnerIso_apply_heq f a) (Layout.mapOwnerIso_apply_heq f b)
    (eval_mapOwner f w)

end TNLean.PEPS.PairEffect.Word
