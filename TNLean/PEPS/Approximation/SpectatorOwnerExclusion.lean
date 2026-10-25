/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.WordOwnerRestriction
import TNLean.Lattice.Compression.WordAppendTailRestriction
import TNLean.Lattice.Compression.LayoutExcludedOwners
import TNLean.Lattice.PartyCircuit.PartyTensorMaps

/-!
# Spectators at an excluded owner

A source-free composition whose relabelled owners all differ from a fixed
party restricts to the scalar identity at that party. Extending the composition
by spectator registers therefore leaves the party's retained spectators
unchanged. These spectators need not be empty, and their spaces are arbitrary.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 233–267, 351–381, 409–434 and 565–588.
-/

noncomputable section
open scoped TensorProduct
namespace TNLean.Lattice.PartyCircuit.Word
open TNLean.Lattice.PartyCircuit
open ContinuousLinearMap

private theorem appendTail_eval_heq_id_of_empty_layouts {P : Type}
    {a b : Layout P} (w : Word a b) (ha : a = []) (hb : b = [])
    (he : HEq w.eval (ContinuousLinearMap.id ℂ ℂ)) (tail : Layout P) :
    HEq (w.appendTail tail).eval (ContinuousLinearMap.id ℂ (Mem tail)) := by
  cases ha
  cases hb
  have h := eval_appendTail w tail
  rw [eq_of_heq he, ContinuousLinearMap.rTensor_id, ContinuousLinearMap.comp_id] at h
  apply heq_of_eq
  ext x
  have hx := DFunLike.congr_fun h (appendIso [] tail x)
  change (w.appendTail tail).eval x = x
  simpa only [ContinuousLinearMap.comp_apply, isoL_apply,
    LinearIsometryEquiv.symm_apply_apply, ContinuousLinearMap.id_apply] using hx

/-- A party outside the range of the core owner map retains only its spectator
registers, on which the actual restricted composition is the identity. The
source-free core and the spectator spaces may be arbitrary.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 233–267,
351–381, 409–434 and 565–588. -/
theorem restrict_mapOwner_appendTail_eval_heq_id_of_disjoint {C P : Type}
    (owner : C → P) (p : P) {a b : Layout C} (u : Word a b)
    (hs : u.sources = []) (howner : ∀ c, owner c ≠ p) (tail : Layout P) :
    HEq (((u.mapOwner owner).appendTail tail).restrict (partySelector p)
      ((sources_appendTail (u.mapOwner owner) tail).trans
        (by simp [sources_mapOwner, hs]))).eval
      (ContinuousLinearMap.id ℂ (Mem (Layout.atParty p tail))) := by
  classical
  have hmap : (u.mapOwner owner).sources = [] := by
    simp [sources_mapOwner, hs]
  have hsel : ∀ c, partySelector p (owner c) = false := by
    intro c
    simp only [partySelector, howner c, decide_false]
  have ha : Layout.restrict (partySelector p) (Layout.mapOwner owner a) = [] :=
    Layout.restrict_mapOwner_eq_nil owner (partySelector p) a hsel
  have hb : Layout.restrict (partySelector p) (Layout.mapOwner owner b) = [] :=
    Layout.restrict_mapOwner_eq_nil owner (partySelector p) b hsel
  have hcore : HEq ((u.mapOwner owner).restrict (partySelector p) hmap).eval
      (ContinuousLinearMap.id ℂ ℂ) :=
    (restrict_mapOwner_eval_eq_id_of_disjoint owner p u hs howner).2
  have hrestriction := restrict_appendTail_eval_heq (partySelector p)
    (u.mapOwner owner) hmap tail
  have hspectator := appendTail_eval_heq_id_of_empty_layouts
    ((u.mapOwner owner).restrict (partySelector p) hmap) ha hb hcore
    (Layout.restrict (partySelector p) tail)
  exact hrestriction.trans hspectator

end TNLean.Lattice.PartyCircuit.Word
