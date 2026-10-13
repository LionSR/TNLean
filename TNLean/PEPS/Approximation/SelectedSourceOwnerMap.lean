/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceOwnerMap
import TNLean.PEPS.Approximation.OwnerMemoryTransport
import TNLean.PEPS.Approximation.PartyTensorMaps

/-!
# Selected source registers after changing owners

If one new owner has exactly one original owner as its fibre, selecting its
source registers commutes with changing owners. Sources whose endpoints merge
are removed from the source inventory, but neither endpoint of a removed source
can lie in the selected fibre. The remaining half-registers keep their original
order and spaces.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 383–434
and 565–588.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect.SourceInventory
variable {P Q : Type}

/-- The selected source-register list is unchanged by removing sources whose
owners merge, when the selected owner's fibre consists of one original party.
The source vectors and the owner map away from that fibre are arbitrary.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 383–434
and 565–588. -/
theorem atParty_layout_mapOwner_of_singleton_fiber (f : P → Q) (p : P) (q : Q)
    (hf : ∀ r, f r = q ↔ r = p) (S : SourceInventory P) :
    Layout.atParty q (mapOwner f S).layout =
      Layout.mapOwner f (Layout.atParty p S.layout) := by
  classical
  have hselect : (fun r : P ↦ decide (f r = q)) = fun r ↦ decide (r = p) := by
    funext r
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using hf r
  have hlist (L : Layout P) :
      Layout.atParty q (Layout.mapOwner f L) =
        Layout.mapOwner f (Layout.atParty p L) := by
    dsimp only [Layout.atParty]
    rw [Layout.restrict_mapOwner, hselect]
  have hsplit {R : Type} (r : R) (L K : Layout R) :
      Layout.atParty r (L ++ K) = Layout.atParty r L ++ Layout.atParty r K := by
    exact Layout.restrict_append (fun r' ↦ decide (r' = r)) L K
  induction S with
  | nil => rfl
  | cons s S ih =>
      by_cases h : f s.left = f s.right
      · have hq : f s.left ≠ q := by
          intro hleft
          have hright : f s.right = q := h.symm.trans hleft
          exact s.distinct (((hf s.left).mp hleft).trans ((hf s.right).mp hright).symm)
        have hl : s.left ≠ p := fun hp ↦ hq ((hf s.left).mpr hp)
        have hr : s.right ≠ p := fun hp ↦ hq (h.trans ((hf s.right).mpr hp))
        have hcons : mapOwner f (s :: S) = mapOwner f S := by
          simp only [mapOwner_cons, PairSource.mapOwner, dite_eq_left h]
        have hhead : Layout.atParty p s.layout = [] := by
          simp [Layout.atParty, PairSource.layout, Layout.restrict_cons, hl, hr]
        rw [hcons, layout_cons, hsplit, hhead, List.nil_append]
        exact ih
      · have hcons : mapOwner f (s :: S) =
            (⟨f s.left, f s.right, h, s.leftSpace, s.rightSpace, s.vector⟩ : PairSource Q) ::
              mapOwner f S := by
          simp only [mapOwner_cons, PairSource.mapOwner, dite_eq_right h]
        have hhead : Layout.atParty q
            (⟨f s.left, f s.right, h, s.leftSpace, s.rightSpace, s.vector⟩ :
              PairSource Q).layout =
              Layout.mapOwner f (Layout.atParty p s.layout) := hlist s.layout
        rw [hcons, layout_cons, hsplit, hhead, ih, layout_cons, hsplit,
          Layout.mapOwner_append]

end TNLean.PEPS.PairEffect.SourceInventory
