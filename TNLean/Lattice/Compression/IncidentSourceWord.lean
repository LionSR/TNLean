/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.SelectedPartialSourceSlots
import TNLean.Lattice.Compression.SourcePrivatePreparation
/-!
# The source-to-output word determined by incident labels

The labels at gates incident to one original party determine an actual word
on its selected source registers. Prepare the recorded product input in the
singleton expansion, compose its chronological residual, and restrict to the
selected party. Relabelling the retained registers and identifying their lists
places this word on the original all-party source and output memories.
No label at another gate is chosen, and no full monomial choice is required.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 137–139, 246–267, 351–381, 409–434 and 565–588.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type}

/-- Construct the actual singleton source-to-output word from the original
incident gate labels and the recorded product input. Its registers are the
selected original all-party source and output registers, with their original
order and spaces. No full monomial choice or extension of the incident labels
is supplied. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`,
lines 137–139, 246–267, 351–381, 409–434 and 565–588. -/
def incidentSourceWord {a b : Layout P} (w : SourceCircuit a b) (p : P)
    (ψ : ProductInput a) (η : OriginalGateLabelsAt w p) :
    Word (Layout.atParty (some ⟨p, rfl⟩) (w.allResidualSourceLayout ++ []))
      (Layout.atParty (some ⟨p, rfl⟩)
        (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) b)) := by
  classical
  let A : P → Bool := fun t ↦ partySelector (some ⟨p, rfl⟩)
    (affectedOwner (fun _ : P ↦ true) t)
  let hp : A p = true := (partySelector_affectedOwner_all_apply p p).trans
    (decide_eq_true rfl)
  let q : Option {t : P // A t = true} := some ⟨p, hp⟩
  let lift : Option {t : P // A t = true} → Option {t : P // true = true} :=
    fun o ↦ o.map (fun t ↦ ⟨t.1, rfl⟩)
  let S := SourceInventory.slotLayout (partialSlots A w)
    (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1))
    (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2))
  let χ := choicesOfOriginalGateLabelsAt w p η
  let prep : Word (S ++ []) (S ++ Layout.mapOwner (affectedOwner A) a) :=
    Word.frameList S (ψ.prepare.mapOwner (affectedOwner A))
  have hprep : prep.sources = [] := by
    dsimp only [prep]
    rw [Word.sources_frameList, Word.sources_mapOwner, ψ.sources_prepare,
      SourceInventory.mapOwner_nil]
  let v : Word (S ++ []) (Layout.mapOwner (affectedOwner A) b) :=
    prep.comp (partialResidual A w χ)
  have hv : v.sources = [] := by
    change (partialResidual A w χ).sources ++ prep.sources = []
    rw [sources_partialResidual, hprep, List.nil_append]
  have hin : Layout.mapOwner lift (Layout.restrict (partySelector q) (S ++ [])) =
      Layout.atParty (some ⟨p, rfl⟩) (w.allResidualSourceLayout ++ []) := by
    rw [List.append_nil, List.append_nil]
    exact mapOwner_atParty_partialSlots_eq_allResidualSourceLayout w p
  have hout : Layout.mapOwner lift
      (Layout.restrict (partySelector q) (Layout.mapOwner (affectedOwner A) b)) =
      Layout.atParty (some ⟨p, rfl⟩)
        (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) b) :=
    mapOwner_selected_originalLayout_eq p b
  exact ((v.restrict (partySelector q) hv).mapOwner lift).castLayouts hin hout

/-- The incident-label source-to-output word introduces no pair preparation.
Its selected source input is free. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 246–267, 409–434 and 565–588. -/
theorem sources_incidentSourceWord {a b : Layout P} (w : SourceCircuit a b) (p : P)
    (ψ : ProductInput a) (η : OriginalGateLabelsAt w p) :
    (incidentSourceWord w p ψ η).sources = [] := by
  classical
  have h {Q R : Type} {c d : Layout Q} (u : Word c d) (hu : u.sources = [])
      (f : Q → Bool) (g : Q → R) {c' d' : Layout R}
      (hi : Layout.mapOwner g (Layout.restrict f c) = c')
      (ho : Layout.mapOwner g (Layout.restrict f d) = d') :
      (((u.restrict f hu).mapOwner g).castLayouts hi ho).sources = [] := by
    exact (Word.sources_castLayouts _ hi ho).trans
      ((Word.sources_mapOwner g _).trans
        ((congrArg (SourceInventory.mapOwner g) (Word.sources_restrict f u hu)).trans
          (SourceInventory.mapOwner_nil g)))
  unfold incidentSourceWord
  exact h _ _ _ _ _ _

end TNLean.PEPS.PairEffect.SourceCircuit
