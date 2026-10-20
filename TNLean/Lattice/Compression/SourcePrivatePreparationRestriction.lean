/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.SourcePrivatePreparation
import TNLean.Lattice.Compression.FrameListRestriction
import TNLean.Lattice.Compression.ActualSourceEmptyOwner
import TNLean.Lattice.Compression.WordOwnerRestriction

/-!
# The exterior restriction of the recorded private preparation

When all original parties are selected, the recorded private preparation and
every fixed source register belong to selected original parties. Restricting
this preparation to the exterior owner therefore gives the identity on the
empty memory. The statement concerns the actual preparation word and does not
depend on a choice of monomial.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*
  (September 24, 2026), proof of Theorem 5.2, `04-compression.tex`,
  lines 137–139, 246–267 and 409–434.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type}

/-- Excluded spectator registers do not change the exterior identity of an
original private product preparation. The spectator list is arbitrary.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`,
lines 137–139, 246–267 and 409–434. -/
private theorem restrict_framed_privatePreparation_none_eval_heq_id {a : Layout P}
    (rs : Layout (Option {_p : P // true = true}))
    (hrs : Layout.restrict Option.isNone rs = []) (ψ : ProductInput a) :
    HEq ((Word.frameList rs (ψ.prepare.mapOwner (affectedOwner (fun _ : P ↦ true)))).restrict
      Option.isNone (by simp [Word.sources_frameList, Word.sources_mapOwner,
        ψ.sources_prepare])).eval (ContinuousLinearMap.id ℂ ℂ) := by
  classical
  have hprepare := (Word.restrict_mapOwner_eval_eq_id_of_disjoint
    (affectedOwner (fun _ : P ↦ true)) none ψ.prepare ψ.sources_prepare
    (by intro p; simp [affectedOwner])).2
  rw [partySelector_none] at hprepare
  have hframe := Word.restrict_frameList_eval_heq_of_eq_nil Option.isNone rs hrs
    (ψ.prepare.mapOwner (affectedOwner (fun _ : P ↦ true)))
    (by simp [Word.sources_mapOwner, ψ.sources_prepare])
  exact hframe.trans hprepare

/-- Preparing the recorded private product input, framed by the actual source
registers, acts as the identity at the exterior owner.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`,
lines 137–139, 246–267 and 409–434. -/
theorem restrict_sourcePrivatePreparation_none_eval_heq_id {a b : Layout P}
    (w : SourceCircuit a b) (ψ : ProductInput a) :
    HEq (((w.sourcePrivatePreparation ψ).restrict Option.isNone
      (sources_sourcePrivatePreparation w ψ)).eval)
      (ContinuousLinearMap.id ℂ ℂ) := by
  exact restrict_framed_privatePreparation_none_eval_heq_id
    w.allResidualSourceLayout (restrict_allResidualSourceLayout_isNone w) ψ

end TNLean.PEPS.PairEffect.SourceCircuit
