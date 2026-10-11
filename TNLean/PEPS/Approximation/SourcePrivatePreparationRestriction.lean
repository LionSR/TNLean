/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourcePrivatePreparation
import TNLean.PEPS.Approximation.FrameListRestriction
import TNLean.PEPS.Approximation.ActualSourceEmptyOwner
import TNLean.PEPS.Approximation.WordOwnerRestriction

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

/-- Preparing the recorded private product input, framed by the actual source
registers, acts as the identity at the exterior owner.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`,
lines 137–139, 246–267 and 409–434. -/
theorem restrict_sourcePrivatePreparation_none_eval_heq_id {a b : Layout P}
    (w : SourceCircuit a b) (ψ : ProductInput a) :
    HEq (((w.sourcePrivatePreparation ψ).restrict Option.isNone
      (sources_sourcePrivatePreparation w ψ)).eval)
      (ContinuousLinearMap.id ℂ ℂ) := by
  classical
  unfold sourcePrivatePreparation
  have hselector :
      partySelector (none : Option {p : P // (fun _ : P => true) p = true}) =
        Option.isNone := by
    funext q
    cases q <;> simp [partySelector]
  have hprepare := (Word.restrict_mapOwner_eval_eq_id_of_disjoint
    (affectedOwner (fun _ : P => true)) none ψ.prepare ψ.sources_prepare
    (by intro p; simp [affectedOwner])).2
  rw [hselector] at hprepare
  have hframe := Word.restrict_frameList_eval_heq_of_eq_nil Option.isNone
    w.allResidualSourceLayout (restrict_allResidualSourceLayout_isNone w)
    (ψ.prepare.mapOwner (affectedOwner (fun _ : P => true)))
    (by simp [Word.sources_mapOwner, ψ.sources_prepare])
  have h := hframe.trans hprepare
  exact h

end TNLean.PEPS.PairEffect.SourceCircuit
