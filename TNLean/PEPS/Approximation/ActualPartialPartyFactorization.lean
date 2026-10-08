/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ActualPartialLocalMaps

/-! # Incident choices in the actual chronological expansion

These results concern actual gate occurrences and their selected monomial labels.
Source: polynomial-PEPS, `04-compression.tex`, lines 351–381.
-/

noncomputable section
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type}

set_option maxHeartbeats 800000 in
-- The actual fixed source registers carry dependent owner and tensor transports.
/-- Grouping the actual all-party residual yields the tensor product of its
incident-choice local maps. The auxiliary owner `none` is retained as a factor,
so empty participating sets and an empty original party type are included.
Source: polynomial-PEPS 04-compression.tex, lines 351–381 and 565–588. -/
theorem groupByPartyIso_partialResidual_eq_tensorPartialLocalRemainingMaps
    {a b : Layout P} (w : SourceCircuit a b) (ξ : Choices (fun _ => true) w)
    (ps : List (Option {p : P // (fun _ : P => true) p = true}))
    (hn : ps.Nodup) (hP : ∀ q, q ∈ ps) :
    isoL (groupByPartyIso ps (Layout.mapOwner (affectedOwner (fun _ => true)) b) hn
      (fun r _ => hP r.owner)) ∘L (partialResidual (fun _ => true) w ξ).eval =
      tensorPartyMaps w.allResidualInput
        (Layout.mapOwner (affectedOwner (fun _ => true)) b)
        (fun q => w.partialLocalRemainingMap (partySelector q)
          (projectAllChoices
            (fun p => partySelector q (affectedOwner (fun _ => true) p)) w ξ)) ps ∘L
        isoL (groupByPartyIso ps w.allResidualInput hn (fun r _ => hP r.owner)) := by
  simpa only [restrict_partialResidual_eq_partialLocalRemainingMap] using
    Word.groupByPartyIso_eval_eq_tensorRestrictions
      (partialResidual (fun _ => true) w ξ) (sources_partialResidual _ _ _) ps hn
        (fun p _ => hP p)

end TNLean.PEPS.PairEffect.SourceCircuit
