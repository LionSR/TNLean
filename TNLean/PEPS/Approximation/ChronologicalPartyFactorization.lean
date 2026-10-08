/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.CanonicalPartyFactorization

/-! # Actual chronological branches in grouped party coordinates

The statements concern the explicitly constructed words, their register order,
and their restrictions to selected parties. They are auxiliary identities for
the chronological construction, before the final physical partial trace.

Source: polynomial-PEPS, `04-compression.tex`, lines 233–267 and 342–381.
-/

noncomputable section
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type}

/-- Canonical grouping of the actual full residual is the tensor product of
its local residuals on the actual incident-choice types. This is an operator
identity; no positivity assertion about sampled operators is used.
Source: polynomial-PEPS 04-compression.tex, lines 233–251 and 351–381. -/
theorem groupByPartyIso_fullRemainingWord_eq_tensorLocalRemainingMaps
    {a b : Layout P} (w : SourceCircuit a b) (ξ : FullLabels w)
    (ps : List P) (hn : ps.Nodup) (hP : ∀ p, p ∈ ps) :
    isoL (groupByPartyIso ps b hn (fun r _ => hP r.owner)) ∘L
      (w.fullRemainingWord ξ).eval =
      tensorPartyMaps (w.fixedSourceLayout ++ a) b
        (fun p => w.localRemainingMap p (choicesOfFullLabels (partySelector p) w ξ)) ps ∘L
        isoL (groupByPartyIso ps (w.fixedSourceLayout ++ a) hn (fun r _ => hP r.owner)) := by
  have he := (w.fullRemainingWord ξ).groupByPartyIso_eval_eq_tensorRestrictions
    (w.sources_fullRemainingWord ξ) ps hn (fun p _ => hP p)
  simpa only [w.restrict_fullRemainingWord_eq_localRemainingMap] using he

/-- The complete actual chronological branch is obtained by inserting its
recorded pair-source product and applying the tensor product of the local
incident-choice residuals. This is an identity of branch operators, before
physical readout or sampling.
Source: polynomial-PEPS 04-compression.tex, lines 233–251 and 342–381. -/
theorem groupByPartyIso_fullBranchWord_eq_tensorLocalRemainingMaps
    {a b : Layout P} (w : SourceCircuit a b) (ξ : FullLabels w)
    (ps : List P) (hn : ps.Nodup) (hP : ∀ p, p ∈ ps) :
    isoL (groupByPartyIso ps b hn (fun r _ => hP r.owner)) ∘L
      (w.fullBranchWord ξ).eval =
      tensorPartyMaps (w.fixedSourceLayout ++ a) b
        (fun p => w.localRemainingMap p (choicesOfFullLabels (partySelector p) w ξ)) ps ∘L
        isoL (groupByPartyIso ps (w.fixedSourceLayout ++ a) hn (fun r _ => hP r.owner)) ∘L
        isoL (appendIso w.fixedSourceLayout a).symm ∘L appendLeft (w.fullSourceVector ξ) := by
  rw [w.eval_fullBranchWord_eq_fullRemainingWord, ← comp_assoc,
    w.groupByPartyIso_fullRemainingWord_eq_tensorLocalRemainingMaps ξ ps hn hP,
    comp_assoc]
end TNLean.PEPS.PairEffect.SourceCircuit
