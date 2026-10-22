/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.WordEvalComparison
import TNLean.Lattice.Compression.IncidentSampledEndpointWord
import TNLean.Lattice.Compression.EndpointRegisterRestriction
import TNLean.Lattice.Compression.WordOwnerEvaluation
import TNLean.Lattice.PartyCircuit.PartyTensorMaps
import Mathlib.Data.List.OfFn

import TNLean.Lattice.Compression.SampledEndpointIncidentComparison

/-! # Comparing the actual sampled endpoint word with its incident construction

After restriction to one original party, the all-party endpoint word and the
word constructed from that party's incident labels have the same ordered
endpoint spaces and maps. Each map retains its original source occurrence,
the independently extracted ket and bra labels, and the same original sample
index and ordered-pair Gaussian array. The local word receives only incident
sample indices; neither labels nor samples are extended to other positions.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–267,
279–355, 409–434 and 565–588.
-/

noncomputable section
open ContinuousLinearMap
namespace TNLean
open TNLean.Lattice.PartyCircuit TNLean.PEPS.PairEffect
namespace Lattice.PartyCircuit.SourceCircuit
variable {P : Type} {a b : Layout P}

/-- Evaluation comparison of two arbitrary words, retaining their own input
and output layouts. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`,
lines 253–267, 279–355, 409–434 and 565–588. -/
private def wordEvalComparison {Q R : Type} {a b : Layout Q} {c d : Layout R}
    (u : Word a b) (v : Word c d) : Prop := Word.IsEvalComparison u v

/-- Two operator comparisons through an arbitrary intermediate word give
equality on fixed original input and output layouts. The composition is proved
before any sampled endpoint maps are supplied.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–267,
279–355, 409–434 and 565–588. -/
private theorem eval_eq_of_two_word_comparisons {Q R : Type}
    {a b : Layout Q} {c d : Layout R}
    (u t : Word a b) (v : Word c d)
    (hinput : wordEvalComparison u v) (hincident : wordEvalComparison v t) :
    u.eval = t.eval := by
  exact eq_of_heq (hinput.trans hincident)

variable (w : SourceCircuit a b) (k : ℕ)
  (lam : ∀ e : sourceLocations w, branchLabels w e.1 →
    Fin (min (sourceDims w e).1 (sourceDims w e).2) → ℝ)
  (E : ∀ e : sourceLocations w, branchLabels w e.1 →
    Matrix (Fin (sourceDims w e).1) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
  (F : ∀ e : sourceLocations w, branchLabels w e.1 →
    Matrix (Fin (sourceDims w e).2) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)

/-- Restriction of the sampled input word differs from restriction of the
sampled endpoint word only by the canonical layout identification. No
sampled matrix is expanded in this comparison.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–267 and 565–588. -/
private theorem restrict_sampledEndpointInputWord_eval_heq_sampledEndpointWord
    (f : Option {_p : P // true = true} → Bool)
    (ξ ζ : Choices (fun _ ↦ true) w) (j : w.sourceLocations → Fin k)
    (ω : SourceGaussianSamples w k) :
    wordEvalComparison
      ((sampledEndpointInputWord w k lam E F ξ ζ j ω).restrict f
        (sources_sampledEndpointInputWord w k lam E F ξ ζ j ω))
      ((sampledEndpointWord w k lam E F ξ ζ j ω).restrict f
        (sources_sampledEndpointWord w k lam E F ξ ζ j ω)) := by
  unfold sampledEndpointInputWord
  exact (heq_of_eq (congrArg Word.eval
    (Word.restrict_castLayouts f (sampledEndpointWord w k lam E F ξ ζ j ω)
      (List.append_nil _).symm (List.append_nil _).symm
      (sources_sampledEndpointWord w k lam E F ξ ζ j ω)))).trans
    (Word.eval_castLayouts_heq _ _ _)

/-- The actual sampled endpoint operator at one original party is the word
constructed directly from its incident ket and bra labels. Both endpoints
retain the same original sample assignment and ordered-pair Gaussian array.
Empty source inventories, sample sets and halfspaces are included; no
positivity, normalization, label or sample extension, or factorization premise
is assumed. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines
253–267, 279–355, 409–434 and 565–588. -/
theorem restrict_sampledEndpointInputWord_eval_eq_incidentSampledEndpointWord
    (p : P) (ξ ζ : Choices (fun _ : P ↦ true) w)
    (j : w.sourceLocations → Fin k) (ω : SourceGaussianSamples w k) :
    ((sampledEndpointInputWord w k lam E F ξ ζ j ω).restrict
      (partySelector (some ⟨p, rfl⟩))
      (sources_sampledEndpointInputWord w k lam E F ξ ζ j ω)).eval =
      (incidentSampledEndpointWord w k lam E F p
        (originalGateLabelsAtOfAllChoices w p ξ)
        (originalGateLabelsAtOfAllChoices w p ζ)
        (fun i ↦ j (partialSlotEquiv
          (fun t ↦ partySelector (some ⟨p, rfl⟩)
            (affectedOwner (fun _ : P ↦ true) t)) w i).1) ω).eval := by
  let u := (sampledEndpointInputWord w k lam E F ξ ζ j ω).restrict
    (partySelector (some ⟨p, rfl⟩))
    (sources_sampledEndpointInputWord w k lam E F ξ ζ j ω)
  let v := (sampledEndpointWord w k lam E F ξ ζ j ω).restrict
    (partySelector (some ⟨p, rfl⟩))
    (sources_sampledEndpointWord w k lam E F ξ ζ j ω)
  let t := incidentSampledEndpointWord w k lam E F p
    (originalGateLabelsAtOfAllChoices w p ξ)
    (originalGateLabelsAtOfAllChoices w p ζ)
    (fun i ↦ j (partialSlotEquiv
      (fun t ↦ partySelector (some ⟨p, rfl⟩)
        (affectedOwner (fun _ : P ↦ true) t)) w i).1) ω
  have hinput : wordEvalComparison u v :=
    restrict_sampledEndpointInputWord_eval_heq_sampledEndpointWord
      w k lam E F (partySelector (some ⟨p, rfl⟩)) ξ ζ j ω
  have hincident : wordEvalComparison v t :=
    restrict_sampledEndpointWord_eval_heq_incidentSampledEndpointWord w k lam E F p ξ ζ j ω
  exact eval_eq_of_two_word_comparisons u t v hinput hincident

end Lattice.PartyCircuit.SourceCircuit
end TNLean
