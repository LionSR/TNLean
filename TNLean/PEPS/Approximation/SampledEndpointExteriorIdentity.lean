/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ActualSampledEndpointInputWord
import TNLean.PEPS.Approximation.PartialSourcePreparation
import TNLean.PEPS.Approximation.EndpointWordRestriction

/-! # Exterior restriction of the actual sampled endpoint word

Every endpoint register of the all-party source inventory belongs to an
original party. Restriction of the sampled endpoint word to the exterior
owner is therefore the identity on the scalar memory. The canonical
identification with the private preparation input preserves this identity.
The endpoint matrices, sample values and independent ket and bra choices are
arbitrary; no positivity or nonvanishing condition is used.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 253–267, 279–309 and 565–588.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect
variable {P : Type}

private theorem restrict_castLayouts_eval_heq {a b a' b' : Layout P}
    (w : Word a b) (f : P → Bool) (ha : a = a') (hb : b = b')
    (hs : w.sources = []) :
    HEq ((w.castLayouts ha hb).restrict f
      ((Word.sources_castLayouts w ha hb).trans hs)).eval
      (w.restrict f hs).eval := by
  cases ha
  cases hb
  rfl

namespace SourceCircuit
variable {a b : Layout P}
variable (w : SourceCircuit a b) (k : ℕ)
  (lam : ∀ e : sourceLocations w, branchLabels w e.1 →
    Fin (min (sourceDims w e).1 (sourceDims w e).2) → ℝ)
  (E : ∀ e : sourceLocations w, branchLabels w e.1 →
    Matrix (Fin (sourceDims w e).1) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)
  (F : ∀ e : sourceLocations w, branchLabels w e.1 →
    Matrix (Fin (sourceDims w e).2) (Fin (min (sourceDims w e).1 (sourceDims w e).2)) ℂ)

/-- The actual sampled endpoint word restricts to the scalar identity at the
exterior owner because both endpoints of every source belong to original parties.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`,
lines 279–309 and 565–588. -/
theorem sampledEndpointWord_none_eval_heq_id
    (ξ ζ : Choices (fun _ ↦ true) w) (j : w.sourceLocations → Fin k)
    (ω : SourceGaussianSamples w k) :
    HEq ((sampledEndpointWord w k lam E F ξ ζ j ω).restrict Option.isNone
      (sources_sampledEndpointWord w k lam E F ξ ζ j ω)).eval
      (ContinuousLinearMap.id ℂ ℂ) := by
  unfold sampledEndpointWord SourceInventory.endpointMatrixWord
  refine (SourceInventory.restrict_endpointWord_eq_nil_and_eval_eq_id
    Option.isNone (partialSlots (fun _ ↦ true) w) w.allSourceU w.allSourceV _ _ ?_ ?_).2
  · intro i
    simp only [(partialSlot_spec (fun _ ↦ true) w i).1, affectedOwner,
      ↓reduceDIte, Option.isNone_some]
  · intro i
    simp only [(partialSlot_spec (fun _ ↦ true) w i).2.1, affectedOwner,
      ↓reduceDIte, Option.isNone_some]

/-- The canonical identification with the private preparation input preserves
the exterior scalar identity. No matrix or scalar is cancelled.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`,
lines 253–267, 279–309 and 565–588. -/
theorem sampledEndpointInputWord_none_eval_heq_id
    (ξ ζ : Choices (fun _ ↦ true) w) (j : w.sourceLocations → Fin k)
    (ω : SourceGaussianSamples w k) :
    HEq ((sampledEndpointInputWord w k lam E F ξ ζ j ω).restrict Option.isNone
      (sources_sampledEndpointInputWord w k lam E F ξ ζ j ω)).eval
      (ContinuousLinearMap.id ℂ ℂ) := by
  unfold sampledEndpointInputWord
  exact (restrict_castLayouts_eval_heq
    (sampledEndpointWord w k lam E F ξ ζ j ω) Option.isNone
    (List.append_nil _).symm (List.append_nil _).symm
    (sources_sampledEndpointWord w k lam E F ξ ζ j ω)).trans
      (sampledEndpointWord_none_eval_heq_id w k lam E F ξ ζ j ω)

end SourceCircuit
end TNLean.PEPS.PairEffect
