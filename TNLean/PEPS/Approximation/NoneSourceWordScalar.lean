/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.NoneResidualScalar
import TNLean.PEPS.Approximation.SourcePrivatePreparationRestriction
import TNLean.PEPS.Approximation.LayoutExcludedOwners

/-! # The auxiliary scalar after preparation of the original private input

The recorded private preparation contributes the identity at the exterior owner.
Composing it with the actual chronological residual therefore retains the product
of the original coefficient sums of empty-party gates. This product may vanish.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 137–139, 246–267 and 565–588.
-/

noncomputable section
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect
private theorem scalar_comp_heq {Q : Type} {a b d : Layout Q}
    (A : Mem a →L[ℂ] Mem b) (B : Mem b →L[ℂ] Mem d)
    (ha : a = []) (hb : b = []) (hd : d = []) (α β : ℂ)
    (hA : HEq A (α • ContinuousLinearMap.id ℂ ℂ))
    (hB : HEq B (β • ContinuousLinearMap.id ℂ ℂ)) :
    HEq (B ∘L A) ((α * β) • ContinuousLinearMap.id ℂ ℂ) := by
  cases ha
  cases hb
  cases hd
  apply heq_of_eq
  rw [eq_of_heq hA, eq_of_heq hB]
  ext
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, smul_smul, mul_comm]

namespace SourceCircuit
variable {P : Type}

/-- The actual prepared source word has the original empty-gate scalar as its
exterior restriction. No monomial, input vector or coefficient sum is normalized.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`,
lines 137–139, 246–267 and 565–588. -/
theorem restrict_partialSourceWord_all_eval_heq_emptyGateScalar
    {a b : Layout P} (w : SourceCircuit a b) (ψ : ProductInput a)
    (ξ : Choices (fun _ : P ↦ true) w) :
    HEq (((w.partialSourceWord ψ ξ).restrict Option.isNone
      (sources_partialSourceWord w ψ ξ)).eval)
      (w.emptyGateScalar • ContinuousLinearMap.id ℂ ℂ) := by
  have hm (L : Layout P) : Layout.restrict Option.isNone
      (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) L) = [] :=
    Layout.restrict_mapOwner_eq_nil _ _ L (by intro p; simp [affectedOwner])
  have hp := restrict_sourcePrivatePreparation_none_eval_heq_id w ψ
  have hr := restrict_partialResidual_all_eval_heq_emptyGateScalar w ξ
  rw [partialSourceWord, Word.restrict, Word.eval_comp]
  have h := scalar_comp_heq
    ((w.sourcePrivatePreparation ψ).restrict Option.isNone
      (sources_sourcePrivatePreparation w ψ)).eval
    ((partialResidual (fun _ : P ↦ true) w ξ).restrict Option.isNone
      (sources_partialResidual (fun _ : P ↦ true) w ξ)).eval
    (by simp only [Layout.restrict_append, restrict_allResidualSourceLayout_isNone w,
      Layout.restrict_nil, List.nil_append])
    (by simp only [Layout.restrict_append, restrict_allResidualSourceLayout_isNone w,
      hm a, List.nil_append])
    (hm b) 1 w.emptyGateScalar (by simpa only [one_smul] using hp) hr
  simpa only [one_mul] using h

end SourceCircuit
end TNLean.PEPS.PairEffect
