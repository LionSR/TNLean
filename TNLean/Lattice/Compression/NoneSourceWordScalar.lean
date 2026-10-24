/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.NoneResidualScalar
import TNLean.Lattice.Compression.SourcePrivatePreparationRestriction
import TNLean.Lattice.Compression.LayoutExcludedOwners

/-! # The auxiliary scalar after preparation of the original private input

The recorded private preparation contributes the identity at the exterior owner.
Composing it with the actual chronological residual therefore retains the product
of the original coefficient sums of empty-party gates. This product may vanish.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 137–139, 246–267 and 565–588.
-/

noncomputable section
open ContinuousLinearMap
namespace TNLean
open TNLean.Lattice.PartyCircuit
namespace Lattice.PartyCircuit
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

/-- Source-free restrictions compose before instantiating any chronological
source data. When all selected memories are empty, their scalars multiply.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 246–267 and 565–588. -/
private theorem restrict_comp_scalar_heq {Q : Type} (f : Q → Bool)
    {a b c : Layout Q} (u : Word a b) (v : Word b c)
    (hu : u.sources = []) (hv : v.sources = [])
    (ha : Layout.restrict f a = []) (hb : Layout.restrict f b = [])
    (hc : Layout.restrict f c = []) (α β : ℂ)
    (hA : HEq ((u.restrict f hu).eval) (α • ContinuousLinearMap.id ℂ ℂ))
    (hB : HEq ((v.restrict f hv).eval) (β • ContinuousLinearMap.id ℂ ℂ)) :
    HEq (((u.comp v).restrict f
      (by simp only [Word.sources, hu, hv, List.nil_append])).eval)
      ((α * β) • ContinuousLinearMap.id ℂ ℂ) := by
  have hcomp : ((u.comp v).restrict f
      (by simp only [Word.sources, hu, hv, List.nil_append])).eval =
      (v.restrict f hv).eval ∘L (u.restrict f hu).eval := rfl
  exact (heq_of_eq hcomp).trans
    (scalar_comp_heq (u.restrict f hu).eval (v.restrict f hv).eval ha hb hc α β hA hB)

end Lattice.PartyCircuit
namespace Lattice.PartyCircuit.SourceCircuit
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
  have h := restrict_comp_scalar_heq Option.isNone
    (w.sourcePrivatePreparation ψ) (partialResidual (fun _ : P ↦ true) w ξ)
    (sources_sourcePrivatePreparation w ψ) (sources_partialResidual (fun _ : P ↦ true) w ξ)
    (by simp only [Layout.restrict_append, restrict_allResidualSourceLayout_isNone w,
      Layout.restrict_nil, List.nil_append])
    (by simp only [Layout.restrict_append, restrict_allResidualSourceLayout_isNone w,
      hm a, List.nil_append])
    (hm b) 1 w.emptyGateScalar (by simpa only [one_smul] using hp) hr
  simpa only [partialSourceWord, one_mul] using h

end Lattice.PartyCircuit.SourceCircuit
end TNLean
