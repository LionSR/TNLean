/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.WordOwnerMap
import TNLean.PEPS.Approximation.PartyFactorization

/-!
# Two-side factorization with internal source preparations

If every pair source has its endpoints on the same side of a specified partition,
changing the owners to the two sides converts every source into a local
preparation. The two actual restrictions then give a tensor product of
contractions, with the original operator recovered through the canonical memory
identifications. The internal-source condition is checked on the original word.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, internal preparations and the two separated contractions,
lines 409–427. This is the factorization after the crossing and corrected source
registers have been made free inputs; their chronological construction is separate.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-block-contraction.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.

Provenance-ID: 8769-party-coarsening-factorization-word.exists_partition_of_sources_internal
Downstream declaration: TNLean.PEPS.PairEffect.Word.exists_partition_of_sources_internal
-/

noncomputable section

open ContinuousLinearMap

namespace TNLean.PEPS.PairEffect.Word

/-- If every original source is internal to one side, the two actual restricted
compositions are source-free contractions whose tensor product is the original
operator in canonical two-side coordinates.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–427. -/
theorem exists_partition_of_sources_internal {P : Type} (f : P → Bool)
    {ℓ ℓ' : Layout P} (w : Word ℓ ℓ') (hw : w.IsAllowed)
    (hS : ∀ s ∈ w.sources, f s.left = f s.right) :
    ∃ a : Word (Layout.restrict (fun b : Bool ↦ b) (Layout.mapOwner f ℓ))
        (Layout.restrict (fun b : Bool ↦ b) (Layout.mapOwner f ℓ')),
      ∃ b : Word (Layout.restrict (fun b : Bool ↦ !b) (Layout.mapOwner f ℓ))
          (Layout.restrict (fun b : Bool ↦ !b) (Layout.mapOwner f ℓ')),
        a.IsAllowed ∧ b.IsAllowed ∧ a.sources = [] ∧ b.sources = [] ∧
        ‖a.eval‖ ≤ 1 ∧ ‖b.eval‖ ≤ 1 ∧
        (isoL (Layout.partitionIso (fun b : Bool ↦ b) (Layout.mapOwner f ℓ')) ∘L
          isoL (Layout.mapOwnerIso f ℓ')) ∘L w.eval =
          TensorProduct.mapL a.eval b.eval ∘L
            (isoL (Layout.partitionIso (fun b : Bool ↦ b) (Layout.mapOwner f ℓ)) ∘L
              isoL (Layout.mapOwnerIso f ℓ)) := by
  have hs : (w.mapOwner f).sources = [] := by
    rw [sources_mapOwner, SourceInventory.mapOwner_eq_nil_iff]
    exact hS
  have hmw := isAllowed_mapOwner f w hw
  have ha := isAllowed_restrict (fun b : Bool ↦ b) (w.mapOwner f) hs hmw
  have hb := isAllowed_restrict (fun b : Bool ↦ !b) (w.mapOwner f) hs hmw
  refine ⟨(w.mapOwner f).restrict (fun b : Bool ↦ b) hs,
    (w.mapOwner f).restrict (fun b : Bool ↦ !b) hs, ha, hb,
    sources_restrict _ _ _, sources_restrict _ _ _,
    norm_eval_le_one _ ha, norm_eval_le_one _ hb, ?_⟩
  have hp := partitionIso_eval (fun b : Bool ↦ b) (w.mapOwner f) hs
  rw [comp_assoc, ← eval_mapOwner_comp, ← comp_assoc, hp, comp_assoc]

end TNLean.PEPS.PairEffect.Word
