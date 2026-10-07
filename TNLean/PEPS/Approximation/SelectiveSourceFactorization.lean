/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SelectiveSourcePreparation
import TNLean.PEPS.Approximation.PartyCoarseningFactorization

/-!
# Local factors after selective source preparation

Fix the source slots that remain free and prepare every other source locally
within one side of a party partition. Composing this preparation with an actual
source-free allowed word gives two source-free local contractions. These
contractions are chosen independently of the vectors later supplied to the free
slots, and their product recovers every such completed preparation.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, the internal preparations and contractions on all free
inputs, lines 409–434.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-block-contraction.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.

Provenance-ID: 8769-selective-factorization-word.exists_selective_partition
Downstream declaration: TNLean.PEPS.PairEffect.Word.exists_selective_partition
-/

noncomputable section
open scoped TensorProduct
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect.Word
open SourceInventory
variable {P : Type}

/-- Preparing only internal sources gives two fixed local contractions, uniformly
in every remaining source vector. Every source whose endpoints lie on different
sides must be selected as free. No normalization condition is imposed on the free
vectors, and the two factors are chosen before those vectors.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434. -/
theorem exists_selective_partition (f : P → Bool) (R : SourceInventory P)
    (U V : Fin R.length → HSpace) (free : Fin R.length → Bool)
    (fixed : ∀ i, free i = false → U i ⊗[ℂ] V i)
    (hfixed : ∀ i h, ‖fixed i h‖ = 1)
    (hmask : ∀ i, free i = false → f (R.get i).left = f (R.get i).right)
    (ℓ : Layout P) {ℓ' : Layout P}
    (v : Word (slotLayout R U V ++ ℓ) ℓ') (hv : v.IsAllowed) (hs : v.sources = []) :
    let L := freeSlotLayout R U V free ++ ℓ
    let split (a : Layout P) :=
      isoL (Layout.partitionIso (fun b : Bool ↦ b) (Layout.mapOwner f a)) ∘L
        isoL (Layout.mapOwnerIso f a)
    ∃ a : Word (Layout.restrict (fun b : Bool ↦ b) (Layout.mapOwner f L))
        (Layout.restrict (fun b : Bool ↦ b) (Layout.mapOwner f ℓ')),
      ∃ b : Word (Layout.restrict (fun b : Bool ↦ !b) (Layout.mapOwner f L))
          (Layout.restrict (fun b : Bool ↦ !b) (Layout.mapOwner f ℓ')),
        a.IsAllowed ∧ b.IsAllowed ∧ a.sources = [] ∧ b.sources = [] ∧
        ‖a.eval‖ ≤ 1 ∧ ‖b.eval‖ ≤ 1 ∧
        split ℓ' ∘L (v.eval ∘L (prepareSelected R U V free fixed ℓ).eval) =
          TensorProduct.mapL a.eval b.eval ∘L split L ∧
        ∀ ζ : ∀ i, U i ⊗[ℂ] V i,
          split ℓ' ∘L (v.eval ∘L
              (prepareSlots R U V (fillSourceVectors R U V free fixed ζ) ℓ).eval) =
            TensorProduct.mapL a.eval b.eval ∘L split L ∘L
              (prepareFreeSlots R U V free ζ ℓ).eval := by
  let J := prepareSelected R U V free fixed ℓ
  have hJ : J.IsAllowed := isAllowed_prepareSelected R U V free fixed hfixed ℓ
  have hint : ∀ s ∈ (Word.comp J v).sources, f s.left = f s.right := by
    intro s hmem
    have hmemJ : s ∈ J.sources := by
      simpa only [sources, hs, List.nil_append] using hmem
    obtain ⟨i, hi, rfl⟩ := (mem_sources_prepareSelected R U V free fixed ℓ s).mp hmemJ
    exact hmask i hi
  obtain ⟨a, b, ha, hb, hsa, hsb, hna, hnb, he⟩ :=
    exists_partition_of_sources_internal f (.comp J v) ⟨hJ, hv⟩ hint
  refine ⟨a, b, ha, hb, hsa, hsb, hna, hnb, he, ?_⟩
  intro ζ
  rw [← eval_prepareSelected_prepareFreeSlots]
  simpa only [eval_comp, comp_assoc] using
    congrArg (fun T ↦ T ∘L (prepareFreeSlots R U V free ζ ℓ).eval) he

end TNLean.PEPS.PairEffect.Word
