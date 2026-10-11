/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceInputPartition

/-!
# Corrected inputs followed by exact crossing inputs

One source-free register permutation puts the corrected source positions first
and the crossing source positions second, retaining the original order within
each block. It is chosen before the branch and before the input source vectors.
The actual partially prepared circuit therefore has two local contraction
factors on these common input spaces.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-exterior-input; Theorem 5.2, lines 409–480.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
-/


noncomputable section
open scoped TensorProduct
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect.SourceCircuit
open TNLean.PEPS.Approximation
open SourceInventory
variable {P : Type}

/-- One actual source-free permutation recovers the original free-slot order
from the corrected and crossing blocks, uniformly for all their vectors. -/
theorem exists_correctedInputReordering {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w)) :
    let A := correctedMask w S
    let R := partialSlots A w
    let U := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1)
    let V := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2)
    let ℓ := Layout.mapOwner (affectedOwner A) a
    ∃ u : Word
      (freeSlotLayout R U V (correctedSlotMask w S) ++
        (freeSlotLayout R U V (crossingSlotMask w S) ++ ℓ))
      (freeSlotLayout R U V (correctedFreeSlots w S) ++ ℓ),
      u.IsAllowed ∧ u.sources = [] ∧ ∀ η : ∀ i, U i ⊗[ℂ] V i,
        u.eval ∘L (prepareFreeSlots R U V (correctedSlotMask w S) η
          (freeSlotLayout R U V (crossingSlotMask w S) ++ ℓ)).eval ∘L
            (prepareFreeSlots R U V (crossingSlotMask w S) η ℓ).eval =
          (prepareFreeSlots R U V (correctedFreeSlots w S) η ℓ).eval := by
  intro A R U V ℓ
  have h := exists_reorderFreeSlots R U V (correctedFreeSlots w S) (correctedSlotMask w S) ℓ
  rw [(correctedFreeSlots_masks w S).1, (correctedFreeSlots_masks w S).2] at h
  exact h

/-- Composing the actual selectively prepared partial circuit with a source-free
register rearrangement gives two genuine local contractions on all its inputs. -/
theorem isTensorPartitioned_reordered_partial {a b : Layout P}
    (w : SourceCircuit a b) (hw : w.IsAllowed) (S : Finset (sourceLocations w)) :
    let A := correctedMask w S
    let R := partialSlots A w
    let U := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1)
    let V := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2)
    let ℓ := Layout.mapOwner (affectedOwner A) a
    let free := correctedFreeSlots w S
    let fixed : ∀ _ξ : Choices A w, ∀ i : Fin R.length, free i = false → U i ⊗[ℂ] V i :=
      fun ξ i _ ↦ partialSlotVector A w ξ i
    ∀ (k : Layout (Option {p // A p = true}))
      (u : Word k (freeSlotLayout R U V free ++ ℓ)),
      u.IsAllowed → u.sources = [] → ∀ ξ : Choices A w,
        Word.IsTensorPartitioned (fun p : Option {p // A p = true} ↦ p.isSome)
          (Word.comp u (Word.comp
            (ℓ₁ := freeSlotLayout R U V free ++ ℓ)
            (ℓ₂ := slotLayout R U V ++ ℓ)
            (ℓ₃ := Layout.mapOwner (affectedOwner A) b)
            (prepareSelected R U V free (fixed ξ) ℓ) (partialResidual A w ξ))) := by
  intro A R U V ℓ free fixed k u hu hus ξ
  let v := Word.comp u (Word.comp (prepareSelected R U V free (fixed ξ) ℓ)
    (partialResidual A w ξ))
  have hv : v.IsAllowed := ⟨hu, isAllowed_prepareSelected R U V free (fixed ξ)
    (fun i _ ↦ (exists_partial_source_preparation_with_original_vectors A w hw).1 ξ i) ℓ,
    isAllowed_partialResidual A w hw ξ⟩
  have hs : ∀ s ∈ v.sources, s.left.isSome = s.right.isSome := by
    intro s hs
    simp only [v, Word.sources, sources_partialResidual, hus, List.nil_append,
      List.append_nil] at hs
    obtain ⟨i, hi, rfl⟩ := (mem_sources_prepareSelected R U V free (fixed ξ) ℓ s).mp hs
    have hcross : crossingSlotMask w S i = false := by
      have h := congrFun (correctedFreeSlots_eq_or w S) i
      change correctedFreeSlots w S i = false at hi
      rw [hi] at h
      exact (Bool.or_eq_false_iff.mp h.symm).2
    exact not_not.mp (of_decide_eq_false hcross)
  obtain ⟨c, d, hc, hd, hcs, hds, hcn, hdn, hprod⟩ :=
    Word.exists_partition_of_sources_internal (fun p ↦ p.isSome) v hv hs
  exact ⟨c, d, hc, hd, hcs, hds, hcn, hdn, fun x ↦ DFunLike.congr_fun hprod x⟩


/-- Absorb a genuine source-free initial preparation before separating the
partial circuit. The only remaining free registers are the corrected and
crossing sources; the two local words are contractions on all of those inputs. -/
theorem isTensorPartitioned_prepared_reordered_partial {a b : Layout P}
    (w : SourceCircuit a b) (hw : w.IsAllowed) (S : Finset (sourceLocations w))
    (p₀ : Word [] a) (hp₀ : p₀.IsAllowed) (hp₀s : p₀.sources = []) :
    let A := correctedMask w S
    let R := partialSlots A w
    let U := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1)
    let V := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2)
    let ℓ := Layout.mapOwner (affectedOwner A) a
    let C := freeSlotLayout R U V (correctedSlotMask w S)
    let T := freeSlotLayout R U V (crossingSlotMask w S)
    let free := correctedFreeSlots w S
    let fixed : ∀ _ξ : Choices A w, ∀ i : Fin R.length, free i = false → U i ⊗[ℂ] V i :=
      fun ξ i _ ↦ partialSlotVector A w ξ i
    let p := (Word.frameList (C ++ T) (p₀.mapOwner (affectedOwner A))).castLayouts
      (List.append_nil _) (List.append_assoc C T ℓ)
    ∀ u : Word (C ++ (T ++ ℓ)) (freeSlotLayout R U V free ++ ℓ),
      u.IsAllowed → u.sources = [] → ∀ ξ : Choices A w,
        Word.IsTensorPartitioned (fun p : Option {p // A p = true} ↦ p.isSome)
          (Word.comp (Word.comp p u) (Word.comp
            (ℓ₁ := freeSlotLayout R U V free ++ ℓ)
            (ℓ₂ := slotLayout R U V ++ ℓ)
            (ℓ₃ := Layout.mapOwner (affectedOwner A) b)
            (prepareSelected R U V free (fixed ξ) ℓ) (partialResidual A w ξ))) := by
  intro A R U V ℓ C T free fixed p u hu hus ξ
  have hp : p.IsAllowed := (Word.isAllowed_castLayouts _ _ _).mpr
    (Word.isAllowed_frameList _ (Word.isAllowed_mapOwner _ p₀ hp₀) _)
  have hps : p.sources = [] := by
    simp only [p, Word.sources_castLayouts, Word.sources_frameList,
      Word.sources_mapOwner, hp₀s, SourceInventory.mapOwner]
    rfl
  exact isTensorPartitioned_reordered_partial w hw S (C ++ T) (.comp p u)
    ⟨hp, hu⟩ (by simp [Word.sources, hps, hus]) ξ

end TNLean.PEPS.PairEffect.SourceCircuit
