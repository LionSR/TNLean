/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceCircuitLifetime
import TNLean.PEPS.Approximation.SourceResidualCoordinates
import TNLean.PEPS.Approximation.SelectiveSourceFactorization

/-!
# Local factors on the corrected and crossing source registers

The selected original source occurrences and every source crossing the affected
party division remain free. All other surviving sources are prepared with their
original normalized vectors. The resulting canonical word factors into two
allowed source-free local contractions on the entire free input memory. Its
input and output register spaces are independent of the branch.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-exterior-input.
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

open Classical in
/-- Retain the corrected occurrences and all exact crossing sources as free inputs.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434. -/
def correctedFreeSlots {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w)) : Fin (partialSlots (correctedMask w S) w).length → Bool :=
  fun i ↦ decide ((partialSlotEquiv (correctedMask w S) w i).1 ∈ S ∨
    correctedMask w S (endpoints w (partialSlotEquiv (correctedMask w S) w i).1).1 ≠
      correctedMask w S (endpoints w (partialSlotEquiv (correctedMask w S) w i).1).2)

/-- The free mask depends only on original positions and their endpoint partition.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434. -/
theorem correctedFreeSlots_eq_true_iff {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w)) (i : Fin (partialSlots (correctedMask w S) w).length) :
    correctedFreeSlots w S i = true ↔
      (partialSlotEquiv (correctedMask w S) w i).1 ∈ S ∨
        correctedMask w S (endpoints w (partialSlotEquiv (correctedMask w S) w i).1).1 ≠
          correctedMask w S (endpoints w (partialSlotEquiv (correctedMask w S) w i).1).2 := by
  classical
  simp only [correctedFreeSlots, decide_eq_true_eq]

/-- Each corrected original occurrence is represented by a free slot.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434. -/
theorem exists_correctedFreeSlot {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w)) (e : sourceLocations w) (he : e ∈ S) :
    ∃ i : Fin (partialSlots (correctedMask w S) w).length,
      (partialSlotEquiv (correctedMask w S) w i).1 = e ∧ correctedFreeSlots w S i = true := by
  classical
  have hl : correctedMask w S (endpoints w e).1 = true := by
    simp only [correctedMask, decide_eq_true_eq, mem_correctedParties]
    exact ⟨e, he, Or.inl rfl⟩
  let j := (partialSlotEquiv (correctedMask w S) w).symm ⟨e, Or.inl hl⟩
  have hj : (partialSlotEquiv (correctedMask w S) w j).1 = e :=
    congrArg Subtype.val ((partialSlotEquiv (correctedMask w S) w).apply_symm_apply _)
  refine ⟨j, hj, (correctedFreeSlots_eq_true_iff w S j).mpr ?_⟩
  exact Or.inl (hj.symm ▸ he)

/-- The two sides of a grouped party are determined by whether it is affected. -/
private theorem isSome_affectedOwner (A : P → Bool) (p : P) :
    (affectedOwner A p).isSome = A p := by
  cases h : A p <;> simp [affectedOwner, h]

/-- Every source prepared in advance has both endpoints on the same side.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–417. -/
private theorem correctedFreeSlots_internal {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w)) (i : Fin (partialSlots (correctedMask w S) w).length)
    (hi : correctedFreeSlots w S i = false) :
    ((partialSlots (correctedMask w S) w).get i).left.isSome =
      ((partialSlots (correctedMask w S) w).get i).right.isSome := by
  have hnot : ¬ correctedFreeSlots w S i = true := by simp [hi]
  rw [correctedFreeSlots_eq_true_iff] at hnot
  have he := not_or.mp hnot |>.2
  rw [(partialSlot_spec (correctedMask w S) w i).1,
    (partialSlot_spec (correctedMask w S) w i).2.1,
    isSome_affectedOwner, isSome_affectedOwner]
  exact not_not.mp he

end TNLean.PEPS.PairEffect.SourceCircuit

namespace TNLean.PEPS.PairEffect.Word
open SourceInventory

/-- The operator of a word is a tensor product of two actual local
contractions after grouping the two classes of owners. The factors are allowed
source-free words, and the identity holds on the entire input memory.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434. -/
def IsTensorPartitioned {Q : Type} (f : Q → Bool) {a b : Layout Q}
    (W : Word a b) : Prop :=
  ∃ c : Word (Layout.restrict (fun x : Bool ↦ x) (Layout.mapOwner f a))
      (Layout.restrict (fun x : Bool ↦ x) (Layout.mapOwner f b)),
    ∃ d : Word (Layout.restrict (fun x : Bool ↦ !x) (Layout.mapOwner f a))
        (Layout.restrict (fun x : Bool ↦ !x) (Layout.mapOwner f b)),
      c.IsAllowed ∧ d.IsAllowed ∧ c.sources = [] ∧ d.sources = [] ∧
      ‖c.eval‖ ≤ 1 ∧ ‖d.eval‖ ≤ 1 ∧
      ∀ x : Mem a,
        Layout.partitionIso (fun z : Bool ↦ z) (Layout.mapOwner f b)
          (Layout.mapOwnerIso f b (W.eval x)) =
        TensorProduct.mapL c.eval d.eval
          (Layout.partitionIso (fun z : Bool ↦ z) (Layout.mapOwner f a)
            (Layout.mapOwnerIso f a x))

/-- Preparing only sources internal to one side produces this factorization
on all remaining free source registers. -/
private theorem isTensorPartitioned_selected {Q : Type} (f : Q → Bool)
    (R : SourceInventory Q) (U V : Fin R.length → HSpace)
    (free : Fin R.length → Bool) (fixed : ∀ i, free i = false → U i ⊗[ℂ] V i)
    (hfixed : ∀ i h, ‖fixed i h‖ = 1)
    (hmask : ∀ i, free i = false → f (R.get i).left = f (R.get i).right)
    (a b : Layout Q) (v : Word (slotLayout R U V ++ a) b)
    (hv : v.IsAllowed) (hvs : v.sources = []) :
    IsTensorPartitioned f (.comp (prepareSelected R U V free fixed a) v) := by
  obtain ⟨c, d, hc, hd, hcs, hds, hcn, hdn, hprod, _⟩ :=
    Word.exists_selective_partition f R U V free fixed hfixed hmask a v hv hvs
  exact ⟨c, d, hc, hd, hcs, hds, hcn, hdn, fun x ↦ DFunLike.congr_fun hprod x⟩

end TNLean.PEPS.PairEffect.Word

namespace TNLean.PEPS.PairEffect.SourceCircuit
open TNLean.PEPS.Approximation
open SourceInventory
variable {P : Type}

/-- The corrected and crossing occurrences form common free input spaces for
all partial monomials. Their canonical remaining operations have two actual
local contraction factors on the entire free-source memory, chosen before any
free source vectors are supplied. The spaces are independent of the branch.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434. -/
theorem exists_corrected_source_partition {a b : Layout P}
    (w : SourceCircuit a b) (hw : w.IsAllowed) (S : Finset (sourceLocations w)) :
    let A := correctedMask w S
    let R := partialSlots A w
    let U := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1)
    let V := fun i : Fin R.length ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2)
    let free : Fin R.length → Bool := correctedFreeSlots w S
    let fixed : ∀ _ξ : Choices A w, ∀ i : Fin R.length, free i = false → U i ⊗[ℂ] V i :=
      fun ξ i _ ↦ partialSlotVector A w ξ i
    ∀ ξ : Choices A w,
      Word.IsTensorPartitioned (fun p : Option {p // A p = true} ↦ p.isSome)
        (.comp (prepareSelected R U V free (fixed ξ) (Layout.mapOwner (affectedOwner A) a))
          (partialResidual A w ξ)) := by
  intro A R U V free fixed ξ
  exact Word.isTensorPartitioned_selected _ R U V free (fixed ξ)
    (fun i _ ↦ (exists_partial_source_preparation_with_original_vectors A w hw).1 ξ i)
    (correctedFreeSlots_internal w S) _ _ (partialResidual A w ξ)
    (isAllowed_partialResidual A w hw ξ) (sources_partialResidual A w ξ)

end TNLean.PEPS.PairEffect.SourceCircuit
