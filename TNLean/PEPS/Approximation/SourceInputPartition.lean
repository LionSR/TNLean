/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.CorrectedSourcePartition
import TNLean.PEPS.Approximation.LayoutEqualityCoordinates
import TNLean.PEPS.Approximation.SourceRegisterPermutation
import TNLean.PEPS.Approximation.TensorSchmidtIsometries

/-!
# Corrected and crossing source input registers

Source occurrences retain their original ordered positions when their endpoint
owners are collected into the affected and exterior classes. The original position masks
separate corrected sources from crossing sources even when several occurrences
have the same endpoint owners. The joint crossing vector lives in the literal
affected and exterior free-register memories.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 384–434.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-exterior-input; Theorem 5.2, lines 409–480.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-source-resource-sourceinputpartition-01
TNLean.PEPS.PairEffect.Layout.memCongr_append_tmul
Provenance-ID: 8769-source-resource-sourceinputpartition-02
TNLean.PEPS.PairEffect.Layout.memCongr_apply_heq
Provenance-ID: 8769-source-resource-sourceinputpartition-03
TNLean.PEPS.PairEffect.SourceCircuit.correctedFreeSlots_eq_or
Provenance-ID: 8769-source-resource-sourceinputpartition-04
TNLean.PEPS.PairEffect.SourceCircuit.correctedFreeSlots_masks
Provenance-ID: 8769-source-resource-sourceinputpartition-05
TNLean.PEPS.PairEffect.SourceCircuit.correctedSlotMask
Provenance-ID: 8769-source-resource-sourceinputpartition-06
TNLean.PEPS.PairEffect.SourceCircuit.correctedSlotMask_endpoints
Provenance-ID: 8769-source-resource-sourceinputpartition-07
TNLean.PEPS.PairEffect.SourceCircuit.correctedSourceLayout
Provenance-ID: 8769-source-resource-sourceinputpartition-08
TNLean.PEPS.PairEffect.SourceCircuit.correctedSourceLayout_owners
Provenance-ID: 8769-source-resource-sourceinputpartition-09
TNLean.PEPS.PairEffect.SourceCircuit.crossingSlotMask
Provenance-ID: 8769-source-resource-sourceinputpartition-10
TNLean.PEPS.PairEffect.SourceCircuit.crossingSlotMask_eq_false_of_corrected
Provenance-ID: 8769-source-resource-sourceinputpartition-11
TNLean.PEPS.PairEffect.SourceCircuit.crossingSourceLayout
Provenance-ID: 8769-source-resource-sourceinputpartition-12
TNLean.PEPS.PairEffect.SourceCircuit.exists_sourceCrossing_schmidt
Provenance-ID: 8769-source-resource-sourceinputpartition-13
TNLean.PEPS.PairEffect.SourceCircuit.norm_sourceCrossingVector
Provenance-ID: 8769-source-resource-sourceinputpartition-14
TNLean.PEPS.PairEffect.SourceCircuit.restrict_correctedSourceLayout_append
Provenance-ID: 8769-source-resource-sourceinputpartition-15
TNLean.PEPS.PairEffect.SourceCircuit.sourceCrossingVector
Provenance-ID: 8769-source-resource-sourceinputpartition-16
TNLean.PEPS.PairEffect.SourceInventory.crossingSourceVector
Provenance-ID: 8769-source-resource-sourceinputpartition-17
TNLean.PEPS.PairEffect.SourceInventory.eval_prepareFreeSlots_eq_appendIso_symm
Provenance-ID: 8769-source-resource-sourceinputpartition-18
TNLean.PEPS.PairEffect.SourceInventory.freeSourceVector
Provenance-ID: 8769-source-resource-sourceinputpartition-19
TNLean.PEPS.PairEffect.SourceInventory.mem_freeSlotLayout
Provenance-ID: 8769-source-resource-sourceinputpartition-20
TNLean.PEPS.PairEffect.SourceInventory.norm_crossingSourceVector
Provenance-ID: 8769-source-resource-sourceinputpartition-21
TNLean.PEPS.PairEffect.SourceInventory.norm_freeSourceVector
-/


noncomputable section
open scoped TensorProduct
namespace TNLean.PEPS.PairEffect.Layout
variable {P : Type}

/-- The append identification commutes with equality of its source-register list. -/
theorem memCongr_append_tmul {a b : Layout P} (h : a = b)
    (ℓ : Layout P) (x : Mem a) (y : Mem ℓ) :
    Layout.memCongr (congrArg (· ++ ℓ) h) ((appendIso a ℓ).symm (x ⊗ₜ[ℂ] y)) =
      (appendIso b ℓ).symm (Layout.memCongr h x ⊗ₜ[ℂ] y) := by
  cases h
  rfl

end TNLean.PEPS.PairEffect.Layout

namespace TNLean.PEPS.PairEffect.SourceInventory
variable {P : Type}

/-- The joint source vector has unit norm, including the terminal scalar factor. -/
private theorem norm_vector_eq_one (R : SourceInventory P) (hR : R.IsNormalized) :
    ‖vector R‖ = 1 := by
  induction R with
  | nil => exact norm_one (α := ℂ)
  | cons r R ih =>
    change ‖(TensorProduct.assocIsometry ℂ r.leftSpace r.rightSpace (Mem (layout R)))
      (r.vector ⊗ₜ vector R)‖ = 1
    rw [LinearIsometryEquiv.norm_map, TensorProduct.norm_tmul,
      hR r (List.mem_cons_self), ih (fun s hs ↦ hR s (List.mem_cons_of_mem r hs)),
      one_mul]

/-- The actual joint vector of the selected sources in their fixed register layout. -/
def freeSourceVector (R : SourceInventory P) (U V : Fin R.length → HSpace)
    (free : Fin R.length → Bool) (η : ∀ i, U i ⊗[ℂ] V i) :
    Mem (freeSlotLayout R U V free) :=
  Layout.memCongr (layout_selectedSources_eq R U V free η (fun _ ↦ 0))
    (vector (selectedSources R U V free η))

/-- Preparing the free sources is tensoring with their actual joint vector. -/
theorem eval_prepareFreeSlots_eq_appendIso_symm (R : SourceInventory P)
    (U V : Fin R.length → HSpace) (free : Fin R.length → Bool)
    (η : ∀ i, U i ⊗[ℂ] V i) (ℓ : Layout P) (x : Mem ℓ) :
    (prepareFreeSlots R U V free η ℓ).eval x =
      (appendIso (freeSlotLayout R U V free) ℓ).symm
        (freeSourceVector R U V free η ⊗ₜ[ℂ] x) := by
  rw [prepareFreeSlots, Word.eval_castLayouts]
  change Layout.memCongr _ ((prepare (selectedSources R U V free η) ℓ).eval x) = _
  rw [eval_prepare_eq_appendIso_symm]
  exact Layout.memCongr_append_tmul _ ℓ _ x

/-- A product of normalized selected sources is normalized, including the empty product. -/
theorem norm_freeSourceVector (R : SourceInventory P) (U V : Fin R.length → HSpace)
    (free : Fin R.length → Bool) (η : ∀ i, U i ⊗[ℂ] V i)
    (hη : ∀ i, free i = true → ‖η i‖ = 1) : ‖freeSourceVector R U V free η‖ = 1 := by
  apply (Layout.memCongr (layout_selectedSources_eq R U V free η (fun _ ↦ 0))).norm_map
    (vector (selectedSources R U V free η)) |>.trans
  apply norm_vector_eq_one
  intro s hs
  obtain ⟨i, hi, rfl⟩ := (mem_selectedSources R U V free η s).mp hs
  exact hη i hi

/-- The selected joint vector in the actual affected and exterior register spaces.
Only canonical owner relabelling and the binary register partition are applied. -/
def crossingSourceVector (f : P → Bool) (R : SourceInventory P)
    (U V : Fin R.length → HSpace) (cross : Fin R.length → Bool)
    (η : ∀ i, U i ⊗[ℂ] V i) :
    Mem (Layout.restrict (fun p : Bool ↦ p)
      (Layout.mapOwner f (freeSlotLayout R U V cross))) ⊗[ℂ]
      Mem (Layout.restrict (fun p : Bool ↦ !p)
        (Layout.mapOwner f (freeSlotLayout R U V cross))) :=
  Layout.partitionIso (fun p : Bool ↦ p) (Layout.mapOwner f (freeSlotLayout R U V cross))
    (Layout.mapOwnerIso f (freeSlotLayout R U V cross) (freeSourceVector R U V cross η))

/-- Gathering the two endpoint classes preserves the norm of the exact crossing sources. -/
theorem norm_crossingSourceVector (f : P → Bool) (R : SourceInventory P)
    (U V : Fin R.length → HSpace) (cross : Fin R.length → Bool)
    (η : ∀ i, U i ⊗[ℂ] V i) (hη : ∀ i, cross i = true → ‖η i‖ = 1) :
    ‖crossingSourceVector f R U V cross η‖ = 1 := by
  exact ((Layout.partitionIso (fun p : Bool ↦ p)
    (Layout.mapOwner f (freeSlotLayout R U V cross))).norm_map _).trans
      (((Layout.mapOwnerIso f (freeSlotLayout R U V cross)).norm_map _).trans
        (norm_freeSourceVector R U V cross η hη))

/-- The free registers retain both original endpoint positions and spaces. -/
theorem mem_freeSlotLayout (R : SourceInventory P) (U V : Fin R.length → HSpace)
    (free : Fin R.length → Bool) (r : Reg P) :
    r ∈ freeSlotLayout R U V free ↔ ∃ i : Fin R.length, free i = true ∧
      (r = ⟨(R.get i).left, U i⟩ ∨ r = ⟨(R.get i).right, V i⟩) := by
  simp [freeSlotLayout, selectedSources_eq_map, layout, List.mem_flatMap, PairSource.layout]

end TNLean.PEPS.PairEffect.SourceInventory

namespace TNLean.PEPS.PairEffect.SourceCircuit
open TNLean.PEPS.Approximation SourceInventory
variable {P : Type}

open Classical in
/-- The corrected original occurrences, expressed in the common partial-slot coordinates. -/
def correctedSlotMask {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w)) :
    Fin (partialSlots (correctedMask w S) w).length → Bool :=
  fun i ↦ decide ((partialSlotEquiv (correctedMask w S) w i).1 ∈ S)

/-- Both endpoint registers of each corrected slot lie on the affected side. -/
theorem correctedSlotMask_endpoints {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w)) (i : Fin (partialSlots (correctedMask w S) w).length)
    (hi : correctedSlotMask w S i = true) :
    ((partialSlots (correctedMask w S) w).get i).left.isSome = true ∧
      ((partialSlots (correctedMask w S) w).get i).right.isSome = true := by
  classical
  let e := (partialSlotEquiv (correctedMask w S) w i).1
  have he : e ∈ S := of_decide_eq_true hi
  have hl : correctedMask w S (endpoints w e).1 = true := by
    simp only [correctedMask, decide_eq_true_eq, mem_correctedParties]
    exact ⟨e, he, Or.inl rfl⟩
  have hr : correctedMask w S (endpoints w e).2 = true := by
    simp only [correctedMask, decide_eq_true_eq, mem_correctedParties]
    exact ⟨e, he, Or.inr rfl⟩
  rw [(partialSlot_spec (correctedMask w S) w i).1,
    (partialSlot_spec (correctedMask w S) w i).2.1]
  exact ⟨by simpa [affectedOwner] using hl, by simpa [affectedOwner] using hr⟩

open Classical in
/-- A crossing slot has one endpoint on each side of the actual affected division. -/
def crossingSlotMask {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w)) :
    Fin (partialSlots (correctedMask w S) w).length → Bool :=
  fun i ↦ decide (((partialSlots (correctedMask w S) w).get i).left.isSome ≠
    ((partialSlots (correctedMask w S) w).get i).right.isSome)

/-- The actual free slots are precisely the corrected or crossing slots. -/
theorem correctedFreeSlots_eq_or {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w)) :
    correctedFreeSlots w S = fun i ↦ correctedSlotMask w S i || crossingSlotMask w S i := by
  classical
  funext i
  simp only [correctedFreeSlots, correctedSlotMask, crossingSlotMask, Bool.decide_or]
  rw [(partialSlot_spec (correctedMask w S) w i).1,
    (partialSlot_spec (correctedMask w S) w i).2.1]
  cases hl : correctedMask w S
      (endpoints w (partialSlotEquiv (correctedMask w S) w i).1).1 <;>
    cases hr : correctedMask w S
      (endpoints w (partialSlotEquiv (correctedMask w S) w i).1).2 <;>
    simp [affectedOwner, hl, hr]

/-- A corrected source cannot cross the division generated by its own endpoints. -/
theorem crossingSlotMask_eq_false_of_corrected {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w)) (i : Fin (partialSlots (correctedMask w S) w).length)
    (hi : correctedSlotMask w S i = true) : crossingSlotMask w S i = false := by
  classical
  obtain ⟨hl, hr⟩ := correctedSlotMask_endpoints w S i hi
  unfold crossingSlotMask
  rw [hl, hr]
  rfl

/-- Splitting the free slots at the corrected mask gives exactly the corrected
positions and the exact crossing positions. -/
theorem correctedFreeSlots_masks {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w)) :
    (fun i ↦ correctedFreeSlots w S i && correctedSlotMask w S i) = correctedSlotMask w S ∧
      (fun i ↦ correctedFreeSlots w S i && !correctedSlotMask w S i) = crossingSlotMask w S := by
  constructor <;> funext i
  · rw [correctedFreeSlots_eq_or]
    cases hc : correctedSlotMask w S i <;> simp [hc]
  · rw [correctedFreeSlots_eq_or]
    cases hc : correctedSlotMask w S i
    · simp [hc]
    · simp [hc, crossingSlotMask_eq_false_of_corrected w S i hc]

/-- The crossing source registers with their owners replaced by the actual side. -/
def crossingSourceLayout {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w)) : Layout Bool :=
  Layout.mapOwner (fun p : Option {p // correctedMask w S p = true} ↦ p.isSome)
    (SourceInventory.freeSlotLayout (partialSlots (correctedMask w S) w)
      (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv (correctedMask w S) w i).1).1))
      (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv (correctedMask w S) w i).1).2))
      (crossingSlotMask w S))

/-- The actual product of exact crossing sources, in fixed affected/exterior
register spaces. Only its vectors depend on the partial branch. -/
def sourceCrossingVector {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w)) (ξ : Choices (correctedMask w S) w) :
    Mem (Layout.restrict (fun p : Bool ↦ p) (crossingSourceLayout w S)) ⊗[ℂ]
      Mem (Layout.restrict (fun p : Bool ↦ !p) (crossingSourceLayout w S)) :=
  SourceInventory.crossingSourceVector
    (fun p : Option {p // correctedMask w S p = true} ↦ p.isSome)
    (partialSlots (correctedMask w S) w)
    (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv (correctedMask w S) w i).1).1))
    (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv (correctedMask w S) w i).1).2))
    (crossingSlotMask w S) (partialSlotVector (correctedMask w S) w ξ)

/-- Exact crossing sources have unit norm, with no nonemptiness assumption on
the set of crossings or the family of branch labels. -/
theorem norm_sourceCrossingVector {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w)) (ξ : Choices (correctedMask w S) w) :
    ‖sourceCrossingVector w S ξ‖ = 1 := by
  exact SourceInventory.norm_crossingSourceVector _ _ _ _ _ _
    (fun i _ ↦ sourceVectorAt_norm w _ _)

/-- Exact crossing sources have a probability Schmidt expansion in their actual
local input memories. The endpoint isometries need not span those memories. -/
theorem exists_sourceCrossing_schmidt {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w)) (ξ : Choices (correctedMask w S) w) :
    ∃ (r : ℕ) (lam : Fin r → ℝ)
      (F : EuclideanSpace ℂ (Fin r) →ₗᵢ[ℂ]
        Mem (Layout.restrict (fun p : Bool ↦ p) (crossingSourceLayout w S)))
      (G : EuclideanSpace ℂ (Fin r) →ₗᵢ[ℂ]
        Mem (Layout.restrict (fun p : Bool ↦ !p) (crossingSourceLayout w S))),
      (∀ j, 0 ≤ lam j) ∧ ∑ j, lam j = 1 ∧
        sourceCrossingVector w S ξ = ∑ j, (Real.sqrt (lam j) : ℂ) •
          (F (EuclideanSpace.basisFun (Fin r) ℂ j) ⊗ₜ[ℂ]
            G (EuclideanSpace.basisFun (Fin r) ℂ j)) := by
  exact PairSource.exists_probability_schmidt_isometries
    (Mem (Layout.restrict (fun p : Bool ↦ p) (crossingSourceLayout w S)))
    (Mem (Layout.restrict (fun p : Bool ↦ !p) (crossingSourceLayout w S)))
    (sourceCrossingVector w S ξ) (norm_sourceCrossingVector w S ξ)

/-- Corrected source registers with their actual two-side owner labels. -/
def correctedSourceLayout {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w)) : Layout Bool :=
  Layout.mapOwner (fun p : Option {p // correctedMask w S p = true} ↦ p.isSome)
    (freeSlotLayout (partialSlots (correctedMask w S) w)
      (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv (correctedMask w S) w i).1).1))
      (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv (correctedMask w S) w i).1).2))
      (correctedSlotMask w S))
/-- Both registers of every corrected source belong to the affected side. -/
theorem correctedSourceLayout_owners {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w)) :
    ∀ r ∈ correctedSourceLayout w S, r.owner = true := by
  intro r hr
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
  obtain ⟨i, hi, rfl | rfl⟩ := (mem_freeSlotLayout _ _ _ _ s).mp hs
  · exact (correctedSlotMask_endpoints w S i hi).1
  · exact (correctedSlotMask_endpoints w S i hi).2
/-- After the corrected block is placed first, only its affected factor grows. -/
theorem restrict_correctedSourceLayout_append {a b : Layout P} (w : SourceCircuit a b)
    (S : Finset (sourceLocations w)) :
    Layout.restrict (fun p : Bool ↦ p) (correctedSourceLayout w S ++ crossingSourceLayout w S) =
        correctedSourceLayout w S ++
          Layout.restrict (fun p : Bool ↦ p) (crossingSourceLayout w S) ∧
      Layout.restrict (fun p : Bool ↦ !p)
          (correctedSourceLayout w S ++ crossingSourceLayout w S) =
        Layout.restrict (fun p : Bool ↦ !p) (crossingSourceLayout w S) := by
  constructor
  · rw [Layout.restrict_append,
      Layout.restrict_eq_self_of_owner _ (correctedSourceLayout_owners w S) rfl]
  · rw [Layout.restrict_append,
      Layout.restrict_eq_nil_of_owner _ (correctedSourceLayout_owners w S) rfl,
      List.nil_append]


end TNLean.PEPS.PairEffect.SourceCircuit
