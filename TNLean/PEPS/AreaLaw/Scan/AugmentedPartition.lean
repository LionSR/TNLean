/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.PhysicalPartition
import QICLean.Representation.ReplicaTransport.Setup

/-!
# Auxiliary factors and physical scanner partitions

The scanner's near and far sides acquire the fixed auxiliary factors C and R.
The near side retains the target X: this is the physical partition P=CXU of
Section 9, not the smaller entropy region U. No replica parameter or quantum
state enters the partition or its moves.
-/

namespace TNLean.PEPS.AreaLaw.Scan

open TensorPower.ReplicaTransport

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Adjoin C on the near side and R on the far side. -/
def augmentedState (σ : PhysicalPartition V) : PhysicalPartition (V ⊕ Bool) :=
  Sum.elim σ some

/-- The actual physical partition with its two fixed auxiliary factors. -/
def augmentedPartition (σ : PhysicalPartition V) : PYF (V ⊕ Bool) :=
  ⟨receiving (augmentedState σ) false, middle (augmentedState σ),
    receiving (augmentedState σ) true⟩

/-- The augmented near, middle and far regions partition every tensor factor. -/
theorem augmentedPartition_isPartition (σ : PhysicalPartition V) :
    (augmentedPartition σ).IsPartition := by
  simp only [PYF.IsPartition, augmentedPartition, receiving, middle]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Finset.disjoint_filter.mpr fun _ _ h ↦ by simp_all
  · exact Finset.disjoint_filter.mpr fun _ _ h ↦ by simp_all
  · exact Finset.disjoint_filter.mpr fun _ _ h ↦ by simp_all
  · ext x
    cases h : augmentedState σ x with
    | none => simp [h]
    | some b => cases b <;> simp [h]

/-- Augmentation preserves the physical ordered-band inclusion. -/
theorem augmentedPartition_nested {σ τ : PhysicalPartition V}
    (h : receiving σ false ∪ middle σ ⊆ receiving τ false) :
    (augmentedPartition σ).P ∪ (augmentedPartition σ).Y ⊆
      (augmentedPartition τ).P := by
  intro x hx
  cases x with
  | inl x =>
    have hx' : x ∈ receiving σ false ∪ middle σ := by
      simpa only [augmentedPartition, receiving, middle, Finset.mem_union,
        Finset.mem_filter, Finset.mem_univ, true_and, augmentedState, Sum.elim_inl] using hx
    simpa only [augmentedPartition, receiving, Finset.mem_filter, Finset.mem_univ,
      true_and, augmentedState, Sum.elim_inl] using h hx'
  | inr b =>
    cases b <;> simp_all only [augmentedPartition, receiving, middle, Finset.mem_union,
      Finset.mem_filter, Finset.mem_univ, true_and, augmentedState, Sum.elim_inr,
      Option.some.injEq, Bool.true_eq_false, reduceCtorEq, or_self]

/-- Move the unassigned physical part only; auxiliary factors never move. -/
def augmentedMove (σ : PhysicalPartition V) (side : Bool) (B : Finset V) : Move (V ⊕ Bool) :=
  if side then .toF ((B ∩ middle σ).map ⟨Sum.inl, Sum.inl_injective⟩)
  else .toP ((B ∩ middle σ).map ⟨Sum.inl, Sum.inl_injective⟩)

/-- The actual moved subsystem is contained in the augmented middle. -/
theorem augmentedMove_isValid (σ : PhysicalPartition V) (side : Bool) (B : Finset V) :
    (augmentedMove σ side B).IsValid (augmentedPartition σ) := by
  cases side <;> simp only [augmentedMove, Bool.false_eq_true, ↓reduceIte,
    Move.IsValid, Move.subsystem]
  all_goals
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    simpa only [augmentedPartition, middle, Finset.mem_filter, Finset.mem_univ,
      true_and, augmentedState, Sum.elim_inl] using (Finset.mem_inter.mp hy).2

/-- Applying the physical move agrees with assigning its previously unassigned sites. -/
theorem augmentedMove_apply (σ : PhysicalPartition V) (side : Bool) (B : Finset V) :
    (augmentedMove σ side B).apply (augmentedPartition σ) =
      augmentedPartition (assign σ side B) := by
  cases side <;> simp only [augmentedMove, Bool.false_eq_true, ↓reduceIte,
    Move.apply, augmentedPartition] <;> congr 1 <;> ext x <;>
    simp only [receiving, middle, Finset.mem_union, Finset.mem_sdiff,
      Finset.mem_map, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ,
      true_and, Function.Embedding.coeFn_mk] <;> cases x with
  | inl x =>
    simp only [augmentedState, Sum.elim_inl, Sum.inl.injEq, exists_eq_right]
    cases hx : σ x with
    | none => by_cases hB : x ∈ B <;> simp only [assign, hx, hB] <;> simp
    | some b => cases b <;> simp only [assign, hx] <;> simp
  | inr b =>
    cases b <;> simp only [augmentedState, Sum.elim_inr, Sum.inl_ne_inr,
      and_false, exists_false, Option.some.injEq, Bool.false_eq_true,
      Bool.true_eq_false, reduceCtorEq] <;> simp

end TNLean.PEPS.AreaLaw.Scan
