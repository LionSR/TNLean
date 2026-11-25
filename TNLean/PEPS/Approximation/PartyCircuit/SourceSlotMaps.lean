/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Circuit.Party.Monomial.Stack
import QICLean.Circuit.Party.Source.Common
import QICLean.Circuit.Party.Source.Preparation

/-!
# Local maps on all source slots

One fixed composition applies prescribed maps to the two registers of every source slot. The
composition is independent of the source vectors. It therefore acts on all
source preparations at once, including sources expressed in proper Schmidt
subspaces of their ambient registers.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 279–355 and 409–427.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

noncomputable section

open Matrix ManyBody
open scoped Matrix.Norms.L2Operator

namespace QuantumCircuit.Party.Word

open SourceInventory

variable {P : Type} [DecidableEq P]

/-- Apply the prescribed endpoint maps in every source slot, leaving the original
input registers untouched. This word does not depend on the source vectors.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 279–355 and 409–427. -/
def mapSourceSlots : (R : SourceInventory P) → (B B' : SlotBases R.length) →
    (∀ i, Matrix (B'.left i) (B.left i) ℂ) → (∀ i, Matrix (B'.right i) (B.right i) ℂ) →
    (X : P → Type) → [∀ p, Fintype (X p)] → [∀ p, DecidableEq (X p)] →
    Word (slotSystem R B X) (slotSystem R B' X)
  | [], _, _, _, _, X, _, _ => PartyCircuit.done X
  | r :: R, B, B', f, g, X, _, _ =>
      (PartyCircuit.liftPair r.distinct (B.left 0) (B.right 0)
        (mapSourceSlots R B.tail B'.tail (fun i ↦ f i.succ) (fun i ↦ g i.succ) X)).comp
        (Word.mapPair r.distinct (f 0) (g 0) (slotSystem R B'.tail X))

variable (X : P → Type) [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]

/-- Endpoint contractions give an allowed composition with no pair sources.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–427. -/
theorem mapSourceSlots_spec (R : SourceInventory P) (B B' : SlotBases R.length)
    (f : ∀ i, Matrix (B'.left i) (B.left i) ℂ) (g : ∀ i, Matrix (B'.right i) (B.right i) ℂ)
    (hf : ∀ i, ‖f i‖ ≤ 1) (hg : ∀ i, ‖g i‖ ≤ 1) :
    (mapSourceSlots R B B' f g X).IsAllowed ∧ (mapSourceSlots R B B' f g X).sources = [] := by
  induction R with
  | nil => exact ⟨trivial, rfl⟩
  | cons r R ih =>
    obtain ⟨ha, hs⟩ := Word.mapPair_spec r.distinct (X := slotSystem R B'.tail X) (f 0) (g 0)
      (hf 0) (hg 0)
    obtain ⟨hta, hts⟩ := ih B.tail B'.tail (fun i ↦ f i.succ) (fun i ↦ g i.succ)
      (fun i ↦ hf i.succ) (fun i ↦ hg i.succ)
    refine ⟨⟨PartyCircuit.isAllowed_liftPair _ _ _ _ SourceGate.isCompatible_frame
      (fun _ _ _ _ _ _ _ _ _ _ _ hg ↦ hg) hta, ha⟩, ?_⟩
    simp only [mapSourceSlots, Word.sources, PartyCircuit.liftPair, hts,
      Word.sources_frame]
    rfl

variable [Fintype P]

/-- The same source-free word transforms every source preparation by the Kronecker
products of its endpoint maps. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 279–355 and 409–427. -/
theorem op_mapSourceSlots_prepareSlots (R : SourceInventory P) (B B' : SlotBases R.length)
    (f : ∀ i, Matrix (B'.left i) (B.left i) ℂ) (g : ∀ i, Matrix (B'.right i) (B.right i) ℂ)
    (η : ∀ i, EuclideanSpace ℂ (B.left i × B.right i)) :
    (mapSourceSlots R B B' f g X).op * (prepareSlots R B η X).op =
      (prepareSlots R B' (fun i ↦ EuclideanSpace.pairMap (f i) (g i) (η i)) X).op := by
  induction R with
  | nil => exact Matrix.one_mul _
  | cons r R ih =>
    change Word.op ((PartyCircuit.liftPair r.distinct (B.left 0) (B.right 0)
        (mapSourceSlots R B.tail B'.tail (fun i ↦ f i.succ) (fun i ↦ g i.succ) X)).comp
        (Word.mapPair r.distinct (f 0) (g 0) (slotSystem R B'.tail X))) *
      Word.op ((prepareSlots R B.tail (fun i ↦ η i.succ) X).comp
        (Word.sourceAt r.distinct (B.left 0) (B.right 0) (η 0) (slotSystem R B.tail X))) =
      Word.op ((prepareSlots R B'.tail (fun i ↦ EuclideanSpace.pairMap (f i.succ) (g i.succ)
        (η i.succ)) X).comp (Word.sourceAt r.distinct (B'.left 0) (B'.right 0)
          (EuclideanSpace.pairMap (f 0) (g 0) (η 0)) (slotSystem R B'.tail X)))
    rw [Word.op_comp, Word.op_comp, Word.op_comp, Matrix.mul_assoc,
      ← Matrix.mul_assoc (Word.op (PartyCircuit.liftPair _ _ _ _)),
      op_liftPair_mul_op_sourceAt, Matrix.mul_assoc]
    erw [ih B.tail B'.tail (fun i ↦ f i.succ) (fun i ↦ g i.succ) (fun i ↦ η i.succ)]
    rw [← Matrix.mul_assoc, Word.op_mapPair_source]
    rfl

end QuantumCircuit.Party.Word
