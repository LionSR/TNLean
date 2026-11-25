/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Circuit.Party.Compression.CorrectedSources.SelectivePreparation
import QICLean.Circuit.Party.Compression.CorrectedSources.TensorPartition
import QICLean.Circuit.Party.Source.Preparation

/-!
# Selective factorization of the original sources of a composition

Enumerate the pair sources of an allowed composition and divide the parties into
two sides. Retain as free every source crossing the division, together with any
chosen internal sources. Preparing all remaining original source vectors leaves
a tensor product of two contractions on the entire free input space. These
contractions are chosen before the vectors supplied to the free source registers.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, source preparation at lines 246–251 and separation on all
free inputs at lines 409–434.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

noncomputable section

open Matrix ManyBody

namespace QuantumCircuit.Party.Word

open SourceInventory

variable {P : Type} [Fintype P] [DecidableEq P] {X Y : P → Type} [∀ p, Fintype (X p)]
  [∀ p, DecidableEq (X p)]

/-- Preparing the original source list of an allowed composition in the slot bases of its
sources recovers the composition through an allowed composition containing no pair sources.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 246–251. -/
private theorem exists_prepareSlots_sources [∀ p, Finite (Y p)] (w : Word X Y)
    (hw : w.IsAllowed) :
    ∃ v : Word (slotSystem w.sources w.sources.bases X) Y,
      v.IsAllowed ∧ v.sources = [] ∧
      v.op * (prepareSlots w.sources w.sources.bases
        (fun i ↦ (w.sources.get i).vector) X).op = w.op := by
  classical
  let := fun p ↦ Fintype.ofFinite (Y p)
  have hE : (ofSlots w.sources w.sources.bases (fun i ↦ (w.sources.get i).vector)).Expands
      w.sources := by
    rw [ofSlots_bases]
  obtain ⟨d, hd, hds, hde⟩ := exists_prepareSlots_recovery _ _ _ _ hE X
  refine ⟨d.comp w.localPart, ⟨hd, isAllowed_localPart hw⟩, ?_, ?_⟩
  · rw [sources_comp, hds, sources_localPart, List.nil_append]
  · rw [Word.op_comp, Matrix.mul_assoc, hde, op_localPart_mul_prepare]

/-- The original source inventory of an allowed composition admits selective
preparation followed by a tensor product of two local contractions, one on each side of the
division `f` of the parties. Every source crossing the division is retained as free. The
factors are chosen before all replacement free vectors, and filling the free slots with their
original vectors recovers the original composition. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 246–251 and 409–434. -/
theorem exists_selective_partition_of_word [∀ p, Fintype (Y p)] (f : P → Bool) (w : Word X Y)
    (hw : w.IsAllowed)
    (free : Fin w.sources.length → Bool)
    (hmask : ∀ i, free i = false →
      f (w.sources.get i).left = f (w.sources.get i).right) :
    let R := w.sources
    let B := R.bases
    let η : ∀ i, EuclideanSpace ℂ (B.left i × B.right i) := fun i ↦ (R.get i).vector
    let fixed : ∀ i, free i = false → EuclideanSpace ℂ (B.left i × B.right i) := fun i _ ↦ η i
    ∃ v : Word (slotSystem R B X) Y,
      v.IsAllowed ∧ v.sources = [] ∧ v.op * (prepareSlots R B η X).op = w.op ∧
      IsTensorPartitioned f (PartyCircuit.comp (prepareSelected R B free fixed X) v) ∧
      w.op = Word.op (PartyCircuit.comp (prepareSelected R B free fixed X) v) *
        (prepareFreeSlots R B free η X).op ∧
      ∀ ζ : ∀ i, EuclideanSpace ℂ (B.left i × B.right i),
        v.op * (prepareSlots R B (fillSourceVectors B free fixed ζ) X).op =
          Word.op (PartyCircuit.comp (prepareSelected R B free fixed X) v) *
            (prepareFreeSlots R B free ζ X).op := by
  intro R B η fixed
  classical
  obtain ⟨v, hv, hs, he⟩ := exists_prepareSlots_sources w hw
  have hfixed : ∀ i h, ‖fixed i h‖ = 1 := fun i _ ↦
    isNormalized_sources w hw (R.get i) (List.get_mem R i)
  obtain ⟨hpart, hζ⟩ := exists_selective_partition f R B free fixed hfixed hmask X v hv hs
  have hfill : fillSourceVectors B free fixed η = η := by
    funext i
    simp [fillSourceVectors, fixed]
  refine ⟨v, hv, hs, he, hpart, ?_, hζ⟩
  rw [← he, ← hζ η, hfill]

end QuantumCircuit.Party.Word
