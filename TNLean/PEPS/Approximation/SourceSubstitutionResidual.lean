/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceCircuitSubstitution
import TNLean.PEPS.Approximation.SourceResidualCoordinates

/-!
# Independence of the remaining operations from surviving source vectors

The source vectors of a partial monomial may vary at every surviving original
occurrence. Vectors whose two endpoints are exterior must remain unchanged:
they have become local preparations after the exterior parties are grouped.
Under precisely this condition, the ordered source layout and the canonical
remaining word are unchanged. This is an equality of the actual compositions,
not merely recovery of one prepared vector.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-subset-expansion.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.
-/

noncomputable section
open scoped TensorProduct
namespace TNLean.PEPS.PairEffect.Word
variable {P Q T : Type}

/-- The same operations and source spaces, allowing source vectors to vary only
when their two owners remain distinct after the prescribed grouping. -/
private inductive SourceVariation (f : P → Q) :
    {a b c d : Layout P} → Word a b → Word c d → Prop
  | refl {a b} (w : Word a b) : SourceVariation f w w
  | comp {a b c a' b' c'} {w : Word a b} {v : Word b c}
      {w' : Word a' b'} {v' : Word b' c'} :
      SourceVariation f w w' → SourceVariation f v v' →
      SourceVariation f (.comp w v) (Word.comp w' v')
  | frame (r : Reg P) {a b c d} {w : Word a b} {w' : Word c d} :
      SourceVariation f w w' → SourceVariation f (Word.frame r w) (Word.frame r w')
  | source {p q : P} (hpq : p ≠ q) (U V : HSpace) (η θ : U ⊗[ℂ] V)
      (tail : Layout P) (h : f p = f q → η = θ) :
      SourceVariation f (.source hpq U V η tail) (.source hpq U V θ tail)

/-- Varying source vectors changes neither endpoint layout. -/
private theorem SourceVariation.layouts {f : P → Q} {a b c d : Layout P}
    {w : Word a b} {v : Word c d} (h : SourceVariation f w v) : a = c ∧ b = d := by
  induction h with
  | refl => exact ⟨rfl, rfl⟩
  | comp _ _ ih ih' => exact ⟨ih.1, ih'.2⟩
  | frame r _ ih => exact ⟨congrArg (r :: ·) ih.1, congrArg (r :: ·) ih.2⟩
  | source => exact ⟨rfl, rfl⟩

/-- Identifying equal layouts does not change the permitted source variations. -/
private theorem SourceVariation.castLayouts {f : P → Q}
    {a b c d a' b' c' d' : Layout P} {w : Word a b} {v : Word c d}
    (h : SourceVariation f w v) (ha : a = a') (hb : b = b')
    (hc : c = c') (hd : d = d') :
    SourceVariation f (w.castLayouts ha hb) (v.castLayouts hc hd) := by
  cases ha; cases hb; cases hc; cases hd
  exact h

/-- Identifying the input layout leaves the underlying word unchanged. -/
private theorem heq_castInput {a b c : Layout P} (w : Word a b) (h : a = c) :
    HEq (w.castInput h) w := by
  cases h
  rfl

/-- Equal source layouts and equal remaining words give equal framed compositions. -/
private theorem comp_frameList_heq {a b c s s' t t' : Layout P}
    (hs : s = s') (ht : t = t') {u : Word (s ++ a) b} {u' : Word (s' ++ a) b}
    {v : Word (t ++ b) c} {v' : Word (t' ++ b) c}
    (hu : HEq u u') (hv : HEq v v') :
    HEq (Word.comp (frameList t u) v) (Word.comp (frameList t' u') v') := by
  cases hs; cases ht
  cases eq_of_heq hu; cases eq_of_heq hv
  rfl

/-- Moving a spectator past equal source layouts preserves the remaining word. -/
private theorem frame_localPart_heq {a b s t : Layout P} (r : Reg P)
    (hst : s = t) {u : Word (s ++ a) b} {v : Word (t ++ a) b} (huv : HEq u v) :
    HEq (Word.comp (moveHead r s a) (Word.frame r u))
      (Word.comp (moveHead r t a) (Word.frame r v)) := by
  cases hst
  cases eq_of_heq huv
  rfl

/-- Source vectors do not enter the remaining local operations. -/
private theorem SourceVariation.localPart {f : P → Q} {a b c d : Layout P}
    {w : Word a b} {v : Word c d} (h : SourceVariation f w v) :
    w.sources.layout = v.sources.layout ∧ HEq w.localPart v.localPart := by
  induction h with
  | refl => exact ⟨rfl, HEq.rfl⟩
  | @comp a b c a' b' c' w v w' v' hw hv ihw ihv =>
      obtain ⟨rfl, rfl⟩ := hw.layouts
      obtain ⟨_, rfl⟩ := hv.layouts
      obtain ⟨hlw, hew⟩ := ihw
      obtain ⟨hlv, hev⟩ := ihv
      refine ⟨?_, ?_⟩
      · simp only [sources, SourceInventory.layout_append, hlw, hlv]
      · exact (heq_castInput _ _).trans
          ((comp_frameList_heq hlw hlv hew hev).trans (heq_castInput _ _).symm)
  | frame r h ih =>
      obtain ⟨rfl, rfl⟩ := h.layouts
      exact ⟨ih.1, frame_localPart_heq r ih.1 ih.2⟩
  | source => exact ⟨rfl, HEq.rfl⟩

/-- Adding unchanged leading registers preserves the permitted source variations. -/
private theorem SourceVariation.frameList {f : P → Q} {a b c d : Layout P}
    {w : Word a b} {v : Word c d} (h : SourceVariation f w v) (tail : Layout P) :
    SourceVariation f (frameList tail w) (frameList tail v) := by
  induction tail with
  | nil => exact h
  | cons r tail ih => exact .frame r ih

/-- Adding unchanged final registers preserves the permitted source variations. -/
private theorem SourceVariation.appendTail {f : P → Q} {a b : Layout P}
    {w v : Word a b} (h : SourceVariation f w v) (tail : Layout P) :
    SourceVariation f (w.appendTail tail) (v.appendTail tail) :=
  .comp (.refl _) (.comp (h.frameList tail) (.refl _))

/-- Grouping owners preserves the permitted variations: each source that becomes
a local preparation has equal vectors on both sides. -/
private theorem SourceVariation.mapOwner (g : P → Q) (f : Q → T)
    {a b c d : Layout P} {w : Word a b} {v : Word c d}
    (h : SourceVariation (fun p ↦ f (g p)) w v) :
    SourceVariation f (w.mapOwner g) (v.mapOwner g) := by
  induction h with
  | refl => exact .refl _
  | comp _ _ ih ih' => exact .comp ih ih'
  | frame r _ ih => exact .frame ⟨g r.owner, r.space⟩ ih
  | @source p q hpq U V η θ tail h =>
      classical
      by_cases hg : g p = g q
      · have hη := h (congrArg f hg)
        subst θ
        exact .refl _
      · simp only [Word.mapOwner, dite_eq_right hg]
        exact .source hg U V η θ (Layout.mapOwner g tail) h

/-- A source with identified spectator layouts admits the same vector variation. -/
private theorem SourceVariation.source_tail {f : P → Q} {p q : P}
    (hpq : p ≠ q) (U V : HSpace) (η θ : U ⊗[ℂ] V)
    {a b : Layout P} (hab : a = b) (h : f p = f q → η = θ) :
    SourceVariation f (.source hpq U V η a) (.source hpq U V θ b) := by
  subst b
  exact .source hpq U V η θ a h

/-- Ordered source records with equal endpoints and halfspaces, whose vectors
agree whenever the prescribed grouping identifies the two endpoints. -/
private inductive InventoryVariation (f : P → Q) : SourceInventory P → SourceInventory P → Prop
  | nil : InventoryVariation f [] []
  | cons {p q : P} (hpq : p ≠ q) (U V : HSpace) (η θ : U ⊗[ℂ] V)
      (h : f p = f q → η = θ) {S T : SourceInventory P} :
      InventoryVariation f S T →
      InventoryVariation f (⟨p, q, hpq, U, V, η⟩ :: S) (⟨p, q, hpq, U, V, θ⟩ :: T)

/-- These source inventories have the same ordered register layout. -/
private theorem InventoryVariation.layout {f : P → Q} {S T : SourceInventory P}
    (h : InventoryVariation f S T) : S.layout = T.layout := by
  induction h with
  | nil => rfl
  | @cons p q hpq U V η θ h S T hST ih =>
      exact congrArg (fun t ↦ (⟨p, U⟩ : Reg P) :: (⟨q, V⟩ : Reg P) :: t) ih

/-- Preparing these inventories changes only the permitted source vectors. -/
private theorem InventoryVariation.prepare {f : P → Q} {S T : SourceInventory P}
    (h : InventoryVariation f S T) (tail : Layout P) :
    SourceVariation f (S.prepare tail) (T.prepare tail) := by
  induction h with
  | nil => exact .refl _
  | cons hpq U V η θ h hST ih =>
      exact .comp ih (.source_tail hpq U V η θ (congrArg (· ++ tail) hST.layout) h)

/-- Slotwise permitted variations give the corresponding ordered inventories. -/
private theorem variation_ofSlots (f : P → Q) (R : SourceInventory P)
    (U V : Fin R.length → HSpace) (η θ : ∀ i, U i ⊗[ℂ] V i)
    (h : ∀ i, f (R.get i).left = f (R.get i).right → η i = θ i) :
    InventoryVariation f (SourceInventory.ofSlots R U V η)
      (SourceInventory.ofSlots R U V θ) := by
  induction R with
  | nil => exact .nil
  | cons r R ih =>
      rw [SourceInventory.ofSlots_cons, SourceInventory.ofSlots_cons]
      exact .cons r.distinct (U 0) (V 0) (η 0) (θ 0) (h 0)
        (ih (fun i ↦ U i.succ) (fun i ↦ V i.succ)
          (fun i ↦ η i.succ) (fun i ↦ θ i.succ) (fun i ↦ h i.succ))

/-- Fixed-coordinate preparation preserves slotwise source variations. -/
private theorem variation_prepareSlots (f : P → Q) (R : SourceInventory P)
    (U V : Fin R.length → HSpace) (η θ : ∀ i, U i ⊗[ℂ] V i)
    (h : ∀ i, f (R.get i).left = f (R.get i).right → η i = θ i)
    (tail : Layout P) :
    SourceVariation f (SourceInventory.prepareSlots R U V η tail)
      (SourceInventory.prepareSlots R U V θ tail) :=
  ((variation_ofSlots f R U V η θ h).prepare tail).castLayouts _ _ _ _

end TNLean.PEPS.PairEffect.Word

namespace TNLean.PEPS.PairEffect.SourceCircuit
open Word
variable {P : Type}

/-- The chronological construction changes only surviving source vectors;
every exterior local preparation retains its original vector. -/
private theorem variation_partialWithSources (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b)
    (η : ∀ e : sourceLocations w, branchLabels w e.1 →
      euc (Fin (sourceDims w e).1) ⊗[ℂ] euc (Fin (sourceDims w e).2))
    (hη : ∀ e ξ, A (endpoints w e).1 = false → A (endpoints w e).2 = false →
      η e ξ = sourceVectorAt w e ξ) (ξ : Choices A w) :
    SourceVariation (fun p ↦ p) (partialWithSources A w η ξ) (partialWord A w ξ) := by
  induction w with
  | id => exact .refl _
  | comp w v ihw ihv =>
      exact .comp
        (ihw (fun e θ ↦ η ⟨Sum.inl e.1, e.2⟩ θ)
          (fun e θ ↦ hη ⟨Sum.inl e.1, e.2⟩ θ) ξ.1)
        (ihv (fun e θ ↦ η ⟨Sum.inr e.1, e.2⟩ θ)
          (fun e θ ↦ hη ⟨Sum.inr e.1, e.2⟩ θ) ξ.2)
  | localMap => exact .refl _
  | @gate C ι _ _ owner a b c G tail =>
      classical
      by_cases ht : ∃ p : C, A (owner p) = true
      · simp only [partialWithSources, partialWord, dite_eq_left ht]
        apply SourceVariation.mapOwner (affectedOwner A) (fun p ↦ p)
        apply SourceVariation.appendTail
        apply SourceVariation.mapOwner owner (affectedOwner A)
        apply SourceVariation.comp
        · apply variation_prepareSlots
          intro i hi
          have hb := (affectedOwner_eq_iff A _ _).mp hi
          rcases hb with heq | ⟨hl, hr⟩
          · exact ((G.slots.get i).distinct (owner.injective heq)).elim
          · exact hη ⟨(), i⟩ _ hl hr
        · exact .refl _
      · simp only [partialWithSources, partialWord, dite_eq_right ht]
        exact .refl _
  | swap => exact .refl _
  | frame r w ih => exact .frame ⟨affectedOwner A r.owner, r.space⟩ (ih η hη ξ)

/-- Replacing only surviving source vectors leaves their ordered register layout
unchanged. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434. -/
theorem layout_sources_partialWithSources (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b)
    (η : ∀ e : sourceLocations w, branchLabels w e.1 →
      euc (Fin (sourceDims w e).1) ⊗[ℂ] euc (Fin (sourceDims w e).2))
    (hη : ∀ e ξ, A (endpoints w e).1 = false → A (endpoints w e).2 = false →
      η e ξ = sourceVectorAt w e ξ) (ξ : Choices A w) :
    (partialWithSources A w η ξ).sources.layout =
      SourceInventory.slotLayout (partialSlots A w)
        (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1))
        (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2)) :=
  (variation_partialWithSources A w η hη ξ).localPart.1.trans
    (slotLayout_partialSlots_eq A w ξ).symm

/-- The canonical remaining operations are independent of the surviving source
vectors. Sources absorbed into an exterior local preparation retain their original
vectors. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434. -/
theorem residualInSlots_partialWithSources (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b)
    (η : ∀ e : sourceLocations w, branchLabels w e.1 →
      euc (Fin (sourceDims w e).1) ⊗[ℂ] euc (Fin (sourceDims w e).2))
    (hη : ∀ e ξ, A (endpoints w e).1 = false → A (endpoints w e).2 = false →
      η e ξ = sourceVectorAt w e ξ) (ξ : Choices A w) :
    (partialWithSources A w η ξ).residualInSlots (partialSlots A w)
        (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1))
        (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2))
        (layout_sources_partialWithSources A w η hη ξ) = partialResidual A w ξ := by
  apply eq_of_heq
  exact (heq_castInput _ _).trans
    ((variation_partialWithSources A w η hη ξ).localPart.2.trans
      (heq_castInput _ _).symm)

end TNLean.PEPS.PairEffect.SourceCircuit
