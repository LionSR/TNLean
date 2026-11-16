/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.PartyCircuit.PreparedSourceGate
import TNLean.Lattice.PartyCircuit.WordAppendTail
import TNLean.Lattice.PartyCircuit.SourceOwnerSupport
import TNLean.Lattice.PartyCircuit.AffectedOwners

/-!
# Chronological compositions of source-prepared gates

Each nonprivate gate has its own participating party type and its own common
source positions. Gates act in their prescribed order with arbitrary spectator
registers. A partial expansion chooses labels only at gates meeting the affected
parties; every other gate retains its complete aggregate contraction.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 21–36, 133–151, 233–267 and 351–417.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

noncomputable section
open scoped TensorProduct
open ContinuousLinearMap
namespace TNLean.Lattice.PartyCircuit
variable {P : Type}

/-- A source-prepared nonprivate gate on the registers of the participating parties `C`,
embedded among all parties by `owner`, next to the untouched registers `tail`.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 133–151 and 233–267. -/
inductive PreparedGate : Layout P → Layout P → Type 1
  | mk {C ι : Type} [Fintype C] [Fintype ι] (owner : C ↪ P)
      {a b : Layout C} {c : ι → ℂ} (G : PreparedSourceGate c a b) (tail : Layout P) :
      PreparedGate (Layout.mapOwner owner a ++ tail) (Layout.mapOwner owner b ++ tail)

namespace PreparedGate

/-- The complete memory operator of a source-prepared gate, with its aggregate contraction
and every spectator identity retained.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 21–36 and 233–267. -/
@[simp] def eval : {a b : Layout P} → PreparedGate a b → (Mem a →L[ℂ] Mem b)
  | _, _, @PreparedGate.mk _ _ _ _ _ owner a b _ G tail =>
      isoL (appendIso (Layout.mapOwner owner b) tail).symm ∘L
        (G.evalAtOwners owner).rTensor (Mem tail) ∘L
          isoL (appendIso (Layout.mapOwner owner a) tail)

/-- The actual participating parties of a source-prepared gate.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 356–364. -/
@[simp] def participants : {a b : Layout P} → PreparedGate a b → Finset P
  | _, _, @PreparedGate.mk _ _ _ _ _ owner _ _ _ _ _ => Finset.univ.map owner

/-- A source-prepared gate is a contraction.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 133–151 and 215–226. -/
theorem norm_eval_le_one : {a b : Layout P} → (g : PreparedGate a b) → ‖g.eval‖ ≤ 1
  | _, _, @PreparedGate.mk _ _ _ _ _ owner _ _ _ G tail =>
      norm_comp_le_one (LinearIsometry.norm_toContinuousLinearMap_le _)
        (norm_comp_le_one
          ((norm_rTensor_le (Mem tail) _).trans (G.norm_evalAtOwners_le_one owner))
          (LinearIsometry.norm_toContinuousLinearMap_le _))

end PreparedGate

/-- Source-prepared gates as a gate family. The prepared gates already carry their aggregate
contraction bounds, so every one of them is allowed.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 133–151. -/
instance : GateFamily (PreparedGate (P := P)) where
  eval := PreparedGate.eval
  IsAllowed _ := True
  norm_eval_le_one g _ := g.norm_eval_le_one
  participants := PreparedGate.participants

@[simp] theorem PreparedGate.gateFamily_eval {a b : Layout P} (g : PreparedGate a b) :
    GateFamily.eval g = g.eval :=
  rfl

@[simp] theorem PreparedGate.gateFamily_isAllowed {a b : Layout P} (g : PreparedGate a b) :
    GateFamily.IsAllowed g :=
  trivial

@[simp] theorem PreparedGate.gateFamily_participants {a b : Layout P} (g : PreparedGate a b) :
    GateFamily.participants g = g.participants :=
  rfl

/-- A chronological composition with source-prepared nonprivate gates: a circuit whose gates
are source-prepared gates, with arbitrary local maps.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 21–36,
133–151 and 233–267. -/
abbrev SourceCircuit : Layout P → Layout P → Type 1 := Circuit LocalCondition.any PreparedGate

namespace SourceCircuit

/-- The empty circuit. -/
@[match_pattern] abbrev id (ℓ : Layout P) : SourceCircuit ℓ ℓ := Circuit.id ℓ

/-- Composition, in chronological order. -/
@[match_pattern] abbrev comp {ℓ₁ ℓ₂ ℓ₃ : Layout P} (w : SourceCircuit ℓ₁ ℓ₂) (w'
    : SourceCircuit ℓ₂ ℓ₃) :
    SourceCircuit ℓ₁ ℓ₃ :=
  Circuit.comp w w'

/-- A local map on registers of one party, next to untouched registers. -/
@[match_pattern] abbrev localMap (p : P) {ℓ₁ ℓ₂ : Layout P} (h₁ : ∀ r ∈ ℓ₁, r.owner = p)
    (h₂ : ∀ r ∈ ℓ₂, r.owner = p) (U : Mem ℓ₁ →L[ℂ] Mem ℓ₂) (ℓ : Layout P) :
    SourceCircuit (ℓ₁ ++ ℓ) (ℓ₂ ++ ℓ) :=
  Circuit.localMap p h₁ h₂ U ℓ True.intro

/-- Exchange of two adjacent tensor factors. -/
@[match_pattern] abbrev swap (r r' : Reg P) (ℓ : Layout P) : SourceCircuit (r :: r' :: ℓ)
    (r' :: r :: ℓ) :=
  Circuit.swap r r' ℓ

/-- A circuit next to an untouched register. -/
@[match_pattern] abbrev frame (r : Reg P) {ℓ ℓ' : Layout P} (w : SourceCircuit ℓ ℓ') :
    SourceCircuit (r :: ℓ) (r :: ℓ') :=
  Circuit.frame r w

/-- A source-prepared gate as a circuit. -/
@[match_pattern] abbrev gate {C ι : Type} [Fintype C] [Fintype ι] (owner : C ↪ P)
    {a b : Layout C} {c : ι → ℂ} (G : PreparedSourceGate c a b) (tail : Layout P) :
    SourceCircuit (Layout.mapOwner owner a ++ tail) (Layout.mapOwner owner b ++ tail) :=
  Circuit.gate (PreparedGate.mk owner G tail)

/-- A circuit framed by a list of untouched registers. -/
abbrev frameList {ℓ ℓ' : Layout P} (ℓ₀ : Layout P) (w : SourceCircuit ℓ ℓ') :
    SourceCircuit (ℓ₀ ++ ℓ) (ℓ₀ ++ ℓ') :=
  Circuit.frameList ℓ₀ w

/-- Identify equal input and output layouts without adding an operation. -/
abbrev castLayouts {ℓ ℓ' a b : Layout P} (w : SourceCircuit ℓ ℓ') (h : ℓ = a) (h' : ℓ' = b) :
    SourceCircuit a b :=
  Circuit.castLayouts w h h'

/-- Induction on the constructors of `SourceCircuit`. -/
@[induction_eliminator, elab_as_elim]
theorem induction {motive : {ℓ ℓ' : Layout P} → SourceCircuit ℓ ℓ' → Prop}
    (id : ∀ ℓ : Layout P, motive (SourceCircuit.id ℓ))
    (comp : ∀ {ℓ₁ ℓ₂ ℓ₃ : Layout P} (w : SourceCircuit ℓ₁ ℓ₂) (w' : SourceCircuit ℓ₂ ℓ₃),
      motive w → motive w' → motive (SourceCircuit.comp w w'))
    (localMap : ∀ (p : P) {ℓ₁ ℓ₂ : Layout P} (h₁ : ∀ r ∈ ℓ₁, r.owner = p)
      (h₂ : ∀ r ∈ ℓ₂, r.owner = p) (U : Mem ℓ₁ →L[ℂ] Mem ℓ₂) (ℓ : Layout P),
      motive (SourceCircuit.localMap p h₁ h₂ U ℓ))
    (gate : ∀ {C ι : Type} [Fintype C] [Fintype ι] (owner : C ↪ P) {a b : Layout C}
      {c : ι → ℂ} (G : PreparedSourceGate c a b) (tail : Layout P),
      motive (SourceCircuit.gate owner G tail))
    (swap : ∀ (r r' : Reg P) (ℓ : Layout P), motive (SourceCircuit.swap r r' ℓ))
    (frame : ∀ (r : Reg P) {ℓ ℓ' : Layout P} (w : SourceCircuit ℓ ℓ'),
      motive w → motive (SourceCircuit.frame r w))
    {ℓ ℓ' : Layout P} (w : SourceCircuit ℓ ℓ') : motive w := by
  induction w with
  | id ℓ₀ => exact id ℓ₀
  | comp w w' ih ih' => exact comp w w' ih ih'
  | localMap p h₁ h₂ U ℓ => exact localMap p h₁ h₂ U ℓ
  | gate g => cases g with | mk owner G tail => exact gate owner G tail
  | swap r r' ℓ => exact swap r r' ℓ
  | frame r w ih => exact frame r w ih

/-- The complete memory operator of a source-prepared gate, with its aggregate contraction
and every spectator identity retained.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 21–36 and 233–267. -/
theorem eval_gate {C ι : Type} [Fintype C] [Fintype ι] (owner : C ↪ P)
    {a b : Layout C} {c : ι → ℂ} (G : PreparedSourceGate c a b) (tail : Layout P) :
    (gate owner G tail).eval =
      isoL (appendIso (Layout.mapOwner owner b) tail).symm ∘L
        (G.evalAtOwners owner).rTensor (Mem tail) ∘L
          isoL (appendIso (Layout.mapOwner owner a) tail) :=
  rfl

/-- Monomial choices occur exactly at gates touching the affected parties.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–381. -/
def Choices (A : P → Bool) : {a b : Layout P} → SourceCircuit a b → Type
  | _, _, .id _ => Unit
  | _, _, .comp w v => Choices A w × Choices A v
  | _, _, .localMap .. => Unit
  | _, _, Circuit.gate (@PreparedGate.mk _ C ι _ _ owner _ _ _ _ _) => by
      classical
      exact if ∃ p : C, A (owner p) = true then ι else Unit
  | _, _, .swap .. => Unit
  | _, _, .frame _ w => Choices A w

/-- A partial expansion has finitely many monomial choices.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–381. -/
instance choicesFintype (A : P → Bool) : {a b : Layout P} →
    (w : SourceCircuit a b) → Fintype (Choices A w)
  | _, _, .id _ => inferInstanceAs (Fintype Unit)
  | _, _, .comp w v => by
      letI := choicesFintype A w
      letI := choicesFintype A v
      exact inferInstanceAs (Fintype (Choices A w × Choices A v))
  | _, _, .localMap .. => inferInstanceAs (Fintype Unit)
  | _, _, Circuit.gate (@PreparedGate.mk _ C ι _ _ owner _ _ _ _ _) => by
      classical
      dsimp only [Choices]
      split <;> infer_instance
  | _, _, .swap .. => inferInstanceAs (Fintype Unit)
  | _, _, .frame _ w => choicesFintype A w

/-- The actual branch of the partial expansion; untouched exterior gates are
retained as whole local operations. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 351–417. -/
def partialWord (A : P → Bool) : {a b : Layout P} → (w : SourceCircuit a b) →
    Choices A w → Word (Layout.mapOwner (affectedOwner A) a)
      (Layout.mapOwner (affectedOwner A) b)
  | _, _, .id a, _ => .id _
  | _, _, .comp w v, ξ => .comp (partialWord A w ξ.1) (partialWord A v ξ.2)
  | _, _, .localMap p ha hb T tail, _ =>
      (Word.localMap p ha hb T tail).mapOwner (affectedOwner A)
  | _, _, Circuit.gate (@PreparedGate.mk _ C ι _ _ owner a b c G tail), ξ => by
      classical
      by_cases h : ∃ p : C, A (owner p) = true
      · have i : ι := by simpa only [Choices, ite_eq_left h] using ξ
        exact (((G.branchWord i).mapOwner owner).appendTail tail).mapOwner (affectedOwner A)
      · exact Word.groupedBlockMap (affectedOwner A) none
          (Layout.mapOwner owner a) (Layout.mapOwner owner b)
          (Layout.affectedOwner_mapOwner_eq_none A owner h a)
          (Layout.affectedOwner_mapOwner_eq_none A owner h b)
          (G.evalAtOwners owner) tail
  | _, _, .swap r t tail, _ => (Word.swap r t tail).mapOwner (affectedOwner A)
  | _, _, .frame r w, ξ => .frame ⟨affectedOwner A r.owner, r.space⟩ (partialWord A w ξ)

/-- Scalar weights are charged only at gates whose labels are actually expanded.
Source: polynomial-PEPS Theorem 5.2, `eq:compression-choice-cost`,
`04-compression.tex`, lines 351–381. -/
def coefficient (A : P → Bool) : {a b : Layout P} → (w : SourceCircuit a b) → Choices A w → ℂ
  | _, _, .id _, _ => 1
  | _, _, .comp w v, ξ => coefficient A w ξ.1 * coefficient A v ξ.2
  | _, _, .localMap .., _ => 1
  | _, _, Circuit.gate (@PreparedGate.mk _ C ι _ _ owner _ _ c _ _), ξ => by
      classical
      by_cases h : ∃ p : C, A (owner p) = true
      · have i : ι := by simpa only [Choices, ite_eq_left h] using ξ
        exact c i
      · exact 1
  | _, _, .swap .., _ => 1
  | _, _, .frame _ w, ξ => coefficient A w ξ

end SourceCircuit
end TNLean.Lattice.PartyCircuit
