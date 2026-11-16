/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.Lattice.PartyCircuit.EffectCircuitReplacement

/-! # Original private and nonprivate circuit operations

Private operations are arbitrary contractions on one party. Nonprivate
operations carry their actual monomial expansions and original participating
sets. The producer preserves the original operator and counts nonprivate
occurrences independently of the replacement construction.

Source: polynomial-PEPS, `04-compression.tex`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-effect-circuit-error; Theorem 5.2, lines 137–151 and 199–251.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
-/

noncomputable section
open scoped TensorProduct
open ContinuousLinearMap
namespace TNLean.Lattice.PartyCircuit
variable {P : Type}

/-- An original nonprivate gate: a weighted list of allowed party chains whose operator is a
contraction, on the registers of the participating parties `C`, whose number is not one.
Source: polynomial-PEPS 04-compression.tex, lines 21–36 and 199–229. -/
inductive OriginalGate : Layout P → Layout P → Type 1
  | mk {C : Type} [Fintype C] (owner : C ↪ P)
      (hC : Fintype.card C ≠ 1) {a b : Layout C} (L : PartyGate a b)
      (hL : ∀ q ∈ L, q.2.IsAllowed) (hG : ‖gate (toGate L)‖ ≤ 1) (tail : Layout P) :
      OriginalGate (Layout.mapOwner owner a ++ tail) (Layout.mapOwner owner b ++ tail)

namespace OriginalGate

/-- An original nonprivate gate without its side conditions. -/
@[simp] def toEffectGate : {a b : Layout P} → OriginalGate a b → EffectGate a b
  | _, _, @OriginalGate.mk _ _ _ owner _ _ _ L _ _ tail => .mk owner L tail

/-- An original nonprivate gate carries its contraction conditions. -/
theorem isAllowed_toEffectGate : {a b : Layout P} → (g : OriginalGate a b) →
    g.toEffectGate.IsAllowed
  | _, _, @OriginalGate.mk _ _ _ _ _ _ _ _ hL hG _ => ⟨hL, hG⟩

end OriginalGate

/-- Original nonprivate gates as a gate family: the operator and the participants are those
of the underlying nonprivate gate, and every gate is allowed.
Source: polynomial-PEPS 04-compression.tex, lines 21–36. -/
instance : GateFamily (OriginalGate (P := P)) where
  eval g := g.toEffectGate.eval
  IsAllowed _ := True
  norm_eval_le_one g _ := g.toEffectGate.norm_eval_le_one g.isAllowed_toEffectGate
  participants g := g.toEffectGate.participants

@[simp] theorem OriginalGate.gateFamily_eval {a b : Layout P} (g : OriginalGate a b) :
    GateFamily.eval g = g.toEffectGate.eval :=
  rfl

@[simp] theorem OriginalGate.gateFamily_isAllowed {a b : Layout P} (g : OriginalGate a b) :
    GateFamily.IsAllowed g :=
  trivial

@[simp] theorem OriginalGate.gateFamily_participants {a b : Layout P} (g : OriginalGate a b) :
    GateFamily.participants g = g.toEffectGate.participants :=
  rfl

/-- An original chronology with arbitrary private contractions and prescribed
nonprivate participating sets: a circuit whose gates are original nonprivate gates and whose
local maps are contractions. Registers exchanged by the syntax retain their owners.
Source: polynomial-PEPS 04-compression.tex, lines 21–36 and 199–229. -/
abbrev OriginalCircuit : Layout P → Layout P → Type 1 :=
  Circuit LocalCondition.contraction OriginalGate

namespace OriginalCircuit

/-- The empty circuit. -/
@[match_pattern] abbrev id (ℓ : Layout P) : OriginalCircuit ℓ ℓ :=
  Circuit.id (κ := LocalCondition.contraction) (G := OriginalGate) ℓ

/-- Composition, in chronological order. -/
@[match_pattern] abbrev comp {ℓ₁ ℓ₂ ℓ₃ : Layout P} (w : OriginalCircuit ℓ₁ ℓ₂) (w'
    : OriginalCircuit ℓ₂ ℓ₃) :
    OriginalCircuit ℓ₁ ℓ₃ :=
  Circuit.comp (κ := LocalCondition.contraction) (G := OriginalGate) w w'

/-- Exchange of two adjacent tensor factors. -/
@[match_pattern] abbrev swap (r r' : Reg P) (ℓ : Layout P) : OriginalCircuit (r :: r' :: ℓ)
    (r' :: r :: ℓ) :=
  Circuit.swap (κ := LocalCondition.contraction) (G := OriginalGate) r r' ℓ

/-- A circuit next to an untouched register. -/
@[match_pattern] abbrev frame (r : Reg P) {ℓ ℓ' : Layout P} (w : OriginalCircuit ℓ ℓ') :
    OriginalCircuit (r :: ℓ) (r :: ℓ') :=
  Circuit.frame (κ := LocalCondition.contraction) (G := OriginalGate) r w

/-- An arbitrary contraction on the registers of one party. -/
@[match_pattern] abbrev privateMap (p : P) {a b : Layout P}
    (ha : ∀ r ∈ a, r.owner = p) (hb : ∀ r ∈ b, r.owner = p)
    (A : Mem a →L[ℂ] Mem b) (hA : ‖A‖ ≤ 1) (tail : Layout P) :
    OriginalCircuit (a ++ tail) (b ++ tail) :=
  Circuit.localMap p ha hb A tail hA

/-- An original nonprivate gate as a circuit. -/
@[match_pattern] abbrev nonprivateGate {C : Type} [Fintype C] (owner : C ↪ P)
    (hC : Fintype.card C ≠ 1) {a b : Layout C} (L : PartyGate a b)
    (hL : ∀ q ∈ L, q.2.IsAllowed) (hG : ‖gate (toGate L)‖ ≤ 1) (tail : Layout P) :
    OriginalCircuit (Layout.mapOwner owner a ++ tail) (Layout.mapOwner owner b ++ tail) :=
  Circuit.gate (OriginalGate.mk owner hC L hL hG tail)

/-- A circuit framed by a list of untouched registers. -/
abbrev frameList {ℓ ℓ' : Layout P} (ℓ₀ : Layout P) (w : OriginalCircuit ℓ ℓ') :
    OriginalCircuit (ℓ₀ ++ ℓ) (ℓ₀ ++ ℓ') :=
  Circuit.frameList (κ := LocalCondition.contraction) (G := OriginalGate) ℓ₀ w

/-- Identify equal input and output layouts without adding an operation. -/
abbrev castLayouts {ℓ ℓ' a b : Layout P} (w : OriginalCircuit ℓ ℓ') (h : ℓ = a) (h' : ℓ' = b) :
    OriginalCircuit a b :=
  Circuit.castLayouts (κ := LocalCondition.contraction) (G := OriginalGate) w h h'

/-- Induction on the constructors of `OriginalCircuit`. -/
@[induction_eliminator, elab_as_elim]
theorem induction {motive : {ℓ ℓ' : Layout P} → OriginalCircuit ℓ ℓ' → Prop}
    (id : ∀ ℓ : Layout P, motive (OriginalCircuit.id ℓ))
    (comp : ∀ {ℓ₁ ℓ₂ ℓ₃ : Layout P} (w : OriginalCircuit ℓ₁ ℓ₂) (w' : OriginalCircuit ℓ₂ ℓ₃),
      motive w → motive w' → motive (OriginalCircuit.comp w w'))
    (privateMap : ∀ (p : P) {a b : Layout P} (ha : ∀ r ∈ a, r.owner = p)
      (hb : ∀ r ∈ b, r.owner = p) (A : Mem a →L[ℂ] Mem b) (hA : ‖A‖ ≤ 1) (tail : Layout P),
      motive (OriginalCircuit.privateMap p ha hb A hA tail))
    (nonprivateGate : ∀ {C : Type} [Fintype C] (owner : C ↪ P) (hC : Fintype.card C ≠ 1)
      {a b : Layout C} (L : PartyGate a b) (hL : ∀ q ∈ L, q.2.IsAllowed)
      (hG : ‖PartyCircuit.gate (toGate L)‖ ≤ 1) (tail : Layout P),
      motive (OriginalCircuit.nonprivateGate owner hC L hL hG tail))
    (swap : ∀ (r r' : Reg P) (ℓ : Layout P), motive (OriginalCircuit.swap r r' ℓ))
    (frame : ∀ (r : Reg P) {ℓ ℓ' : Layout P} (w : OriginalCircuit ℓ ℓ'),
      motive w → motive (OriginalCircuit.frame r w))
    {ℓ ℓ' : Layout P} (w : OriginalCircuit ℓ ℓ') : motive w := by
  induction w with
  | id ℓ₀ => exact id ℓ₀
  | comp w w' ih ih' => exact comp w w' ih ih'
  | localMap p h₁ h₂ U ℓ hU => exact privateMap p h₁ h₂ U hU ℓ
  | gate g =>
      cases g with
      | mk owner hC L hL hG tail => exact nonprivateGate owner hC L hL hG tail
  | swap r r' ℓ => exact swap r r' ℓ
  | frame r w ih => exact frame r w ih

/-- Embed the original chronology into the effect-elimination syntax without
expanding private gates. Source: polynomial-PEPS 04-compression.tex, lines 199–212. -/
def produce : {a b : Layout P} → OriginalCircuit a b → EffectCircuit a b
  | _, _, .id a => .id a
  | _, _, .comp w v => .comp w.produce v.produce
  | _, _, .localMap p ha hb A tail _ => .localMap p ha hb A tail
  | _, _, .gate (@OriginalGate.mk _ _ _ owner _ _ _ L _ _ tail) => EffectCircuit.gate owner L tail
  | _, _, .swap r s tail => .swap r s tail
  | _, _, .frame r w => .frame r w.produce

/-- Count original nonprivate gates, excluding private maps and permutations
of tensor-factor order. Source: polynomial-PEPS 04-compression.tex, lines 199–202. -/
abbrev nonprivateCount {a b : Layout P} (w : OriginalCircuit a b) : ℕ :=
  w.gateCount

/-- The produced circuit has exactly the original operator, including all
spectator identities. Source: polynomial-PEPS 04-compression.tex, lines 21–36. -/
theorem eval_produce {a b : Layout P} (w : OriginalCircuit a b) :
    w.produce.eval = w.eval := by
  induction w with
  | id => rfl
  | comp w v ihw ihv => simp only [produce, Circuit.eval_comp, ihw, ihv]
  | privateMap => rfl
  | nonprivateGate => rfl
  | swap => rfl
  | frame r w ih => simp only [produce, Circuit.eval_frame, ih]

/-- The producer establishes contraction and constituent normalization; these
are not operator-comparison premises.
Source: polynomial-PEPS 04-compression.tex, lines 28–35 and 55–57. -/
theorem isAllowed_produce {a b : Layout P} (w : OriginalCircuit a b) :
    w.produce.IsAllowed := by
  induction w with
  | id => trivial
  | comp w v ihw ihv => exact ⟨ihw, ihv⟩
  | privateMap p ha hb A hA tail => exact hA
  | nonprivateGate owner hC L hL hG tail => exact ⟨hL, hG⟩
  | swap => trivial
  | frame r w ih => exact ih

/-- Exactly one expanded occurrence is produced for each original nonprivate
gate. Source: polynomial-PEPS 04-compression.tex, lines 199–217. -/
theorem expandedGateCount_produce {a b : Layout P} (w : OriginalCircuit a b) :
    w.produce.expandedGateCount = w.nonprivateCount := by
  induction w with
  | id => rfl
  | comp w v ihw ihv => exact congrArg₂ (· + ·) ihw ihv
  | privateMap => rfl
  | nonprivateGate => rfl
  | swap => rfl
  | frame r w ih => exact ih

/-- Original nonprivate occurrences are kept distinct even when their operators
coincide. Source: polynomial-PEPS 04-compression.tex, lines 199–229. -/
abbrev nonprivateLocations {a b : Layout P} (w : OriginalCircuit a b) : Type :=
  Circuit.gateLocations w

/-- The producer neither merges nor creates nonprivate gate occurrences.
Source: polynomial-PEPS 04-compression.tex, lines 199–229. -/
def produceLocationsEquiv : {a b : Layout P} → (w : OriginalCircuit a b) →
    nonprivateLocations w ≃ Circuit.gateLocations w.produce
  | _, _, .id _ => Equiv.refl _
  | _, _, .comp w v => Equiv.sumCongr (produceLocationsEquiv w) (produceLocationsEquiv v)
  | _, _, .localMap .. => Equiv.refl _
  | _, _, .gate (@OriginalGate.mk _ _ _ _ _ _ _ _ _ _ _) => Equiv.refl _
  | _, _, .swap .. => Equiv.refl _
  | _, _, .frame _ w => produceLocationsEquiv w

/-- Original participating sets are preserved by the occurrence correspondence.
Source: polynomial-PEPS 04-compression.tex, line 229. -/
theorem participants_produce {a b : Layout P} (w : OriginalCircuit a b)
    (g : w.nonprivateLocations) :
    Circuit.participants w.produce (w.produceLocationsEquiv g) = Circuit.participants w g := by
  induction w with
  | id => exact nomatch g
  | comp w v ihw ihv =>
      cases g with
      | inl g => exact ihw g
      | inr g => exact ihv g
  | privateMap => exact nomatch g
  | nonprivateGate => rfl
  | swap => exact nomatch g
  | frame r w ih => exact ih g

/-- A nonprivate occurrence has a number of participants different from one.
Empty participating sets are permitted, as in the manuscript definition.
Source: polynomial-PEPS 04-compression.tex, lines 25–27. -/
theorem card_participants_ne_one {a b : Layout P} (w : OriginalCircuit a b)
    (g : w.nonprivateLocations) : (w.participants g).card ≠ 1 := by
  induction w with
  | id => exact nomatch g
  | comp w v ihw ihv =>
      cases g with
      | inl g => exact ihw g
      | inr g => exact ihv g
  | privateMap => exact nomatch g
  | nonprivateGate owner hC L hL hG tail =>
      simpa only [Circuit.participants, GateFamily.participants, OriginalGate.toEffectGate,
        EffectGate.participants, Finset.card_map, Finset.card_univ] using hC
  | swap => exact nomatch g
  | frame r w ih => exact ih g

/-- Original effect-count and coefficient-sum bounds, before any permutation
averages are expanded. Source: polynomial-PEPS 04-compression.tex, lines 199–208. -/
def IsExpansionBounded (r : ℕ) (S : ℝ) : {a b : Layout P} → OriginalCircuit a b → Prop
  | _, _, .id _ => True
  | _, _, .comp w v => w.IsExpansionBounded r S ∧ v.IsExpansionBounded r S
  | _, _, OriginalCircuit.privateMap .. => True
  | _, _, Circuit.gate (@OriginalGate.mk _ _ _ _ _ _ _ L _ _ _) =>
      (∀ q ∈ L, q.2.toEffectChain.effectCount ≤ r) ∧ (L.map fun q => ‖q.1‖).sum ≤ S
  | _, _, .swap .. => True
  | _, _, .frame _ w => w.IsExpansionBounded r S

/-- The producer transports exactly the original expansion bounds, rather than
assuming bounds on a replacement expansion.
Source: polynomial-PEPS 04-compression.tex, lines 199–208. -/
theorem isExpansionBounded_produce_iff {a b : Layout P} (w : OriginalCircuit a b)
    (r : ℕ) (S : ℝ) : w.produce.IsExpansionBounded r S ↔ w.IsExpansionBounded r S := by
  induction w with
  | id => rfl
  | comp w v ihw ihv =>
      exact and_congr ihw ihv
  | privateMap => rfl
  | nonprivateGate => rfl
  | swap => rfl
  | frame r w ih => exact ih
end OriginalCircuit

namespace ProductInput
/-- One register holds the entire original private memory of each party,
with every finite party represented once.
Source: polynomial-PEPS 04-compression.tex, lines 137–139. -/
def wholePartyLayout [Fintype P] (H : P → HSpace) : Layout P :=
  Finset.univ.toList.map fun p => (⟨p, H p⟩ : Reg P)

/-- The source's product input, with no separability condition inside a party's
private memory. Source: polynomial-PEPS 04-compression.tex, lines 137–139. -/
def ofAllParties [Fintype P] (H : P → HSpace) (x : ∀ p, H p)
    (hx : ∀ p, ‖x p‖ = 1) : ProductInput (wholePartyLayout H) :=
  ofParties H x hx Finset.univ.toList

/-- The list of original party owners is precisely an enumeration of all parties.
Source: polynomial-PEPS 04-compression.tex, lines 137–139. -/
theorem owners_wholePartyLayout [Fintype P] (H : P → HSpace) :
    (wholePartyLayout H).map Reg.owner = (Finset.univ : Finset P).toList := by
  simp only [wholePartyLayout, List.map_map, Function.comp_def, List.map_id_fun', id_eq]

/-- There is exactly one original whole-memory register for each party.
Source: polynomial-PEPS 04-compression.tex, lines 137–139. -/
theorem nodup_owners_wholePartyLayout [Fintype P] (H : P → HSpace) :
    ((wholePartyLayout H).map Reg.owner).Nodup := by
  rw [owners_wholePartyLayout]
  exact Finset.nodup_toList _

/-- No original party is omitted from the private input.
Source: polynomial-PEPS 04-compression.tex, lines 137–139. -/
theorem mem_owners_wholePartyLayout [Fintype P] (H : P → HSpace) (p : P) :
    p ∈ (wholePartyLayout H).map Reg.owner := by
  rw [owners_wholePartyLayout, Finset.mem_toList]
  exact Finset.mem_univ p
end ProductInput

end TNLean.Lattice.PartyCircuit
