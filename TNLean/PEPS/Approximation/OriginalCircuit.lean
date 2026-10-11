/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.PEPS.Approximation.EffectCircuitReplacement

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
namespace TNLean.PEPS.PairEffect
variable {P : Type}

/-- An original chronology with arbitrary private contractions and prescribed
nonprivate participating sets. Registers exchanged by the syntax retain their owners.
Source: polynomial-PEPS 04-compression.tex, lines 21–36 and 199–229. -/
inductive OriginalCircuit : Layout P → Layout P → Type 1
  | id (a : Layout P) : OriginalCircuit a a
  | comp {a b d : Layout P} (w : OriginalCircuit a b) (v : OriginalCircuit b d) :
      OriginalCircuit a d
  | privateMap (p : P) {a b : Layout P}
      (ha : ∀ r ∈ a, r.owner = p) (hb : ∀ r ∈ b, r.owner = p)
      (A : Mem a →L[ℂ] Mem b) (hA : ‖A‖ ≤ 1) (tail : Layout P) :
      OriginalCircuit (a ++ tail) (b ++ tail)
  | nonprivateGate {C : Type} [Fintype C] (owner : C ↪ P)
      (hC : Fintype.card C ≠ 1) {a b : Layout C} (L : PartyGate a b)
      (hL : ∀ q ∈ L, q.2.IsAllowed) (hG : ‖gate (toGate L)‖ ≤ 1) (tail : Layout P) :
      OriginalCircuit (Layout.mapOwner owner a ++ tail) (Layout.mapOwner owner b ++ tail)
  | swap (r s : Reg P) (tail : Layout P) : OriginalCircuit (r :: s :: tail) (s :: r :: tail)
  | frame (r : Reg P) {a b : Layout P} (w : OriginalCircuit a b) :
      OriginalCircuit (r :: a) (r :: b)

namespace OriginalCircuit
/-- The original operator, evaluated directly from its local maps and original
monomial expansions. Source: polynomial-PEPS 04-compression.tex, lines 21–36. -/
def eval : {a b : Layout P} → OriginalCircuit a b → Mem a →L[ℂ] Mem b
  | _, _, .id _ => .id ℂ _
  | _, _, .comp w v => v.eval ∘L w.eval
  | _, _, @OriginalCircuit.privateMap _ _ a b _ _ A _ tail =>
      isoL (appendIso b tail).symm ∘L A.rTensor (Mem tail) ∘L isoL (appendIso a tail)
  | _, _, @OriginalCircuit.nonprivateGate _ _ _ owner _ a b L _ _ tail =>
      isoL (appendIso (Layout.mapOwner owner b) tail).symm ∘L
        (isoL (Layout.mapOwnerIso owner b) ∘L gate (toGate L) ∘L
          isoL (Layout.mapOwnerIso owner a).symm).rTensor (Mem tail) ∘L
            isoL (appendIso (Layout.mapOwner owner a) tail)
  | _, _, .swap r s tail => leftCommL r.space s.space (Mem tail)
  | _, _, .frame r w => w.eval.lTensor r.space

/-- Embed the original chronology into the effect-elimination syntax without
expanding private gates. Source: polynomial-PEPS 04-compression.tex, lines 199–212. -/
def produce : {a b : Layout P} → OriginalCircuit a b → EffectCircuit a b
  | _, _, .id a => .id a
  | _, _, .comp w v => .comp w.produce v.produce
  | _, _, .privateMap p ha hb A _ tail => .localMap p ha hb A tail
  | _, _, @OriginalCircuit.nonprivateGate _ C _ owner _ a b L _ _ tail =>
      @EffectCircuit.gate P C _ owner a b L tail
  | _, _, .swap r s tail => .swap r s tail
  | _, _, .frame r w => .frame r w.produce

/-- Count original nonprivate gates, excluding private maps and permutations
of tensor-factor order. Source: polynomial-PEPS 04-compression.tex, lines 199–202. -/
def nonprivateCount : {a b : Layout P} → OriginalCircuit a b → ℕ
  | _, _, .id _ => 0
  | _, _, .comp w v => w.nonprivateCount + v.nonprivateCount
  | _, _, .privateMap .. => 0
  | _, _, @OriginalCircuit.nonprivateGate _ _ _ _ _ _ _ _ _ _ _ => 1
  | _, _, .swap .. => 0
  | _, _, .frame _ w => w.nonprivateCount

/-- The produced circuit has exactly the original operator, including all
spectator identities. Source: polynomial-PEPS 04-compression.tex, lines 21–36. -/
theorem eval_produce {a b : Layout P} (w : OriginalCircuit a b) :
    w.produce.eval = w.eval := by
  induction w with
  | id => rfl
  | comp w v ihw ihv => simp only [produce, EffectCircuit.eval, eval, ihw, ihv]
  | privateMap => rfl
  | nonprivateGate => rfl
  | swap => rfl
  | frame r w ih => simp only [produce, EffectCircuit.eval, eval, ih]

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
  | comp w v ihw ihv =>
      simp only [produce, EffectCircuit.expandedGateCount, nonprivateCount, ihw, ihv]
  | privateMap => rfl
  | nonprivateGate => rfl
  | swap => rfl
  | frame r w ih => exact ih
end OriginalCircuit

namespace EffectCircuit
/-- The expanded occurrences of the analytic circuit, excluding private maps
and changes of tensor order. Source: polynomial-PEPS 04-compression.tex, lines 199–229. -/
def gateLocations : {a b : Layout P} → EffectCircuit a b → Type
  | _, _, .id _ => Empty
  | _, _, .comp w v => gateLocations w ⊕ gateLocations v
  | _, _, .localMap .. => Empty
  | _, _, @EffectCircuit.gate _ _ _ _ _ _ _ _ => Unit
  | _, _, .swap .. => Empty
  | _, _, .frame _ w => gateLocations w

/-- The original prescribed participating set at each expanded occurrence.
Source: polynomial-PEPS 04-compression.tex, lines 25–27 and 229. -/
def participants : {a b : Layout P} → (w : EffectCircuit a b) → gateLocations w → Finset P
  | _, _, .id _ => Empty.elim
  | _, _, .comp w v => Sum.elim (participants w) (participants v)
  | _, _, .localMap .. => Empty.elim
  | _, _, @EffectCircuit.gate _ _ _ owner _ _ _ _ => fun _ => Finset.univ.map owner
  | _, _, .swap .. => Empty.elim
  | _, _, .frame _ w => participants w
end EffectCircuit

namespace OriginalCircuit
/-- Original nonprivate occurrences are kept distinct even when their operators
coincide. Source: polynomial-PEPS 04-compression.tex, lines 199–229. -/
def nonprivateLocations : {a b : Layout P} → OriginalCircuit a b → Type
  | _, _, .id _ => Empty
  | _, _, .comp w v => nonprivateLocations w ⊕ nonprivateLocations v
  | _, _, .privateMap .. => Empty
  | _, _, @OriginalCircuit.nonprivateGate _ _ _ _ _ _ _ _ _ _ _ => Unit
  | _, _, .swap .. => Empty
  | _, _, .frame _ w => nonprivateLocations w

/-- The source-facing original participant image at a nonprivate occurrence.
Source: polynomial-PEPS 04-compression.tex, lines 25–27 and 229. -/
def participants : {a b : Layout P} → (w : OriginalCircuit a b) →
    nonprivateLocations w → Finset P
  | _, _, .id _ => Empty.elim
  | _, _, .comp w v => Sum.elim (participants w) (participants v)
  | _, _, .privateMap .. => Empty.elim
  | _, _, @OriginalCircuit.nonprivateGate _ _ _ owner _ _ _ _ _ _ _ =>
      fun _ => Finset.univ.map owner
  | _, _, .swap .. => Empty.elim
  | _, _, .frame _ w => participants w

/-- The producer neither merges nor creates nonprivate gate occurrences.
Source: polynomial-PEPS 04-compression.tex, lines 199–229. -/
def produceLocationsEquiv : {a b : Layout P} → (w : OriginalCircuit a b) →
    nonprivateLocations w ≃ EffectCircuit.gateLocations w.produce
  | _, _, .id _ => Equiv.refl _
  | _, _, .comp w v => Equiv.sumCongr (produceLocationsEquiv w) (produceLocationsEquiv v)
  | _, _, .privateMap .. => Equiv.refl _
  | _, _, @OriginalCircuit.nonprivateGate _ _ _ _ _ _ _ _ _ _ _ => Equiv.refl _
  | _, _, .swap .. => Equiv.refl _
  | _, _, .frame _ w => produceLocationsEquiv w

/-- Original participating sets are preserved by the occurrence correspondence.
Source: polynomial-PEPS 04-compression.tex, line 229. -/
theorem participants_produce {a b : Layout P} (w : OriginalCircuit a b)
    (g : w.nonprivateLocations) :
    EffectCircuit.participants w.produce (w.produceLocationsEquiv g) = w.participants g := by
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
      simpa only [participants, Finset.card_map, Finset.card_univ] using hC
  | swap => exact nomatch g
  | frame r w ih => exact ih g

/-- Original effect-count and coefficient-sum bounds, before any permutation
averages are expanded. Source: polynomial-PEPS 04-compression.tex, lines 199–208. -/
def IsExpansionBounded (r : ℕ) (S : ℝ) : {a b : Layout P} → OriginalCircuit a b → Prop
  | _, _, .id _ => True
  | _, _, .comp w v => w.IsExpansionBounded r S ∧ v.IsExpansionBounded r S
  | _, _, .privateMap .. => True
  | _, _, @OriginalCircuit.nonprivateGate _ _ _ _ _ _ _ L _ _ _ =>
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
      simp only [produce, EffectCircuit.IsExpansionBounded, IsExpansionBounded, ihw, ihv]
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

end TNLean.PEPS.PairEffect
