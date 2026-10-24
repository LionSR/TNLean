/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.PartyCircuit.ApproximateCircuitResources

/-!
# Changing the monomial lists of a fixed original chronology

An original operator is assigned to each gate occurrence of a reference
chronology. New monomial lists may be chosen independently at those same
occurrences. This changes only the lists: the private maps, participant
embeddings, spectator registers, input and output layouts, and chronological
composition are retained. Evaluation with the original operators is therefore
unchanged. The occurrence correspondence and all participant and lifetime
identities are consequences of this construction.

No assumption on the reference lists is needed. In particular, the reference
chronology does not have to provide an exact or allowed monomial expansion.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 21–43,
137–151 and 590–600.
-/

noncomputable section
namespace TNLean.Lattice.PartyCircuit.EffectCircuit
variable {P : Type}

/-- One monomial list on the original local input and output spaces of each
nonprivate gate occurrence. Composition keeps distinct occurrences separate.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 21–43 and 590–600. -/
@[reducible] def GateLists : {a b : Layout P} → EffectCircuit a b → Type 1
  | _, _, .id _ => PUnit
  | _, _, .comp w v => GateLists w × GateLists v
  | _, _, .localMap .. => PUnit
  | _, _, @EffectCircuit.gate _ _ _ _ a b _ _ => PartyGate a b
  | _, _, .swap .. => PUnit
  | _, _, .frame _ w => GateLists w

/-- Replace only the monomial list at each original gate occurrence.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 590–600. -/
def reexpand : {a b : Layout P} → (w : EffectCircuit a b) →
    w.GateLists → EffectCircuit a b
  | _, _, .id a, _ => .id a
  | _, _, .comp w v, lists => .comp (w.reexpand lists.1) (v.reexpand lists.2)
  | _, _, .localMap p ha hb A tail, _ => .localMap p ha hb A tail
  | _, _, @EffectCircuit.gate _ _ _ owner _ _ _ tail, lists => .gate owner lists tail
  | _, _, .swap r s tail, _ => .swap r s tail
  | _, _, .frame r w, lists => .frame r (w.reexpand lists)

/-- The same original operators on the reexpanded chronology.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 590–600. -/
def reexpandGateMaps : {a b : Layout P} → (w : EffectCircuit a b) →
    (lists : w.GateLists) → w.GateMaps → (w.reexpand lists).GateMaps
  | _, _, .id _, _, _ => PUnit.unit
  | _, _, .comp w v, lists, G =>
      (w.reexpandGateMaps lists.1 G.1, v.reexpandGateMaps lists.2 G.2)
  | _, _, .localMap .., _, _ => PUnit.unit
  | _, _, @EffectCircuit.gate _ _ _ _ _ _ _ _, _, G => G
  | _, _, .swap .., _, _ => PUnit.unit
  | _, _, .frame _ w, lists, G => w.reexpandGateMaps lists G

/-- Original-operator evaluation is invariant under a change of monomial lists.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 590–600. -/
theorem evalWithGateMaps_reexpand {a b : Layout P} (w : EffectCircuit a b) :
    ∀ (lists : w.GateLists) (G : w.GateMaps),
      (w.reexpand lists).evalWithGateMaps (w.reexpandGateMaps lists G) =
        w.evalWithGateMaps G := by
  induction w with
  | id => intro lists G; rfl
  | comp w v ihw ihv =>
      intro lists G
      exact congrArg₂ ContinuousLinearMap.comp (ihv lists.2 G.2) (ihw lists.1 G.1)
  | localMap => intro lists G; rfl
  | gate => intro lists G; rfl
  | swap => intro lists G; rfl
  | frame r w ih =>
      intro lists G
      exact congrArg (fun A ↦ A.lTensor r.space) (ih lists G)

/-- Reexpansion preserves the original chronological gate occurrences.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 21–43 and 590–600. -/
def reexpandLocationsEquiv : {a b : Layout P} → (w : EffectCircuit a b) →
    (lists : w.GateLists) → (w.reexpand lists).gateLocations ≃ w.gateLocations
  | _, _, .id _, _ => Equiv.refl _
  | _, _, .comp w v, lists => Equiv.sumCongr
      (w.reexpandLocationsEquiv lists.1) (v.reexpandLocationsEquiv lists.2)
  | _, _, .localMap .., _ => Equiv.refl _
  | _, _, @EffectCircuit.gate _ _ _ _ _ _ _ _, _ => Equiv.refl _
  | _, _, .swap .., _ => Equiv.refl _
  | _, _, .frame _ w, lists => w.reexpandLocationsEquiv lists

/-- The correspondence retains each exact prescribed participating set.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 21–36 and 590–600. -/
theorem participants_reexpand {a b : Layout P} (w : EffectCircuit a b) :
    ∀ (lists : w.GateLists) (g : (w.reexpand lists).gateLocations),
      (w.reexpand lists).participants g =
        w.participants (w.reexpandLocationsEquiv lists g) := by
  induction w with
  | id => intro lists g; exact nomatch g
  | comp w v ihw ihv =>
      intro lists g
      cases g with
      | inl g => exact ihw lists.1 g
      | inr g => exact ihv lists.2 g
  | localMap => intro lists g; exact nomatch g
  | gate => intro lists g; rfl
  | swap => intro lists g; exact nomatch g
  | frame r w ih => exact ih

/-- Reexpansion does not add or remove nonprivate gate occurrences.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–151 and 590–600. -/
theorem expandedGateCount_reexpand {a b : Layout P} (w : EffectCircuit a b) :
    ∀ lists : w.GateLists, (w.reexpand lists).expandedGateCount = w.expandedGateCount := by
  induction w with
  | id => intro lists; rfl
  | comp w v ihw ihv =>
      intro lists
      exact congrArg₂ (· + ·) (ihw lists.1) (ihv lists.2)
  | localMap => intro lists; rfl
  | gate => intro lists; rfl
  | swap => intro lists; rfl
  | frame r w ih => exact ih

/-- Every party has exactly the same whole-lifetime gate participation count
at every choice of approximation precision.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 140–142 and 590–600. -/
theorem participationCount_reexpand {a b : Layout P} (w : EffectCircuit a b)
    (lists : w.GateLists) (p : P) :
    Nat.card {g : (w.reexpand lists).gateLocations // p ∈ (w.reexpand lists).participants g} =
      Nat.card {g : w.gateLocations // p ∈ w.participants g} := by
  apply Nat.card_congr
  exact (w.reexpandLocationsEquiv lists).subtypeEquiv (fun g ↦ by
    rw [w.participants_reexpand lists g])

end TNLean.Lattice.PartyCircuit.EffectCircuit
