/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SelectedChainProbability
import Mathlib.Tactic.FinCases

/-!
# Regression tests for selected-chain probabilities

The two-time bound uses the actual nominal-front selections, fixes all offsets,
and permits the same label to be prescribed more than once. The event may be
restricted further without any independence assumption on that restriction.
-/

set_option autoImplicit false

open TNLean.PEPS.AreaLaw.Scan
open scoped BigOperators

namespace TNLeanTest.SelectedChainProbability

variable {V I : Type*} [Fintype I] [LinearOrder I]
  (S : CollarScan V I)

-- Two distinct times in the same band require two independent choice coordinates.
example (hM : 0 < S.M) (offsets : Fin S.K → Fin S.m) (g : Fin S.K)
    (side : Bool) (i : I)
    (E : (Fin 2 → ChargeChoices S.K S.M) → Prop) [DecidablePred E]
    (hhit : ∀ c, E c → ∀ t : Fin 2,
      (c t g).1 = side ∧ S.selected g (offsets g) (t.val + 1) (c t g) = some i) :
    (∑ c : Fin 2 → ChargeChoices S.K S.M,
      if E c then ((1 / (2 * (S.M : ℝ))) ^ S.K) ^ 2 else 0) ≤
        (1 / (2 * (S.M : ℝ))) ^ 2 := by
  simpa using S.sum_chargePathWeight_le_of_selected hM offsets Finset.univ
    (fun _ ↦ g) (fun _ ↦ side) (fun _ ↦ i) E (fun c hc t _ ↦ hhit c hc t)

-- No prescribed hit means total event mass at most one, even with no charge rounds.
example (hM : 0 < S.M) {k : ℕ} (offsets : Fin S.K → Fin S.m)
    (band : Fin k → Fin S.K) (side : Fin k → Bool) (label : Fin k → I)
    (E : (Fin k → ChargeChoices S.K S.M) → Prop) [DecidablePred E] :
    (∑ c : Fin k → ChargeChoices S.K S.M,
      if E c then ((1 / (2 * (S.M : ℝ))) ^ S.K) ^ k else 0) ≤ 1 := by
  simpa using S.sum_chargePathWeight_le_of_selected hM offsets ∅ band side label E
    (by simp)

-- Prescribing both side and label remains necessary even if all anchors coincide.
example (hM : 0 < S.M) (g : Fin S.K) (r k : ℕ) (side : Bool) (i : I) :
    (∑ c : ChargeChoices S.K S.M,
      if (c g).1 = side ∧ S.selected g r k (c g) = some i
      then chargeWeight c else 0) ≤ 1 / (2 * (S.M : ℝ)) :=
  S.sum_chargeWeight_selected_le hM g r k side i


-- A finite cover may use overlapping chains; the union bound needs no disjointness.
example (hM : 0 < S.M) (offsets : Fin S.K → Fin S.m) (g : Fin S.K) (i : I)
    (E : (Fin 2 → ChargeChoices S.K S.M) → Prop) [DecidablePred E]
    (hcover : ∀ c, E c → ∃ side : Bool, ∀ t : Fin 2,
      (c t g).1 = side ∧ S.selected g (offsets g) (t.val + 1) (c t g) = some i) :
    (∑ c : Fin 2 → ChargeChoices S.K S.M,
      if E c then ((1 / (2 * (S.M : ℝ))) ^ S.K) ^ 2 else 0) ≤
        2 * (1 / (2 * (S.M : ℝ))) ^ 2 := by
  have h := S.sum_chargePathWeight_le_sum_of_selected_cover hM offsets
    (Finset.univ : Finset Bool) (fun _ ↦ Finset.univ) (fun _ _ ↦ g)
    (fun b _ ↦ b) (fun _ _ ↦ i) E ?_
  · simpa [two_mul] using h
  · intro c hc
    obtain ⟨b, hb⟩ := hcover c hc
    exact ⟨b, Finset.mem_univ b, fun t _ ↦ hb t⟩


-- Natural event times are the direct interface used by extracted charge ancestries.
example (hM : 0 < S.M) (offsets : Fin S.K → Fin S.m) (g : Fin S.K)
    (side : Bool) (i : I)
    (E : (Fin 2 → ChargeChoices S.K S.M) → Prop) [DecidablePred E]
    (hhit : ∀ c, E c → ∀ t : Fin 2,
      (c t g).1 = side ∧ S.selected g (offsets g) (t.val + 1) (c t g) = some i) :
    (∑ c : Fin 2 → ChargeChoices S.K S.M,
      if E c then ((1 / (2 * (S.M : ℝ))) ^ S.K) ^ 2 else 0) ≤
        (1 / (2 * (S.M : ℝ))) ^ 2 := by
  apply S.sum_chargePathWeight_le_of_selected_list hM offsets g side [(0, i), (1, i)]
    (by
      intro e he
      have he' : e = (0, i) ∨ e = (1, i) := by simpa using he
      rcases he' with rfl | rfl <;> norm_num)
    (by simp) E
  intro c hc e he
  have he' : e = (0, i) ∨ e = (1, i) := by simpa using he
  rcases he' with rfl | rfl
  · exact hhit c hc 0
  · exact hhit c hc 1


-- A cover consisting of the empty list has unit bound without assuming labels exist.
example (hM : 0 < S.M) {k : ℕ} (offsets : Fin S.K → Fin S.m)
    (g : Fin S.K) (side : Bool)
    (E : (Fin k → ChargeChoices S.K S.M) → Prop) [DecidablePred E] :
    (∑ c : Fin k → ChargeChoices S.K S.M,
      if E c then ((1 / (2 * (S.M : ℝ))) ^ S.K) ^ k else 0) ≤ 1 := by
  classical
  have h := S.sum_chargePathWeight_le_sum_of_selected_list_cover hM offsets g side {[]}
    (by simp) (by simp) E (by
      intro c _
      refine ⟨[], Finset.mem_singleton_self _, ?_⟩
      simp)
  simpa using h

-- Both labels have the same anchor. Three slots leave one genuinely blank choice.
private abbrev repeatedAnchorScan : CollarScan (Fin 1) (Fin 2) where
  graph := ⊥
  A := Finset.univ
  depth := fun _ ↦ 2
  anchor := fun _ ↦ 0
  n := 3
  m := 1
  K := 1
  D := 1
  r₀ := 0
  C₁ := 1

private def chosenSlot (t : Fin 2) : Fin repeatedAnchorScan.M :=
  ⟨t.val, by
    have ht := t.isLt
    norm_num [CollarScan.M, chargeSlotCount, repeatedAnchorScan]
    omega⟩

private theorem selected_chosenSlot (t : Fin 2) :
    repeatedAnchorScan.selected 0 0 (t.val + 1) (false, chosenSlot t) = some t := by
  fin_cases t <;>
    norm_num [CollarScan.selected, CollarScan.candidates, paddedChargeSlot,
      orderedChargeCandidates, chargeCandidates, CollarScan.front, nominalFront,
      initialFront, fillCount, CollarScan.lower, CollarScan.upper, orientedDepth,
      repeatedAnchorScan, chosenSlot, Fin.sort_univ, List.finRange_succ]

-- Distinct prescribed labels at two charge times cost two factors of one sixth.
example :
    (∑ c : Fin 2 → ChargeChoices repeatedAnchorScan.K repeatedAnchorScan.M,
      if ∀ t : Fin 2, c t 0 = (false, chosenSlot t)
      then ((1 / (2 * (repeatedAnchorScan.M : ℝ))) ^ repeatedAnchorScan.K) ^ 2
      else 0) ≤ (1 / 36 : ℝ) := by
  have h := repeatedAnchorScan.sum_chargePathWeight_le_of_selected
    (by norm_num [CollarScan.M, chargeSlotCount, repeatedAnchorScan])
    (fun _ ↦ 0) Finset.univ (fun _ ↦ 0) (fun _ ↦ false) (fun t ↦ t)
    (fun c ↦ ∀ t : Fin 2, c t 0 = (false, chosenSlot t)) ?_
  · convert h using 1
    norm_num [CollarScan.M, chargeSlotCount, repeatedAnchorScan]
  · intro c hc t _
    rw [hc t]
    exact ⟨rfl, selected_chosenSlot t⟩

end TNLeanTest.SelectedChainProbability

set_option linter.hashCommand false

/--
info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.sum_chargeWeight_selected_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CollarScan.sum_chargeWeight_selected_le

/--
info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.sum_chargePathWeight_le_of_selected'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CollarScan.sum_chargePathWeight_le_of_selected


/--
info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.sum_chargePathWeight_le_sum_of_selected_cover'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CollarScan.sum_chargePathWeight_le_sum_of_selected_cover


/--
info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.sum_chargePathWeight_le_of_selected_list'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CollarScan.sum_chargePathWeight_le_of_selected_list


/--
info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.sum_chargePathWeight_le_sum_of_selected_list_cover'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CollarScan.sum_chargePathWeight_le_sum_of_selected_list_cover
