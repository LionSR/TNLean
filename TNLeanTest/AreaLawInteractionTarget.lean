/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.GraphInteractionTarget

/-!
# Target-sensitive interaction-chain regressions

These consumers distinguish the target-sensitive coefficient from the unrestricted chain
weight, check that the initial support contributes at length zero, and retain repeated visits
to a singleton support. Disconnected target coefficients vanish with arbitrary real weights.
-/

open TNLean.PEPS.AreaLaw

namespace TNLeanTest

example (F : Finset (Finset (Fin 2))) (w : Finset (Fin 2) → ℝ) :
    interactionChainTargetWeightSum F w 1 {0, 1} 0 = 1 := by
  simp [interactionChainTargetWeightSum]

example (F : Finset (Finset (Fin 2))) (w : Finset (Fin 2) → ℝ) :
    interactionChainTargetWeightSum F w 1 {0} 0 = 0 := by
  simp [interactionChainTargetWeightSum]

example {V : Type*} [DecidableEq V] (a : V) (J : ℝ) (n : ℕ) :
    interactionChainTargetWeightSum {{a}} (fun _ ↦ J) a {a} n = J ^ n := by
  have hfilter : ({{a}} : Finset (Finset V)).filter (fun Y ↦ ¬ Disjoint Y {a}) = {{a}} := by
    apply Finset.filter_eq_self.mpr
    intro Y hY
    have hYa : Y = {a} := Finset.mem_singleton.mp hY
    subst Y
    exact Finset.not_disjoint_iff.mpr ⟨a, by simp, by simp⟩
  induction n with
  | zero => simp [interactionChainTargetWeightSum]
  | succ n ih =>
      rw [interactionChainTargetWeightSum, hfilter, Finset.sum_singleton, ih,
        pow_succ, mul_comm]

example {V : Type*} [DecidableEq V] (y : V) (w : Finset V → ℝ) (n : ℕ) :
    interactionChainTargetWeightSum {∅} w y ∅ n = 0 := by
  cases n <;> simp [interactionChainTargetWeightSum]

-- In a disconnected two-site graph, even negative weights cannot reach the other site.
example (w : Finset (Fin 2) → ℝ) (n : ℕ) :
    interactionChainTargetWeightSum {{0}, {1}} w 1 {0} n = 0 := by
  have hrange : ∀ X ∈ ({{0}, {1}} : Finset (Finset (Fin 2))),
      ∀ a ∈ X, ∀ z ∈ X, ∃ p : (⊥ : SimpleGraph (Fin 2)).Walk a z, p.length ≤ 0 := by
    intro X hX a ha z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hX
    rcases hX with rfl | rfl <;>
      simp only [Finset.mem_singleton] at ha hz <;>
      subst a <;> subst z <;> exact ⟨SimpleGraph.Walk.nil, by simp⟩
  apply interactionChainTargetWeightSum_eq_zero_of_edist_eq_top
    {{0}, {1}} w (⊥ : SimpleGraph (Fin 2)) 0 hrange 1 n {0} (by simp) 0 (by simp)
  apply SimpleGraph.edist_eq_top_of_not_reachable
  intro h
  exact (by decide : (0 : Fin 2) ≠ 1) (SimpleGraph.reachable_bot.mp h)

-- Zero continuation tests the initial support even if it is absent from the family.
example : interactionChainTargetWeightSum (∅ : Finset (Finset (Fin 1)))
    (fun _ ↦ 0) 0 {0} 0 = 1 := by
  simp [interactionChainTargetWeightSum]

example : interactionChainTargetWeightSum (∅ : Finset (Finset (Fin 1)))
    (fun _ ↦ 0) 0 {0} 1 = 0 := by
  simp [interactionChainTargetWeightSum]

set_option linter.hashCommand false

/--
info: 'TNLean.PEPS.AreaLaw.interactionChainTargetWeightSum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.interactionChainTargetWeightSum
/--
info: 'TNLean.PEPS.AreaLaw.interactionChainTargetWeightSum_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.interactionChainTargetWeightSum_nonneg
/--
info: 'TNLean.PEPS.AreaLaw.interactionChainTargetWeightSum_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.interactionChainTargetWeightSum_le
/--
info: 'TNLean.PEPS.AreaLaw.interactionChainTargetWeightSum_eq_zero_of_no_walk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.interactionChainTargetWeightSum_eq_zero_of_no_walk
/--
info: 'TNLean.PEPS.AreaLaw.interactionChainTargetWeightSum_eq_zero_of_lt_edist' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.interactionChainTargetWeightSum_eq_zero_of_lt_edist
/--
info: 'TNLean.PEPS.AreaLaw.interactionChainTargetWeightSum_eq_zero_of_edist_eq_top' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.interactionChainTargetWeightSum_eq_zero_of_edist_eq_top
/--
info: 'TNLean.PEPS.AreaLaw.interactionChainTargetWeightSum_le_indicator_pow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.interactionChainTargetWeightSum_le_indicator_pow

end TNLeanTest
