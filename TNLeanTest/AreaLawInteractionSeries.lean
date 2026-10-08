/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.GraphInteractionSeries

/-!
# Interaction propagation-series consumers

These checks retain the zero-time initial support, both time directions, the zero-budget
constant term, and the exact exponential series for arbitrarily signed singleton weights.
-/

open TNLean.PEPS.AreaLaw

namespace TNLeanTest

variable {V : Type*} [DecidableEq V]

example (F : Finset (Finset V)) (w : Finset V → ℝ) (y : V) (X : Finset V) (t : ℝ) :
    interactionChainPropagationSeries F w y X (-t) =
      interactionChainPropagationSeries F w y X t := by
  simp only [interactionChainPropagationSeries, abs_neg]

example (F : Finset (Finset V)) (w : Finset V → ℝ) (y : V) (X : Finset V) :
    interactionChainPropagationSeries F w y X 0 = if y ∈ X then 1 else 0 := by
  rw [interactionChainPropagationSeries, tsum_eq_single 0]
  · simp [interactionChainTargetWeightSum]
  · intro n hn
    simp [hn]

example (a : V) (t : ℝ) :
    interactionChainPropagationSeries {{a}} (fun _ ↦ 0) a {a} t = 1 := by
  have htarget (n : ℕ) :
      interactionChainTargetWeightSum {{a}} (fun _ ↦ 0) a {a} n =
        if n = 0 then 1 else 0 := by
    cases n <;> simp [interactionChainTargetWeightSum]
  simp [interactionChainPropagationSeries, htarget]

example (a : V) (J t : ℝ) :
    interactionChainPropagationSeries {{a}} (fun _ ↦ J) a {a} t =
      Real.exp (2 * |t| * J) := by
  have hfilter : ({{a}} : Finset (Finset V)).filter (fun Y ↦ ¬ Disjoint Y {a}) = {{a}} := by
    apply Finset.filter_eq_self.mpr
    intro Y hY
    have hYa : Y = {a} := Finset.mem_singleton.mp hY
    subst Y
    exact Finset.not_disjoint_iff.mpr ⟨a, by simp, by simp⟩
  have htarget (n : ℕ) :
      interactionChainTargetWeightSum {{a}} (fun _ ↦ J) a {a} n = J ^ n := by
    induction n with
    | zero => simp [interactionChainTargetWeightSum]
    | succ n ih =>
        rw [interactionChainTargetWeightSum, hfilter, Finset.sum_singleton, ih,
          pow_succ, mul_comm]
  unfold interactionChainPropagationSeries
  have hsum : HasSum (fun n : ℕ ↦ (2 * |t| * J) ^ n / n.factorial)
      (Real.exp (2 * |t| * J)) := by
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (2 * |t| * J)
  calc
    _ = ∑' n : ℕ, (2 * |t| * J) ^ n / n.factorial := by
      apply tsum_congr
      intro n
      rw [htarget, mul_pow]
      ring
    _ = _ := hsum.tsum_eq

-- The disconnected conclusion permits arbitrary weights and either sign of time.
example (F : Finset (Finset V)) (w : Finset V → ℝ) (G : SimpleGraph V) (R : ℕ)
    (hrange : ∀ X ∈ F, ∀ a ∈ X, ∀ z ∈ X, ∃ p : G.Walk a z, p.length ≤ R)
    (y : V) (X : Finset V) (hX : X ∈ F) (a : V) (ha : a ∈ X)
    (hd : G.edist a y = ⊤) (t : ℝ) :
    interactionChainPropagationSeries F w y X (-t) = 0 :=
  interactionChainPropagationSeries_eq_zero_of_edist_eq_top F w G R hrange y X hX a ha hd (-t)

set_option linter.hashCommand false

/--
info: 'TNLean.PEPS.AreaLaw.interactionChainTargetWeightSum_le_exponential' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.interactionChainTargetWeightSum_le_exponential
/--
info: 'TNLean.PEPS.AreaLaw.interactionChainPropagationSeries' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.interactionChainPropagationSeries
/--
info: 'TNLean.PEPS.AreaLaw.interactionChainPropagationSeries_summable_and_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.interactionChainPropagationSeries_summable_and_le
/--
info: 'TNLean.PEPS.AreaLaw.interactionChainPropagationSeries_eq_zero_of_edist_eq_top' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.interactionChainPropagationSeries_eq_zero_of_edist_eq_top

end TNLeanTest
