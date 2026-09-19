/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ScalarThreeCocycleCyclicTwoExamples

/-!
# Tests for explicit scalar three-cocycles on Z₂

Full-signature checks for the two representatives, their normalization, cocycle
identity, phase modulus, gauge classes, and normalized fusion-gauge invariance.
-/

open TNLean.Algebra TNLean.Algebra.ScalarThreeCochain

local notation "s₂" => (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2))

example (p : Fin 2) : ScalarThreeCochain (Multiplicative (ZMod 2)) :=
  cyclicTwoCocycle p

example (p : Fin 2) (a b c : Multiplicative (ZMod 2)) :
    cyclicTwoCocycle p a b c =
      if a = s₂ ∧ b = s₂ ∧ c = s₂ then (-1) ^ p.val else 1 := rfl

example (p : Fin 2) : cyclicTwoCocycle p s₂ s₂ s₂ = (-1) ^ p.val :=
  cyclicTwoCocycle_generator p

example : cyclicTwoCocycle 0 = fun _ _ _ => 1 := cyclicTwoCocycle_zero

example (p : Fin 2) : IsNormalized (cyclicTwoCocycle p) :=
  cyclicTwoCocycle_isNormalized p

example (p : Fin 2) : IsCocycle (cyclicTwoCocycle p) :=
  cyclicTwoCocycle_isCocycle p

example (p : Fin 2) (a b c : Multiplicative (ZMod 2)) :
    ‖(cyclicTwoCocycle p a b c : ℂ)‖ = 1 := cyclicTwoCocycle_norm p a b c

example (p : Fin 2) : sigma (cyclicTwoCocycle p) s₂ = (-1) ^ p.val :=
  cyclicTwoCocycle_sigma_generator p

example : ¬ IsTrivialGaugeClass (cyclicTwoCocycle 1) :=
  cyclicTwoCocycle_one_not_isTrivialGaugeClass

example (p q : Fin 2) :
    CohomologousTo (cyclicTwoCocycle p) (cyclicTwoCocycle q) ↔ p = q :=
  cyclicTwoCocycle_cohomologousTo_iff p q

example (p : Fin 2) {β : ScalarCocycle (Multiplicative (ZMod 2))}
    (hβ : β.IsNormalized) :
    fusionGauge β (cyclicTwoCocycle p) s₂ s₂ s₂ = (-1) ^ p.val :=
  cyclicTwoCocycle_fusionGauge_generator p hβ

example : cyclicTwoCocycle 1 s₂ s₂ s₂ = -1 := by simp

example : cyclicTwoCocycle 1 s₂ 1 s₂ = 1 :=
  (cyclicTwoCocycle_isNormalized 1).2.1 s₂ s₂

example : IsTrivialGaugeClass (cyclicTwoCocycle 0) := by
  rw [cyclicTwoCocycle_zero]
  exact CohomologousTo.refl _

-- Axiom-report commands are intentional in this regression-test section.
section AxiomChecks
set_option linter.hashCommand false

/-- info: 'TNLean.Algebra.ScalarThreeCochain.cyclicTwoCocycle_generator' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cyclicTwoCocycle_generator

/-- info: 'TNLean.Algebra.ScalarThreeCochain.cyclicTwoCocycle_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cyclicTwoCocycle_zero

/-- info: 'TNLean.Algebra.ScalarThreeCochain.cyclicTwoCocycle_isNormalized' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cyclicTwoCocycle_isNormalized

/-- info: 'TNLean.Algebra.ScalarThreeCochain.cyclicTwoCocycle_isCocycle' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cyclicTwoCocycle_isCocycle

/-- info: 'TNLean.Algebra.ScalarThreeCochain.cyclicTwoCocycle_norm' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cyclicTwoCocycle_norm

/-- info: 'TNLean.Algebra.ScalarThreeCochain.cyclicTwoCocycle_sigma_generator' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cyclicTwoCocycle_sigma_generator

/-- info: 'TNLean.Algebra.ScalarThreeCochain.cyclicTwoCocycle_one_not_isTrivialGaugeClass' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cyclicTwoCocycle_one_not_isTrivialGaugeClass

/-- info: 'TNLean.Algebra.ScalarThreeCochain.cyclicTwoCocycle_cohomologousTo_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cyclicTwoCocycle_cohomologousTo_iff

/-- info: 'TNLean.Algebra.ScalarThreeCochain.cyclicTwoCocycle_fusionGauge_generator' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cyclicTwoCocycle_fusionGauge_generator

end AxiomChecks
