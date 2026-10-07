/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.GraphInteractionDiamondCounting
import Mathlib.Tactic.NormNum

/-!
# Consumer regressions for exact diamond interaction budgets

The tests retain empty supports and domains, distinguish the exact radius-one constants
from the auxiliary square constants, and allow repeated visits to singleton supports.
The support-size theorem is also used on an infinite ambient vertex type.
-/

open scoped BigOperators
open TNLean.PEPS.AreaLaw

namespace TNLeanTest

-- The support-size theorem needs no globally finite vertex type.
example (R : ℕ) :
    (∅ : Finset (ℤ × ℤ)).card ≤ 1 + 2 * R * (R + 1) := by
  exact card_support_le_diamond (G := (⊥ : SimpleGraph (ℤ × ℤ))) id
    Function.injective_id (by intro x y h; simp at h) ∅ R (by simp)

-- An empty vertex type requires no anchor to bound the empty support.
example (R : ℕ) : (∅ : Finset (Fin 0)).card ≤ 1 + 2 * R * (R + 1) := by
  exact card_support_le_diamond (G := (⊥ : SimpleGraph (Fin 0)))
    (fun x : Fin 0 ↦ Fin.elim0 x) (by intro x y h; exact Fin.elim0 x)
    (by intro x y h; exact Fin.elim0 x) ∅ R (by simp)

section FiniteGraph

variable {V : Type*} [Finite V] [DecidableEq V] {G : SimpleGraph V}
variable (coord : V → ℤ × ℤ) (hcoord : Function.Injective coord)
variable (hstep : ∀ ⦃x y : V⦄, G.Adj x y → latticeL1Distance (coord x) (coord y) ≤ 1)

omit [Finite V] [DecidableEq V] in
private theorem singleton_diamond_range (a : V) :
    ∀ X ∈ ({{a}} : Finset (Finset V)), ∀ u ∈ X, ∀ v ∈ X,
      ∃ p : G.Walk u v, p.length ≤ 0 := by
  intro X hX u hu v hv
  have hXeq : X = {a} := by simpa using hX
  subst X
  have hueq : u = a := by simpa using hu
  have hveq : v = a := by simpa using hv
  subst u
  subst v
  exact ⟨SimpleGraph.Walk.nil, by simp⟩

-- A zero-radius neighborhood retains its single singleton support: μ₀ = 1.
example (a : V) : (({{a}} : Finset (Finset V)).filter (fun X ↦ a ∈ X)).card ≤ 1 := by
  simpa using card_supports_containing_le_diamond coord hcoord hstep {{a}} 0
    (singleton_diamond_range (G := G) a) a

-- A singleton term may be revisited arbitrarily often, giving J^n rather than vanishing.
example (a : V) (J : ℝ) (hJ : 0 ≤ J) (n : ℕ) :
    interactionChainWeightSum {{a}} (fun _ ↦ J) {a} n ≤ J ^ n := by
  simpa using interactionChainWeightSum_le_diamond_pow coord hcoord hstep {{a}} 0
    (singleton_diamond_range (G := G) a) (fun _ ↦ J) J hJ (fun _ _ ↦ hJ)
    (fun _ _ ↦ le_rfl) n {a} (by simp)

-- Norm weights require no physical model.
example {E : Type*} [SeminormedAddGroup E] (a : V) (h : Finset V → E)
    (J : ℝ) (hJ : 0 ≤ J) (hh : ‖h {a}‖ ≤ J) :
    (∑ X ∈ ({{a}} : Finset (Finset V)).filter (fun X ↦ a ∈ X), ‖h X‖) ≤ J := by
  simpa using sum_supportNorms_containing_le_diamond coord hcoord hstep {{a}} 0
    (singleton_diamond_range (G := G) a) h J hJ (by simpa using hh) a

-- The exact radius-one multiplicity is 16, not the square alternative's 256.
example (F : Finset (Finset V))
    (hrange : ∀ X ∈ F, ∀ a ∈ X, ∀ x ∈ X, ∃ p : G.Walk a x, p.length ≤ 1)
    (a : V) : (F.filter (fun X ↦ a ∈ X)).card ≤ 16 := by
  simpa using card_supports_containing_le_diamond coord hcoord hstep F 1 hrange a

-- The exact radius-one continuation constant is 5 * 16 * J = 80 * J.
example (F : Finset (Finset V))
    (hrange : ∀ X ∈ F, ∀ a ∈ X, ∀ x ∈ X, ∃ p : G.Walk a x, p.length ≤ 1)
    (w : Finset V → ℝ) (J : ℝ) (hJ : 0 ≤ J)
    (hw0 : ∀ X ∈ F, 0 ≤ w X) (hwJ : ∀ X ∈ F, w X ≤ J)
    (n : ℕ) (X : Finset V) (hX : X ∈ F) :
    interactionChainWeightSum F w X n ≤ (80 * J) ^ n := by
  have h := interactionChainWeightSum_le_diamond_pow coord hcoord hstep F 1 hrange
    w J hJ hw0 hwJ n X hX
  norm_num [← mul_assoc] at h ⊢
  exact h

-- At zero budget the empty support still has its length-zero continuation of weight one.
example : interactionChainWeightSum ({∅} : Finset (Finset V)) (fun _ ↦ 0) ∅ 0 ≤
    (0 : ℝ) ^ 0 := by
  simpa using interactionChainWeightSum_le_diamond_pow coord hcoord hstep {∅} 0
    (by simp) (fun _ ↦ 0) 0 (by rfl) (by simp) (by simp) 0 ∅ (by simp)

-- Empty supports cannot start positive-length chains, even when their weight is nonzero.
example (w : Finset V → ℝ) :
    interactionChainWeightSum ({∅} : Finset (Finset V)) w ∅ 1 = 0 := by
  simp [interactionChainWeightSum]

end FiniteGraph

set_option linter.hashCommand false

/-- info: 'TNLean.PEPS.AreaLaw.card_support_le_diamond' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.card_support_le_diamond

/-- info: 'TNLean.PEPS.AreaLaw.card_supports_containing_le_diamond' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.card_supports_containing_le_diamond

/-- info: 'TNLean.PEPS.AreaLaw.sum_supportWeights_containing_le_diamond' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.sum_supportWeights_containing_le_diamond

/-- info: 'TNLean.PEPS.AreaLaw.sum_supportNorms_containing_le_diamond' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.sum_supportNorms_containing_le_diamond

/-- info: 'TNLean.PEPS.AreaLaw.interactionChainWeightSum_le_diamond_pow' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.interactionChainWeightSum_le_diamond_pow

/-- info: 'TNLean.PEPS.AreaLaw.interactionChainWeightSum_norm_le_diamond_pow' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.interactionChainWeightSum_norm_le_diamond_pow

end TNLeanTest
