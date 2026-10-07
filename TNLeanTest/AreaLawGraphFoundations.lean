/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.GraphInteractionBudget
import TNLean.PEPS.AreaLaw.GraphInteractionChain
import TNLean.PEPS.AreaLaw.GraphInteractionCounting
import TNLean.PEPS.AreaLaw.GraphLatticeCounting

/-!
# Consumer regressions for graph interaction foundations

These examples check empty families and supports, empty domains and regions, radius zero,
repeated singleton interactions, disconnected sites, and the contribution of the initial
support to the chain-length bound. The final commands print the actual theorem axioms for
external checking; no expected output is assumed here.
-/

open scoped BigOperators
open TNLean.PEPS.AreaLaw

namespace TNLeanTest

section Budgets

variable {V : Type*} [DecidableEq V]

-- The erase count also applies when the neighborhood and family are empty.
example (a : V) :
    (∅ : Finset (Finset V)).card ≤ 2 ^ ((∅ : Finset V).erase a).card :=
  card_supportFamily_le_pow_card_erase ∅ ∅ a (by simp)

-- A singleton neighborhood includes its one singleton support.
example (a : V) : ({{a}} : Finset (Finset V)).card ≤ 1 := by
  exact le_trans (card_supportFamily_le_pow {{a}} {a} a (by simp) (by simp)) (by simp)

-- The meeting budget accepts an empty region even when the parameter b is negative.
example (F : Finset (Finset V)) (w : Finset V → ℝ) (b : ℝ)
    (hw : ∀ X ∈ F, 0 ≤ w X) :
    (∑ X ∈ F.filter (fun X => ¬ Disjoint X (∅ : Finset V)), w X) ≤ 0 := by
  calc
    _ ≤ (∅ : Finset V).card * b := sum_supportWeights_meeting_le F ∅ w b hw (by simp)
    _ = 0 := by simp

-- With no continuation, the chain weight is one, including the zero-budget case.
example : interactionChainWeightSum ({∅} : Finset (Finset V)) (fun _ => 1) ∅ 0 ≤
    (0 : ℝ) ^ 0 := by
  simpa using interactionChainWeightSum_le_pow ({∅} : Finset (Finset V)) (fun _ => 1)
    0 0 (by norm_num) (by simp) (by simp) (by intro a; simp) 0 ∅ (by simp)

end Budgets

section Chains

variable {V : Type*} {G : SimpleGraph V} {X : Set V} {supports : List (Set V)} {x y : V}

-- A zero-range chain cannot reach a site different from its first site.
example (hchain : List.IsChain (fun A B : Set V ↦ (A ∩ B).Nonempty) (X :: supports))
    (hrange : ∀ A ∈ X :: supports, ∀ u ∈ A, ∀ v ∈ A,
      ∃ p : G.Walk u v, p.length ≤ 0)
    (hx : x ∈ X) (hy : y ∈ (X :: supports).getLast (by simp)) : x = y := by
  obtain ⟨p, hp⟩ := exists_walk_length_le_mul_of_isChain hchain hrange hx hy
  have hzero : p.length = 0 := le_antisymm (by simpa using hp) (Nat.zero_le _)
  exact SimpleGraph.Walk.eq_of_length_eq_zero hzero

-- In the bottom graph, distinct sites retain infinite distance and exclude finite chains.
example (hne : x ≠ y) (R : ℕ)
    (hrange : ∀ A ∈ X :: supports, ∀ u ∈ A, ∀ v ∈ A,
      ∃ p : (⊥ : SimpleGraph V).Walk u v, p.length ≤ R)
    (hx : x ∈ X) (hy : y ∈ (X :: supports).getLast (by simp)) :
    (⊥ : SimpleGraph V).edist x y = ⊤ ∧
      ¬ List.IsChain (fun A B : Set V ↦ (A ∩ B).Nonempty) (X :: supports) := by
  have hd : (⊥ : SimpleGraph V).edist x y = ⊤ :=
    SimpleGraph.edist_eq_top_of_not_reachable
      (fun h ↦ hne (SimpleGraph.reachable_bot.mp h))
  exact ⟨hd, not_isChain_of_edist_eq_top hd hrange hx hy⟩

-- Component exclusion uses the same induced-graph range premise as the distance bound.
example (hne : x ≠ y) (R : ℕ)
    (hrange : ∀ A ∈ X :: supports, ∀ u ∈ A, ∀ v ∈ A,
      ∃ p : (⊥ : SimpleGraph V).Walk u v, p.length ≤ R)
    (hx : x ∈ X) (hy : y ∈ (X :: supports).getLast (by simp)) :
    ¬ List.IsChain (fun A B : Set V ↦ (A ∩ B).Nonempty) (X :: supports) := by
  apply not_isChain_of_connectedComponent_ne (G := (⊥ : SimpleGraph V)) _ hrange hx hy
  intro hcomponents
  exact hne (SimpleGraph.reachable_bot.mp
    (SimpleGraph.ConnectedComponent.exact hcomponents))

-- Both singleton supports have actual zero-length local walks, but no chain joins them.
example : (⊥ : SimpleGraph (Fin 2)).edist 0 1 = ⊤ ∧
    ¬ List.IsChain (fun A B : Set (Fin 2) ↦ (A ∩ B).Nonempty) [{0}, {1}] := by
  have hd : (⊥ : SimpleGraph (Fin 2)).edist 0 1 = ⊤ :=
    SimpleGraph.edist_eq_top_of_not_reachable
      (fun h ↦ (by decide : (0 : Fin 2) ≠ 1) (SimpleGraph.reachable_bot.mp h))
  have hrange : ∀ A ∈ [({0} : Set (Fin 2)), {1}], ∀ u ∈ A, ∀ v ∈ A,
      ∃ p : (⊥ : SimpleGraph (Fin 2)).Walk u v, p.length ≤ 0 := by
    intro A hA u hu v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
    rcases hA with rfl | rfl <;>
      simp only [Set.mem_singleton_iff] at hu hv <;>
      subst u <;>
      subst v <;>
      exact ⟨SimpleGraph.Walk.nil, by simp⟩
  exact ⟨hd, not_isChain_of_edist_eq_top (X := {0}) (supports := [{1}])
    hd hrange (by simp) (by simp)⟩

-- No continuation still permits travel within the initial support: m + 1 is essential.
example : (⊤ : SimpleGraph (Fin 2)).edist 0 1 ≤ (1 : ℕ∞) ∧
    ¬ (⊤ : SimpleGraph (Fin 2)).edist 0 1 ≤ 0 := by
  constructor
  · have hrange : ∀ A ∈ [(Set.univ : Set (Fin 2))], ∀ u ∈ A, ∀ v ∈ A,
        ∃ p : (⊤ : SimpleGraph (Fin 2)).Walk u v, p.length ≤ 1 := by
      intro _ _ u _ v _
      by_cases huv : u = v
      · subst v
        exact ⟨SimpleGraph.Walk.nil, by simp⟩
      · have hadj : (⊤ : SimpleGraph (Fin 2)).Adj u v := by simpa using huv
        exact ⟨hadj.toWalk, by simp⟩
    simpa using edist_le_mul_of_isChain (G := (⊤ : SimpleGraph (Fin 2)))
      (X := Set.univ) (supports := []) (R := 1) (List.isChain_singleton _)
      hrange (Set.mem_univ 0) (Set.mem_univ 1)
  · exact not_le_of_gt (SimpleGraph.edist_pos_of_ne
      (G := (⊤ : SimpleGraph (Fin 2))) (by decide : (0 : Fin 2) ≠ 1))

end Chains

-- An empty domain needs no anchor when the support-count theorem receives the empty support.
example (R : ℕ) : (∅ : Finset (Fin 0)).card ≤ (2 * R + 1) ^ 2 := by
  exact card_support_le_square (G := (⊥ : SimpleGraph (Fin 0)))
    (fun x : Fin 0 => Fin.elim0 x) (by intro x y h; exact Fin.elim0 x)
    (by intro x y h; exact Fin.elim0 x) ∅ R (by simp)

-- A radius-zero graph ball in a singleton domain has at most one site.
example : (Finset.univ : Finset PUnit).card ≤ 1 := by
  exact le_trans (card_le_square_of_edist_le (G := (⊥ : SimpleGraph PUnit))
    (fun _ : PUnit => ((0, 0) : ℤ × ℤ)) Finset.univ
    (fun _ _ _ => Subsingleton.elim _ _) (by intro x y h; simp at h)
    PUnit.unit 0 (by intro x hx; cases x; simp)) (by simp)

section Singletons

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [Fintype V] [DecidableEq V] in
private theorem singleton_support_range (a : V) :
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

-- Singleton terms are retained in the lattice interaction count, including at radius zero.
example (coord : V → ℤ × ℤ) (hcoord : Function.Injective coord)
    (hstep : ∀ ⦃x y : V⦄, G.Adj x y → latticeL1Distance (coord x) (coord y) ≤ 1)
    (a : V) : (({{a}} : Finset (Finset V)).filter (fun X => a ∈ X)).card ≤ 1 := by
  simpa using card_supports_containing_le_square coord hcoord hstep {{a}} 0
    (singleton_support_range (G := G) a) a

-- A singleton interaction may be revisited at every step; its n-step bound is J^n.
example (coord : V → ℤ × ℤ) (hcoord : Function.Injective coord)
    (hstep : ∀ ⦃x y : V⦄, G.Adj x y → latticeL1Distance (coord x) (coord y) ≤ 1)
    (a : V) (J : ℝ) (hJ : 0 ≤ J) (n : ℕ) :
    interactionChainWeightSum {{a}} (fun _ => J) {a} n ≤ J ^ n := by
  simpa using interactionChainWeightSum_le_lattice_pow coord hcoord hstep {{a}} 0
    (singleton_support_range (G := G) a) (fun _ => J) J hJ (fun _ _ => hJ)
    (fun _ _ => le_rfl) n {a} (by simp)

end Singletons

set_option linter.hashCommand false

/--
info: 'TNLean.PEPS.AreaLaw.card_supportFamily_le_pow_card_erase' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.card_supportFamily_le_pow_card_erase

/--
info: 'TNLean.PEPS.AreaLaw.card_supportFamily_le_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.card_supportFamily_le_pow

/--
info: 'TNLean.PEPS.AreaLaw.sum_supportWeights_containing_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.sum_supportWeights_containing_le

/--
info: 'TNLean.PEPS.AreaLaw.sum_supportWeights_meeting_le_sum_siteWeights' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.sum_supportWeights_meeting_le_sum_siteWeights

/--
info: 'TNLean.PEPS.AreaLaw.sum_supportWeights_meeting_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.sum_supportWeights_meeting_le

/--
info: 'TNLean.PEPS.AreaLaw.interactionChainWeightSum_le_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.interactionChainWeightSum_le_pow

/--
info: 'TNLean.PEPS.AreaLaw.interactionChainWeightSum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.interactionChainWeightSum

/--
info: 'TNLean.PEPS.AreaLaw.exists_walk_length_le_sum_of_isChain' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.exists_walk_length_le_sum_of_isChain

/--
info: 'TNLean.PEPS.AreaLaw.exists_walk_length_le_mul_of_isChain' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.exists_walk_length_le_mul_of_isChain

/--
info: 'TNLean.PEPS.AreaLaw.edist_le_mul_of_isChain' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.edist_le_mul_of_isChain

/--
info: 'TNLean.PEPS.AreaLaw.reachable_of_isChain' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.reachable_of_isChain

/--
info: 'TNLean.PEPS.AreaLaw.connectedComponent_eq_of_isChain' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.connectedComponent_eq_of_isChain

/--
info: 'TNLean.PEPS.AreaLaw.not_isChain_of_connectedComponent_ne' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.not_isChain_of_connectedComponent_ne

/--
info: 'TNLean.PEPS.AreaLaw.not_isChain_of_edist_eq_top' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.not_isChain_of_edist_eq_top

/--
info: 'TNLean.PEPS.AreaLaw.not_isChain_of_mul_lt_edist' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.not_isChain_of_mul_lt_edist

/--
info: 'TNLean.PEPS.AreaLaw.latticeL1Distance_self' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.latticeL1Distance_self

/--
info: 'TNLean.PEPS.AreaLaw.latticeL1Distance' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.latticeL1Distance

/--
info: 'TNLean.PEPS.AreaLaw.latticeL1Distance_triangle' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.latticeL1Distance_triangle

/--
info: 'TNLean.PEPS.AreaLaw.latticeL1Distance_le_walk_length' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.latticeL1Distance_le_walk_length

/--
info: 'TNLean.PEPS.AreaLaw.latticeL1Distance_le_of_edist_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.latticeL1Distance_le_of_edist_le

/--
info: 'TNLean.PEPS.AreaLaw.card_le_square_of_latticeL1Distance_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.card_le_square_of_latticeL1Distance_le

/--
info: 'TNLean.PEPS.AreaLaw.card_le_square_of_walks' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.card_le_square_of_walks

/--
info: 'TNLean.PEPS.AreaLaw.card_le_square_of_edist_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.card_le_square_of_edist_le

/--
info: 'TNLean.PEPS.AreaLaw.card_support_le_square' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.card_support_le_square

/--
info: 'TNLean.PEPS.AreaLaw.card_supports_containing_le_square' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.card_supports_containing_le_square

/--
info: 'TNLean.PEPS.AreaLaw.sum_supportWeights_containing_le_square' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.sum_supportWeights_containing_le_square

/--
info: 'TNLean.PEPS.AreaLaw.interactionChainWeightSum_le_lattice_pow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.interactionChainWeightSum_le_lattice_pow

end TNLeanTest
