/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.PairProduct

/-!
# Composing local circuits in series and in parallel

A local circuit of depth `T` on the ring of `N` sites (`MPSPreparation.IsLocalCircuitOfDepth`)
is a product of `T` layers of gates on disjoint neighbouring pairs. This file records the local
circuits whose gates all act inside a set of sites `R` (`MPSPreparation.IsCircuitOn`) and
proves the two ways of composing them used in the preparation of arXiv:2307.01696:

* in series, depths add (`MPSPreparation.IsCircuitOn.mul`);
* in parallel, circuits acting inside pairwise disjoint sets of sites run in the same layers,
  so the depth is the largest of the depths (`MPSPreparation.IsCircuitOn.finset_noncommProd`).

A product of `K` gates on neighbouring sites of a block of consecutive sites is a circuit of
depth `K` inside that block (`MPSPreparation.IsPairProduct.isCircuitOn`). These are the steps
behind the depth count of arXiv:2307.01696: the unitaries `U_i` of eq. (10) act on disjoint
blocks, and each "can be implemented in `T=O(q)`" (paragraph before "The sequential-RG
circuit").
-/

open Matrix MPSTensor
open scoped BigOperators

namespace MPSPreparation

variable {d N : ℕ} [NeZero N]

namespace Layer

/-- All gates of the layer act inside the set of sites `R`. -/
def IsIn (L : Layer d N) (R : Set (Fin N)) : Prop := ∀ k ∈ L.bonds, bond k ⊆ R

theorem IsIn.mono {L : Layer d N} {R R' : Set (Fin N)} (h : L.IsIn R) (hR : R ⊆ R') :
    L.IsIn R' := fun k hk => (h k hk).trans hR

theorem op_mem_supportedOperators {L : Layer d N} {R : Set (Fin N)} (h : L.IsIn R) :
    L.op ∈ supportedOperators d R :=
  L.partialOp_mem_supportedOperators _ _ h

/-- The layer without gates. -/
def empty : Layer d N where
  bonds := ∅
  gate := fun _ => 1
  gate_mem_unitary := by simp
  gate_mem_supportedOperators := by simp
  pairwiseDisjoint := by simp

theorem empty_op : (empty : Layer d N).op = 1 := by
  simp [op, partialOp, empty]

theorem empty_isIn (R : Set (Fin N)) : (empty : Layer d N).IsIn R := by
  simp [IsIn, empty]

/-- The layer with the single gate `Z` on the pair `{k, k + 1}`. -/
def single (k : Fin N) (Z : Matrix (Cfg d N) (Cfg d N) ℂ)
    (hZu : Z ∈ unitary (Matrix (Cfg d N) (Cfg d N) ℂ)) (hZ : Z ∈ supportedOperators d (bond k)) :
    Layer d N where
  bonds := {k}
  gate := fun _ => Z
  gate_mem_unitary := fun _ _ => hZu
  gate_mem_supportedOperators := fun l hl => by
    rw [Finset.mem_singleton.mp hl]; exact hZ
  pairwiseDisjoint := by simp

theorem single_op (k : Fin N) (Z : Matrix (Cfg d N) (Cfg d N) ℂ)
    (hZu : Z ∈ unitary (Matrix (Cfg d N) (Cfg d N) ℂ)) (hZ : Z ∈ supportedOperators d (bond k)) :
    (single k Z hZu hZ).op = Z := by
  simp [op, partialOp, single]

theorem single_isIn (k : Fin N) (Z : Matrix (Cfg d N) (Cfg d N) ℂ)
    (hZu : Z ∈ unitary (Matrix (Cfg d N) (Cfg d N) ℂ)) (hZ : Z ∈ supportedOperators d (bond k))
    {R : Set (Fin N)} (hR : bond k ⊆ R) : (single k Z hZu hZ).IsIn R := by
  intro l hl
  rw [show l = k from Finset.mem_singleton.mp hl]
  exact hR

/-- Two layers acting inside disjoint sets of sites run as one layer. -/
def union (L₁ L₂ : Layer d N) {R₁ R₂ : Set (Fin N)} (h₁ : L₁.IsIn R₁) (h₂ : L₂.IsIn R₂)
    (hR : Disjoint R₁ R₂) : Layer d N where
  bonds := L₁.bonds ∪ L₂.bonds
  gate := fun k => if k ∈ L₁.bonds then L₁.gate k else L₂.gate k
  gate_mem_unitary := fun k hk => by
    by_cases h : k ∈ L₁.bonds
    · rw [ite_eq_left h]; exact L₁.gate_mem_unitary k h
    · rw [ite_eq_right h]
      exact L₂.gate_mem_unitary k ((Finset.mem_union.mp hk).resolve_left h)
  gate_mem_supportedOperators := fun k hk => by
    by_cases h : k ∈ L₁.bonds
    · rw [ite_eq_left h]; exact L₁.gate_mem_supportedOperators k h
    · rw [ite_eq_right h]
      exact L₂.gate_mem_supportedOperators k ((Finset.mem_union.mp hk).resolve_left h)
  pairwiseDisjoint := by
    intro k hk l hl hkl
    rcases Finset.mem_union.mp hk with hk | hk <;> rcases Finset.mem_union.mp hl with hl | hl
    · exact L₁.pairwiseDisjoint hk hl hkl
    · exact hR.mono (h₁ k hk) (h₂ l hl)
    · exact (hR.mono (h₁ l hl) (h₂ k hk)).symm
    · exact L₂.pairwiseDisjoint hk hl hkl

theorem union_isIn {L₁ L₂ : Layer d N} {R₁ R₂ : Set (Fin N)} (h₁ : L₁.IsIn R₁)
    (h₂ : L₂.IsIn R₂) (hR : Disjoint R₁ R₂) : (union L₁ L₂ h₁ h₂ hR).IsIn (R₁ ∪ R₂) := by
  intro k hk
  rcases Finset.mem_union.mp hk with hk | hk
  · exact (h₁ k hk).trans Set.subset_union_left
  · exact (h₂ k hk).trans Set.subset_union_right

theorem disjoint_bonds {L₁ L₂ : Layer d N} {R₁ R₂ : Set (Fin N)} (h₁ : L₁.IsIn R₁)
    (h₂ : L₂.IsIn R₂) (hR : Disjoint R₁ R₂) : Disjoint L₁.bonds L₂.bonds := by
  rw [Finset.disjoint_left]
  intro k hk hk'
  have h1 := h₁ k hk (Set.mem_insert k _)
  have h2 := h₂ k hk' (Set.mem_insert k _)
  exact Set.disjoint_left.mp hR h1 h2

theorem union_op {L₁ L₂ : Layer d N} {R₁ R₂ : Set (Fin N)} (h₁ : L₁.IsIn R₁)
    (h₂ : L₂.IsIn R₂) (hR : Disjoint R₁ R₂) : (union L₁ L₂ h₁ h₂ hR).op = L₁.op * L₂.op := by
  have hdisj := disjoint_bonds h₁ h₂ hR
  have hc : ((L₁.bonds ∪ L₂.bonds : Finset (Fin N)) : Set (Fin N)).Pairwise
      (Function.onFun Commute (union L₁ L₂ h₁ h₂ hR).gate) :=
    (union L₁ L₂ h₁ h₂ hR).gate_commute _ subset_rfl
  calc (union L₁ L₂ h₁ h₂ hR).op
      = (L₁.bonds ∪ L₂.bonds).noncommProd (union L₁ L₂ h₁ h₂ hR).gate hc := rfl
    _ = _ := Finset.noncommProd_union_of_disjoint hdisj _ hc
    _ = L₁.op * L₂.op := by
      congr 1
      · exact Finset.noncommProd_congr rfl (fun k hk => by simp [union, hk]) _
      · exact Finset.noncommProd_congr rfl
          (fun k hk => by simp [union, Finset.disjoint_right.mp hdisj hk]) _

end Layer

/-- The unitary of a circuit whose layers act inside `R` acts on `R`. -/
theorem circuitOp_mem_supportedOperators {R : Set (Fin N)} :
    ∀ Ls : List (Layer d N), (∀ L ∈ Ls, L.IsIn R) → circuitOp Ls ∈ supportedOperators d R
  | [], _ => one_mem_supportedOperators R
  | L :: Ls, h => mul_mem_supportedOperators
      (circuitOp_mem_supportedOperators Ls fun L' hL' => h L' (List.mem_cons_of_mem _ hL'))
      (Layer.op_mem_supportedOperators (h L List.mem_cons_self))

theorem circuitOp_append (Ls Ls' : List (Layer d N)) :
    circuitOp (Ls ++ Ls') = circuitOp Ls' * circuitOp Ls := by
  induction Ls with
  | nil => simp [circuitOp]
  | cons L Ls ih => rw [List.cons_append, circuitOp, circuitOp, ih, Matrix.mul_assoc]

/-- `U` is a local circuit of depth `T` all of whose gates act inside the set of sites `R`.

Source: arXiv:2307.01696, main text before Theorem 1 ("depth-`T` local quantum circuits"),
restricted to gates inside `R` as in the parallel application of the block unitaries in the
paragraph "The sequential-RG circuit". -/
def IsCircuitOn (R : Set (Fin N)) (T : ℕ) (U : Matrix (Cfg d N) (Cfg d N) ℂ) : Prop :=
  ∃ Ls : List (Layer d N), Ls.length = T ∧ (∀ L ∈ Ls, L.IsIn R) ∧ U = circuitOp Ls

namespace IsCircuitOn

variable {R R' : Set (Fin N)} {T T' : ℕ} {U U' : Matrix (Cfg d N) (Cfg d N) ℂ}

theorem isLocalCircuitOfDepth (h : IsCircuitOn R T U) : IsLocalCircuitOfDepth U T := by
  obtain ⟨Ls, hl, -, rfl⟩ := h
  exact ⟨Ls, hl, rfl⟩

theorem mem_supportedOperators (h : IsCircuitOn R T U) : U ∈ supportedOperators d R := by
  obtain ⟨Ls, -, hR, rfl⟩ := h
  exact circuitOp_mem_supportedOperators Ls hR

theorem mem_unitary (h : IsCircuitOn R T U) : U ∈ unitary (Matrix (Cfg d N) (Cfg d N) ℂ) := by
  obtain ⟨Ls, -, -, rfl⟩ := h
  exact circuitOp_mem_unitary Ls

theorem mono_set (h : IsCircuitOn R T U) (hR : R ⊆ R') : IsCircuitOn R' T U := by
  obtain ⟨Ls, hl, hLs, rfl⟩ := h
  exact ⟨Ls, hl, fun L hL => (hLs L hL).mono hR, rfl⟩

theorem one (R : Set (Fin N)) (T : ℕ) : IsCircuitOn (d := d) R T 1 := by
  refine ⟨List.replicate T Layer.empty, by simp, by simp [Layer.empty_isIn], ?_⟩
  induction T with
  | zero => rfl
  | succ T ih => rw [List.replicate_succ, circuitOp, ← ih, Layer.empty_op, Matrix.mul_one]

/-- Circuits in series: the depths add. -/
theorem mul (h : IsCircuitOn R T U) (h' : IsCircuitOn R T' U') :
    IsCircuitOn R (T + T') (U' * U) := by
  obtain ⟨Ls, hl, hLs, rfl⟩ := h
  obtain ⟨Ls', hl', hLs', rfl⟩ := h'
  refine ⟨Ls ++ Ls', by simp [hl, hl'], fun L hL => ?_, (circuitOp_append Ls Ls').symm⟩
  rcases List.mem_append.mp hL with hL | hL
  · exact hLs L hL
  · exact hLs' L hL

theorem mono (h : IsCircuitOn R T U) (hT : T ≤ T') : IsCircuitOn R T' U := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hT
  simpa using h.mul (one (d := d) R k)

/-- A single gate on a neighbouring pair inside `R`. -/
theorem single {k : Fin N} {Z : Matrix (Cfg d N) (Cfg d N) ℂ}
    (hZu : Z ∈ unitary (Matrix (Cfg d N) (Cfg d N) ℂ)) (hZ : Z ∈ supportedOperators d (bond k))
    (hR : bond k ⊆ R) : IsCircuitOn R 1 Z :=
  ⟨[Layer.single k Z hZu hZ], rfl, by simpa using Layer.single_isIn k Z hZu hZ hR, by
    simp [circuitOp, Layer.single_op]⟩

private theorem zip_union :
    ∀ (Ls₁ Ls₂ : List (Layer d N)) {R₁ R₂ : Set (Fin N)}, Disjoint R₁ R₂ →
      Ls₁.length = Ls₂.length → (∀ L ∈ Ls₁, L.IsIn R₁) → (∀ L ∈ Ls₂, L.IsIn R₂) →
      IsCircuitOn (R₁ ∪ R₂) Ls₁.length (circuitOp Ls₁ * circuitOp Ls₂)
  | [], [], _, _, _, _, _, _ => by simpa [circuitOp] using one (d := d) _ 0
  | [], _ :: _, _, _, _, h, _, _ => by simp at h
  | _ :: _, [], _, _, _, h, _, _ => by simp at h
  | L₁ :: Ls₁, L₂ :: Ls₂, R₁, R₂, hR, hl, h₁, h₂ => by
    have h₁' : ∀ L ∈ Ls₁, L.IsIn R₁ := fun L hL => h₁ L (List.mem_cons_of_mem _ hL)
    have h₂' : ∀ L ∈ Ls₂, L.IsIn R₂ := fun L hL => h₂ L (List.mem_cons_of_mem _ hL)
    have hL₁ := h₁ L₁ List.mem_cons_self
    have hL₂ := h₂ L₂ List.mem_cons_self
    obtain ⟨Ms, hMl, hMs, hMeq⟩ := zip_union Ls₁ Ls₂ hR (by simpa using hl) h₁' h₂'
    refine ⟨Layer.union L₁ L₂ hL₁ hL₂ hR :: Ms, by simp [hMl], ?_, ?_⟩
    · intro L hL
      rcases List.mem_cons.mp hL with rfl | hL
      · exact Layer.union_isIn hL₁ hL₂ hR
      · exact hMs L hL
    · change circuitOp Ls₁ * L₁.op * (circuitOp Ls₂ * L₂.op) =
        circuitOp Ms * (Layer.union L₁ L₂ hL₁ hL₂ hR).op
      rw [← hMeq, Layer.union_op]
      have hc : Commute (circuitOp Ls₂) L₁.op :=
        commute_of_mem_supportedOperators hR.symm (circuitOp_mem_supportedOperators Ls₂ h₂')
          (Layer.op_mem_supportedOperators hL₁)
      calc circuitOp Ls₁ * L₁.op * (circuitOp Ls₂ * L₂.op)
          = circuitOp Ls₁ * (L₁.op * circuitOp Ls₂) * L₂.op := by
            simp only [Matrix.mul_assoc]
        _ = circuitOp Ls₁ * (circuitOp Ls₂ * L₁.op) * L₂.op := by rw [hc.eq]
        _ = circuitOp Ls₁ * circuitOp Ls₂ * (L₁.op * L₂.op) := by
            simp only [Matrix.mul_assoc]

/-- Circuits in parallel: two circuits of depth `T` acting inside disjoint sets of sites
run in the same `T` layers. -/
theorem par {R₁ R₂ : Set (Fin N)} (hR : Disjoint R₁ R₂) {U₁ U₂ : Matrix (Cfg d N) (Cfg d N) ℂ}
    (h₁ : IsCircuitOn R₁ T U₁) (h₂ : IsCircuitOn R₂ T U₂) :
    IsCircuitOn (R₁ ∪ R₂) T (U₁ * U₂) := by
  obtain ⟨Ls₁, hl₁, hLs₁, rfl⟩ := h₁
  obtain ⟨Ls₂, hl₂, hLs₂, rfl⟩ := h₂
  have := zip_union Ls₁ Ls₂ hR (hl₁.trans hl₂.symm) hLs₁ hLs₂
  rwa [hl₁] at this

/-- Circuits in parallel: a family of circuits of depth `T` acting inside pairwise disjoint
sets of sites is a circuit of depth `T`. -/
theorem finset_noncommProd {ι : Type*} (s : Finset ι) (R : ι → Set (Fin N))
    (hR : (s : Set ι).PairwiseDisjoint R) (U : ι → Matrix (Cfg d N) (Cfg d N) ℂ)
    (hU : ∀ i ∈ s, IsCircuitOn (R i) T (U i))
    (hcomm : (s : Set ι).Pairwise (Function.onFun Commute U)) :
    IsCircuitOn (⋃ i ∈ s, R i) T (s.noncommProd U hcomm) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one (d := d) (∅ : Set (Fin N)) T
  | insert a s ha ih =>
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha]
    have hdisj : Disjoint (R a) (⋃ i ∈ s, R i) := by
      rw [Set.disjoint_iUnion₂_right]
      intro i hi
      exact hR (by simp) (by simp [hi]) (fun h => ha (h ▸ hi))
    have := (hU a (by simp)).par hdisj
      (ih (hR.subset (by simp)) (fun i hi => hU i (by simp [hi])) (hcomm.mono (by simp)))
    simpa [Finset.set_biUnion_insert] using this

end IsCircuitOn

/-- **A product of two-site gates on a window is a circuit.** Let `e` place the `m` sites of an
open chain as consecutive sites of the ring (`e (i + 1) = e i + 1`). A product of at most `K`
gates on neighbouring sites of the open chain, placed by `e`, is a local circuit of depth `K`
whose gates act inside the range of `e`. -/
theorem IsPairProduct.isCircuitOn {m K : ℕ} {e : Fin m → Fin N} (he : Function.Injective e)
    (hsucc : ∀ i j : Fin m, j.val = i.val + 1 → e j = e i + 1)
    {X : Matrix (Cfg d m) (Cfg d m) ℂ} (hX : IsPairProduct d m K X) :
    IsCircuitOn (Set.range e) K (MPSPreparation.embedOp e X) := by
  obtain ⟨l, hl, hg, rfl⟩ := hX
  refine IsCircuitOn.mono ?_ hl
  clear hl
  induction l with
  | nil => simpa using IsCircuitOn.one (d := d) (Set.range e) 0
  | cons Z l ih =>
    obtain ⟨hZu, p, p', hp, hZ⟩ := hg Z List.mem_cons_self
    have hZ' : MPSPreparation.embedOp e Z ∈ supportedOperators d (bond (e p)) := by
      have := embedOp_mem_supportedOperators_image he hZ
      rwa [Set.image_pair, hsucc p p' hp] at this
    have h1 := IsCircuitOn.single (embedOp_mem_unitary he hZu) hZ'
      (R := Set.range e) (by
        rintro x (rfl | rfl)
        · exact ⟨p, rfl⟩
        · exact ⟨p', (hsucc p p' hp)⟩)
    have h2 := ih fun Z' hZ' => hg Z' (List.mem_cons_of_mem _ hZ')
    rw [List.prod_cons, ← embedOp_mul he, List.length_cons]
    exact h2.mul h1

end MPSPreparation
