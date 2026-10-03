/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.PairProduct

/-!
# Composing local circuits in series and in parallel

A local circuit of depth `T` on a bond geometry (`QuantumCircuit.IsBondCircuitOfDepth`) is a
product of `T` layers of gates on disjoint bonds. This file records the local circuits whose
gates all act inside a set of sites `R` (`QuantumCircuit.IsBondCircuitOn`, and on the ring
`QuantumCircuit.IsCircuitOn`) and proves the two ways of composing them used in the
preparation of arXiv:2307.01696:

* in series, depths add (`QuantumCircuit.IsBondCircuitOn.mul`);
* in parallel, circuits of the same depth `T` acting inside pairwise disjoint sets of sites
  run in the same layers, so their product has depth `T`
  (`QuantumCircuit.IsBondCircuitOn.finset_noncommProd`, for geometries whose bonds are
  nonempty, and `QuantumCircuit.IsCircuitOn.finset_noncommProd` on the ring); circuits of
  different depths are first padded to the largest depth with
  `QuantumCircuit.IsBondCircuitOn.mono`.

On the ring, a product of `K` gates on neighbouring sites of a block of consecutive sites is a
circuit of depth `K` inside that block (`QuantumCircuit.IsPairProduct.isCircuitOn`), and such products
placed on pairwise disjoint blocks form a circuit of depth `K`
(`QuantumCircuit.isCircuitOn_list_prod_embedOp`). These are the steps
behind the depth count of arXiv:2307.01696: the unitaries `U_i` of eq. (10) act on disjoint
blocks, and each "can be implemented in `T=O(q)`" (paragraph before "The sequential-RG
circuit").
-/

open Matrix
open scoped BigOperators

namespace QuantumCircuit

variable {d : ℕ} {ι β : Type*} [Fintype ι] [DecidableEq ι] {bond : β → Set ι}

namespace BondLayer

/-- All gates of the layer act inside the set of sites `R`. -/
def IsIn (L : BondLayer d bond) (R : Set ι) : Prop := ∀ k ∈ L.bonds, bond k ⊆ R

theorem IsIn.mono {L : BondLayer d bond} {R R' : Set ι} (h : L.IsIn R) (hR : R ⊆ R') :
    L.IsIn R' := fun k hk => (h k hk).trans hR

theorem op_mem_supportedOperators {L : BondLayer d bond} {R : Set ι} (h : L.IsIn R) :
    L.op ∈ supportedOperators d R :=
  L.partialOp_mem_supportedOperators _ _ h

/-- The layer without gates. -/
def empty : BondLayer d bond where
  bonds := ∅
  gate := fun _ => 1
  gate_mem_unitary := by simp
  gate_mem_supportedOperators := by simp
  pairwiseDisjoint := by simp

theorem empty_op : (empty : BondLayer d bond).op = 1 := by
  simp [op, partialOp, empty]

theorem empty_isIn (R : Set ι) : (empty : BondLayer d bond).IsIn R := by
  simp [IsIn, empty]

/-- The layer with the single gate `Z` on the bond `b`. -/
def single (b : β) (Z : Matrix (ι → Fin d) (ι → Fin d) ℂ)
    (hZu : Z ∈ unitary (Matrix (ι → Fin d) (ι → Fin d) ℂ))
    (hZ : Z ∈ supportedOperators d (bond b)) :
    BondLayer d bond where
  bonds := {b}
  gate := fun _ => Z
  gate_mem_unitary := fun _ _ => hZu
  gate_mem_supportedOperators := fun l hl => by
    rw [Finset.mem_singleton.mp hl]; exact hZ
  pairwiseDisjoint := by simp

theorem single_op (b : β) (Z : Matrix (ι → Fin d) (ι → Fin d) ℂ)
    (hZu : Z ∈ unitary (Matrix (ι → Fin d) (ι → Fin d) ℂ))
    (hZ : Z ∈ supportedOperators d (bond b)) :
    (single b Z hZu hZ).op = Z := by
  simp [op, partialOp, single]

theorem single_isIn (b : β) (Z : Matrix (ι → Fin d) (ι → Fin d) ℂ)
    (hZu : Z ∈ unitary (Matrix (ι → Fin d) (ι → Fin d) ℂ))
    (hZ : Z ∈ supportedOperators d (bond b))
    {R : Set ι} (hR : bond b ⊆ R) : (single b Z hZu hZ).IsIn R := by
  intro l hl
  rw [show l = b from Finset.mem_singleton.mp hl]
  exact hR

/-- Layers acting inside disjoint sets of sites use disjoint sets of nonempty bonds. -/
theorem disjoint_bonds (hne : ∀ b, (bond b).Nonempty) {L₁ L₂ : BondLayer d bond}
    {R₁ R₂ : Set ι} (h₁ : L₁.IsIn R₁) (h₂ : L₂.IsIn R₂) (hR : Disjoint R₁ R₂) :
    Disjoint L₁.bonds L₂.bonds := by
  rw [Finset.disjoint_left]
  intro k hk hk'
  obtain ⟨i, hi⟩ := hne k
  exact Set.disjoint_left.mp hR (h₁ k hk hi) (h₂ k hk' hi)

variable [DecidableEq β]

/-- Two layers acting inside disjoint sets of sites run as one layer. -/
def union (L₁ L₂ : BondLayer d bond) {R₁ R₂ : Set ι} (h₁ : L₁.IsIn R₁) (h₂ : L₂.IsIn R₂)
    (hR : Disjoint R₁ R₂) : BondLayer d bond where
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

theorem union_isIn {L₁ L₂ : BondLayer d bond} {R₁ R₂ : Set ι} (h₁ : L₁.IsIn R₁)
    (h₂ : L₂.IsIn R₂) (hR : Disjoint R₁ R₂) : (union L₁ L₂ h₁ h₂ hR).IsIn (R₁ ∪ R₂) := by
  intro k hk
  rcases Finset.mem_union.mp hk with hk | hk
  · exact (h₁ k hk).trans Set.subset_union_left
  · exact (h₂ k hk).trans Set.subset_union_right

theorem union_op (hne : ∀ b, (bond b).Nonempty) {L₁ L₂ : BondLayer d bond} {R₁ R₂ : Set ι}
    (h₁ : L₁.IsIn R₁) (h₂ : L₂.IsIn R₂) (hR : Disjoint R₁ R₂) :
    (union L₁ L₂ h₁ h₂ hR).op = L₁.op * L₂.op := by
  have hdisj := disjoint_bonds hne h₁ h₂ hR
  have hc : ((L₁.bonds ∪ L₂.bonds : Finset β) : Set β).Pairwise
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

end BondLayer

/-- The unitary of a circuit whose layers act inside `R` acts on `R`. -/
theorem circuitOp_mem_supportedOperators {R : Set ι} :
    ∀ Ls : List (BondLayer d bond), (∀ L ∈ Ls, L.IsIn R) → circuitOp Ls ∈ supportedOperators d R
  | [], _ => one_mem_supportedOperators R
  | L :: Ls, h => mul_mem_supportedOperators
      (circuitOp_mem_supportedOperators Ls fun L' hL' => h L' (List.mem_cons_of_mem _ hL'))
      (BondLayer.op_mem_supportedOperators (h L List.mem_cons_self))

variable (bond) in
/-- `U` is a local circuit of depth `T` on the bond geometry `bond`, all of whose gates act
inside the set of sites `R`.

Source: arXiv:2307.01696, main text before Theorem 1 ("depth-`T` local quantum circuits"),
restricted to gates inside `R` as in the parallel application of the block unitaries in the
paragraph "The sequential-RG circuit". -/
def IsBondCircuitOn (R : Set ι) (T : ℕ) (U : Matrix (ι → Fin d) (ι → Fin d) ℂ) : Prop :=
  ∃ Ls : List (BondLayer d bond), Ls.length = T ∧ (∀ L ∈ Ls, L.IsIn R) ∧ U = circuitOp Ls

namespace IsBondCircuitOn

variable {R R' : Set ι} {T T' : ℕ} {U U' : Matrix (ι → Fin d) (ι → Fin d) ℂ}

theorem isBondCircuitOfDepth (h : IsBondCircuitOn bond R T U) :
    IsBondCircuitOfDepth bond U T := by
  obtain ⟨Ls, hl, -, rfl⟩ := h
  exact ⟨Ls, hl, rfl⟩

theorem mem_supportedOperators (h : IsBondCircuitOn bond R T U) :
    U ∈ supportedOperators d R := by
  obtain ⟨Ls, -, hR, rfl⟩ := h
  exact circuitOp_mem_supportedOperators Ls hR

theorem mem_unitary (h : IsBondCircuitOn bond R T U) : U ∈ unitary
    (Matrix (ι → Fin d) (ι → Fin d) ℂ) := by
  obtain ⟨Ls, -, -, rfl⟩ := h
  exact circuitOp_mem_unitary Ls

theorem mono_set (h : IsBondCircuitOn bond R T U) (hR : R ⊆ R') :
    IsBondCircuitOn bond R' T U := by
  obtain ⟨Ls, hl, hLs, rfl⟩ := h
  exact ⟨Ls, hl, fun L hL => (hLs L hL).mono hR, rfl⟩

variable (bond) in
theorem one (R : Set ι) (T : ℕ) : IsBondCircuitOn (d := d) bond R T 1 := by
  refine ⟨List.replicate T BondLayer.empty, by simp, by simp [BondLayer.empty_isIn], ?_⟩
  induction T with
  | zero => rfl
  | succ T ih => rw [List.replicate_succ, circuitOp, ← ih, BondLayer.empty_op, Matrix.mul_one]

/-- Circuits in series: the depths add. -/
theorem mul (h : IsBondCircuitOn bond R T U) (h' : IsBondCircuitOn bond R T' U') :
    IsBondCircuitOn bond R (T + T') (U' * U) := by
  obtain ⟨Ls, hl, hLs, rfl⟩ := h
  obtain ⟨Ls', hl', hLs', rfl⟩ := h'
  refine ⟨Ls ++ Ls', by simp [hl, hl'], fun L hL => ?_, (circuitOp_append Ls Ls').symm⟩
  rcases List.mem_append.mp hL with hL | hL
  · exact hLs L hL
  · exact hLs' L hL

theorem mono (h : IsBondCircuitOn bond R T U) (hT : T ≤ T') : IsBondCircuitOn bond R T' U := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hT
  simpa using h.mul (one (d := d) bond R k)

/-- A single gate on a bond inside `R`. -/
theorem single {b : β} {Z : Matrix (ι → Fin d) (ι → Fin d) ℂ}
    (hZu : Z ∈ unitary (Matrix (ι → Fin d) (ι → Fin d) ℂ))
    (hZ : Z ∈ supportedOperators d (bond b))
    (hR : bond b ⊆ R) : IsBondCircuitOn bond R 1 Z :=
  ⟨[BondLayer.single b Z hZu hZ], rfl, by simpa using BondLayer.single_isIn b Z hZu hZ hR, by
    simp [circuitOp, BondLayer.single_op]⟩

variable [DecidableEq β]

private theorem zip_union (hne : ∀ b, (bond b).Nonempty) :
    ∀ (Ls₁ Ls₂ : List (BondLayer d bond)) {R₁ R₂ : Set ι}, Disjoint R₁ R₂ →
      Ls₁.length = Ls₂.length → (∀ L ∈ Ls₁, L.IsIn R₁) → (∀ L ∈ Ls₂, L.IsIn R₂) →
      IsBondCircuitOn bond (R₁ ∪ R₂) Ls₁.length (circuitOp Ls₁ * circuitOp Ls₂)
  | [], [], _, _, _, _, _, _ => by simpa [circuitOp] using one (d := d) bond _ 0
  | [], _ :: _, _, _, _, h, _, _ => by simp at h
  | _ :: _, [], _, _, _, h, _, _ => by simp at h
  | L₁ :: Ls₁, L₂ :: Ls₂, R₁, R₂, hR, hl, h₁, h₂ => by
    have h₁' : ∀ L ∈ Ls₁, L.IsIn R₁ := fun L hL => h₁ L (List.mem_cons_of_mem _ hL)
    have h₂' : ∀ L ∈ Ls₂, L.IsIn R₂ := fun L hL => h₂ L (List.mem_cons_of_mem _ hL)
    have hL₁ := h₁ L₁ List.mem_cons_self
    have hL₂ := h₂ L₂ List.mem_cons_self
    obtain ⟨Ms, hMl, hMs, hMeq⟩ := zip_union hne Ls₁ Ls₂ hR (by simpa using hl) h₁' h₂'
    refine ⟨BondLayer.union L₁ L₂ hL₁ hL₂ hR :: Ms, by simp [hMl], ?_, ?_⟩
    · intro L hL
      rcases List.mem_cons.mp hL with rfl | hL
      · exact BondLayer.union_isIn hL₁ hL₂ hR
      · exact hMs L hL
    · change circuitOp Ls₁ * L₁.op * (circuitOp Ls₂ * L₂.op) =
        circuitOp Ms * (BondLayer.union L₁ L₂ hL₁ hL₂ hR).op
      rw [← hMeq, BondLayer.union_op hne]
      have hc : Commute (circuitOp Ls₂) L₁.op :=
        commute_of_mem_supportedOperators hR.symm (circuitOp_mem_supportedOperators Ls₂ h₂')
          (BondLayer.op_mem_supportedOperators hL₁)
      calc circuitOp Ls₁ * L₁.op * (circuitOp Ls₂ * L₂.op)
          = circuitOp Ls₁ * (L₁.op * circuitOp Ls₂) * L₂.op := by
            simp only [Matrix.mul_assoc]
        _ = circuitOp Ls₁ * (circuitOp Ls₂ * L₁.op) * L₂.op := by rw [hc.eq]
        _ = circuitOp Ls₁ * circuitOp Ls₂ * (L₁.op * L₂.op) := by
            simp only [Matrix.mul_assoc]

/-- Circuits in parallel: two circuits of depth `T` acting inside disjoint sets of sites
run in the same `T` layers, when every bond is nonempty. -/
theorem par (hne : ∀ b, (bond b).Nonempty) {R₁ R₂ : Set ι} (hR : Disjoint R₁ R₂)
    {U₁ U₂ : Matrix (ι → Fin d) (ι → Fin d) ℂ}
    (h₁ : IsBondCircuitOn bond R₁ T U₁) (h₂ : IsBondCircuitOn bond R₂ T U₂) :
    IsBondCircuitOn bond (R₁ ∪ R₂) T (U₁ * U₂) := by
  obtain ⟨Ls₁, hl₁, hLs₁, rfl⟩ := h₁
  obtain ⟨Ls₂, hl₂, hLs₂, rfl⟩ := h₂
  have := zip_union hne Ls₁ Ls₂ hR (hl₁.trans hl₂.symm) hLs₁ hLs₂
  rwa [hl₁] at this

/-- Circuits in parallel: a family of circuits of depth `T` acting inside pairwise disjoint
sets of sites is a circuit of depth `T`, when every bond is nonempty. -/
theorem finset_noncommProd (hne : ∀ b, (bond b).Nonempty) {κ : Type*} (s : Finset κ)
    (R : κ → Set ι) (hR : (s : Set κ).PairwiseDisjoint R)
    (U : κ → Matrix (ι → Fin d) (ι → Fin d) ℂ)
    (hU : ∀ i ∈ s, IsBondCircuitOn bond (R i) T (U i))
    (hcomm : (s : Set κ).Pairwise (Function.onFun Commute U)) :
    IsBondCircuitOn bond (⋃ i ∈ s, R i) T (s.noncommProd U hcomm) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one (d := d) bond (∅ : Set ι) T
  | insert a s ha ih =>
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha]
    have hdisj : Disjoint (R a) (⋃ i ∈ s, R i) := by
      rw [Set.disjoint_iUnion₂_right]
      intro i hi
      exact hR (by simp) (by simp [hi]) (fun h => ha (h ▸ hi))
    have := (hU a (by simp)).par hne hdisj
      (ih (hR.subset (by simp)) (fun i hi => hU i (by simp [hi])) (hcomm.mono (by simp)))
    simpa [Finset.set_biUnion_insert] using this

end IsBondCircuitOn

/-! ### Circuits on the ring -/

section Ring

variable {N : ℕ} [NeZero N]

/-- `U` is a local circuit of depth `T` on the ring all of whose gates act inside the set of
sites `R`.

Source: arXiv:2307.01696, main text before Theorem 1 ("depth-`T` local quantum circuits"),
restricted to gates inside `R` as in the parallel application of the block unitaries in the
paragraph "The sequential-RG circuit". -/
abbrev IsCircuitOn (R : Set (Fin N)) (T : ℕ) (U : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) :
    Prop :=
  IsBondCircuitOn ringBond R T U

namespace IsCircuitOn

variable {T : ℕ}

/-- Circuits in parallel on the ring: two circuits of depth `T` acting inside disjoint sets of
sites run in the same `T` layers. -/
theorem par {R₁ R₂ : Set (Fin N)} (hR : Disjoint R₁ R₂)
    {U₁ U₂ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ}
    (h₁ : IsCircuitOn R₁ T U₁) (h₂ : IsCircuitOn R₂ T U₂) :
    IsCircuitOn (R₁ ∪ R₂) T (U₁ * U₂) :=
  IsBondCircuitOn.par ringBond_nonempty hR h₁ h₂

/-- Circuits in parallel on the ring: a family of circuits of depth `T` acting inside pairwise
disjoint sets of sites is a circuit of depth `T`. -/
theorem finset_noncommProd {κ : Type*} (s : Finset κ) (R : κ → Set (Fin N))
    (hR : (s : Set κ).PairwiseDisjoint R) (U : κ → Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)
    (hU : ∀ i ∈ s, IsCircuitOn (R i) T (U i))
    (hcomm : (s : Set κ).Pairwise (Function.onFun Commute U)) :
    IsCircuitOn (⋃ i ∈ s, R i) T (s.noncommProd U hcomm) :=
  IsBondCircuitOn.finset_noncommProd ringBond_nonempty s R hR U hU hcomm

end IsCircuitOn

/-- **A product of two-site gates on a window is a circuit.** Let `e` place the `m` sites of an
open chain as consecutive sites of the ring (`e (i + 1) = e i + 1`). A product of at most `K`
gates on neighbouring sites of the open chain, placed by `e`, is a local circuit of depth `K`
whose gates act inside the range of `e`. -/
theorem IsPairProduct.isCircuitOn {m K : ℕ} {e : Fin m → Fin N} (he : Function.Injective e)
    (hsucc : ∀ i j : Fin m, j.val = i.val + 1 → e j = e i + 1)
    {X : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ} (hX : IsPairProduct d m K X) :
    IsCircuitOn (Set.range e) K (QuantumCircuit.embedOp e X) := by
  obtain ⟨l, hl, hg, rfl⟩ := hX
  refine IsBondCircuitOn.mono ?_ hl
  clear hl
  induction l with
  | nil => simpa using IsBondCircuitOn.one (d := d) ringBond (Set.range e) 0
  | cons Z l ih =>
    obtain ⟨hZu, p, p', hp, hZ⟩ := hg Z List.mem_cons_self
    have hZ' : QuantumCircuit.embedOp e Z ∈ supportedOperators d (ringBond (e p)) := by
      have := embedOp_mem_supportedOperators_image he hZ
      rwa [Set.image_pair, hsucc p p' hp] at this
    have h1 := IsBondCircuitOn.single (embedOp_mem_unitary he hZu) hZ'
      (R := Set.range e) (by
        rintro x (rfl | rfl)
        · exact ⟨p, rfl⟩
        · exact ⟨p', (hsucc p p' hp)⟩)
    have h2 := ih fun Z' hZ' => hg Z' (List.mem_cons_of_mem _ hZ')
    rw [List.prod_cons, ← embedOp_mul he, List.length_cons]
    exact h2.mul h1

/-- A product of pair products placed on pairwise disjoint windows of consecutive sites is a
local circuit of depth `K`. -/
theorem isCircuitOn_list_prod_embedOp {κ : Type*} {m : κ → ℕ} {K : ℕ}
    (e : ∀ i, Fin (m i) → Fin N) (Y : ∀ i, Matrix (Fin (m i) → Fin d) (Fin (m i) → Fin d) ℂ)
    (he : ∀ i, Function.Injective (e i))
    (hsucc : ∀ i (a a' : Fin (m i)), a'.val = a.val + 1 → e i a' = e i a + 1)
    (hY : ∀ i, IsPairProduct d (m i) K (Y i)) :
    ∀ l : List κ, l.Pairwise (fun i i' => Disjoint (Set.range (e i)) (Set.range (e i'))) →
      IsCircuitOn {x | ∃ i ∈ l, x ∈ Set.range (e i)} K
        ((l.map fun i => embedOp (e i) (Y i)).prod)
  | [], _ => by
    simpa using IsBondCircuitOn.one (d := d) ringBond
      ({x | ∃ i ∈ ([] : List κ), x ∈ Set.range (e i)}) K
  | i :: l, hl => by
    rw [List.pairwise_cons] at hl
    have h₁ := (hY i).isCircuitOn (he i) (hsucc i)
    have h₂ := isCircuitOn_list_prod_embedOp e Y he hsucc hY l hl.2
    have hdisj : Disjoint (Set.range (e i)) {x | ∃ i' ∈ l, x ∈ Set.range (e i')} := by
      rw [Set.disjoint_left]
      rintro x hx ⟨i', hi', hx'⟩
      exact Set.disjoint_left.mp (hl.1 i' hi') hx hx'
    rw [List.map_cons, List.prod_cons]
    refine (h₁.par hdisj h₂).mono_set fun x hx => ?_
    rcases hx with hx | ⟨i', hi', hx⟩
    · exact ⟨i, List.mem_cons_self, hx⟩
    · exact ⟨i', List.mem_cons_of_mem _ hi', hx⟩

end Ring

end QuantumCircuit
