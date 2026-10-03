/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Gates.TwoSiteUniversality

/-!
# Products of gates on windows of consecutive sites

A gate on a window of `m` consecutive sites of the open chain of `n` sites is a unitary acting on
the sites `a, a + 1, …, a + m - 1` that lie in the chain, for some `a`; near the right end the
window is cut off, so such a gate acts on at most `m` consecutive sites. This file records the
operators that are products of at most `K` such gates (`QuantumCircuit.IsWindowProduct`) and
shows:

* the class is closed under products and under placing the chain inside a larger chain as a
  block of consecutive sites (`QuantumCircuit.IsWindowProduct.embedOp`);
* a unitary on `l ≤ m` sites placed on consecutive sites is a single gate
  (`QuantumCircuit.isWindowGate_embedOp`);
* for windows of two sites the gates are the gates on neighbouring sites
  (`QuantumCircuit.IsWindowProduct.isPairProduct_two`), and for windows of `m ≥ 2` sites every
  gate is a product of a number of gates on neighbouring sites bounded in terms of `d` and `m`
  only (`QuantumCircuit.IsWindowProduct.exists_isPairProduct`).

Gates on `k + 1` consecutive sites are the gates of the sequential preparation of a matrix
product state of bond dimension `D ≤ d^k`: the isometries of arXiv:2307.01696, eq. (14)
(paragraph "The sequential-RG circuit") and of arXiv:quant-ph/0501096, eq. `induction`, each act
on a bond register of `k` sites and one fresh site.
-/

open Matrix

namespace QuantumCircuit

variable {d m n : ℕ}

/-- The sites `a, a + 1, …, a + m - 1` of the open chain of `n` sites, cut off at the right
end of the chain. -/
def windowSites (n a m : ℕ) : Set (Fin n) := {p | a ≤ p.val ∧ p.val < a + m}

/-- A unitary gate acting on a window of `m` consecutive sites of the open chain of `n` sites.

Source: arXiv:2307.01696, main text before Theorem 1 and paragraph "The sequential-RG circuit"
(unitaries "with constant support"). -/
def IsWindowGate (m : ℕ) (Z : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) : Prop :=
  Z ∈ unitary (Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) ∧
    ∃ a, Z ∈ supportedOperators d (windowSites n a m)

/-- `X` is a product of at most `K` unitary gates, each acting on a window of `m` consecutive
sites of the open chain of `n` sites.

Source: arXiv:2307.01696, paragraph "The sequential-RG circuit" (the sequential circuit of the
isometries of eq. (14), each with constant support). -/
def IsWindowProduct (d n m K : ℕ) (X : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) : Prop :=
  ∃ l : List (Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ), l.length ≤ K ∧
    (∀ Z ∈ l, IsWindowGate m Z) ∧ X = l.prod

/-- A unitary on `l ≤ m` sites placed on the consecutive sites `a, …, a + l - 1` is a gate on a
window of `m` sites. -/
theorem isWindowGate_embedOp {l : ℕ} (hl : l ≤ m) {e : Fin l → Fin n}
    (he : Function.Injective e) {a : ℕ} (hea : ∀ i, (e i).val = a + i.val)
    {X : Matrix (Fin l → Fin d) (Fin l → Fin d) ℂ}
    (hX : X ∈ unitary (Matrix (Fin l → Fin d) (Fin l → Fin d) ℂ)) :
    IsWindowGate m (embedOp e X) := by
  refine ⟨embedOp_mem_unitary he hX, a, supportedOperators_mono ?_
    (embedOp_mem_supportedOperators he X)⟩
  rintro _ ⟨i, rfl⟩
  simp only [windowSites, Set.mem_ofPred_eq, hea]
  omega

/-- A unitary on all the sites of a chain of `n ≤ m` sites is a gate on a window of `m`
sites. -/
theorem isWindowGate_of_le {Z : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ} (hnm : n ≤ m)
    (hZ : Z ∈ unitary (Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ)) : IsWindowGate m Z :=
  ⟨hZ, 0, supportedOperators_mono
    (fun p _ => show 0 ≤ p.val ∧ p.val < 0 + m from ⟨Nat.zero_le _, by omega⟩)
    (mem_supportedOperators_univ Z)⟩

namespace IsWindowProduct

theorem one (K : ℕ) : IsWindowProduct d n m K 1 :=
  ⟨[], by simp, by simp, by simp⟩

theorem mono {K K' : ℕ} (hK : K ≤ K') {X : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ}
    (hX : IsWindowProduct d n m K X) : IsWindowProduct d n m K' X := by
  obtain ⟨l, hl, hg, rfl⟩ := hX
  exact ⟨l, hl.trans hK, hg, rfl⟩

theorem mul {K K' : ℕ} {X Y : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ}
    (hX : IsWindowProduct d n m K X) (hY : IsWindowProduct d n m K' Y) :
    IsWindowProduct d n m (K + K') (X * Y) := by
  obtain ⟨l, hl, hg, rfl⟩ := hX
  obtain ⟨l', hl', hg', rfl⟩ := hY
  refine ⟨l ++ l', by simp; omega, fun Z hZ => ?_, by simp⟩
  rcases List.mem_append.mp hZ with h | h
  · exact hg Z h
  · exact hg' Z h

theorem of_isWindowGate {Z : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ} (hZ : IsWindowGate m Z) :
    IsWindowProduct d n m 1 Z :=
  ⟨[Z], by simp, by simpa using hZ, by simp⟩

theorem mem_unitary {K : ℕ} {X : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ}
    (hX : IsWindowProduct d n m K X) :
    X ∈ unitary (Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) := by
  obtain ⟨l, -, hg, rfl⟩ := hX
  induction l with
  | nil => exact Submonoid.one_mem _
  | cons Z l ih =>
    rw [List.prod_cons]
    exact Submonoid.mul_mem _ (hg Z (by simp)).1 (ih fun Z' h => hg Z' (by simp [h]))

/-- Placing the chain of `n` sites as the consecutive sites `a, a + 1, …, a + n - 1` of a chain
of `n'` sites keeps products of gates on windows. -/
theorem embedOp {n' K : ℕ} {e : Fin n → Fin n'} (he : Function.Injective e) {a : ℕ}
    (hea : ∀ i, (e i).val = a + i.val) {X : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ}
    (hX : IsWindowProduct d n m K X) : IsWindowProduct d n' m K (embedOp e X) := by
  obtain ⟨l, hl, hg, rfl⟩ := hX
  refine ⟨l.map (QuantumCircuit.embedOp e), by simpa using hl, fun Z hZ => ?_,
    embedOp_list_prod he l⟩
  obtain ⟨Z', hZ', rfl⟩ := List.mem_map.mp hZ
  obtain ⟨hu, b, hS⟩ := hg Z' hZ'
  refine ⟨embedOp_mem_unitary he hu, a + b, supportedOperators_mono ?_
    (embedOp_mem_supportedOperators_image he hS)⟩
  rintro _ ⟨i, hi, rfl⟩
  simp only [windowSites, Set.mem_ofPred_eq, hea] at hi ⊢
  omega

/-- On a chain of at least two sites, a gate on a window of two sites is a gate on two
neighbouring sites. -/
theorem _root_.QuantumCircuit.IsWindowGate.isNeighbourGate (hn : 2 ≤ n)
    {Z : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ} (hZ : IsWindowGate 2 Z) : IsNeighbourGate Z := by
  obtain ⟨hu, a, hS⟩ := hZ
  refine ⟨hu, ⟨min a (n - 2), by omega⟩, ⟨min a (n - 2) + 1, by omega⟩, rfl,
    supportedOperators_mono ?_ hS⟩
  intro p hp
  simp only [windowSites, Set.mem_ofPred_eq] at hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Fin.ext_iff]
  omega

/-- On a chain of at least two sites, a product of gates on windows of two sites is a product of
gates on neighbouring sites. -/
theorem isPairProduct_two (hn : 2 ≤ n) {K : ℕ} {X : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ}
    (hX : IsWindowProduct d n 2 K X) : IsPairProduct d n K X := by
  obtain ⟨l, hl, hg, rfl⟩ := hX
  exact ⟨l, hl, fun Z hZ => (hg Z hZ).isNeighbourGate hn, rfl⟩

/-- **Gates on windows through gates on neighbouring sites.** For `m ≥ 2` there is `C`,
depending only on `d` and `m`, such that on every chain of at least two sites a product of at
most `K` gates on windows of `m` sites is a product of at most `K C` gates on neighbouring
sites.

arXiv:2307.01696, caption of Fig. 1: the unitaries with constant support "can be further
expressed with a low-depth circuit of local gates". -/
theorem exists_isPairProduct (hd : 0 < d) (hm : 2 ≤ m) :
    ∃ C, ∀ n K, 2 ≤ n → ∀ X : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ,
      IsWindowProduct d n m K X → IsPairProduct d n (K * C) X := by
  classical
  have hex : ∀ l, ∃ C, 2 ≤ l → ∀ X : Matrix (Fin l → Fin d) (Fin l → Fin d) ℂ,
      X ∈ unitary (Matrix (Fin l → Fin d) (Fin l → Fin d) ℂ) → IsPairProduct d l C X := by
    intro l
    by_cases hl : 2 ≤ l
    · obtain ⟨C, hC⟩ := QuantumCircuit.exists_isPairProduct (d := d) hd hl
      exact ⟨C, fun _ => hC⟩
    · exact ⟨0, fun h => absurd h hl⟩
  choose f hf using hex
  refine ⟨∑ l ∈ Finset.range (m + 1), f l, fun n K hn X hX => ?_⟩
  obtain ⟨l, hl, hg, rfl⟩ := hX
  have hgate : ∀ Z ∈ l, IsPairProduct d n (∑ l ∈ Finset.range (m + 1), f l) Z := by
    intro Z hZ
    obtain ⟨hu, a, hS⟩ := hg Z hZ
    set w := min m n with hw
    set a' := min a (n - w) with ha'
    let e : Fin w → Fin n := fun j => ⟨a' + j.val, by omega⟩
    have he : Function.Injective e := fun j j' h => Fin.ext (by simpa [e] using h)
    have hsub : windowSites n a m ⊆ Set.range e := by
      intro p hp
      simp only [windowSites, Set.mem_ofPred_eq] at hp
      exact ⟨⟨p.val - a', by omega⟩, Fin.ext (by simp [e]; omega)⟩
    obtain ⟨Y, rfl⟩ := exists_embedOp_eq_of_mem_supportedOperators he
      (supportedOperators_mono hsub hS)
    have hY := hf w (by omega) Y (mem_unitary_of_embedOp_mem_unitary he hd hu)
    refine (hY.embedOp he (a := a') fun i => rfl).mono ?_
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
  exact (IsPairProduct.list_prod l hgate).mono (Nat.mul_le_mul_right _ hl)

end IsWindowProduct

end QuantumCircuit
