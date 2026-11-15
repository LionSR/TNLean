/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.LocalCircuit
import Mathlib.Order.Interval.Finset.Fin

/-!
# A fixed depth-two circuit with dressed interval truncations

The circuit used in the endpoint audit of arXiv:2405.00439, Section V,
`detectG` (`Papers/2405.00439/MPU-DW.tex`, lines 2081–2087 and 2108–2117),
has gates `(w u) ⊗ u` on the unshifted pairs, followed by `1 ⊗ w†` on
the shifted pairs. Here the physical sites are pairs `(cell, leg)`, with
`leg : Bool`. Each layer is an actual `QuantumCircuit.BondLayer`.

All interval operators are obtained from this one circuit by retaining exactly
the gates whose two nominal sites are in the chosen cells. The full circuit is
the on-site symmetry. On a proper nonwrapping interval of cells with positive
left cut, its retained circuit is dressed by `w` on the leftmost even site.
These are project counterexample constructions, not a definition of a canonical
MPU truncation or a proof of the source's anomaly detection assertion.
-/

open Matrix

namespace MPOTensor.FiniteGroupDetector

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {d : ℕ}

private theorem rectKronecker_mem_unitary (A : κ × Bool → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ s, A s ∈ unitary (Matrix (Fin d) (Fin d) ℂ)) :
    rectKronecker A ∈ unitary (Matrix (κ × Bool → Fin d) (κ × Bool → Fin d) ℂ) := by
  have hleft : ∀ s, (A s)ᴴ * A s = 1 := fun s ↦ Unitary.star_mul_self_of_mem (hA s)
  have hright : ∀ s, A s * (A s)ᴴ = 1 := fun s ↦ Unitary.mul_star_self_of_mem (hA s)
  constructor
  · change (rectKronecker A)ᴴ * rectKronecker A = 1
    rw [rectKronecker_conjTranspose, rectKronecker_mul]
    simp only [hleft, rectKronecker_one]
  · change rectKronecker A * (rectKronecker A)ᴴ = 1
    rw [rectKronecker_conjTranspose, rectKronecker_mul]
    simp only [hright, rectKronecker_one]

/-- The nominal pair of a gate, with independent permutations of the two legs.
Source context: the depth-two circuit truncation in arXiv:2405.00439,
Section V, lines 2081–2087. -/
def pairedBond (σ : Bool → Equiv.Perm κ) (k : κ) : Set (κ × Bool) :=
  Set.range fun b ↦ (σ b k, b)

/-- The product gate with one-site factors `A false` and `A true` on its
specified pair, extended by identities elsewhere. Source context:
arXiv:2405.00439, Section V, lines 2081–2087. -/
noncomputable def pairedGate (σ : Bool → Equiv.Perm κ)
    (A : Bool → Matrix (Fin d) (Fin d) ℂ) (k : κ) :
    Matrix (κ × Bool → Fin d) (κ × Bool → Fin d) ℂ :=
  rectKronecker fun s ↦ if σ s.2 k = s.1 then A s.2 else 1

omit [Fintype κ] [DecidableEq κ] in
private theorem pairedBond_disjoint (σ : Bool → Equiv.Perm κ) {k l : κ} (hkl : k ≠ l) :
    Disjoint (pairedBond σ k) (pairedBond σ l) := by
  rw [Set.disjoint_left]
  rintro s ⟨b, hb⟩ ⟨b', hb'⟩
  have heq := hb.trans hb'.symm
  have hbb : b = b' := congrArg Prod.snd heq
  subst b'
  exact hkl ((σ b).injective (congrArg Prod.fst heq))

private theorem pairedGate_supported (σ : Bool → Equiv.Perm κ)
    (A : Bool → Matrix (Fin d) (Fin d) ℂ) (k : κ) :
    pairedGate σ A k ∈ QuantumCircuit.supportedOperators d (pairedBond σ k) := by
  apply QuantumCircuit.rectKronecker_mem_supportedOperators
  intro s hs
  have hne : σ s.2 k ≠ s.1 := fun h ↦ hs ⟨s.2, Prod.ext h rfl⟩
  simp [hne]

private theorem pairedGate_unitary (σ : Bool → Equiv.Perm κ)
    (A : Bool → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ b, A b ∈ unitary (Matrix (Fin d) (Fin d) ℂ)) (k : κ) :
    pairedGate σ A k ∈ unitary (Matrix (κ × Bool → Fin d) (κ × Bool → Fin d) ℂ) := by
  apply rectKronecker_mem_unitary
  intro s
  split_ifs
  · exact hA s.2
  · exact Submonoid.one_mem _

private theorem pairedGate_list_prod (σ : Bool → Equiv.Perm κ)
    (A : Bool → Matrix (Fin d) (Fin d) ℂ) (l : List κ) (hl : l.Nodup) :
    (l.map (pairedGate σ A)).prod =
      rectKronecker fun s ↦ if (σ s.2).symm s.1 ∈ l then A s.2 else 1 := by
  induction l with
  | nil => simp
  | cons k l ih =>
    obtain ⟨hk, ht⟩ := List.nodup_cons.mp hl
    rw [List.map_cons, List.prod_cons, ih ht, pairedGate, rectKronecker_mul]
    congr 1
    funext s
    by_cases h : σ s.2 k = s.1
    · have hinv : (σ s.2).symm s.1 = k := by rw [← h]; simp
      simp [h, hinv, hk]
    · have hinv : (σ s.2).symm s.1 ≠ k := by
        intro heq
        apply h
        rw [← heq, Equiv.apply_symm_apply]
      simp [h, hinv]

/-- The common two-matching bond geometry. The second component selects a
circuit layer. Source context: arXiv:2405.00439, Section V, lines 2081–2087. -/
def pairCircuitBond (σ : Bool → Bool → Equiv.Perm κ) (p : κ × Bool) : Set (κ × Bool) :=
  pairedBond (σ p.2) p.1

/-- One actual layer of pair gates, retaining the cells in `S`.
Source context: arXiv:2405.00439, Section V, lines 2081–2087. -/
noncomputable def pairCircuitLayer (σ : Bool → Bool → Equiv.Perm κ) (color : Bool)
    (A : Bool → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ b, A b ∈ unitary (Matrix (Fin d) (Fin d) ℂ)) (S : Finset κ) :
    QuantumCircuit.BondLayer d (pairCircuitBond σ) where
  bonds := S.image fun k ↦ (k, color)
  gate p := pairedGate (σ color) A p.1
  gate_mem_unitary p _ := pairedGate_unitary _ _ hA p.1
  gate_mem_supportedOperators p hp := by
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hp
    exact pairedGate_supported _ _ k
  pairwiseDisjoint := by
    intro p hp q hq hpq
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hq
    exact pairedBond_disjoint _ fun h ↦ hpq (Prod.ext h rfl)

/-- The layer operator is the tensor product of its retained gate factors.
This identifies the actual finite product of pair gates, rather than supplying
its value as a hypothesis. Source context: arXiv:2405.00439, Section V,
lines 2081–2087. -/
theorem pairCircuitLayer_op (σ : Bool → Bool → Equiv.Perm κ) (color : Bool)
    (A : Bool → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ b, A b ∈ unitary (Matrix (Fin d) (Fin d) ℂ)) (S : Finset κ) :
    (pairCircuitLayer σ color A hA S).op =
      rectKronecker fun s ↦ if (σ color s.2).symm s.1 ∈ S then A s.2 else 1 := by
  have hinj : Function.Injective (fun k : κ ↦ (k, color)) :=
    fun _ _ h ↦ congrArg Prod.fst h
  have hn := S.nodup_toList.map hinj
  have hset : S.image (fun k ↦ (k, color)) = (S.toList.map fun k ↦ (k, color)).toFinset := by
    ext p
    simp only [Finset.mem_image, List.mem_toFinset, List.mem_map, Finset.mem_toList]
  let L := pairCircuitLayer σ color A hA S
  have hcomm := L.gate_commute L.bonds subset_rfl
  change (↑(S.image fun k ↦ (k, color)) : Set (κ × Bool)).Pairwise
    (Function.onFun Commute fun p ↦ pairedGate (σ color) A p.1) at hcomm
  have hcomm' : (↑(S.toList.map fun k ↦ (k, color)).toFinset : Set (κ × Bool)).Pairwise
      (Function.onFun Commute fun p ↦ pairedGate (σ color) A p.1) := by
    simpa only [hset] using hcomm
  change (S.image fun k ↦ (k, color)).noncommProd
    (fun p ↦ pairedGate (σ color) A p.1) hcomm = _
  have hprod : (S.image fun k ↦ (k, color)).noncommProd
      (fun p ↦ pairedGate (σ color) A p.1) hcomm =
      ((S.toList.map fun k ↦ (k, color)).map fun p ↦ pairedGate (σ color) A p.1).prod := by
    simpa only [hset] using Finset.noncommProd_toFinset
      (S.toList.map fun k ↦ (k, color)) (fun p ↦ pairedGate (σ color) A p.1) hcomm' hn
  rw [hprod]
  simp only [List.map_map, Function.comp_apply]
  simpa using pairedGate_list_prod (σ color) A S.toList S.nodup_toList

/-- Unshifted first-layer pairs, then shifted second-layer pairs.
Source context: arXiv:2405.00439, Section V, lines 2081–2087. -/
def dressedCircuitMatchings (τ : Equiv.Perm κ) (color leg : Bool) : Equiv.Perm κ :=
  if color then if leg then Equiv.refl κ else τ else Equiv.refl κ

omit [Fintype κ] [DecidableEq κ] in
private theorem pairedBond_subset_cells (σ : Bool → Equiv.Perm κ) (S : Finset κ)
    (k : κ) : pairedBond σ k ⊆ {s : κ × Bool | s.1 ∈ S} ↔
      σ false k ∈ S ∧ σ true k ∈ S := by
  constructor
  · intro h
    exact ⟨h ⟨false, rfl⟩, h ⟨true, rfl⟩⟩
  · rintro ⟨hf, ht⟩ _ ⟨b, rfl⟩
    cases b
    · exact hf
    · exact ht

/-- The retained first layer consists exactly of the original gates whose
nominal two-site bonds lie in the chosen cells. Source context: gate deletion
in arXiv:2405.00439, Section V, lines 2081–2087. -/
theorem pairCircuitLayer_first_retained (τ : Equiv.Perm κ)
    (A : Bool → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ b, A b ∈ unitary (Matrix (Fin d) (Fin d) ℂ)) (S : Finset κ)
    (p : κ × Bool) :
    p ∈ (pairCircuitLayer (dressedCircuitMatchings τ) false A hA S).bonds ↔
      p ∈ (pairCircuitLayer (dressedCircuitMatchings τ) false A hA Finset.univ).bonds ∧
        pairCircuitBond (dressedCircuitMatchings τ) p ⊆ {s | s.1 ∈ S} := by
  rcases p with ⟨k, b⟩
  cases b <;> simp [pairCircuitLayer, pairCircuitBond, pairedBond_subset_cells,
    dressedCircuitMatchings]

/-- The retained shifted layer consists exactly of the original gates whose
nominal two-site bonds lie in the chosen cells. This uses the nominal bond even
when one factor of the gate is an identity. Source context: gate deletion in
arXiv:2405.00439, Section V, lines 2081–2087. -/
theorem pairCircuitLayer_second_retained (τ : Equiv.Perm κ)
    (A : Bool → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ b, A b ∈ unitary (Matrix (Fin d) (Fin d) ℂ)) (S : Finset κ)
    (p : κ × Bool) :
    p ∈ (pairCircuitLayer (dressedCircuitMatchings τ) true A hA
      (S.filter fun k ↦ τ k ∈ S)).bonds ↔
      p ∈ (pairCircuitLayer (dressedCircuitMatchings τ) true A hA Finset.univ).bonds ∧
        pairCircuitBond (dressedCircuitMatchings τ) p ⊆ {s | s.1 ∈ S} := by
  rcases p with ⟨k, b⟩
  cases b <;> simp [pairCircuitLayer, pairCircuitBond, pairedBond_subset_cells,
    dressedCircuitMatchings, and_comm]

private def firstPairFactors (u w : unitary (Matrix (Fin d) (Fin d) ℂ))
    (b : Bool) : Matrix (Fin d) (Fin d) ℂ := if b then u else w * u

private def secondPairFactors (w : unitary (Matrix (Fin d) (Fin d) ℂ))
    (b : Bool) : Matrix (Fin d) (Fin d) ℂ := if b then 1 else star (w : Matrix _ _ ℂ)

private theorem firstPairFactors_unitary (u w : unitary (Matrix (Fin d) (Fin d) ℂ))
    (b : Bool) : firstPairFactors u w b ∈ unitary (Matrix (Fin d) (Fin d) ℂ) := by
  cases b
  · exact (w * u).property
  · exact u.property

private theorem secondPairFactors_unitary (w : unitary (Matrix (Fin d) (Fin d) ℂ))
    (b : Bool) : secondPairFactors w b ∈ unitary (Matrix (Fin d) (Fin d) ℂ) := by
  cases b
  · exact Unitary.star_mem w.property
  · exact Submonoid.one_mem _

/-- The two actual circuit layers after deleting gates not contained in the
chosen cells. A second-layer gate survives precisely when both its original
cell and its shifted even cell belong to `S`. Source: the gate-deletion
construction in arXiv:2405.00439, Section V, lines 2081–2087. -/
noncomputable def dressedPairCircuit (τ : Equiv.Perm κ)
    (u w : unitary (Matrix (Fin d) (Fin d) ℂ)) (S : Finset κ) :
    List (QuantumCircuit.BondLayer d (pairCircuitBond (dressedCircuitMatchings τ))) :=
  [pairCircuitLayer (dressedCircuitMatchings τ) false (firstPairFactors u w)
      (firstPairFactors_unitary u w) S,
    pairCircuitLayer (dressedCircuitMatchings τ) true (secondPairFactors w)
      (secondPairFactors_unitary w) (S.filter fun k ↦ τ k ∈ S)]

/-- The retained circuit has depth two. Source context: arXiv:2405.00439,
Section V, lines 2081–2087. -/
@[simp] theorem dressedPairCircuit_length (τ : Equiv.Perm κ)
    (u w : unitary (Matrix (Fin d) (Fin d) ℂ)) (S : Finset κ) :
    (dressedPairCircuit τ u w S).length = 2 := rfl

/-- On the full periodic chain the fixed circuit is precisely the on-site
symmetry. Source context: arXiv:2405.00439, Section V, lines 2081–2087;
the circuit is the explicit construction in the endpoint audit. -/
theorem circuitOp_dressedPairCircuit_univ (τ : Equiv.Perm κ)
    (u w : unitary (Matrix (Fin d) (Fin d) ℂ)) :
    QuantumCircuit.circuitOp (dressedPairCircuit τ u w Finset.univ) =
      rectKronecker fun _ : κ × Bool ↦ (u : Matrix (Fin d) (Fin d) ℂ) := by
  simp only [dressedPairCircuit, QuantumCircuit.circuitOp, Matrix.one_mul,
    pairCircuitLayer_op, rectKronecker_mul]
  congr 1
  funext s
  rcases s with ⟨k, b⟩
  cases b <;> simp [dressedCircuitMatchings, firstPairFactors, secondPairFactors,
    ← Matrix.mul_assoc, Unitary.star_mul_self_of_mem w.property]

/-- Retaining a region with one entry boundary leaves the dressing exactly on
that boundary's even site. The boundary condition is a statement about cells
of the retained gates, not an assumed equality of circuit operators.
Source context: arXiv:2405.00439, Section V, lines 2081–2087. -/
theorem circuitOp_dressedPairCircuit_single_entry (τ : Equiv.Perm κ)
    (u w : unitary (Matrix (Fin d) (Fin d) ℂ)) (S : Finset κ) (a : κ)
    (ha : a ∈ S) (hentry : ∀ k ∈ S, τ.symm k ∈ S ↔ k ≠ a) :
    QuantumCircuit.circuitOp (dressedPairCircuit τ u w S) =
      rectKronecker (fun s : κ × Bool ↦ if s = (a, false) then
        (w : Matrix (Fin d) (Fin d) ℂ) else 1) *
      rectKronecker (fun s : κ × Bool ↦ if s.1 ∈ S then
        (u : Matrix (Fin d) (Fin d) ℂ) else 1) := by
  simp only [dressedPairCircuit, QuantumCircuit.circuitOp, Matrix.one_mul,
    pairCircuitLayer_op, rectKronecker_mul]
  congr 1
  funext s
  rcases s with ⟨k, b⟩
  cases b
  · by_cases hk : k ∈ S
    · have hpred := hentry k hk
      by_cases hka : k = a
      · subst k
        simp [dressedCircuitMatchings, firstPairFactors, ha, hpred]
      · simp [dressedCircuitMatchings, firstPairFactors, secondPairFactors, hk, hpred,
          hka, ← Matrix.mul_assoc, Unitary.star_mul_self_of_mem w.property]
    · have hka : k ≠ a := by intro h; subst k; exact hk ha
      simp [dressedCircuitMatchings, hk, hka]
  · simp [dressedCircuitMatchings, firstPairFactors, secondPairFactors]

/-- The successor permutation of the cells in their cyclic order. -/
def cellSuccessor (M : ℕ) [NeZero M] : Equiv.Perm (Fin M) :=
  (Equiv.subRight (1 : Fin M)).symm

/-- A nonwrapping interval with positive left cut has exactly one entry
boundary for the fixed shifted matching. Source context: arXiv:2405.00439,
Section V, lines 2081–2087. -/
theorem cellSuccessor_Icc_single_entry {M : ℕ} [NeZero M] (a b : Fin M)
    (ha : 0 < a.val) :
    ∀ k ∈ Finset.Icc a b, (cellSuccessor M).symm k ∈ Finset.Icc a b ↔ k ≠ a := by
  intro k hk
  have hk0 : k ≠ 0 := by
    intro heq
    have hak : a.val ≤ k.val := (Finset.mem_Icc.mp hk).1
    have hval := congrArg Fin.val heq
    simp only [Fin.val_zero] at hval
    omega
  change k - 1 ∈ Finset.Icc a b ↔ k ≠ a
  simp only [Finset.mem_Icc, Fin.le_def,
    Fin.val_sub_one_of_ne_zero hk0]
  simp only [Finset.mem_Icc, Fin.le_def] at hk
  omega

end MPOTensor.FiniteGroupDetector
