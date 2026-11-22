/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Circuit.Model.Unitary
import TNLean.Algebra.FinKronecker
import Mathlib.Order.Interval.Finset.Fin

/-!
# A fixed depth-two circuit with dressed interval truncations

The circuit used in the endpoint audit of arXiv:2405.00439, Section V,
`detectG` (`Papers/2405.00439/MPU-DW.tex`, lines 2081–2087 and 2108–2117),
has gates `(w u) ⊗ u` on the unshifted pairs, followed by `1 ⊗ w†` on
the shifted pairs. Here the physical sites are pairs `(cell, leg)`, with
`leg : Bool`. The geometry has one cell for every nominal pair, and each layer
is an actual `QuantumCircuit.Layer` of unitary gates on disjoint cells.

All interval operators are obtained from this one circuit by retaining exactly
the gates whose two nominal sites are in the chosen cells. The full circuit is
the on-site symmetry. On a proper nonwrapping interval of cells with positive
left cut, its retained circuit is dressed by `w` on the leftmost even site.
These are project counterexample constructions, not a definition of a canonical
MPU truncation or a proof of the source's anomaly detection assertion.
-/

open Matrix QuantumCircuit

namespace MPOTensor.FiniteGroupDetector

variable {κ : Type} [Fintype κ] [DecidableEq κ] {d : ℕ}

/-- The nominal pair of a gate, with independent permutations of the two legs.
Source context: the depth-two circuit truncation in arXiv:2405.00439,
Section V, lines 2081–2087. -/
def pairedBond (σ : Bool → Equiv.Perm κ) (k : κ) : Finset (κ × Bool) :=
  Finset.univ.image fun b ↦ (σ b k, b)

/-- The product gate with one-site factors `A false` and `A true` on its
specified pair, extended by identities elsewhere. Source context:
arXiv:2405.00439, Section V, lines 2081–2087. -/
noncomputable def pairedGate (σ : Bool → Equiv.Perm κ)
    (A : Bool → Matrix (Fin d) (Fin d) ℂ) (k : κ) :
    Matrix (κ × Bool → Fin d) (κ × Bool → Fin d) ℂ :=
  rectKronecker fun s ↦ if σ s.2 k = s.1 then A s.2 else 1

omit [Fintype κ] in
private theorem pairedBond_disjoint (σ : Bool → Equiv.Perm κ) {k l : κ} (hkl : k ≠ l) :
    Disjoint (pairedBond σ k) (pairedBond σ l) := by
  rw [Finset.disjoint_left]
  intro s hs hs'
  obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hs
  obtain ⟨b', _, hb'⟩ := Finset.mem_image.mp hs'
  have heq := hb.trans hb'.symm
  have hbb : b = b' := congrArg Prod.snd heq
  subst b'
  exact hkl ((σ b).injective (congrArg Prod.fst heq))

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
def pairCircuitBond (σ : Bool → Bool → Equiv.Perm κ) (p : κ × Bool) : Finset (κ × Bool) :=
  pairedBond (σ p.2) p.1

/-- The geometry of the nominal pairs: one cell `pairCircuitBond σ p` of cost `1` for every
`p`. Source context: arXiv:2405.00439, Section V, lines 2081–2087. -/
abbrev pairCircuitGeometry (σ : Bool → Bool → Equiv.Perm κ) : Geometry (κ × Bool) where
  Cell := κ × Bool
  cell := pairCircuitBond σ
  cost _ := 1

/-- The one-site factor at the site `s` of the pair gate on the cell `p`. -/
def pairedFactor (σ : Bool → Bool → Equiv.Perm κ) (A : Bool → Matrix (Fin d) (Fin d) ℂ)
    (p s : κ × Bool) : Matrix (Fin d) (Fin d) ℂ :=
  if σ p.2 s.2 p.1 = s.1 then A s.2 else 1

/-- The product of the one-site factors of a cell, placed on the cell, is the pair gate. -/
private theorem place_prodOp_pairedFactor (σ : Bool → Bool → Equiv.Perm κ)
    (A : Bool → Matrix (Fin d) (Fin d) ℂ) (p : κ × Bool) :
    ManyBody.place ((pairCircuitGeometry σ).cell p)
        (ManyBody.prodOp (X := fun _ : {s // s ∈ (pairCircuitGeometry σ).cell p} ↦ Fin d)
          fun s ↦ pairedFactor σ A p s.1) =
      pairedGate (σ p.2) A p.1 := by
  rw [← ManyBody.placeAlong_subtype]
  refine ManyBody.placeAlong_prodOp _ _ (pairedFactor σ A p) (fun _ ↦ rfl) fun s hs ↦ ?_
  have hne : σ p.2 s.2 p.1 ≠ s.1 := fun h ↦
    hs ⟨s, Finset.mem_image.mpr ⟨s.2, Finset.mem_univ _, Prod.ext h rfl⟩⟩ rfl
  simp [pairedFactor, hne]

/-- One actual layer of pair gates, retaining the cells in `S`.
Source context: arXiv:2405.00439, Section V, lines 2081–2087. -/
noncomputable def pairCircuitLayer (σ : Bool → Bool → Equiv.Perm κ) (color : Bool)
    (A : Bool → Matrix (Fin d) (Fin d) ℂ) (S : Finset κ) :
    Layer (pairCircuitGeometry σ) KrausGate (fun _ ↦ Fin d) (fun _ ↦ Fin d) :=
  Layer.ofCells (S.image fun k ↦ (k, color))
    (by
      intro p hp q hq hpq
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hq
      exact pairedBond_disjoint (σ color) fun h ↦ hpq (Prod.ext h rfl))
    fun p ↦ KrausFamily.single
      (ManyBody.prodOp (X := fun _ : {s // s ∈ (pairCircuitGeometry σ).cell p.1} ↦ Fin d)
        fun s ↦ pairedFactor σ A p.1 s.1)

omit [Fintype κ] in
/-- With unitary one-site factors, every gate of the layer is unitary. -/
theorem forall_isUnitary_pairCircuitLayer (σ : Bool → Bool → Equiv.Perm κ) (color : Bool)
    (A : Bool → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ b, A b ∈ unitary (Matrix (Fin d) (Fin d) ℂ)) (S : Finset κ) :
    (pairCircuitLayer σ color A S).Forall KrausGate.ev KrausFamily.IsUnitary :=
  Layer.forall_ofCells _ (KrausFamily.isUnitary_single (one_mem _)) _ _ _ fun p ↦
    KrausFamily.isUnitary_single (ManyBody.prodOp_mem_unitary fun s ↦ by
      unfold pairedFactor
      split_ifs
      · exact hA _
      · exact one_mem _)

/-- The layer operator is the tensor product of its retained gate factors.
This identifies the actual finite product of pair gates, rather than supplying
its value as a hypothesis. Source context: arXiv:2405.00439, Section V,
lines 2081–2087. -/
theorem pairCircuitLayer_kraus (σ : Bool → Bool → Equiv.Perm κ) (color : Bool)
    (A : Bool → Matrix (Fin d) (Fin d) ℂ) (S : Finset κ)
    (i : (pairCircuitLayer σ color A S).Index) :
    (pairCircuitLayer σ color A S).kraus KrausGate.ev i =
      rectKronecker fun s ↦ if (σ color s.2).symm s.1 ∈ S then A s.2 else 1 := by
  classical
  have hinj : Function.Injective fun c : (S.image fun k ↦ (k, color)) ↦ c.1.1 := by
    intro c c' h
    obtain ⟨k, -, hk⟩ := Finset.mem_image.mp c.2
    obtain ⟨k', -, hk'⟩ := Finset.mem_image.mp c'.2
    apply Subtype.ext
    have h' : (c : κ × Bool).1 = (c' : κ × Bool).1 := h
    rw [← hk, ← hk'] at h' ⊢
    simp only at h'
    rw [h']
  have hmem : ∀ k, k ∈ ((Finset.univ : Finset (S.image fun k ↦ (k, color))).toList.map
      fun c ↦ c.1.1) ↔ k ∈ S := by
    intro k
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨c, hc⟩
      obtain ⟨k', hk', hk⟩ := Finset.mem_image.mp c.2
      rw [← hc, ← hk]
      exact hk'
    · intro hk
      exact ⟨⟨(k, color), Finset.mem_image_of_mem _ hk⟩, rfl⟩
  have hcolor : ((Finset.univ : Finset (S.image fun k ↦ (k, color))).toList.map
      fun c ↦ pairedGate (σ c.1.2) A c.1.1) =
      ((Finset.univ : Finset (S.image fun k ↦ (k, color))).toList.map fun c ↦ c.1.1).map
        (pairedGate (σ color) A) := by
    rw [List.map_map]
    refine List.map_congr_left fun c _ ↦ ?_
    obtain ⟨k, -, hk⟩ := Finset.mem_image.mp c.2
    simp only [Function.comp_apply, ← hk]
  refine (Layer.kraus_ofCells (Γ := pairCircuitGeometry σ) KrausGate.ev
    (S.image fun k ↦ (k, color)) _ _
    (Finset.univ : Finset (S.image fun k ↦ (k, color))).toList (Finset.nodup_toList _)
    (fun c ↦ Finset.mem_toList.mpr (Finset.mem_univ c)) i).trans ?_
  refine (congrArg List.prod (List.map_congr_left
    (g := fun c : (S.image fun k ↦ (k, color)) ↦ pairedGate (σ c.1.2) A c.1.1)
    fun c _ ↦ place_prodOp_pairedFactor σ A c.1)).trans ?_
  rw [hcolor, pairedGate_list_prod (σ color) A _ ((Finset.nodup_toList _).map hinj)]
  simp only [hmem]

/-- Unshifted first-layer pairs, then shifted second-layer pairs.
Source context: arXiv:2405.00439, Section V, lines 2081–2087. -/
def dressedCircuitMatchings (τ : Equiv.Perm κ) (color leg : Bool) : Equiv.Perm κ :=
  if color then if leg then Equiv.refl κ else τ else Equiv.refl κ

omit [Fintype κ] in
private theorem pairedBond_subset_cells (σ : Bool → Equiv.Perm κ) (S : Finset κ)
    (k : κ) : ↑(pairedBond σ k) ⊆ {s : κ × Bool | s.1 ∈ S} ↔
      σ false k ∈ S ∧ σ true k ∈ S := by
  constructor
  · intro h
    exact ⟨h (Finset.mem_image.mpr ⟨false, Finset.mem_univ _, rfl⟩),
      h (Finset.mem_image.mpr ⟨true, Finset.mem_univ _, rfl⟩)⟩
  · rintro ⟨hf, ht⟩ s hs
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hs
    cases b
    · exact hf
    · exact ht

/-- The retained first layer consists exactly of the original gates whose
nominal two-site bonds lie in the chosen cells. Source context: gate deletion
in arXiv:2405.00439, Section V, lines 2081–2087. -/
theorem pairCircuitLayer_first_retained (τ : Equiv.Perm κ)
    (A : Bool → Matrix (Fin d) (Fin d) ℂ) (S : Finset κ)
    (p : κ × Bool) :
    p ∈ (pairCircuitLayer (dressedCircuitMatchings τ) false A S).cells ↔
      p ∈ (pairCircuitLayer (dressedCircuitMatchings τ) false A Finset.univ).cells ∧
        ↑(pairCircuitBond (dressedCircuitMatchings τ) p) ⊆ {s : κ × Bool | s.1 ∈ S} := by
  rcases p with ⟨k, b⟩
  cases b <;> simp [pairCircuitLayer, Layer.ofCells, pairCircuitBond, pairedBond_subset_cells,
    dressedCircuitMatchings, Finset.mem_image, Prod.mk.injEq]

/-- The retained shifted layer consists exactly of the original gates whose
nominal two-site bonds lie in the chosen cells. This uses the nominal bond even
when one factor of the gate is an identity. Source context: gate deletion in
arXiv:2405.00439, Section V, lines 2081–2087. -/
theorem pairCircuitLayer_second_retained (τ : Equiv.Perm κ)
    (A : Bool → Matrix (Fin d) (Fin d) ℂ) (S : Finset κ)
    (p : κ × Bool) :
    p ∈ (pairCircuitLayer (dressedCircuitMatchings τ) true A
      (S.filter fun k ↦ τ k ∈ S)).cells ↔
      p ∈ (pairCircuitLayer (dressedCircuitMatchings τ) true A Finset.univ).cells ∧
        ↑(pairCircuitBond (dressedCircuitMatchings τ) p) ⊆ {s : κ × Bool | s.1 ∈ S} := by
  rcases p with ⟨k, b⟩
  cases b <;> simp [pairCircuitLayer, Layer.ofCells, pairCircuitBond, pairedBond_subset_cells,
    dressedCircuitMatchings, and_comm, Finset.mem_image, Prod.mk.injEq]

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
    UnitaryCircuit (pairCircuitGeometry (dressedCircuitMatchings τ)) (fun _ ↦ Fin d) :=
  (UnitaryCircuit.ofLayer (pairCircuitLayer (dressedCircuitMatchings τ) false
      (firstPairFactors u w) S)
    (forall_isUnitary_pairCircuitLayer _ _ _ (firstPairFactors_unitary u w) S)).comp
  (UnitaryCircuit.ofLayer (pairCircuitLayer (dressedCircuitMatchings τ) true
      (secondPairFactors w) (S.filter fun k ↦ τ k ∈ S))
    (forall_isUnitary_pairCircuitLayer _ _ _ (secondPairFactors_unitary w) _))

omit [Fintype κ] in
/-- The retained circuit has two layers. Source context: arXiv:2405.00439,
Section V, lines 2081–2087. -/
@[simp] theorem dressedPairCircuit_length (τ : Equiv.Perm κ)
    (u w : unitary (Matrix (Fin d) (Fin d) ℂ)) (S : Finset κ) :
    (dressedPairCircuit τ u w S).layers.length = 2 := rfl

/-- The operator of the retained circuit: the shifted layer after the unshifted one. -/
private theorem op_dressedPairCircuit (τ : Equiv.Perm κ)
    (u w : unitary (Matrix (Fin d) (Fin d) ℂ)) (S : Finset κ) :
    (dressedPairCircuit τ u w S).op =
      (rectKronecker fun s ↦ if (dressedCircuitMatchings τ true s.2).symm s.1 ∈
        S.filter (fun k ↦ τ k ∈ S) then secondPairFactors w s.2 else 1) *
      rectKronecker fun s ↦ if (dressedCircuitMatchings τ false s.2).symm s.1 ∈ S then
        firstPairFactors u w s.2 else 1 := by
  obtain ⟨i₁⟩ := (Layer.nonempty_unique_index_of_forall_isUnitary
    (forall_isUnitary_pairCircuitLayer (dressedCircuitMatchings τ) false _
      (firstPairFactors_unitary u w) S)).map fun h ↦ h.default
  obtain ⟨i₂⟩ := (Layer.nonempty_unique_index_of_forall_isUnitary
    (forall_isUnitary_pairCircuitLayer (dressedCircuitMatchings τ) true _
      (secondPairFactors_unitary w) (S.filter fun k ↦ τ k ∈ S))).map fun h ↦ h.default
  rw [dressedPairCircuit, UnitaryCircuit.op_comp, UnitaryCircuit.op_ofLayer _ _ i₁,
    UnitaryCircuit.op_ofLayer _ _ i₂, pairCircuitLayer_kraus, pairCircuitLayer_kraus]

/-- On the full periodic chain the fixed circuit is precisely the on-site
symmetry. Source context: arXiv:2405.00439, Section V, lines 2081–2087;
the circuit is the explicit construction in the endpoint audit. -/
theorem op_dressedPairCircuit_univ (τ : Equiv.Perm κ)
    (u w : unitary (Matrix (Fin d) (Fin d) ℂ)) :
    (dressedPairCircuit τ u w Finset.univ).op =
      rectKronecker fun _ : κ × Bool ↦ (u : Matrix (Fin d) (Fin d) ℂ) := by
  rw [op_dressedPairCircuit, rectKronecker_mul]
  congr 1
  funext s
  rcases s with ⟨k, b⟩
  cases b <;> simp [dressedCircuitMatchings, firstPairFactors, secondPairFactors,
    ← Matrix.mul_assoc, Unitary.star_mul_self_of_mem w.property]

/-- Retaining a region with one entry boundary leaves the dressing exactly on
that boundary's even site. The boundary condition is a statement about cells
of the retained gates, not an assumed equality of circuit operators.
Source context: arXiv:2405.00439, Section V, lines 2081–2087. -/
theorem op_dressedPairCircuit_single_entry (τ : Equiv.Perm κ)
    (u w : unitary (Matrix (Fin d) (Fin d) ℂ)) (S : Finset κ) (a : κ)
    (ha : a ∈ S) (hentry : ∀ k ∈ S, τ.symm k ∈ S ↔ k ≠ a) :
    (dressedPairCircuit τ u w S).op =
      rectKronecker (fun s : κ × Bool ↦ if s = (a, false) then
        (w : Matrix (Fin d) (Fin d) ℂ) else 1) *
      rectKronecker (fun s : κ × Bool ↦ if s.1 ∈ S then
        (u : Matrix (Fin d) (Fin d) ℂ) else 1) := by
  rw [op_dressedPairCircuit, rectKronecker_mul, rectKronecker_mul]
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

/-- A nonwrapping interval with an exterior cell has exactly one entry
boundary for the fixed shifted matching. Either its left cut is positive
or its right cut leaves a cell before the periodic wraparound. Source
context: arXiv:2405.00439, Section V, lines 2081–2087. -/
theorem cellSuccessor_Icc_single_entry {M : ℕ} [NeZero M] (a b : Fin M)
    (hproper : 0 < a.val ∨ b.val + 1 < M) :
    ∀ k ∈ Finset.Icc a b, (cellSuccessor M).symm k ∈ Finset.Icc a b ↔ k ≠ a := by
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    have ha : a = 0 := by
      apply Fin.ext
      have hak : a.val ≤ (0 : Fin M).val := (Finset.mem_Icc.mp hk).1
      simp only [Fin.val_zero] at hak ⊢
      exact Nat.eq_zero_of_le_zero hak
    subst a
    have hb : b.val + 1 < M := by
      simpa only [Fin.val_zero, Nat.lt_irrefl, false_or] using hproper
    have hN : 1 < M := by omega
    have hval : (1 : Fin M).val = 1 := by
      rw [Fin.val_one', Nat.mod_eq_of_lt hN]
    have hne : (1 : Fin M) ≠ 0 := by
      intro h
      have h' := congrArg Fin.val h
      rw [hval, Fin.val_zero] at h'
      omega
    have hpred : ((0 : Fin M) - 1).val = M - 1 := by
      rw [zero_sub, Fin.val_neg, ite_eq_right hne, hval]
    change (0 : Fin M) - 1 ∈ Finset.Icc 0 b ↔ (0 : Fin M) ≠ 0
    constructor
    · intro h
      have hle : ((0 : Fin M) - 1).val ≤ b.val := (Finset.mem_Icc.mp h).2
      rw [hpred] at hle
      omega
    · intro h
      exact (h rfl).elim
  · change k - 1 ∈ Finset.Icc a b ↔ k ≠ a
    simp only [Finset.mem_Icc, Fin.le_def, Fin.val_sub_one_of_ne_zero hk0]
    have hka : a.val ≤ k.val := (Finset.mem_Icc.mp hk).1
    have hkb : k.val ≤ b.val := (Finset.mem_Icc.mp hk).2
    constructor
    · intro h heq
      subst k
      have hkval : a.val ≠ 0 := by
        intro hval
        apply hk0
        apply Fin.ext
        simpa only [Fin.val_zero] using hval
      omega
    · intro h
      have hval : k.val ≠ a.val := fun heq ↦ h (Fin.ext heq)
      omega

end MPOTensor.FiniteGroupDetector
