/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Channel.PhysicalPort
import Mathlib.GroupTheory.Perm.ViaEmbedding
import TNLean.Circuit.Channel.PortMatching
import Mathlib.Data.List.OfFn

/-!
# Routing a physical-port layer to selected memory qudits

Select one memory wire at each spatial site. Swap each selected wire with its physical
port, apply a physical layer, and undo the onsite swaps. The result acts exactly on the
selected memory wires and identically on every other wire. Its physical depth is one.
This is an operator identity, so no initialization or independence assumption on any
unused wire is needed.

Source: the fixed physical-qudit/onsite-ancilla gate convention in
Piroli, Styliaris and Cirac, arXiv:2103.13367, Supplement pp. 7–8.
-/

open Matrix

namespace QuantumCircuit

namespace PhysicalPortLayout

variable {N W : ℕ} (P : PhysicalPortLayout N W)

private def selectWire (e : Fin N ↪ Fin W) (x : Fin W) : Fin W :=
  Equiv.swap (P.port (P.site x)) (e (P.site x)) x

private theorem site_selectWire (e : Fin N ↪ Fin W) (he : ∀ i, P.site (e i) = i)
    (x : Fin W) : P.site (P.selectWire e x) = P.site x := by
  rw [selectWire, Equiv.swap_apply_def]
  split_ifs <;> simp only [he, P.site_port]

private theorem selectWire_involutive (e : Fin N ↪ Fin W)
    (he : ∀ i, P.site (e i) = i) : Function.Involutive (P.selectWire e) := by
  intro x
  change Equiv.swap (P.port (P.site (P.selectWire e x)))
    (e (P.site (P.selectWire e x))) (P.selectWire e x) = x
  rw [site_selectWire P e he]
  simp [selectWire]

/-- Swap the port with a chosen wire separately at each site. -/
def selectionPermutation (e : Fin N ↪ Fin W) (he : ∀ i, P.site (e i) = i) :
    Equiv.Perm (Fin W) :=
  (P.selectWire_involutive e he).toPerm (P.selectWire e)

/-- Port selection moves no wire between spatial sites. -/
theorem selectionPermutation_site (e : Fin N ↪ Fin W) (he : ∀ i, P.site (e i) = i)
    (x : Fin W) : P.site (P.selectionPermutation e he x) = P.site x :=
  P.site_selectWire e he x

/-- Each physical port is exchanged with its selected memory wire. -/
theorem selectionPermutation_port (e : Fin N ↪ Fin W) (he : ∀ i, P.site (e i) = i)
    (i : Fin N) : P.selectionPermutation e he (P.port i) = e i := by
  simp [selectionPermutation, selectWire, P.site_port]

/-- The inverse selection is the same onsite swap. -/
theorem selectionPermutation_symm (e : Fin N ↪ Fin W) (he : ∀ i, P.site (e i) = i) :
    (P.selectionPermutation e he).symm = P.selectionPermutation e he := rfl

end PhysicalPortLayout

variable {d N W : ℕ} [NeZero N]

/-- Any physical layer can instead act on one selected memory qudit per site, at the same
physical depth, while restoring every unselected wire exactly. -/
theorem IsPhysicalPortUnitary.selected_layer (P : PhysicalPortLayout N W)
    (e : Fin N ↪ Fin W) (he : ∀ i, P.site (e i) = i) (L : Layer d N) :
    IsPhysicalPortUnitary P 1 (embedOp e L.op) := by
  let π := P.selectionPermutation e he
  have hπ : IsPhysicalPortUnitary (d := d) P 0 (permOp π) :=
    .onsitePermutation π (P.selectionPermutation_site e he)
  have h := (hπ.mul (IsPhysicalPortUnitary.layer (P := P) L)).mul hπ.conjTranspose
  have hplace : (π : Fin W → Fin W) ∘ P.port = e := by
    funext i
    exact P.selectionPermutation_port e he i
  simpa only [Nat.zero_add, Nat.add_zero, permOp_mul_mul_conjTranspose,
    embedOp_submatrix_perm, hplace] using h

/-- Lifting a wire permutation through an embedding permutes just the selected wires. -/
theorem embedOp_permOp_viaEmbedding {m n : ℕ} (e : Fin m ↪ Fin n)
    (σ : Equiv.Perm (Fin m)) :
    embedOp e (permOp (d := d) σ) = permOp (σ.viaEmbedding e) := by
  classical
  ext x y
  rw [embedOp_apply]
  simp only [permOp, of_apply]
  have hiff : y = x ∘ σ.viaEmbedding e ↔
      AgreeOff e x y ∧ y ∘ e = (x ∘ e) ∘ σ := by
    constructor
    · rintro rfl
      constructor
      · intro i hi
        rw [Function.comp_apply, Equiv.Perm.viaEmbedding_apply_of_notMem]
        rintro ⟨j, hj⟩
        exact hi j hj
      · funext j
        simp only [Function.comp_apply, Equiv.Perm.viaEmbedding_apply]
    · rintro ⟨hoff, hon⟩
      funext i
      by_cases hi : i ∈ Set.range e
      · obtain ⟨j, rfl⟩ := hi
        simpa only [Function.comp_apply, Equiv.Perm.viaEmbedding_apply] using congrFun hon j
      · rw [Function.comp_apply, Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hi]
        exact (hoff i (fun j hj => hi ⟨j, hj⟩)).symm
  by_cases h : y = x ∘ σ.viaEmbedding e
  · obtain ⟨hoff, hon⟩ := hiff.mp h
    rw [ite_eq_left hoff, ite_eq_left hon, ite_eq_left h]
  · rw [ite_eq_right h]
    split_ifs with hoff hon
    · exact absurd (hiff.mpr ⟨hoff, hon⟩) h
    · rfl
    · rfl

/-- A permutation layer on physical ports has an exact one-layer realization on any
selected memory wires; all unselected ports and memory remain untouched. -/
theorem IsPhysicalPortUnitary.selected_permutation_layer (P : PhysicalPortLayout N W)
    (e : Fin N ↪ Fin W) (he : ∀ i, P.site (e i) = i) (L : Layer d N)
    (σ : Equiv.Perm (Fin N)) (hL : L.op = permOp σ) :
    IsPhysicalPortUnitary (d := d) P 1 (permOp (σ.viaEmbedding e)) := by
  have h := IsPhysicalPortUnitary.selected_layer P e he L
  rwa [hL, embedOp_permOp_viaEmbedding] at h

end QuantumCircuit

/-!
## Parallel register communication through fixed-dimensional ports

A register with `k` qudit digits at each spatial site is routed by selecting one digit at
a time. Each digit uses one physical-port layer, independently of the number of disjoint
neighboring bonds. The resulting wire permutation applies the prescribed site permutation
separately to each digit and fixes every wire outside the selected registers.

For a matching of neighboring bonds this gives an exact register swap in `k` physical
layers. All unselected ports and memories are restored for arbitrary joint input states.
This is the bounded-register communication step for Piroli, Styliaris and Cirac,
arXiv:2103.13367, Supplement pp. 7–8.
-/

namespace QuantumCircuit

variable {d k N W : ℕ}

/-- Apply a site permutation successively to each selected register digit. -/
noncomputable def registerPermutation (e : Fin k → (Fin N ↪ Fin W))
    (σ : Equiv.Perm (Fin N)) : Equiv.Perm (Fin W) :=
  (List.ofFn fun t => σ.viaEmbedding (e t)).prod

private theorem registerPermutation_apply_of_fixed (e : Fin k → (Fin N ↪ Fin W))
    (σ : Equiv.Perm (Fin N)) (x : Fin W)
    (hx : ∀ t, σ.viaEmbedding (e t) x = x) : registerPermutation e σ x = x := by
  apply List.prod_induction (fun τ : Equiv.Perm (Fin W) => τ x = x)
  · intro τ υ hτ hυ
    simp only [Equiv.Perm.mul_apply, hυ, hτ]
  · rfl
  · intro τ hτ
    obtain ⟨t, rfl⟩ := List.mem_ofFn.mp hτ
    exact hx t

private theorem registerPermutation_pairwise (e : Fin k → (Fin N ↪ Fin W))
    (σ : Equiv.Perm (Fin N))
    (he : Pairwise fun t u => Disjoint (Set.range (e t)) (Set.range (e u))) :
    (List.ofFn fun t => σ.viaEmbedding (e t)).Pairwise Equiv.Perm.Disjoint := by
  rw [List.pairwise_ofFn]
  intro t u htu x
  by_cases hx : x ∈ Set.range (e t)
  · right
    exact Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _
      (fun hu => Set.disjoint_left.mp (he (ne_of_lt htu)) hx hu)
  · left
    exact Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hx

/-- Distinct register digits follow the same site permutation without affecting each other. -/
theorem registerPermutation_apply (e : Fin k → (Fin N ↪ Fin W))
    (σ : Equiv.Perm (Fin N))
    (he : Pairwise fun t u => Disjoint (Set.range (e t)) (Set.range (e u)))
    (t : Fin k) (i : Fin N) : registerPermutation e σ (e t i) = e t (σ i) := by
  by_cases hi : σ i = i
  · rw [hi]
    apply registerPermutation_apply_of_fixed
    intro u
    by_cases hut : u = t
    · subst u
      rw [Equiv.Perm.viaEmbedding_apply, hi]
    · exact Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _
        (fun hu => Set.disjoint_left.mp (he (Ne.symm hut)) ⟨i, rfl⟩ hu)
  · have hmove : e t i ∈ (σ.viaEmbedding (e t)).support := by
      rw [Equiv.Perm.mem_support, Equiv.Perm.viaEmbedding_apply]
      exact (e t).injective.ne hi
    have hmem : σ.viaEmbedding (e t) ∈ (List.ofFn fun u => σ.viaEmbedding (e u)) :=
      List.mem_ofFn.mpr ⟨t, rfl⟩
    exact (Equiv.Perm.eq_on_support_mem_disjoint hmem
      (registerPermutation_pairwise e σ he) _ hmove).symm.trans
        (Equiv.Perm.viaEmbedding_apply _ _ _)

/-- Every wire outside all selected register digits is fixed. -/
theorem registerPermutation_apply_of_notMem (e : Fin k → (Fin N ↪ Fin W))
    (σ : Equiv.Perm (Fin N)) (x : Fin W) (hx : ∀ t, x ∉ Set.range (e t)) :
    registerPermutation e σ x = x :=
  registerPermutation_apply_of_fixed e σ x fun t =>
    Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ (hx t)

/-- An involutive site permutation gives an involutive permutation of disjoint registers. -/
theorem registerPermutation_involutive (e : Fin k → (Fin N ↪ Fin W))
    (σ : Equiv.Perm (Fin N))
    (he : Pairwise fun t u => Disjoint (Set.range (e t)) (Set.range (e u)))
    (hσ : Function.Involutive σ) : Function.Involutive (registerPermutation e σ) := by
  intro x
  by_cases hx : ∃ t i, e t i = x
  · obtain ⟨t, i, rfl⟩ := hx
    rw [registerPermutation_apply e σ he, registerPermutation_apply e σ he, hσ i]
  · have hfix : registerPermutation e σ x = x :=
      registerPermutation_apply_of_notMem e σ x fun t ⟨i, hi⟩ => hx ⟨t, i, hi⟩
    rw [hfix, hfix]

namespace IsPhysicalPortUnitary

variable [NeZero N]

private theorem permOp_prod (P : PhysicalPortLayout N W) (l : List (Equiv.Perm (Fin W)))
    (hl : ∀ σ ∈ l, IsPhysicalPortUnitary (d := d) P 1 (permOp σ)) :
    IsPhysicalPortUnitary (d := d) P l.length (permOp l.prod) := by
  induction l with
  | nil => simpa only [List.length_nil, List.prod_nil, permOp_one] using one (d := d) P
  | cons σ l ih =>
    have htail := ih fun τ hτ => hl τ (List.mem_cons_of_mem σ hτ)
    simpa only [List.length_cons, List.prod_cons, permOp_mul, Nat.add_comm] using
      (hl σ List.mem_cons_self).mul htail

/-- Swapping all `k` digits along a matching has physical depth at most `k`,
independently of the number of selected neighboring bonds. -/
theorem register_matching (P : PhysicalPortLayout N W) (e : Fin k → (Fin N ↪ Fin W))
    (he : ∀ t i, P.site (e t i) = i) (K : Finset (Fin N))
    (hK : (K : Set (Fin N)).PairwiseDisjoint ringBond) :
    IsPhysicalPortUnitary (d := d) P k
      (permOp (registerPermutation e (PortMatching.perm K hK))) := by
  have h := permOp_prod (d := d) P
    (List.ofFn fun t => (PortMatching.perm K hK).viaEmbedding (e t)) (by
      intro σ hσ
      obtain ⟨t, rfl⟩ := List.mem_ofFn.mp hσ
      exact selected_permutation_layer P (e t) (he t) (PortMatching.layer d K hK)
        (PortMatching.perm K hK) (PortMatching.layer_op K hK))
  simpa only [registerPermutation, List.length_ofFn] using h

end IsPhysicalPortUnitary

end QuantumCircuit
