/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.PairProduct
import Mathlib.GroupTheory.Perm.Support

/-!
# Parallel SWAP routing on a matching of physical ports

A collection of pairwise disjoint neighboring bonds determines an involutive site
permutation. Its two endpoints are exchanged on every selected bond, and every other site
is fixed. The same permutation is implemented by one actual nearest-neighbor SWAP layer,
with no change to the dimension of each physical port.

The construction also covers the one-site ring: its self-loop swap is the identity.
This supplies the parallel communication step for fixed-dimensional physical ports in
Piroli, Styliaris and Cirac, arXiv:2103.13367, Supplement pp. 7–8.
-/

open Matrix

namespace QuantumCircuit

variable {d N : ℕ}

/-- Site permutations act multiplicatively on the full chain Hilbert space. -/
def permOpHom : Equiv.Perm (Fin N) →* Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ where
  toFun := permOp
  map_one' := by
    ext x y
    simp only [permOp, of_apply, Equiv.Perm.coe_one, Function.comp_id, one_apply, eq_comm]
  map_mul' σ τ := by
    ext x y
    simp only [permOp, of_apply, mul_apply, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' Finset.univ (x ∘ σ)]
    simp only [Finset.mem_univ, ite_true, Equiv.Perm.coe_mul]
    rfl

/-- The identity site permutation induces the identity chain operator. -/
@[simp] theorem permOp_one : permOp (d := d) (1 : Equiv.Perm (Fin N)) = 1 :=
  (permOpHom (d := d)).map_one

/-- Composition of site permutations is multiplication of their chain operators. -/
theorem permOp_mul (σ τ : Equiv.Perm (Fin N)) :
    permOp (d := d) (σ * τ) = permOp σ * permOp τ :=
  (permOpHom (d := d)).map_mul σ τ

/-- The adjoint chain permutation reverses the site permutation. -/
@[simp] theorem permOp_conjTranspose (π : Equiv.Perm (Fin N)) :
    (permOp (d := d) π)ᴴ = permOp π.symm := by
  ext x y
  simp only [permOp, of_apply, conjTranspose_apply, apply_ite star, star_one, star_zero]
  congr 1
  apply propext
  constructor
  · intro h
    funext i
    have := congrFun h (π.symm i)
    simpa using this.symm
  · intro h
    funext i
    have := congrFun h (π i)
    simpa using this.symm

namespace PortMatching

variable [NeZero N]

private theorem swap_apply_of_notMem_bond {i x : Fin N} (hx : x ∉ bond i) :
    Equiv.swap i (i + 1) x = x := by
  have hx' : x ≠ i ∧ x ≠ i + 1 := by simpa only [bond, Set.mem_insert_iff,
    Set.mem_singleton_iff, not_or] using hx
  exact Equiv.swap_apply_of_ne_of_ne hx'.1 hx'.2

private theorem swap_disjoint_of_disjoint_bond {i j : Fin N}
    (h : Disjoint (bond i) (bond j)) :
    Equiv.Perm.Disjoint (Equiv.swap i (i + 1)) (Equiv.swap j (j + 1)) := by
  intro x
  by_cases hx : x ∈ bond i
  · exact Or.inr (swap_apply_of_notMem_bond fun hj => Set.disjoint_left.mp h hx hj)
  · exact Or.inl (swap_apply_of_notMem_bond hx)

private theorem swap_commute (K : Finset (Fin N))
    (hK : (K : Set (Fin N)).PairwiseDisjoint bond) :
    (K : Set (Fin N)).Pairwise
      (Function.onFun Commute (fun i => Equiv.swap i (i + 1))) :=
  fun _ hi _ hj hij => (swap_disjoint_of_disjoint_bond (hK hi hj hij)).commute

/-- Simultaneously exchange the endpoints of all bonds in a matching. -/
noncomputable def perm (K : Finset (Fin N))
    (hK : (K : Set (Fin N)).PairwiseDisjoint bond) : Equiv.Perm (Fin N) :=
  K.noncommProd (fun i => Equiv.swap i (i + 1)) (swap_commute K hK)

/-- A site outside every selected bond is fixed. -/
theorem perm_apply_of_notMem (K : Finset (Fin N))
    (hK : (K : Set (Fin N)).PairwiseDisjoint bond) {x : Fin N}
    (hx : ∀ i ∈ K, x ∉ bond i) : perm K hK x = x := by
  apply Finset.noncommProd_induction K (fun i => Equiv.swap i (i + 1))
    (swap_commute K hK) (fun σ => σ x = x)
  · intro σ τ hσ hτ
    simp only [Equiv.Perm.mul_apply, hτ, hσ]
  · rfl
  · intro i hi
    exact swap_apply_of_notMem_bond (hx i hi)

/-- On one selected bond, the parallel permutation is exactly that bond's swap. -/
theorem perm_apply_of_mem (K : Finset (Fin N))
    (hK : (K : Set (Fin N)).PairwiseDisjoint bond) {i x : Fin N}
    (hi : i ∈ K) (hx : x ∈ bond i) : perm K hK x = Equiv.swap i (i + 1) x := by
  have hE : (↑(K.erase i) : Set (Fin N)).PairwiseDisjoint bond :=
    fun _ hj _ hk hjk => hK (Finset.mem_of_mem_erase hj) (Finset.mem_of_mem_erase hk) hjk
  have hfix : perm (K.erase i) hE x = x := by
    apply perm_apply_of_notMem
    intro j hj
    exact fun hxj => Set.disjoint_left.mp
      (hK hi (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj).symm) hx hxj
  have hprod : perm K hK = Equiv.swap i (i + 1) * perm (K.erase i) hE :=
    (Finset.mul_noncommProd_erase K hi (fun j => Equiv.swap j (j + 1))
      (swap_commute K hK)).symm
  rw [hprod, Equiv.Perm.mul_apply, hfix]

/-- The left endpoint moves to the right endpoint. -/
@[simp] theorem perm_apply_left (K : Finset (Fin N))
    (hK : (K : Set (Fin N)).PairwiseDisjoint bond) {i : Fin N} (hi : i ∈ K) :
    perm K hK i = i + 1 := by
  rw [perm_apply_of_mem K hK hi (by simp [bond]), Equiv.swap_apply_left]

/-- The right endpoint moves to the left endpoint. -/
@[simp] theorem perm_apply_right (K : Finset (Fin N))
    (hK : (K : Set (Fin N)).PairwiseDisjoint bond) {i : Fin N} (hi : i ∈ K) :
    perm K hK (i + 1) = i := by
  rw [perm_apply_of_mem K hK hi (by simp [bond]), Equiv.swap_apply_right]

/-- Parallel swaps on a matching are involutive. -/
theorem perm_involutive (K : Finset (Fin N))
    (hK : (K : Set (Fin N)).PairwiseDisjoint bond) : Function.Involutive (perm K hK) := by
  intro x
  by_cases hx : ∃ i ∈ K, x ∈ bond i
  · obtain ⟨i, hi, hx⟩ := hx
    rcases hx with rfl | rfl
    · rw [perm_apply_left K hK hi, perm_apply_right K hK hi]
    · rw [perm_apply_right K hK hi, perm_apply_left K hK hi]
  · have hfix : perm K hK x = x :=
      perm_apply_of_notMem K hK fun i hi hxi => hx ⟨i, hi, hxi⟩
    rw [hfix, hfix]

/-- Reversing the matching permutation gives the same permutation. -/
@[simp] theorem perm_symm (K : Finset (Fin N))
    (hK : (K : Set (Fin N)).PairwiseDisjoint bond) : (perm K hK).symm = perm K hK := by
  apply Equiv.ext
  intro x
  apply (perm K hK).injective
  rw [Equiv.apply_symm_apply, perm_involutive K hK x]

private theorem swap_mem_supportedOperators (i : Fin N) :
    permOp (d := d) (Equiv.swap i (i + 1)) ∈ supportedOperators d (bond i) := by
  by_cases hi : i = i + 1
  · rw [← hi, Equiv.swap_self]
    change permOpHom (1 : Equiv.Perm (Fin N)) ∈ supportedOperators d (bond i)
    rw [map_one]
    exact one_mem_supportedOperators _
  · rw [permOp_swap_eq_embedOp hi]
    simpa only [range_pairSites, bond] using
      embedOp_mem_supportedOperators (pairSites_injective hi) (swapTwo (d := d))

/-- One physical layer, containing a SWAP on every selected neighboring bond. -/
def layer (d : ℕ) (K : Finset (Fin N))
    (hK : (K : Set (Fin N)).PairwiseDisjoint bond) : Layer d N where
  bonds := K
  gate i := permOp (Equiv.swap i (i + 1))
  gate_mem_unitary _i _ := permOp_mem_unitary _
  gate_mem_supportedOperators i _ := swap_mem_supportedOperators i
  pairwiseDisjoint := hK

/-- The concrete SWAP layer implements the simultaneous site permutation exactly. -/
theorem layer_op (K : Finset (Fin N))
    (hK : (K : Set (Fin N)).PairwiseDisjoint bond) :
    (layer d K hK).op = permOp (perm K hK) := by
  exact (Finset.map_noncommProd K (fun i => Equiv.swap i (i + 1))
    (swap_commute K hK) (permOpHom (d := d))).symm

/-- The one-site ring has no communication: even its selected self-loop acts identically. -/
@[simp] theorem layer_op_one_site (K : Finset (Fin 1))
    (hK : (K : Set (Fin 1)).PairwiseDisjoint bond) : (layer d K hK).op = 1 := by
  rw [layer_op]
  have hperm : perm K hK = 1 := Subsingleton.elim _ _
  rw [hperm]
  exact (permOpHom (d := d)).map_one

end PortMatching

end QuantumCircuit
