/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Teleportation.Round

/-!
# Teleportation chains between distant sites

The tree-RG circuit of arXiv:2307.01696, eq. (16), applies isometries to registers that are far
apart on the chain. The paragraph "Tree-RG circuit with measurements" observes that these
registers "can be teleported at neighboring registers with a constant overhead". This file
provides the chains of hops that do so, in the measurement-round model
(`QuantumCircuit.MeasurementRound`):

* for any valid lists of hops `there` and `back` and any layer of gates `G`, the round
  teleporting along `there`, followed by the round applying `G` and teleporting along `back`,
  acts on every outcome as `P_back G P_there` up to a scalar
  (`QuantumCircuit.TeleportHop.exists_eq_smul_of_mem_outputs_conj`); the two rounds have depth
  `2` and `3`, whatever the distances;
* the forward chain of `L` hops from `a` to `a + 2L` and the backward chain from `a + 2L` to
  `a`, whose permutations of sites are inverse to each other
  (`QuantumCircuit.TeleportHop.sitePerm_backwardChain`), and which leave `|0⟩` at the sites
  `a, …, a + 2L - 1` when the sites `a + 1, …, a + 2L` carry `|0⟩`
  (`QuantumCircuit.TeleportHop.isZeroOn_chainPerm_forwardChain`).

The gates between distant sites built from these chains are in
`TNLean.Circuit.Teleportation.LongRangeGates`.

## Main definitions

* `QuantumCircuit.TeleportHop.chainHop`, `QuantumCircuit.TeleportHop.chainHopBack`,
  `QuantumCircuit.TeleportHop.forwardChain`, `QuantumCircuit.TeleportHop.backwardChain`.

## Main results

* `QuantumCircuit.TeleportHop.exists_eq_smul_of_mem_outputs_conj`.
* `QuantumCircuit.TeleportHop.sitePerm_forwardChain`,
  `QuantumCircuit.TeleportHop.sitePerm_backwardChain`,
  `QuantumCircuit.TeleportHop.isZeroOn_chainPerm_forwardChain`.

## References

* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), eq. (16) and paragraph "Tree-RG circuit with
  measurements".
-/

open Matrix
open scoped BigOperators

namespace QuantumCircuit

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Permutations of sites -/

variable [NeZero d]

/-- Permuting the sites moves the sites carrying `|0⟩`. -/
theorem IsZeroOn.permMatrix_cfgPerm_mulVec_image {S : Finset ι} {v : (ι → Fin d) → ℂ}
    (h : IsZeroOn S v) (π : Equiv.Perm ι) :
    IsZeroOn (S.image π) ((cfgPerm π).permMatrix ℂ *ᵥ v) := by
  intro y hy j hj
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
  rw [permMatrix_mulVec] at hy
  exact h _ hy i hi

/-- An operator acting on sites outside `S` keeps `|0⟩` at the sites of `S`. -/
theorem IsZeroOn.mulVec_of_mem_supportedOperators {S : Finset ι} {v : (ι → Fin d) → ℂ}
    (h : IsZeroOn S v) {T : Finset ι} (hST : Disjoint S T)
    {A : Matrix (ι → Fin d) (ι → Fin d) ℂ}
    (hA : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) T) :
    IsZeroOn S (A *ᵥ v) := by
  have hP : ∀ u : (ι → Fin d) → ℂ, IsZeroOn S u ↔ ctrlProj S 0 *ᵥ u = u := by
    intro u
    constructor
    · intro hu
      funext x
      rw [ctrlProj, mulVec_diagonal]
      by_cases hx : ∀ i ∈ S, x i = (0 : ι → Fin d) i
      · rw [ite_eq_left hx, one_mul]
      · rw [ite_eq_right hx, zero_mul]
        by_contra h0
        exact hx fun i hi => hu x (Ne.symm h0) i hi
    · intro hu x hx i hi
      rw [← hu, ctrlProj, mulVec_diagonal] at hx
      by_contra hne
      exact hx (by rw [ite_eq_right fun h' => hne (h' i hi), zero_mul])
  have hc : Commute (ctrlProj S (0 : ι → Fin d)) A :=
    ManyBody.commute_of_mem_supportedOperators_of_disjoint
        (ctrlProj_mem_supportedOperators S 0) hA hST
  rw [hP] at h ⊢
  rw [mulVec_mulVec, hc.eq, ← mulVec_mulVec, h]

variable {N : ℕ} [NeZero N]

/-! ### The sites `a + j` -/

section Offsets

open Fin.NatCast

theorem add_natCast_injective (a : Fin N) {j k : ℕ} (hj : j < N) (hk : k < N)
    (h : a + (j : Fin N) = a + (k : Fin N)) : j = k := by
  have := congrArg Fin.val (add_left_cancel h)
  rwa [Fin.val_cast_of_lt hj, Fin.val_cast_of_lt hk] at this

theorem add_natCast_succ (a : Fin N) (j : ℕ) :
    a + (j : Fin N) + 1 = a + ((j + 1 : ℕ) : Fin N) := by
  rw [add_assoc, Nat.cast_succ]

/-- The sites `a + j` and `a + k` differ when `j ≠ k`, both offsets below `N`. -/
theorem add_natCast_ne (a : Fin N) {j k : ℕ} (hj : j < N) (hk : k < N) (hjk : j ≠ k) :
    a + (j : Fin N) ≠ a + (k : Fin N) := fun h => hjk (add_natCast_injective a hj hk h)

end Offsets

namespace TeleportHop

/-! ### Two rounds around a layer of gates -/

/-- **Gates conjugated by teleportation.** Let `there` and `back` be valid lists of hops and `G`
a layer of gates, and let `v` carry `|0⟩` at the sites `e`, `f` of `there`, with `G P_there v`
carrying `|0⟩` at the sites `e`, `f` of `back`. Then every output of the round teleporting along
`there`, followed by the round applying `G` and teleporting along `back`, is a scalar multiple of
`P_back G P_there v`. The rounds have depth `2` and `3`.

Source: arXiv:2307.01696, paragraph "Tree-RG circuit with measurements". -/
theorem exists_eq_smul_of_mem_outputs_conj {there back : List (TeleportHop N)}
    (hthere : Valid there) (hback : Valid back) (G : RingLayer d N) {v : (Fin N → Fin d) → ℂ}
    (hv : IsZeroOn (pairSites there) v)
    (hGv : IsZeroOn (pairSites back) (G.op *ᵥ (chainPerm there *ᵥ v)))
    {w : (Fin N → Fin d) → ℂ}
    (hw : w ∈ MeasurementRound.outputs [round [] there hthere, round [G] back hback] v) :
    ∃ c : ℂ, w = c • ((chainPerm back * G.op * chainPerm there) *ᵥ v) := by
  have h₁ := isImplementationOn_round (d := d) [] hthere
  have h₂ := isImplementationOn_round [G] hback
  obtain ⟨c, u, hu, rfl⟩ := h₁.exists_mem_outputs (by simpa [circuitOp] using hv) hw
  have hGv' : (chainPerm there * circuitOp ([] : List (RingLayer d N))) *ᵥ v ∈
      {v | IsZeroOn (pairSites back) (circuitOp [G] *ᵥ v)} := by
    simpa [circuitOp] using hGv
  obtain ⟨c', u', hu', rfl⟩ := h₂.exists_mem_outputs hGv' hu
  rw [MeasurementRound.outputs_nil, Set.mem_singleton_iff] at hu'
  subst hu'
  refine ⟨c * c', ?_⟩
  simp [circuitOp, smul_smul, mulVec_mulVec, Matrix.mul_assoc]

/-! ### The chains between two distant sites -/

section Chains

open Fin.NatCast

/-- The forward hop from `a + j` to `a + j + 2`. -/
def chainHop (a : Fin N) (j : ℕ) (hj : j + 2 < N) : TeleportHop N where
  c := a + (j : Fin N)
  e := a + ((j + 1 : ℕ) : Fin N)
  f := a + ((j + 2 : ℕ) : Fin N)
  k₁ := a + ((j + 1 : ℕ) : Fin N)
  k₂ := a + (j : Fin N)
  bond_k₁ := by rw [ringBond, add_natCast_succ]
  bond_k₂ := by rw [ringBond, add_natCast_succ]
  c_ne_e h := by have := add_natCast_injective a (by omega) (by omega) h; omega
  c_ne_f h := by have := add_natCast_injective a (by omega) (by omega) h; omega
  e_ne_f h := by have := add_natCast_injective a (by omega) (by omega) h; omega

/-- The backward hop from `a + j + 2` to `a + j`. -/
def chainHopBack (a : Fin N) (j : ℕ) (hj : j + 2 < N) : TeleportHop N where
  c := a + ((j + 2 : ℕ) : Fin N)
  e := a + ((j + 1 : ℕ) : Fin N)
  f := a + (j : Fin N)
  k₁ := a + (j : Fin N)
  k₂ := a + ((j + 1 : ℕ) : Fin N)
  bond_k₁ := by rw [ringBond, add_natCast_succ, Finset.pair_comm]
  bond_k₂ := by rw [ringBond, add_natCast_succ, Finset.pair_comm]
  c_ne_e h := by have := add_natCast_injective a (by omega) (by omega) h; omega
  c_ne_f h := by have := add_natCast_injective a (by omega) (by omega) h; omega
  e_ne_f h := by have := add_natCast_injective a (by omega) (by omega) h; omega

/-- The forward chain of `L` hops from `a` to `a + 2L`, the most recent hop first. -/
def forwardChain (a : Fin N) : (L : ℕ) → 2 * L < N → List (TeleportHop N)
  | 0, _ => []
  | L + 1, hL => chainHop a (2 * L) (by omega) :: forwardChain a L (by omega)

/-- The backward chain of `L` hops from `a + 2L` to `a`, the most recent hop first. -/
def backwardChain (a : Fin N) : (L : ℕ) → 2 * L < N → List (TeleportHop N)
  | 0, _ => []
  | L + 1, hL => backwardChain a L (by omega) ++ [chainHopBack a (2 * L) (by omega)]

/-- The relation between a hop `h` and an earlier hop `h'` in a valid list. -/
def After (h h' : TeleportHop N) : Prop :=
  h.e ∉ h'.sites ∧ h.f ∉ h'.sites ∧ h.c ≠ h'.c ∧ h.c ≠ h'.e

theorem valid_iff_pairwise {hs : List (TeleportHop N)} : Valid hs ↔ hs.Pairwise After := by
  induction hs with
  | nil => simp [Valid]
  | cons h hs ih =>
    rw [List.pairwise_cons, ← ih]
    constructor
    · rintro ⟨hv, he, hf, hc⟩
      exact ⟨fun h' hh' => ⟨fun hi => he (mem_allSites.mpr ⟨h', hh', hi⟩),
        fun hi => hf (mem_allSites.mpr ⟨h', hh', hi⟩), (hc h' hh').1, (hc h' hh').2⟩, hv⟩
    · rintro ⟨hR, hv⟩
      refine ⟨hv, fun hi => ?_, fun hi => ?_, fun h' hh' => ⟨(hR h' hh').2.2.1, (hR h' hh').2.2.2⟩⟩
      · obtain ⟨h', hh', hi⟩ := mem_allSites.mp hi; exact (hR h' hh').1 hi
      · obtain ⟨h', hh', hi⟩ := mem_allSites.mp hi; exact (hR h' hh').2.1 hi

theorem sitePerm_append (hs hs' : List (TeleportHop N)) :
    sitePerm (hs ++ hs') = sitePerm hs * sitePerm hs' := by
  induction hs with
  | nil => simp [sitePerm]
  | cons h hs ih => rw [List.cons_append, sitePerm, sitePerm, ih, mul_assoc]

theorem pairSites_append (hs hs' : List (TeleportHop N)) :
    pairSites (hs ++ hs') = pairSites hs ∪ pairSites hs' := by
  induction hs with
  | nil => simp [pairSites]
  | cons h hs ih => rw [List.cons_append, pairSites, pairSites, ih, Finset.union_assoc]

theorem mem_forwardChain {a : Fin N} {L : ℕ} {hL : 2 * L < N} {h : TeleportHop N}
    (hh : h ∈ forwardChain a L hL) : ∃ i < L, ∃ hi, h = chainHop a (2 * i) hi := by
  induction L with
  | zero => simp [forwardChain] at hh
  | succ L ih =>
    rcases List.mem_cons.mp hh with rfl | hh
    · exact ⟨L, by omega, _, rfl⟩
    · obtain ⟨i, hi, hi', rfl⟩ := ih hh
      exact ⟨i, by omega, hi', rfl⟩

theorem mem_backwardChain {a : Fin N} {L : ℕ} {hL : 2 * L < N} {h : TeleportHop N}
    (hh : h ∈ backwardChain a L hL) : ∃ i < L, ∃ hi, h = chainHopBack a (2 * i) hi := by
  induction L with
  | zero => simp [backwardChain] at hh
  | succ L ih =>
    rcases List.mem_append.mp hh with hh | hh
    · obtain ⟨i, hi, hi', rfl⟩ := ih hh
      exact ⟨i, by omega, hi', rfl⟩
    · rw [List.mem_singleton] at hh
      exact ⟨L, by omega, _, hh⟩

theorem valid_forwardChain (a : Fin N) (L : ℕ) (hL : 2 * L < N) :
    Valid (forwardChain a L hL) := by
  rw [valid_iff_pairwise]
  induction L with
  | zero => exact List.Pairwise.nil
  | succ L ih =>
    refine List.Pairwise.cons (fun h' hh' => ?_) (ih (by omega))
    obtain ⟨i, hi, hi', rfl⟩ := mem_forwardChain hh'
    simp only [After, sites, chainHop, Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;>
      exact add_natCast_ne a (by omega) (by omega) (by omega)

theorem valid_backwardChain (a : Fin N) (L : ℕ) (hL : 2 * L < N) :
    Valid (backwardChain a L hL) := by
  rw [valid_iff_pairwise]
  induction L with
  | zero => exact List.Pairwise.nil
  | succ L ih =>
    refine List.pairwise_append.mpr ⟨ih (by omega), List.pairwise_singleton _ _,
      fun h' hh' h'' hh'' => ?_⟩
    obtain ⟨i, hi, hi', rfl⟩ := mem_backwardChain hh'
    rw [List.mem_singleton] at hh''
    subst hh''
    simp only [After, sites, chainHopBack, Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;>
      exact add_natCast_ne a (by omega) (by omega) (by omega)

/-- The forward chain moves `a` to `a + 2L` and fixes the sites `a + j` with `2L < j`. -/
theorem sitePerm_forwardChain (a : Fin N) (L : ℕ) (hL : 2 * L < N) :
    sitePerm (forwardChain a L hL) a = a + ((2 * L : ℕ) : Fin N) ∧
      ∀ j, 2 * L < j → j < N → sitePerm (forwardChain a L hL) (a + (j : Fin N)) =
        a + (j : Fin N) := by
  induction L with
  | zero => simp [forwardChain, sitePerm]
  | succ L ih =>
    obtain ⟨h1, h2⟩ := ih (by omega)
    simp only [forwardChain, sitePerm, chainHop, Equiv.Perm.mul_apply]
    refine ⟨?_, fun j hj hjN => ?_⟩
    · rw [h1, Equiv.swap_apply_left]
      congr 2
    · rw [h2 j (by omega) hjN, Equiv.swap_apply_of_ne_of_ne
        (add_natCast_ne a hjN (by omega) (by omega)) (add_natCast_ne a hjN (by omega) (by omega))]

theorem sitePerm_backwardChain (a : Fin N) (L : ℕ) (hL : 2 * L < N) :
    sitePerm (backwardChain a L hL) = (sitePerm (forwardChain a L hL))⁻¹ := by
  induction L with
  | zero => simp [forwardChain, backwardChain, sitePerm]
  | succ L ih =>
    rw [backwardChain, sitePerm_append, ih (by omega), forwardChain]
    simp only [sitePerm, mul_one, _root_.mul_inv_rev, Equiv.swap_inv]
    congr 1
    exact Equiv.swap_comm _ _

/-- The sites `e` and `f` of the forward chain are the sites `a + j`, `1 ≤ j ≤ 2L`. -/
theorem pairSites_forwardChain_subset (a : Fin N) (L : ℕ) (hL : 2 * L < N) :
    pairSites (forwardChain a L hL) ⊆
      (Finset.Icc 1 (2 * L)).image fun j : ℕ => a + (j : Fin N) := by
  induction L with
  | zero => simp [forwardChain, pairSites]
  | succ L ih =>
    intro i hi
    simp only [forwardChain, pairSites, chainHop, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton] at hi
    simp only [Finset.mem_image, Finset.mem_Icc]
    rcases hi with (rfl | rfl) | hi
    · exact ⟨2 * L + 1, ⟨by omega, by omega⟩, rfl⟩
    · exact ⟨2 * L + 2, ⟨by omega, by omega⟩, rfl⟩
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (ih (by omega) hi)
      rw [Finset.mem_Icc] at hj
      exact ⟨j, ⟨hj.1, by omega⟩, rfl⟩

/-- The sites `e` and `f` of the backward chain are the sites `a + j`, `j < 2L`. -/
theorem pairSites_backwardChain_subset (a : Fin N) (L : ℕ) (hL : 2 * L < N) :
    pairSites (backwardChain a L hL) ⊆
      (Finset.range (2 * L)).image fun j : ℕ => a + (j : Fin N) := by
  induction L with
  | zero => simp [backwardChain, pairSites]
  | succ L ih =>
    rw [backwardChain, pairSites_append]
    intro i hi
    simp only [pairSites, chainHopBack, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, Finset.union_empty] at hi
    simp only [Finset.mem_image, Finset.mem_range]
    rcases hi with hi | rfl | rfl
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (ih (by omega) hi)
      exact ⟨j, by simp at hj; omega, rfl⟩
    · exact ⟨2 * L + 1, by omega, rfl⟩
    · exact ⟨2 * L, by omega, rfl⟩

theorem allSites_forwardChain_subset (a : Fin N) (L : ℕ) (hL : 2 * L < N) :
    allSites (forwardChain a L hL) ⊆
      (Finset.range (2 * L + 1)).image fun j : ℕ => a + (j : Fin N) := by
  intro i hi
  obtain ⟨h, hh, hi⟩ := mem_allSites.mp hi
  obtain ⟨k, hk, hk', rfl⟩ := mem_forwardChain hh
  simp only [sites, chainHop, Finset.mem_insert, Finset.mem_singleton] at hi
  simp only [Finset.mem_image, Finset.mem_range]
  rcases hi with rfl | rfl | rfl
  · exact ⟨2 * k, by omega, rfl⟩
  · exact ⟨2 * k + 1, by omega, rfl⟩
  · exact ⟨2 * k + 2, by omega, rfl⟩

/-- After the forward chain, a vector with `|0⟩` at the sites `a + j`, `1 ≤ j ≤ 2L`, has `|0⟩` at
the sites `a + j`, `j < 2L`. -/
theorem isZeroOn_chainPerm_forwardChain (a : Fin N) (L : ℕ) (hL : 2 * L < N)
    {v : (Fin N → Fin d) → ℂ}
    (hv : IsZeroOn ((Finset.Icc 1 (2 * L)).image fun j : ℕ => a + (j : Fin N)) v) :
    IsZeroOn ((Finset.range (2 * L)).image fun j : ℕ => a + (j : Fin N))
      (chainPerm (forwardChain a L hL) *ᵥ v) := by
  induction L generalizing v with
  | zero => intro y _ i hi; simp at hi
  | succ L ih =>
    have hv' : IsZeroOn ((Finset.Icc 1 (2 * L)).image fun j : ℕ => a + (j : Fin N)) v :=
      hv.mono (Finset.image_subset_image (Finset.Icc_subset_Icc_right (by omega)))
    have hrest : IsZeroOn {a + ((2 * L + 1 : ℕ) : Fin N), a + ((2 * L + 2 : ℕ) : Fin N)} v := by
      refine hv.mono ?_
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      simp only [Finset.mem_image, Finset.mem_Icc]
      rcases hi with rfl | rfl <;> exact ⟨_, ⟨by omega, by omega⟩, rfl⟩
    have hrest' := hrest.chainPerm_mulVec (hs := forwardChain a L (by omega)) (by
      rw [Finset.disjoint_left]
      intro i hi hi'
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (allSites_forwardChain_subset a L (by omega) hi')
      rw [Finset.mem_range] at hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with hi | hi
      · exact add_natCast_ne a (by omega) (by omega) (by omega) hi
      · exact add_natCast_ne a (by omega) (by omega) (by omega) hi)
    have hall : IsZeroOn (((Finset.range (2 * L)).image fun j : ℕ => a + (j : Fin N)) ∪
        {a + ((2 * L + 1 : ℕ) : Fin N), a + ((2 * L + 2 : ℕ) : Fin N)})
        (chainPerm (forwardChain a L (by omega)) *ᵥ v) :=
      fun y hy i hi => (Finset.mem_union.mp hi).elim (ih (by omega) hv' y hy i) (hrest' y hy i)
    rw [forwardChain, chainPerm_cons, ← mulVec_mulVec, swapPerm]
    refine (hall.permMatrix_cfgPerm_mulVec_image _).mono ?_
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    rw [Finset.mem_range] at hj
    simp only [chainHop, Finset.mem_image, Finset.mem_union, Finset.mem_range, Finset.mem_insert,
      Finset.mem_singleton]
    rcases Nat.lt_or_ge j (2 * L) with hj' | hj'
    · refine ⟨a + (j : Fin N), Or.inl ⟨j, hj', rfl⟩, ?_⟩
      exact Equiv.swap_apply_of_ne_of_ne (add_natCast_ne a (by omega) (by omega) (by omega))
        (add_natCast_ne a (by omega) (by omega) (by omega))
    · rcases (show j = 2 * L ∨ j = 2 * L + 1 by omega) with rfl | rfl
      · exact ⟨_, Or.inr (Or.inr rfl), Equiv.swap_apply_right _ _⟩
      · refine ⟨a + ((2 * L + 1 : ℕ) : Fin N), Or.inr (Or.inl rfl), ?_⟩
        exact Equiv.swap_apply_of_ne_of_ne (add_natCast_ne a (by omega) (by omega) (by omega))
          (add_natCast_ne a (by omega) (by omega) (by omega))

end Chains

end TeleportHop

end QuantumCircuit
