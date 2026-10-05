/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Channel.PortRouting
import TNLean.Circuit.Channel.PortChannelRouting

/-!
# Data and scratch registers behind a physical port

Each spatial site has one physical qudit, a `k`-qudit data register and a `k`-qudit
scratch register. Register digits are distinct wires, and all register routing uses
the physical port. This finite layout supplies the bounded-memory interface for
Piroli, Styliaris and Cirac's gate convention (arXiv:2103.13367, Supplement pp. 7–8).
-/

namespace QuantumCircuit.PortRegisters

variable {N k : ℕ}

/-- The single physical port is followed by the data and scratch qudits. -/
def layout (N k : ℕ) : PhysicalPortLayout N (N * (1 + k + k)) where
  site w := (finProdFinEquiv.symm w).1
  port :=
    { toFun := fun i => finProdFinEquiv (i, (⟨0, by omega⟩ : Fin (1 + k + k)))
      inj' := fun i j h => congrArg Prod.fst (finProdFinEquiv.injective h) }
  site_port i := by simp

/-- A wire specified by its spatial site and local slot. -/
def wire (i : Fin N) (s : Fin (1 + k + k)) : Fin (N * (1 + k + k)) :=
  finProdFinEquiv (i, s)

@[simp] theorem site_wire (i : Fin N) (s : Fin (1 + k + k)) :
    (layout N k).site (wire i s) = i := by
  change (finProdFinEquiv.symm (finProdFinEquiv (i, s))).1 = i
  rw [Equiv.symm_apply_apply]

private def dataSlot (t : Fin k) : Fin (1 + k + k) := ⟨1 + t.val, by omega⟩
private def scratchSlot (t : Fin k) : Fin (1 + k + k) := ⟨1 + k + t.val, by omega⟩

/-- The data register at a spatial site. -/
def data (i : Fin N) : Fin k ↪ Fin (N * (1 + k + k)) where
  toFun t := wire i (dataSlot t)
  inj' t u h := by
    have h' := congrArg (fun x => (finProdFinEquiv.symm x).2.val) h
    simp only [wire, Equiv.symm_apply_apply, dataSlot] at h'
    exact Fin.ext (by omega)

/-- A same-size local scratch register, disjoint from the data register and port. -/
def scratch (i : Fin N) : Fin k ↪ Fin (N * (1 + k + k)) where
  toFun t := wire i (scratchSlot t)
  inj' t u h := by
    have h' := congrArg (fun x => (finProdFinEquiv.symm x).2.val) h
    simp only [wire, Equiv.symm_apply_apply, scratchSlot] at h'
    exact Fin.ext (by omega)

@[simp] theorem site_data (i : Fin N) (t : Fin k) :
    (layout N k).site (data i t) = i := site_wire i _

@[simp] theorem site_scratch (i : Fin N) (t : Fin k) :
    (layout N k).site (scratch i t) = i := site_wire i _

/-- Data and scratch wires cannot coincide, even when the sites coincide. -/
theorem data_ne_scratch (i j : Fin N) (t u : Fin k) : data i t ≠ scratch j u := by
  intro h
  have h' := congrArg (fun x => (finProdFinEquiv.symm x).2.val) h
  simp only [data, scratch, Function.Embedding.coeFn_mk, wire,
    Equiv.symm_apply_apply, dataSlot, scratchSlot] at h'
  omega

/-- Select a data digit at the left endpoints and a scratch digit at all other sites. -/
def selection (K : Finset (Fin N)) (t : Fin k) : Fin N ↪ Fin (N * (1 + k + k)) where
  toFun i := if i ∈ K then data i t else scratch i t
  inj' i j h := by
    have h' := congrArg (layout N k).site h
    simpa only [apply_ite, site_data, site_scratch, ite_self] using h'

@[simp] theorem selection_apply (K : Finset (Fin N)) (t : Fin k) (i : Fin N) :
    selection K t i = if i ∈ K then data i t else scratch i t := rfl

@[simp] theorem site_selection (K : Finset (Fin N)) (t : Fin k) (i : Fin N) :
    (layout N k).site (selection K t i) = i := by
  simp only [selection_apply, apply_ite, site_data, site_scratch, ite_self]

/-- Distinct routed digits select disjoint sets of wires. -/
theorem selection_ranges_disjoint (K : Finset (Fin N)) :
    Pairwise (fun t u : Fin k => Disjoint (Set.range (selection K t))
      (Set.range (selection K u))) := by
  intro t u htu
  rw [Set.disjoint_left]
  rintro x ⟨i, hi⟩ ⟨j, hj⟩
  have h : selection K t i = selection K u j := hi.trans hj.symm
  have hij : i = j := by
    simpa only [site_selection] using congrArg (layout N k).site h
  subst j
  by_cases hiK : i ∈ K
  · exact htu ((data i).injective (by simpa only [selection_apply, ite_eq_left hiK] using h))
  · exact htu ((scratch i).injective (by simpa only [selection_apply, ite_eq_right hiK] using h))

/-- The two data registers on distinct sites, in left-then-right register order. -/
def pairData (i j : Fin N) (hij : i ≠ j) :
    Fin (k + k) ↪ Fin (N * (1 + k + k)) :=
  finSumFinEquiv.symm.toEmbedding.trans
    { toFun := Sum.elim (data i) (data j)
      inj' := by
        intro a b hab
        cases a with
        | inl a =>
          cases b with
          | inl b => exact congrArg Sum.inl ((data i).injective hab)
          | inr b => exact (hij (by simpa using congrArg (layout N k).site hab)).elim
        | inr a =>
          cases b with
          | inl b => exact (hij (by simpa using (congrArg (layout N k).site hab).symm)).elim
          | inr b => exact congrArg Sum.inr ((data j).injective hab) }

@[simp] theorem pairData_left (i j : Fin N) (hij : i ≠ j) (t : Fin k) :
    pairData i j hij (Fin.castAdd k t) = data i t := by
  change Sum.elim (data i) (data j) (finSumFinEquiv.symm (Fin.castAdd k t)) = _
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

@[simp] theorem pairData_right (i j : Fin N) (hij : i ≠ j) (t : Fin k) :
    pairData i j hij (Fin.natAdd k t) = data j t := by
  change Sum.elim (data i) (data j) (finSumFinEquiv.symm (Fin.natAdd k t)) = _
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

end QuantumCircuit.PortRegisters

/-!
## Bringing paired data registers to one spatial site

On every selected neighboring bond, move the left data register into the right scratch
register, leaving the right data register fixed. Disjoint bonds share the same routing,
and one register digit is transferred in each physical-port layer. An arbitrary channel
on either pair can then act locally, after which reversing the routing restores the other
wires. The complete two-register channel therefore has physical depth at most `2 * k`.

Source: bounded onsite memories with fixed-dimensional physical-qudit communication,
Piroli, Styliaris and Cirac, arXiv:2103.13367, Supplement pp. 7–8.
-/

open Matrix
open scoped BigOperators

namespace QuantumCircuit

namespace PortMatching

variable {N : ℕ} [NeZero N]

/-- The right endpoint of a nontrivial selected bond cannot start another selected bond. -/
theorem right_notMem (K : Finset (Fin N))
    (hK : (K : Set (Fin N)).PairwiseDisjoint bond) {i : Fin N}
    (hi : i ∈ K) (hne : i ≠ i + 1) : i + 1 ∉ K := by
  intro hj
  exact Set.disjoint_left.mp (hK hi hj hne)
    (show i + 1 ∈ bond i by simp [bond])
    (show i + 1 ∈ bond (i + 1) by simp [bond])

end PortMatching

namespace PortRegisters

variable {d N k r : ℕ} [NeZero N]

/-- The common routing that exchanges left data digits with right scratch digits. -/
noncomputable def routingPermutation (K : Finset (Fin N))
    (hK : (K : Set (Fin N)).PairwiseDisjoint bond) :
    Equiv.Perm (Fin (N * (1 + k + k))) :=
  registerPermutation (selection K) (PortMatching.perm K hK)

omit [NeZero N] in
/-- Data at a site not selected as a left endpoint is absent from every routed digit. -/
theorem data_notMem_selection (K : Finset (Fin N)) {i : Fin N} (hi : i ∉ K)
    (t u : Fin k) : data i t ∉ Set.range (selection K u) := by
  rintro ⟨j, hj⟩
  have hji : j = i := by
    simpa only [site_selection, site_data] using congrArg (layout N k).site hj
  subst j
  exact data_ne_scratch i i t u (by simpa [selection_apply, hi] using hj.symm)

/-- The left data register moves to the right scratch register on every selected bond. -/
theorem routingPermutation_data_left (K : Finset (Fin N))
    (hK : (K : Set (Fin N)).PairwiseDisjoint bond) {i : Fin N}
    (hi : i ∈ K) (hne : i ≠ i + 1) (t : Fin k) :
    routingPermutation K hK (data i t) = scratch (i + 1) t := by
  have hleft : selection K t i = data i t := by simp [selection_apply, hi]
  rw [← hleft, routingPermutation, registerPermutation_apply _ _ (selection_ranges_disjoint K),
    PortMatching.perm_apply_left K hK hi]
  simp [selection_apply, PortMatching.right_notMem K hK hi hne]

/-- Data at every site outside the left endpoints remains exactly fixed. -/
theorem routingPermutation_data_of_notMem (K : Finset (Fin N))
    (hK : (K : Set (Fin N)).PairwiseDisjoint bond) {i : Fin N}
    (hi : i ∉ K) (t : Fin k) : routingPermutation K hK (data i t) = data i t :=
  registerPermutation_apply_of_notMem _ _ _ fun u => data_notMem_selection K hi t u

/-- Both data registers of a selected nontrivial bond are routed into its right site. -/
theorem routingPermutation_pairData_site (K : Finset (Fin N))
    (hK : (K : Set (Fin N)).PairwiseDisjoint bond) {i : Fin N}
    (hi : i ∈ K) (hne : i ≠ i + 1) (a : Fin (k + k)) :
    (layout N k).site (routingPermutation K hK (pairData i (i + 1) hne a)) = i + 1 := by
  refine Fin.addCases (fun t => ?_) (fun t => ?_) a
  · rw [pairData_left, routingPermutation_data_left K hK hi hne, site_scratch]
  · rw [pairData_right, routingPermutation_data_of_notMem K hK
      (PortMatching.right_notMem K hK hi hne), site_data]

/-- The shared data-to-scratch routing uses at most one physical layer per digit. -/
theorem routingPermutation_isPhysicalPortUnitary (K : Finset (Fin N))
    (hK : (K : Set (Fin N)).PairwiseDisjoint bond) :
    IsPhysicalPortUnitary (d := d) (layout N k) k (permOp (routingPermutation K hK)) :=
  IsPhysicalPortUnitary.register_matching (layout N k) (selection K)
    (site_selection K) K hK

/-- Every channel on the two data registers of a selected bond has a concrete
physical-port realization of depth at most twice the register length. -/
theorem pairData_isPhysicalPortProtocol (K : Finset (Fin N))
    (hK : (K : Set (Fin N)).PairwiseDisjoint bond) {i : Fin N}
    (hi : i ∈ K) (hne : i ≠ i + 1)
    (A : Fin r → Matrix (Fin (k + k) → Fin d) (Fin (k + k) → Fin d) ℂ)
    (hA : ∑ a, (A a)ᴴ * A a = 1) :
    IsPhysicalPortProtocol (layout N k) (2 * k)
      (rectangularKrausMap fun a => embedOp (pairData i (i + 1) hne) (A a)) :=
  IsPhysicalPortProtocol.of_register_routing (layout N k) (pairData i (i + 1) hne) A hA
    (routingPermutation K hK) (routingPermutation_isPhysicalPortUnitary K hK) (i + 1)
    (routingPermutation_pairData_site K hK hi hne)

end PortRegisters

end QuantumCircuit
