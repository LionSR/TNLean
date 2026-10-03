/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Teleportation.Chains

/-!
# Layers of gates between distant sites in constant depth with measurements

The paragraph "Tree-RG circuit with measurements" of arXiv:2307.01696 observes that the
isometries of eq. (16) "act on a constant number of sites which, although spatially separated,
can be teleported at neighboring registers with a constant overhead", so that "every isometry in
eq. (16) takes constant time using measurement". This file proves this for a whole layer of
two-site gates on pairwise disjoint stretches of the ring.

A *long-range gate* (`QuantumCircuit.LongRangeGate`) is a two-site unitary `u` on the sites `a`
and `a + 2L + 1` of the ring, with `2L + 1 < N`. For a list of long-range gates whose stretches
`a, a + 1, …, a + 2L + 1` are pairwise disjoint, two measurement rounds of total depth `5`
(`QuantumCircuit.LongRangeGate.rounds`) do the following, in parallel for all the gates:
teleport the content of `a` along the forward chain of `L` hops to `a + 2L`; apply `u` to the
neighbouring pair `{a + 2L, a + 2L + 1}`; teleport the content of `a + 2L` back to `a` along the
backward chain. On the vectors with `|0⟩` at the `2L` sites strictly between `a` and
`a + 2L + 1` for every gate, every outcome gives a scalar multiple of the product of the gates
`u` at the sites `a`, `a + 2L + 1`
(`QuantumCircuit.LongRangeGate.isRoundsImplementationOn_rounds`). No outcome is post-selected,
and the depth does not depend on the distances `2L + 1` nor on the number of gates.

Implementations by sequences of rounds compose
(`QuantumCircuit.MeasurementRound.IsRoundsImplementationOn.append`), so several such layers are
applied one after the other (`TNLean.MPS.Preparation.TreeMeasurement`).

**Scope restriction (odd separations, disjoint stretches):** a gate joins the sites `a` and
`a + 2L + 1`, at odd separation, the stretches of the gates of a layer are pairwise disjoint, and
the `2L` sites strictly between `a` and `a + 2L + 1` carry `|0⟩`; gates at even separation or on
overlapping stretches are not covered, whereas the cited paragraph of arXiv:2307.01696 speaks of
teleporting spatially separated sites in general. Documented in
`docs/paper-gaps/mswc24_tree_measurement_scope.tex`.

## Main definitions

* `QuantumCircuit.LongRangeGate`, `QuantumCircuit.LongRangeGate.op`.
* `QuantumCircuit.LongRangeGate.rounds` — the two rounds applying a layer of long-range gates.

## Main results

* `QuantumCircuit.TeleportHop.valid_flatMap`, `QuantumCircuit.TeleportHop.sitePerm_flatMap_apply`
  — chains on pairwise disjoint sets of sites run in parallel.
* `QuantumCircuit.LongRangeGate.sum_depth_rounds` — the two rounds have depth `5`.
* `QuantumCircuit.LongRangeGate.isRoundsImplementationOn_rounds`.

## References

* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), eq. (16) and paragraph "Tree-RG circuit with
  measurements".
-/

open Matrix
open scoped BigOperators

namespace QuantumCircuit

variable {d N : ℕ} [NeZero N]

/-! ### Permutations of sites supported on a set -/

/-- A permutation fixing every point outside `S` maps `S` into `S`. -/
theorem _root_.Equiv.Perm.apply_mem_of_forall_notMem {α : Type*} {π : Equiv.Perm α}
    {S : Set α} (hπ : ∀ i ∉ S, π i = i) {i : α} (hi : i ∈ S) : π i ∈ S := by
  by_contra h
  exact h (by rw [π.injective (hπ _ h)]; exact hi)

/-- Conjugating a product by `P` with inverse `Q` conjugates every factor. -/
theorem _root_.List.mul_prod_mul_of_mul_eq_one {M : Type*} [Monoid M] {P Q : M}
    (hQP : Q * P = 1) (hPQ : P * Q = 1) (l : List M) :
    P * l.prod * Q = (l.map fun X => P * X * Q).prod := by
  induction l with
  | nil => simpa using hPQ
  | cons X l ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons, ← ih]
    calc P * (X * l.prod) * Q = P * X * (Q * P) * l.prod * Q := by
          rw [hQP, mul_one]; simp only [mul_assoc]
      _ = P * X * Q * (P * l.prod * Q) := by simp only [mul_assoc]

namespace TeleportHop

theorem sitePerm_apply_of_notMem {hs : List (TeleportHop N)} {i : Fin N}
    (hi : i ∉ allSites hs) : sitePerm hs i = i := by
  induction hs with
  | nil => rfl
  | cons h hs ih =>
    have hi' : i ∉ h.sites := fun h' => hi (Or.inl h')
    simp only [sites, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hi'
    rw [sitePerm, Equiv.Perm.mul_apply, ih fun h' => hi (Or.inr h'),
      Equiv.swap_apply_of_ne_of_ne hi'.1 hi'.2.2]

theorem mem_allSites_flatMap {ι : Type*} {l : List ι} {f : ι → List (TeleportHop N)}
    {i : Fin N} : i ∈ allSites (l.flatMap f) ↔ ∃ g ∈ l, i ∈ allSites (f g) := by
  simp only [mem_allSites, List.mem_flatMap]
  exact ⟨fun ⟨h, ⟨g, hg, hh⟩, hi⟩ => ⟨g, hg, h, hh, hi⟩,
    fun ⟨g, hg, h, hh, hi⟩ => ⟨h, ⟨g, hg, hh⟩, hi⟩⟩

theorem mem_pairSites_flatMap {ι : Type*} {l : List ι} {f : ι → List (TeleportHop N)}
    {i : Fin N} : i ∈ pairSites (l.flatMap f) ↔ ∃ g ∈ l, i ∈ pairSites (f g) := by
  induction l with
  | nil => simp [pairSites]
  | cons g l ih => simp [List.flatMap_cons, pairSites_append, ih]

theorem chainPerm_append (hs hs' : List (TeleportHop N)) :
    chainPerm (d := d) (hs ++ hs') = chainPerm hs * chainPerm hs' := by
  simp only [chainPerm, sitePerm_append, permMatrix_cfgPerm_mul_permMatrix_cfgPerm]

/-- Two hops with disjoint sites can follow each other in a valid list. -/
theorem after_of_disjoint {h h' : TeleportHop N} (hd : Disjoint h.sites h'.sites) :
    After h h' := by
  have hmem : ∀ {i}, i ∈ h.sites → i ∉ h'.sites := fun hi hi' =>
    Set.disjoint_left.mp hd hi hi'
  refine ⟨hmem (by simp [sites]), hmem (by simp [sites]), fun he => ?_, fun he => ?_⟩
  · exact hmem (show h.c ∈ h.sites by simp [sites]) (he ▸ by simp [sites])
  · exact hmem (show h.c ∈ h.sites by simp [sites]) (he ▸ by simp [sites])

/-- The sites of a hop of a list are sites of the list. -/
theorem sites_subset_allSites {h : TeleportHop N} {hs : List (TeleportHop N)} (hh : h ∈ hs) :
    h.sites ⊆ allSites hs := fun _ hi => mem_allSites.mpr ⟨h, hh, hi⟩

/-- **Parallel chains.** Lists of hops whose sites lie in pairwise disjoint sets form a valid
list when concatenated. -/
theorem valid_flatMap {ι : Type*} {l : List ι} {f : ι → List (TeleportHop N)}
    {S : ι → Set (Fin N)} (hf : ∀ g ∈ l, Valid (f g)) (hS : ∀ g ∈ l, allSites (f g) ⊆ S g)
    (hl : l.Pairwise fun g g' => Disjoint (S g) (S g')) : Valid (l.flatMap f) := by
  rw [valid_iff_pairwise, List.pairwise_flatMap]
  refine ⟨fun g hg => valid_iff_pairwise.mp (hf g hg), ?_⟩
  refine List.Pairwise.imp_of_mem (fun {g g'} hg hg' hd h hh h' hh' => ?_) hl
  exact after_of_disjoint (hd.mono ((sites_subset_allSites hh).trans (hS g hg))
    ((sites_subset_allSites hh').trans (hS g' hg')))

/-- On the set `S g`, the permutation of sites of parallel chains is that of the chain `f g`. -/
theorem sitePerm_flatMap_apply {ι : Type*} {l : List ι} {f : ι → List (TeleportHop N)}
    {S : ι → Set (Fin N)} (hS : ∀ g ∈ l, allSites (f g) ⊆ S g)
    (hl : l.Pairwise fun g g' => Disjoint (S g) (S g')) {g : ι} (hg : g ∈ l) {i : Fin N}
    (hi : i ∈ S g) : sitePerm (l.flatMap f) i = sitePerm (f g) i := by
  induction l with
  | nil => simp at hg
  | cons g₀ l ih =>
    rw [List.pairwise_cons] at hl
    have hS' : ∀ g ∈ l, allSites (f g) ⊆ S g := fun g hg => hS g (List.mem_cons_of_mem _ hg)
    rw [List.flatMap_cons, sitePerm_append, Equiv.Perm.mul_apply]
    rcases List.mem_cons.mp hg with rfl | hg
    · have hfix : sitePerm (l.flatMap f) i = i := sitePerm_apply_of_notMem fun hi' => by
        obtain ⟨g', hg', hi'⟩ := mem_allSites_flatMap.mp hi'
        exact Set.disjoint_left.mp (hl.1 g' hg') hi (hS' g' hg' hi')
      rw [hfix]
    · rw [ih hS' hl.2 hg]
      refine sitePerm_apply_of_notMem fun hi' => ?_
      have hmem : sitePerm (f g) i ∈ S g :=
        Equiv.Perm.apply_mem_of_forall_notMem
          (fun j hj => sitePerm_apply_of_notMem fun hj' => hj (hS' g hg hj')) hi
      exact Set.disjoint_left.mp (hl.1 g hg) (hS g₀ List.mem_cons_self hi') hmem

/-- Off the sets `S g`, the permutation of sites of parallel chains is the identity. -/
theorem sitePerm_flatMap_apply_of_notMem {ι : Type*} {l : List ι} {f : ι → List (TeleportHop N)}
    {S : ι → Set (Fin N)} (hS : ∀ g ∈ l, allSites (f g) ⊆ S g) {i : Fin N}
    (hi : ∀ g ∈ l, i ∉ S g) : sitePerm (l.flatMap f) i = i := by
  refine sitePerm_apply_of_notMem fun hi' => ?_
  obtain ⟨g, hg, hi'⟩ := mem_allSites_flatMap.mp hi'
  exact hi g hg (hS g hg hi')

open Fin.NatCast in
theorem allSites_backwardChain_subset (a : Fin N) (L : ℕ) (hL : 2 * L < N) :
    allSites (backwardChain a L hL) ⊆ {i | ∃ j ≤ 2 * L, i = a + (j : Fin N)} := by
  intro i hi
  obtain ⟨h, hh, hi⟩ := mem_allSites.mp hi
  obtain ⟨k, hk, hk', rfl⟩ := mem_backwardChain hh
  simp only [sites, chainHopBack, Set.mem_insert_iff, Set.mem_singleton_iff] at hi
  rcases hi with rfl | rfl | rfl
  · exact ⟨2 * k + 2, by omega, rfl⟩
  · exact ⟨2 * k + 1, by omega, rfl⟩
  · exact ⟨2 * k, by omega, rfl⟩

end TeleportHop

/-! ### Long-range gates -/

/-- A *long-range gate*: a two-site unitary `u` acting on the sites `a` and `a + 2L + 1` of the
ring, with `2L + 1 < N`.

Source: arXiv:2307.01696, paragraph "Tree-RG circuit with measurements" (isometries acting on
"a constant number of sites which, although spatially separated, can be teleported at
neighboring registers"). -/
structure LongRangeGate (d N : ℕ) [NeZero N] where
  /-- The near site of the gate. -/
  a : Fin N
  /-- The number of hops of the chain from `a` to `a + 2L`. -/
  L : ℕ
  lt : 2 * L + 1 < N
  /-- The two-site unitary, acting on the sites `a` and `a + 2L + 1`. -/
  u : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ
  u_mem_unitary : u ∈ unitary (Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ)

namespace LongRangeGate

open Fin.NatCast TeleportHop

variable (g : LongRangeGate d N)

/-- The far site `a + 2L + 1` of the gate. -/
def far : Fin N := g.a + ((2 * g.L + 1 : ℕ) : Fin N)

/-- The site `a + 2L` to which the content of `a` is teleported, the left site of the
neighbouring pair `{a + 2L, a + 2L + 1}`. -/
def near : Fin N := g.a + ((2 * g.L : ℕ) : Fin N)

/-- The stretch `a, a + 1, …, a + 2L + 1` of the gate. -/
def span : Set (Fin N) := {i | ∃ j ≤ 2 * g.L + 1, i = g.a + (j : Fin N)}

/-- The `2L` sites `a + 1, …, a + 2L` strictly between the two sites of the gate. -/
def interior : Set (Fin N) := {i | ∃ j, 1 ≤ j ∧ j ≤ 2 * g.L ∧ i = g.a + (j : Fin N)}

/-- The `2L` sites `a, …, a + 2L - 1`, which carry `|0⟩` after the forward chain. -/
def cleared : Finset (Fin N) := (Finset.range (2 * g.L)).image fun j : ℕ => g.a + (j : Fin N)

/-- The gate on the chain: `u` at the sites `a` and `a + 2L + 1`. -/
noncomputable def op : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ := embedOp ![g.a, g.far] g.u

/-- The forward chain of `L` hops from `a` to `a + 2L`. -/
def there : List (TeleportHop N) := forwardChain g.a g.L (by have := g.lt; omega)

/-- The backward chain of `L` hops from `a + 2L` to `a`. -/
def back : List (TeleportHop N) := backwardChain g.a g.L (by have := g.lt; omega)

theorem near_ne_far : g.near ≠ g.far :=
  add_natCast_ne g.a (by have := g.lt; omega) g.lt (by omega)

omit [NeZero N] in
private theorem pair_injective {k k' : Fin N} (h : k ≠ k') : Function.Injective ![k, k'] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

/-- The gate `u` on the neighbouring pair `{a + 2L, a + 2L + 1}`. -/
noncomputable def localGate : Matrix (Fin N → Fin d)
    (Fin N → Fin d) ℂ := embedOp ![g.near, g.far] g.u

theorem localGate_mem_unitary :
    g.localGate ∈ unitary (Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) :=
  embedOp_mem_unitary (pair_injective g.near_ne_far) g.u_mem_unitary

theorem localGate_mem_supportedOperators :
    g.localGate ∈ supportedOperators d (ringBond g.near) := by
  have := embedOp_mem_supportedOperators (d := d) (pair_injective g.near_ne_far) g.u
  rw [Matrix.range_cons_cons_empty] at this
  rw [ringBond, near, add_natCast_succ]
  exact this

theorem a_ne_far : g.a ≠ g.far := by
  intro h
  refine add_natCast_ne g.a (j := 0) (k := 2 * g.L + 1) (by have := g.lt; omega) g.lt
    (by omega) ?_
  rw [Nat.cast_zero, add_zero]
  exact h

theorem op_mem_unitary : g.op ∈ unitary (Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) :=
  embedOp_mem_unitary (pair_injective g.a_ne_far) g.u_mem_unitary

/-- The gate acts on its two sites `a` and `a + 2L + 1`. -/
theorem op_mem_supportedOperators : g.op ∈ supportedOperators d {g.a, g.far} := by
  have := embedOp_mem_supportedOperators (d := d) (pair_injective g.a_ne_far) g.u
  rwa [Matrix.range_cons_cons_empty] at this

theorem far_mem_span : g.far ∈ g.span := ⟨2 * g.L + 1, le_rfl, rfl⟩

theorem bond_near_subset_span : ringBond g.near ⊆ g.span := by
  rintro i (rfl | rfl)
  · exact ⟨2 * g.L, by omega, rfl⟩
  · rw [near, add_natCast_succ]; exact ⟨2 * g.L + 1, le_rfl, rfl⟩

theorem interior_subset_span : g.interior ⊆ g.span :=
  fun _ ⟨j, _, hj, hi⟩ => ⟨j, by omega, hi⟩

theorem cleared_subset_span : (g.cleared : Set (Fin N)) ⊆ g.span := by
  intro i hi
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
  exact ⟨j, by simp at hj; omega, rfl⟩

theorem allSites_there_subset_span : allSites g.there ⊆ g.span :=
  (allSites_forwardChain_subset _ _ _).trans fun _ ⟨j, hj, hi⟩ => ⟨j, by omega, hi⟩

theorem allSites_back_subset_span : allSites g.back ⊆ g.span :=
  (allSites_backwardChain_subset _ _ _).trans fun _ ⟨j, hj, hi⟩ => ⟨j, by omega, hi⟩

theorem disjoint_cleared_bond_near : Disjoint (g.cleared : Set (Fin N)) (ringBond g.near) := by
  have hL := g.lt
  rw [Set.disjoint_left]
  intro i hi hi'
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
  have hj := Finset.mem_range.mp hj
  rw [ringBond, near, add_natCast_succ] at hi'
  rcases hi' with hi' | hi'
  · exact add_natCast_ne g.a (by omega) (by omega) (by omega) hi'
  · exact add_natCast_ne g.a (by omega) hL (by omega) hi'

theorem sitePerm_back_near : sitePerm g.back g.near = g.a := by
  rw [back, sitePerm_backwardChain, Equiv.Perm.inv_eq_iff_eq]
  exact (sitePerm_forwardChain _ _ _).1.symm

theorem sitePerm_back_far : sitePerm g.back g.far = g.far := by
  rw [back, sitePerm_backwardChain, Equiv.Perm.inv_eq_iff_eq]
  exact ((sitePerm_forwardChain _ _ _).2 _ (by omega) g.lt).symm

theorem sitePerm_back_sitePerm_there (i : Fin N) :
    sitePerm g.back (sitePerm g.there i) = i := by
  rw [back, sitePerm_backwardChain, there]
  simp

/-! ### Layers of long-range gates -/

variable {g}

section Layer

variable {gs : List (LongRangeGate d N)}
  (hgs : gs.Pairwise fun g g' => Disjoint g.span g'.span)

include hgs in
theorem pairwise_disjoint_bond :
    gs.Pairwise fun g g' => Disjoint (ringBond g.near) (ringBond g'.near) :=
  hgs.imp fun {g g'} h => h.mono g.bond_near_subset_span g'.bond_near_subset_span

/-- The layer of the gates `u` on the neighbouring pairs `{a + 2L, a + 2L + 1}`. -/
noncomputable def localLayer : Layer d N :=
  layerOfList gs near localGate (pairwise_disjoint_bond hgs)
    (fun g _ => g.localGate_mem_unitary) fun g _ => g.localGate_mem_supportedOperators

theorem localLayer_op : (localLayer hgs).op = (gs.map localGate).prod :=
  layerOfList_op _ _ _ _ _ _

include hgs in
theorem valid_there : Valid (gs.flatMap there) :=
  valid_flatMap (fun _ _ => valid_forwardChain _ _ _) (fun g _ => g.allSites_there_subset_span)
    hgs

include hgs in
theorem valid_back : Valid (gs.flatMap back) :=
  valid_flatMap (fun _ _ => valid_backwardChain _ _ _) (fun g _ => g.allSites_back_subset_span)
    hgs

variable [NeZero d]

include hgs in
/-- After the forward chains, the sites `a, …, a + 2L - 1` of every gate carry `|0⟩`. -/
theorem isZeroOn_chainPerm_there {v : (Fin N → Fin d) → ℂ} (hv : ∀ g ∈ gs, IsZeroOn g.interior v) :
    ∀ g ∈ gs, IsZeroOn (g.cleared : Set (Fin N)) (chainPerm (gs.flatMap there) *ᵥ v) := by
  induction gs with
  | nil => simp
  | cons g₀ gs ih =>
    rw [List.pairwise_cons] at hgs
    have hrest : ∀ g ∈ gs, IsZeroOn g.interior v := fun g hg => hv g (List.mem_cons_of_mem _ hg)
    rw [List.flatMap_cons, chainPerm_append, ← mulVec_mulVec]
    have hdisj : ∀ {S : Set (Fin N)}, S ⊆ g₀.span →
        Disjoint S (allSites (gs.flatMap there)) := by
      intro S hS
      rw [Set.disjoint_left]
      intro i hi hi'
      obtain ⟨g, hg, hi'⟩ := mem_allSites_flatMap.mp hi'
      exact Set.disjoint_left.mp (hgs.1 g hg) (hS hi) (g.allSites_there_subset_span hi')
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · have hw : IsZeroOn g.interior (chainPerm (gs.flatMap there) *ᵥ v) :=
        (hv g List.mem_cons_self).chainPerm_mulVec (hdisj g.interior_subset_span)
      refine (isZeroOn_chainPerm_forwardChain _ _ _ hw).mono fun i hi => ?_
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      exact ⟨j, Finset.mem_range.mp hj, rfl⟩
    · refine (ih hgs.2 hrest g hg).chainPerm_mulVec ?_
      exact (hgs.1 g hg).symm.mono g.cleared_subset_span g₀.allSites_there_subset_span

include hgs in
/-- The gates on the neighbouring pairs keep `|0⟩` at the sites `a, …, a + 2L - 1` of every
gate. -/
theorem isZeroOn_localLayer {w : (Fin N → Fin d) → ℂ}
    (hw : ∀ g ∈ gs, IsZeroOn (g.cleared : Set (Fin N)) w) :
    ∀ g ∈ gs, IsZeroOn (g.cleared : Set (Fin N)) ((localLayer hgs).op *ᵥ w) := by
  have : Std.Symm fun g g' : LongRangeGate d N => Disjoint g.span g'.span :=
    ⟨fun _ _ h => h.symm⟩
  intro g hg
  rw [localLayer_op]
  refine (hw g hg).mulVec_of_mem_supportedOperators disjoint_compl_right
    (list_prod_mem_supportedOperators _ fun A hA => ?_)
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hA
  refine supportedOperators_mono
    (show ringBond g'.near ⊆ ((g.cleared : Set (Fin N)))ᶜ from fun i hi hi' => ?_)
    g'.localGate_mem_supportedOperators
  by_cases hgg : g = g'
  · subst hgg
    exact Set.disjoint_left.mp g.disjoint_cleared_bond_near hi' hi
  · exact Set.disjoint_left.mp (hgs.forall hg hg' hgg) (g.cleared_subset_span hi')
      (g'.bond_near_subset_span hi)

omit [NeZero d] in
include hgs in
/-- The backward chains invert the forward chains. -/
theorem sitePerm_there_eq_symm :
    sitePerm (gs.flatMap there) = (sitePerm (gs.flatMap back)).symm := by
  refine Equiv.ext fun i => ?_
  rw [Equiv.eq_symm_apply]
  by_cases hi : ∃ g ∈ gs, i ∈ g.span
  · obtain ⟨g, hg, hi⟩ := hi
    have hmem : sitePerm g.there i ∈ g.span :=
      Equiv.Perm.apply_mem_of_forall_notMem (fun j hj => sitePerm_apply_of_notMem fun hj' =>
        hj (g.allSites_there_subset_span hj')) hi
    rw [sitePerm_flatMap_apply (fun g _ => g.allSites_there_subset_span) hgs hg hi,
      sitePerm_flatMap_apply (fun g _ => g.allSites_back_subset_span) hgs hg hmem,
      sitePerm_back_sitePerm_there]
  · simp only [not_exists, not_and] at hi
    rw [sitePerm_flatMap_apply_of_notMem (fun g _ => g.allSites_there_subset_span) hi,
      sitePerm_flatMap_apply_of_notMem (fun g _ => g.allSites_back_subset_span) hi]

omit [NeZero d] in
include hgs in
/-- **The layer conjugated by the chains.** The backward chains, the gates on the neighbouring
pairs, and the forward chains compose to the product of the long-range gates. -/
theorem chainPerm_back_mul_localLayer_mul_chainPerm_there :
    chainPerm (gs.flatMap back) * (localLayer hgs).op * chainPerm (gs.flatMap there) =
      (gs.map op).prod := by
  set σ := sitePerm (gs.flatMap back)
  have hPQ : (cfgPerm (d := d) σ).permMatrix ℂ * (cfgPerm σ.symm).permMatrix ℂ = 1 := by
    rw [permMatrix_cfgPerm_mul_permMatrix_cfgPerm, show σ * σ.symm = 1 by ext; simp,
      permMatrix_cfgPerm_one]
  have hQP : (cfgPerm (d := d) σ.symm).permMatrix ℂ * (cfgPerm σ).permMatrix ℂ = 1 := by
    rw [permMatrix_cfgPerm_mul_permMatrix_cfgPerm, show σ.symm * σ = 1 by ext; simp,
      permMatrix_cfgPerm_one]
  rw [chainPerm, chainPerm, sitePerm_there_eq_symm hgs, localLayer_op,
    List.mul_prod_mul_of_mul_eq_one hQP hPQ, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun g hg => ?_)
  rw [Function.comp_apply, localGate, permMatrix_cfgPerm_mul_embedOp_mul, op]
  have hback : ∀ {i}, i ∈ g.span → σ i = sitePerm g.back i := fun hi =>
    sitePerm_flatMap_apply (fun g _ => g.allSites_back_subset_span) hgs hg hi
  congr 1
  funext t
  fin_cases t
  · simp only [Fin.zero_eta, Fin.isValue, Function.comp_apply, Matrix.cons_val_zero]
    rw [hback (g.bond_near_subset_span (Or.inl rfl)), sitePerm_back_near]
  · simp only [Fin.mk_one, Fin.isValue, Function.comp_apply, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    rw [hback g.far_mem_span, sitePerm_back_far]

/-- The two measurement rounds applying a layer of long-range gates: teleport the content of
every near site `a` along its forward chain to `a + 2L`; then apply the gates `u` to the
neighbouring pairs `{a + 2L, a + 2L + 1}` and teleport the content of every `a + 2L` back to `a`
along the backward chains.

Source: arXiv:2307.01696, paragraph "Tree-RG circuit with measurements". -/
noncomputable def rounds : List (MeasurementRound d N) :=
  [round [] (gs.flatMap there) (valid_there hgs),
    round [localLayer hgs] (gs.flatMap back) (valid_back hgs)]

/-- The two rounds have depth `5` in total, whatever the distances and the number of gates. -/
theorem sum_depth_rounds : ((rounds (d := d) hgs).map MeasurementRound.depth).sum = 5 := by
  simp [rounds, depth_round]

/-- **A layer of long-range gates in constant depth with measurements.** For long-range gates
on pairwise disjoint stretches, the two rounds `rounds`, of total depth `5`, implement the
product of the gates on the vectors with `|0⟩` at the `2L` sites strictly between the two sites
of every gate: whatever the outcomes, every output is a scalar multiple of the product of the
gates `u` at the sites `a`, `a + 2L + 1` applied to the input. No outcome is post-selected.

Source: arXiv:2307.01696, paragraph "Tree-RG circuit with measurements" ("Isometries ... act on
a constant number of sites which, although spatially separated, can be teleported at
neighboring registers with a constant overhead ... Therefore every isometry ... takes constant
time using measurement"). -/
theorem isRoundsImplementationOn_rounds :
    MeasurementRound.IsRoundsImplementationOn (rounds (d := d) hgs)
      {v | ∀ g ∈ gs, IsZeroOn g.interior v} (gs.map op).prod := by
  intro v hv w hw
  have h₁ : IsZeroOn (TeleportHop.pairSites (gs.flatMap there)) v := fun x hx i hi => by
    obtain ⟨g, hg, hi⟩ := mem_pairSites_flatMap.mp hi
    exact hv g hg x hx i (pairSites_forwardChain_subset _ _ _ hi)
  have h₂ : IsZeroOn (TeleportHop.pairSites (gs.flatMap back))
      ((localLayer hgs).op *ᵥ (chainPerm (gs.flatMap there) *ᵥ v)) := fun x hx i hi => by
    obtain ⟨g, hg, hi⟩ := mem_pairSites_flatMap.mp hi
    exact isZeroOn_localLayer hgs (isZeroOn_chainPerm_there hgs hv) g hg x hx i
      (pairSites_backwardChain_subset _ _ _ hi)
  obtain ⟨c, hc⟩ := exists_eq_smul_of_mem_outputs_conj (valid_there hgs) (valid_back hgs)
    (localLayer hgs) h₁ h₂ hw
  exact ⟨c, by rw [hc, chainPerm_back_mul_localLayer_mul_chainPerm_there]⟩

end Layer

end LongRangeGate

end QuantumCircuit
