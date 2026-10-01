/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.TeleportationChains

/-!
# Layers of gates between distant sites in constant depth with measurements

The paragraph "Tree-RG circuit with measurements" of arXiv:2307.01696 observes that the
isometries of eq. (16) "act on a constant number of sites which, although spatially separated,
can be teleported at neighboring registers with a constant overhead", so that "every isometry in
eq. (16) takes constant time using measurement". This file proves this for a whole layer of
two-site gates on pairwise disjoint stretches of the ring.

A *long-range gate* (`MPSPreparation.LongRangeGate`) is a two-site unitary `u` on the sites `a`
and `a + 2L + 1` of the ring, with `2L + 1 < N`. For a list of long-range gates whose stretches
`a, a + 1, …, a + 2L + 1` are pairwise disjoint, two measurement rounds of total depth `5`
(`MPSPreparation.LongRangeGate.rounds`) do the following, in parallel for all the gates:
teleport the content of `a` along the forward chain of `L` hops to `a + 2L`; apply `u` to the
neighbouring pair `{a + 2L, a + 2L + 1}`; teleport the content of `a + 2L` back to `a` along the
backward chain. On the vectors with `|0⟩` at the `2L` sites strictly between `a` and
`a + 2L + 1` for every gate, every outcome gives a scalar multiple of the product of the gates
`u` at the sites `a`, `a + 2L + 1`
(`MPSPreparation.LongRangeGate.isRoundsImplementationOn_rounds`). No outcome is post-selected,
and the depth does not depend on the distances `2L + 1` nor on the number of gates.

Implementations by sequences of rounds compose
(`MPSPreparation.MeasurementRound.IsRoundsImplementationOn.append`), which gives preparations
by several such layers.

## Main definitions

* `MPSPreparation.MeasurementRound.IsRoundsImplementationOn` — a sequence of rounds acts as a
  given matrix on a set of vectors, for every sequence of outcomes, up to a scalar.
* `MPSPreparation.LongRangeGate`, `MPSPreparation.LongRangeGate.op`.
* `MPSPreparation.LongRangeGate.rounds` — the two rounds applying a layer of long-range gates.

## Main results

* `MPSPreparation.MeasurementRound.IsRoundsImplementationOn.append`,
  `MPSPreparation.MeasurementRound.IsRoundsImplementationOn.isPreparedWithMeasurementRoundsInDepth`.
* `MPSPreparation.LongRangeGate.sum_depth_rounds` — the two rounds have depth `5`.
* `MPSPreparation.LongRangeGate.isRoundsImplementationOn_rounds`.

## References

* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), eq. (16) and paragraph "Tree-RG circuit with
  measurements".
-/

open Matrix MPSTensor
open scoped BigOperators

namespace MPSPreparation

variable {d N : ℕ} [NeZero N]

/-! ### Sequences of rounds implementing a matrix -/

namespace MeasurementRound

theorem mem_outputs_append {Rs Rs' : List (MeasurementRound d N)} {v w : Cfg d N → ℂ} :
    w ∈ outputs (Rs ++ Rs') v ↔ ∃ u ∈ outputs Rs v, w ∈ outputs Rs' u := by
  induction Rs generalizing v with
  | nil => simp
  | cons R Rs ih =>
    simp only [List.cons_append, R.mem_outputs_cons, ih]
    exact ⟨fun ⟨m, u, hu, hw⟩ => ⟨u, ⟨m, hu⟩, hw⟩, fun ⟨u, ⟨m, hu⟩, hw⟩ => ⟨m, u, hu, hw⟩⟩

/-- The sequence of rounds `Rs` *implements* the matrix `W` on the set `E` of vectors when, for
every `v ∈ E`, every output of `Rs` from `v` is a scalar multiple of `W v`: whatever the
outcomes, the rounds act on `E` as `W`, up to a scalar.

Source: arXiv:2307.01696, paragraph "Tree-RG circuit with measurements" ("correcting (without
postselection) based on the measurement outcomes"). -/
def IsRoundsImplementationOn (Rs : List (MeasurementRound d N)) (E : Set (Cfg d N → ℂ))
    (W : Matrix (Cfg d N) (Cfg d N) ℂ) : Prop :=
  ∀ v ∈ E, ∀ w ∈ outputs Rs v, ∃ c : ℂ, w = c • (W *ᵥ v)

theorem isRoundsImplementationOn_nil (E : Set (Cfg d N → ℂ)) :
    IsRoundsImplementationOn ([] : List (MeasurementRound d N)) E 1 := by
  intro v _ w hw
  rw [outputs_nil, Set.mem_singleton_iff] at hw
  exact ⟨1, by rw [hw, one_mulVec, one_smul]⟩

theorem IsRoundsImplementationOn.mono {Rs : List (MeasurementRound d N)}
    {E E' : Set (Cfg d N → ℂ)} {W : Matrix (Cfg d N) (Cfg d N) ℂ}
    (h : IsRoundsImplementationOn Rs E W) (hE : E' ⊆ E) : IsRoundsImplementationOn Rs E' W :=
  fun v hv => h v (hE hv)

/-- **Implementations compose.** If `Rs` implements `W` on `E`, `W` maps `E` into `E'`, and
`Rs'` implements `W'` on `E'`, then `Rs` followed by `Rs'` implements `W' W` on `E`. -/
theorem IsRoundsImplementationOn.append {Rs Rs' : List (MeasurementRound d N)}
    {E E' : Set (Cfg d N → ℂ)} {W W' : Matrix (Cfg d N) (Cfg d N) ℂ}
    (h : IsRoundsImplementationOn Rs E W) (h' : IsRoundsImplementationOn Rs' E' W')
    (hE : ∀ v ∈ E, W *ᵥ v ∈ E') : IsRoundsImplementationOn (Rs ++ Rs') E (W' * W) := by
  intro v hv w hw
  obtain ⟨u, hu, hw⟩ := mem_outputs_append.mp hw
  obtain ⟨c, rfl⟩ := h v hv u hu
  obtain ⟨w', hw', rfl⟩ := mem_outputs_smul c hw
  obtain ⟨c', rfl⟩ := h' _ (hE v hv) w' hw'
  exact ⟨c * c', by rw [smul_smul, mulVec_mulVec]⟩

/-- **Preparation from an implementation.** If `Rs` implements `W` on `E` and the nonzero
product vector `π` lies in `E`, then `W π` is prepared with measurement rounds in the total
depth of `Rs`. -/
theorem IsRoundsImplementationOn.isPreparedWithMeasurementRoundsInDepth
    {Rs : List (MeasurementRound d N)} {E : Set (Cfg d N → ℂ)}
    {W : Matrix (Cfg d N) (Cfg d N) ℂ} (h : IsRoundsImplementationOn Rs E W)
    {v : Fin N → Fin d → ℂ} (hv : productVector v ≠ 0) (hvE : productVector v ∈ E) :
    IsPreparedWithMeasurementRoundsInDepth (Rs.map depth).sum (W *ᵥ productVector v) :=
  ⟨v, Rs, le_rfl, hv, fun w hw _ => h _ hvE w hw⟩

end MeasurementRound

/-! ### Permutations of sites supported on a set -/

/-- A permutation fixing every site outside `S` maps `S` into `S`. -/
private theorem perm_apply_mem {π : Equiv.Perm (Fin N)} {S : Set (Fin N)}
    (hπ : ∀ i ∉ S, π i = i) {i : Fin N} (hi : i ∈ S) : π i ∈ S := by
  by_contra h
  exact h (by rw [π.injective (hπ _ h)]; exact hi)

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

theorem chainPerm_append (hs hs' : List (TeleportHop N)) :
    chainPerm (d := d) (hs ++ hs') = chainPerm hs * chainPerm hs' := by
  rw [chainPerm_eq, chainPerm_eq, chainPerm_eq, sitePerm_append,
    permMatrix_cfgPerm_mul_permMatrix_cfgPerm]

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
        perm_apply_mem
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
  u : Matrix (Cfg d 2) (Cfg d 2) ℂ
  u_mem_unitary : u ∈ unitary (Matrix (Cfg d 2) (Cfg d 2) ℂ)

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
noncomputable def op : Matrix (Cfg d N) (Cfg d N) ℂ := embedOp ![g.a, g.far] g.u

/-- The forward chain of `L` hops from `a` to `a + 2L`. -/
def there : List (TeleportHop N) := forwardChain g.a g.L (by have := g.lt; omega)

/-- The backward chain of `L` hops from `a + 2L` to `a`. -/
def back : List (TeleportHop N) := backwardChain g.a g.L (by have := g.lt; omega)

theorem near_ne_far : g.near ≠ g.far :=
  add_natCast_ne g.a (by have := g.lt; omega) g.lt (by omega)

private theorem pair_injective {k k' : Fin N} (h : k ≠ k') : Function.Injective ![k, k'] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

/-- The gate `u` on the neighbouring pair `{a + 2L, a + 2L + 1}`. -/
noncomputable def localGate : Matrix (Cfg d N) (Cfg d N) ℂ := embedOp ![g.near, g.far] g.u

theorem localGate_mem_unitary :
    g.localGate ∈ unitary (Matrix (Cfg d N) (Cfg d N) ℂ) :=
  embedOp_mem_unitary (pair_injective g.near_ne_far) g.u_mem_unitary

theorem localGate_mem_supportedOperators : g.localGate ∈ supportedOperators d (bond g.near) := by
  have := embedOp_mem_supportedOperators (d := d) (pair_injective g.near_ne_far) g.u
  rw [Matrix.range_cons_cons_empty] at this
  rw [bond, near, add_natCast_succ]
  exact this

theorem a_mem_span : g.a ∈ g.span := ⟨0, by omega, by simp⟩

theorem far_mem_span : g.far ∈ g.span := ⟨2 * g.L + 1, le_rfl, rfl⟩

theorem bond_near_subset_span : bond g.near ⊆ g.span := by
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

theorem disjoint_cleared_bond_near : Disjoint (g.cleared : Set (Fin N)) (bond g.near) := by
  have hL := g.lt
  rw [Set.disjoint_left]
  intro i hi hi'
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
  have hj := Finset.mem_range.mp hj
  rw [bond, near, add_natCast_succ] at hi'
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
    gs.Pairwise fun g g' => Disjoint (bond g.near) (bond g'.near) :=
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

end Layer

end LongRangeGate

end MPSPreparation
