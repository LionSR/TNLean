/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.CircuitComposition
import TNLean.MPS.Preparation.LongRangeGates

/-!
# Gates between distant registers of several sites in constant depth with measurements

The isometries of the tree-RG circuit of arXiv:2307.01696, eq. (16), act on registers carrying
`ℂ^{D²}`, which occupy several sites of the ring once `D² > d`. The paragraph "Tree-RG circuit
with measurements" teleports such registers "at neighboring registers with a constant
overhead". This file proves this for a layer of gates on pairs of registers of `s` sites.

A *register gate* (`MPSPreparation.RegisterGate`) is a unitary `X` on `2s` sites acting on the
two registers `a, …, a + s - 1` and `a + 2L + s, …, a + 2L + 2s - 1` of the ring, with
`2L + 2s ≤ N`. For a list of register gates whose stretches `a, …, a + 2L + 2s - 1` are pairwise
disjoint, the measurement rounds `MPSPreparation.RegisterGate.rounds` do the following, in
parallel for all the gates: teleport the site `a + t` of the first register to `a + 2L + t`
along a chain of `L` hops, one round of depth `2` for each `t`, from `t = s - 1` down to `t = 0`;
apply the unitaries `X` to the `2s` consecutive sites `a + 2L, …, a + 2L + 2s - 1` by a local
circuit; teleport the sites back, one round for each `t`, from `t = 0` up to `t = s - 1`. The
site `a + t` is moved only after the sites `a + t + 1, …, a + s - 1` of its register, so its
chain meets only sites carrying `|0⟩`.

On the vectors with `|0⟩` at the `2L` sites strictly between the two registers of every gate,
every outcome gives a scalar multiple of the product of the gates `X` at their registers
(`MPSPreparation.RegisterGate.isRoundsImplementationOn_rounds`). No outcome is post-selected.
If every `X` is a product of at most `K` gates on neighbouring sites, the rounds have total depth
`4s + K + 2`, independent of the distances `2L` and of the number of gates
(`MPSPreparation.RegisterGate.exists_rounds`).

## Main definitions

* `MPSPreparation.RegisterGate`, `MPSPreparation.RegisterGate.op`.
* `MPSPreparation.RegisterGate.rounds` — the rounds applying a layer of register gates.

## Main results

* `MPSPreparation.RegisterGate.sum_depth_rounds` — the rounds have depth `4s + K + 2`.
* `MPSPreparation.RegisterGate.isRoundsImplementationOn_rounds`.
* `MPSPreparation.RegisterGate.exists_rounds`.

## References

* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), eq. (16) and paragraph "Tree-RG circuit with
  measurements".
-/

open Matrix MPSTensor
open scoped BigOperators

namespace MPSPreparation

open Fin.NatCast TeleportHop

variable {d N s : ℕ} [NeZero N]

/-! ### Permutations and sites carrying `|0⟩` -/

omit [NeZero N] in
/-- If the permutation `π` maps no site outside `S` into `S'`, it moves the sites carrying
`|0⟩` from `S` onto `S'`. -/
theorem IsZeroOn.permMatrix_cfgPerm_mulVec_of_mapsTo [NeZero d] {S S' : Set (Fin N)}
    {v : Cfg d N → ℂ} (h : IsZeroOn S v) {π : Equiv.Perm (Fin N)}
    (hπ : ∀ x, x ∉ S → π x ∉ S') : IsZeroOn S' ((cfgPerm π).permMatrix ℂ *ᵥ v) := by
  refine (h.permMatrix_cfgPerm_mulVec_image π).mono fun y hy => ?_
  refine ⟨π.symm y, ?_, by simp⟩
  by_contra hx
  exact hπ _ hx (by simpa using hy)

omit [NeZero N] in
/-- Conjugating a product by `P` with inverse `Q` conjugates every factor. -/
theorem mul_list_prod_mul_of_mul_eq_one {n : Type*} [Fintype n] [DecidableEq n]
    {P Q : Matrix n n ℂ} (hQP : Q * P = 1) (hPQ : P * Q = 1) (l : List (Matrix n n ℂ)) :
    P * l.prod * Q = (l.map fun X => P * X * Q).prod := by
  induction l with
  | nil => simpa using hPQ
  | cons X l ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons, ← ih]
    calc P * (X * l.prod) * Q = P * X * (Q * P) * l.prod * Q := by
          rw [hQP, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = P * X * Q * (P * l.prod * Q) := by simp only [Matrix.mul_assoc]

/-! ### Register gates -/

/-- A *register gate*: a unitary `X` on `2s` sites acting on the two registers
`a, …, a + s - 1` and `a + 2L + s, …, a + 2L + 2s - 1` of the ring, with `2L + 2s ≤ N`.

Source: arXiv:2307.01696, paragraph "Tree-RG circuit with measurements" (isometries acting on
"a constant number of sites which, although spatially separated, can be teleported at
neighboring registers"). -/
structure RegisterGate (d N s : ℕ) [NeZero N] where
  /-- The first site of the first register. -/
  a : Fin N
  /-- The number of hops of the chain teleporting each site of the first register. -/
  L : ℕ
  le : 2 * L + 2 * s ≤ N
  /-- The unitary on the two registers, the first register on its first `s` sites. -/
  X : Matrix (Cfg d (s + s)) (Cfg d (s + s)) ℂ

namespace RegisterGate

variable (g : RegisterGate d N s)

/-- The offset from `a` of the site `t` of the two registers. -/
def offset (t : Fin (s + s)) : ℕ := if t.val < s then t.val else t.val + 2 * g.L

/-- The sites of the two registers: `a + t` for `t < s` and `a + 2L + t` for `s ≤ t < 2s`. -/
def sites (t : Fin (s + s)) : Fin N := g.a + (g.offset t : Fin N)

/-- The `2s` consecutive sites `a + 2L, …, a + 2L + 2s - 1` on which `X` is applied after the
first register is teleported. -/
def localSites (t : Fin (s + s)) : Fin N := g.a + ((2 * g.L + t.val : ℕ) : Fin N)

/-- The stretch `a, …, a + 2L + 2s - 1` of the gate. -/
def span : Set (Fin N) := {i | ∃ j < 2 * g.L + 2 * s, i = g.a + (j : Fin N)}

/-- The `2L` sites `a + t, …, a + t + 2L - 1`, which carry `|0⟩` before the chain of the site
`t - 1` of the first register and after the chain of the site `t`. -/
def zone (t : ℕ) : Set (Fin N) := {i | ∃ j, t ≤ j ∧ j < t + 2 * g.L ∧ i = g.a + (j : Fin N)}

/-- The `2L` sites `a + s, …, a + s + 2L - 1` strictly between the two registers. -/
def interior : Set (Fin N) := g.zone s

/-- The gate on the ring: `X` at the two registers. -/
noncomputable def op : Matrix (Cfg d N) (Cfg d N) ℂ := embedOp g.sites g.X

/-- The gate `X` on the consecutive sites `a + 2L, …, a + 2L + 2s - 1`. -/
noncomputable def localOp : Matrix (Cfg d N) (Cfg d N) ℂ := embedOp g.localSites g.X

theorem offset_lt (t : Fin (s + s)) : g.offset t < 2 * g.L + 2 * s := by
  unfold offset; split_ifs <;> omega

theorem sites_injective : Function.Injective g.sites := by
  intro t t' h
  have hN := g.le
  have := add_natCast_injective g.a (by have := g.offset_lt t; omega)
    (by have := g.offset_lt t'; omega) h
  unfold offset at this
  exact Fin.ext (by split_ifs at this <;> omega)

theorem localSites_injective : Function.Injective g.localSites := by
  intro t t' h
  have hN := g.le
  exact Fin.ext (by
    have := add_natCast_injective g.a (by omega) (by omega) h
    omega)

theorem localSites_succ (t t' : Fin (s + s)) (h : t'.val = t.val + 1) :
    g.localSites t' = g.localSites t + 1 := by
  rw [localSites, localSites, add_natCast_succ, h, Nat.add_assoc]

theorem sites_mem_span (t : Fin (s + s)) : g.sites t ∈ g.span := ⟨_, g.offset_lt t, rfl⟩

theorem localSites_mem_span (t : Fin (s + s)) : g.localSites t ∈ g.span :=
  ⟨_, by omega, rfl⟩

theorem zone_subset_span {t : ℕ} (ht : t ≤ s) : g.zone t ⊆ g.span :=
  fun _ ⟨j, _, hj, hi⟩ => ⟨j, by omega, hi⟩

theorem op_mem_unitary (hX : g.X ∈ unitary (Matrix (Cfg d (s + s)) (Cfg d (s + s)) ℂ)) :
    g.op ∈ unitary (Matrix (Cfg d N) (Cfg d N) ℂ) :=
  embedOp_mem_unitary g.sites_injective hX

theorem op_mem_supportedOperators : g.op ∈ supportedOperators d (Set.range g.sites) :=
  embedOp_mem_supportedOperators g.sites_injective g.X

/-- The sites `a + j` of the stretch are distinct. -/
theorem add_eq_add_iff {j j' : ℕ} (hj : j < 2 * g.L + 2 * s) (hj' : j' < 2 * g.L + 2 * s) :
    g.a + (j : Fin N) = g.a + (j' : Fin N) ↔ j = j' := by
  have := g.le
  exact ⟨add_natCast_injective g.a (by omega) (by omega), fun h => h ▸ rfl⟩

/-! ### The chains of one register gate -/

variable [NeZero s]

theorem two_mul_L_lt : 2 * g.L < N := by
  have := g.le; have := NeZero.ne s; omega

/-- The forward chain of `L` hops teleporting the site `a + t` to `a + t + 2L`. -/
def there (t : ℕ) : List (TeleportHop N) :=
  forwardChain (g.a + (t : Fin N)) g.L g.two_mul_L_lt

/-- The backward chain of `L` hops teleporting the site `a + t + 2L` to `a + t`. -/
def back (t : ℕ) : List (TeleportHop N) :=
  backwardChain (g.a + (t : Fin N)) g.L g.two_mul_L_lt

omit [NeZero s] in
private theorem add_add (t j : ℕ) :
    g.a + (t : Fin N) + (j : Fin N) = g.a + ((t + j : ℕ) : Fin N) := by
  rw [add_assoc, Nat.cast_add]

theorem allSites_there_subset (t : ℕ) :
    allSites (g.there t) ⊆ {i | ∃ j, t ≤ j ∧ j ≤ t + 2 * g.L ∧ i = g.a + (j : Fin N)} := by
  intro i hi
  obtain ⟨j, hj, rfl⟩ := allSites_forwardChain_subset _ _ _ hi
  exact ⟨t + j, by omega, by omega, g.add_add t j⟩

theorem allSites_back_subset (t : ℕ) :
    allSites (g.back t) ⊆ {i | ∃ j, t ≤ j ∧ j ≤ t + 2 * g.L ∧ i = g.a + (j : Fin N)} := by
  intro i hi
  obtain ⟨j, hj, rfl⟩ := allSites_backwardChain_subset _ _ _ hi
  exact ⟨t + j, by omega, by omega, g.add_add t j⟩

theorem allSites_there_subset_span {t : ℕ} (ht : t < s) : allSites (g.there t) ⊆ g.span := by
  intro i hi
  obtain ⟨j, -, hj, rfl⟩ := g.allSites_there_subset t hi
  exact ⟨j, by omega, rfl⟩

theorem allSites_back_subset_span {t : ℕ} (ht : t < s) : allSites (g.back t) ⊆ g.span := by
  intro i hi
  obtain ⟨j, -, hj, rfl⟩ := g.allSites_back_subset t hi
  exact ⟨j, by omega, rfl⟩

theorem pairSites_there_subset (t : ℕ) : TeleportHop.pairSites (g.there t) ⊆ g.zone (t + 1) := by
  intro i hi
  obtain ⟨j, hj1, hj2, rfl⟩ := pairSites_forwardChain_subset _ _ _ hi
  exact ⟨t + j, by omega, by omega, g.add_add t j⟩

theorem pairSites_back_subset (t : ℕ) : TeleportHop.pairSites (g.back t) ⊆ g.zone t := by
  intro i hi
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (pairSites_backwardChain_subset _ _ _ hi)
  exact ⟨t + j, by omega, by simp at hj; omega, g.add_add t j⟩

/-- The site `a + j` is fixed by the chains of the site `t` when `j < t` or `t + 2L < j`. -/
theorem sitePerm_there_apply_of_lt {t j : ℕ} (ht : t < s) (hj : j < 2 * g.L + 2 * s)
    (htj : j < t ∨ t + 2 * g.L < j) :
    sitePerm (g.there t) (g.a + (j : Fin N)) = g.a + (j : Fin N) := by
  rcases htj with htj | htj
  · refine sitePerm_apply_of_notMem fun hi => ?_
    obtain ⟨j', hj1, hj2, he⟩ := g.allSites_there_subset t hi
    have : j = j' := (g.add_eq_add_iff hj (by have := g.le; omega)).mp he
    omega
  · have hN := g.le
    have := (sitePerm_forwardChain (g.a + (t : Fin N)) g.L g.two_mul_L_lt).2 (j - t)
      (by omega) (by omega)
    rwa [g.add_add, Nat.add_sub_cancel' (by omega)] at this

theorem sitePerm_there_apply_self (t : ℕ) :
    sitePerm (g.there t) (g.a + (t : Fin N)) = g.a + ((t + 2 * g.L : ℕ) : Fin N) := by
  rw [there, (sitePerm_forwardChain _ _ _).1, g.add_add]

theorem sitePerm_back_eq_inv (t : ℕ) : sitePerm (g.back t) = (sitePerm (g.there t))⁻¹ :=
  sitePerm_backwardChain _ _ _

theorem sitePerm_back_apply_of_lt {t j : ℕ} (ht : t < s) (hj : j < 2 * g.L + 2 * s)
    (htj : j < t ∨ t + 2 * g.L < j) :
    sitePerm (g.back t) (g.a + (j : Fin N)) = g.a + (j : Fin N) := by
  rw [sitePerm_back_eq_inv, Equiv.Perm.inv_eq_iff_eq]
  exact (g.sitePerm_there_apply_of_lt ht hj htj).symm

theorem sitePerm_back_apply_self (t : ℕ) :
    sitePerm (g.back t) (g.a + ((t + 2 * g.L : ℕ) : Fin N)) = g.a + (t : Fin N) := by
  rw [sitePerm_back_eq_inv, Equiv.Perm.inv_eq_iff_eq, sitePerm_there_apply_self]

/-- The chain of the site `t` maps no site outside `zone (t + 1)` into `zone t`. -/
theorem sitePerm_there_notMem_zone {t : ℕ} (ht : t < s) {x : Fin N} (hx : x ∈ g.span)
    (hx' : x ∉ g.zone (t + 1)) : sitePerm (g.there t) x ∉ g.zone t := by
  obtain ⟨j, hj, rfl⟩ := hx
  rintro ⟨j', h1, h2, he⟩
  have hj' : j' < 2 * g.L + 2 * s := by omega
  rcases Nat.lt_trichotomy j t with hjt | rfl | hjt
  · rw [g.sitePerm_there_apply_of_lt ht hj (Or.inl hjt), g.add_eq_add_iff hj hj'] at he
    omega
  · rw [g.sitePerm_there_apply_self, g.add_eq_add_iff (by omega) hj'] at he
    omega
  · have : t + 2 * g.L < j := by
      by_contra h
      exact hx' ⟨j, by omega, by omega, rfl⟩
    rw [g.sitePerm_there_apply_of_lt ht hj (Or.inr this), g.add_eq_add_iff hj hj'] at he
    omega

/-- The backward chain of the site `t` maps no site outside `zone t` into `zone (t + 1)`. -/
theorem sitePerm_back_notMem_zone {t : ℕ} (ht : t < s) {x : Fin N} (hx : x ∈ g.span)
    (hx' : x ∉ g.zone t) : sitePerm (g.back t) x ∉ g.zone (t + 1) := by
  obtain ⟨j, hj, rfl⟩ := hx
  rintro ⟨j', h1, h2, he⟩
  have hj' : j' < 2 * g.L + 2 * s := by omega
  rcases Nat.lt_or_ge j t with hjt | hjt
  · rw [g.sitePerm_back_apply_of_lt ht hj (Or.inl hjt), g.add_eq_add_iff hj hj'] at he
    omega
  have hjt' : t + 2 * g.L ≤ j := by
    by_contra h
    exact hx' ⟨j, hjt, by omega, rfl⟩
  rcases hjt'.lt_or_eq with hjt' | rfl
  · rw [g.sitePerm_back_apply_of_lt ht hj (Or.inr hjt'), g.add_eq_add_iff hj hj'] at he
    omega
  · rw [g.sitePerm_back_apply_self, g.add_eq_add_iff (by omega) hj'] at he
    omega

/-! ### Layers of register gates -/

variable {g}

section Layer

variable {gs : List (RegisterGate d N s)}
  (hgs : gs.Pairwise fun g g' => Disjoint g.span g'.span)

/-- The forward chains of the site `t` of every gate. -/
def thereAll (gs : List (RegisterGate d N s)) (t : ℕ) : List (TeleportHop N) :=
  gs.flatMap fun g => g.there t

/-- The backward chains of the site `t` of every gate. -/
def backAll (gs : List (RegisterGate d N s)) (t : ℕ) : List (TeleportHop N) :=
  gs.flatMap fun g => g.back t

/-- The sites of the zones `zone t` of all the gates. -/
def zoneAll (gs : List (RegisterGate d N s)) (t : ℕ) : Set (Fin N) :=
  {i | ∃ g ∈ gs, i ∈ g.zone t}

include hgs in
theorem valid_thereAll {t : ℕ} (ht : t < s) : Valid (thereAll gs t) :=
  valid_flatMap (fun _ _ => valid_forwardChain _ _ _)
    (fun g _ => g.allSites_there_subset_span ht) hgs

include hgs in
theorem valid_backAll {t : ℕ} (ht : t < s) : Valid (backAll gs t) :=
  valid_flatMap (fun _ _ => valid_backwardChain _ _ _)
    (fun g _ => g.allSites_back_subset_span ht) hgs

include hgs in
/-- On the stretch of a gate, the forward chains of all the gates act as its own. -/
theorem sitePerm_thereAll_apply {t : ℕ} (ht : t < s) {g : RegisterGate d N s} (hg : g ∈ gs)
    {i : Fin N} (hi : i ∈ g.span) : sitePerm (thereAll gs t) i = sitePerm (g.there t) i :=
  sitePerm_flatMap_apply (fun g _ => g.allSites_there_subset_span ht) hgs hg hi

include hgs in
theorem sitePerm_backAll_apply {t : ℕ} (ht : t < s) {g : RegisterGate d N s} (hg : g ∈ gs)
    {i : Fin N} (hi : i ∈ g.span) : sitePerm (backAll gs t) i = sitePerm (g.back t) i :=
  sitePerm_flatMap_apply (fun g _ => g.allSites_back_subset_span ht) hgs hg hi

omit [NeZero N] in
/-- A permutation fixing every site outside `S` maps `S` into `S`. -/
private theorem perm_apply_mem {π : Equiv.Perm (Fin N)} {S : Set (Fin N)}
    (hπ : ∀ i ∉ S, π i = i) {i : Fin N} (hi : i ∈ S) : π i ∈ S := by
  by_contra h
  exact h (by rw [π.injective (hπ _ h)]; exact hi)

omit [NeZero s] in
include hgs in
private theorem notMem_zoneAll_of_mem_span {t : ℕ} (ht : t ≤ s) {g : RegisterGate d N s}
    (hg : g ∈ gs) {y : Fin N} (hy : y ∈ g.span) (hy' : y ∉ g.zone t) : y ∉ zoneAll gs t := by
  have : Std.Symm fun g g' : RegisterGate d N s => Disjoint g.span g'.span :=
    ⟨fun _ _ h => h.symm⟩
  rintro ⟨g', hg', hy''⟩
  by_cases hgg : g = g'
  · exact hy' (hgg ▸ hy'')
  · exact Set.disjoint_left.mp (hgs.forall hg hg' hgg) hy (g'.zone_subset_span ht hy'')

include hgs in
/-- The forward chains of the site `t` move the sites carrying `|0⟩` from the zones `t + 1` to
the zones `t`. -/
theorem isZeroOn_chainPerm_thereAll [NeZero d] {t : ℕ} (ht : t < s) {v : Cfg d N → ℂ}
    (hv : IsZeroOn (zoneAll gs (t + 1)) v) :
    IsZeroOn (zoneAll gs t) (chainPerm (thereAll gs t) *ᵥ v) := by
  refine hv.permMatrix_cfgPerm_mulVec_of_mapsTo fun x hx => ?_
  by_cases hxs : ∃ g ∈ gs, x ∈ g.span
  · obtain ⟨g, hg, hxg⟩ := hxs
    have hfix : ∀ i ∉ g.span, sitePerm (g.there t) i = i := fun i hi =>
      sitePerm_apply_of_notMem fun hi' => hi (g.allSites_there_subset_span ht hi')
    rw [sitePerm_thereAll_apply hgs ht hg hxg]
    exact notMem_zoneAll_of_mem_span hgs ht.le hg (perm_apply_mem hfix hxg)
      (g.sitePerm_there_notMem_zone ht hxg fun h => hx ⟨g, hg, h⟩)
  · simp only [not_exists, not_and] at hxs
    rw [thereAll, sitePerm_flatMap_apply_of_notMem (fun g _ => g.allSites_there_subset_span ht) hxs]
    rintro ⟨g, hg, hxg⟩
    exact hxs g hg (g.zone_subset_span ht.le hxg)

include hgs in
/-- The backward chains of the site `t` move the sites carrying `|0⟩` from the zones `t` to the
zones `t + 1`. -/
theorem isZeroOn_chainPerm_backAll [NeZero d] {t : ℕ} (ht : t < s) {v : Cfg d N → ℂ}
    (hv : IsZeroOn (zoneAll gs t) v) :
    IsZeroOn (zoneAll gs (t + 1)) (chainPerm (backAll gs t) *ᵥ v) := by
  refine hv.permMatrix_cfgPerm_mulVec_of_mapsTo fun x hx => ?_
  by_cases hxs : ∃ g ∈ gs, x ∈ g.span
  · obtain ⟨g, hg, hxg⟩ := hxs
    have hfix : ∀ i ∉ g.span, sitePerm (g.back t) i = i := fun i hi =>
      sitePerm_apply_of_notMem fun hi' => hi (g.allSites_back_subset_span ht hi')
    rw [sitePerm_backAll_apply hgs ht hg hxg]
    exact notMem_zoneAll_of_mem_span hgs (by omega) hg (perm_apply_mem hfix hxg)
      (g.sitePerm_back_notMem_zone ht hxg fun h => hx ⟨g, hg, h⟩)
  · simp only [not_exists, not_and] at hxs
    rw [backAll, sitePerm_flatMap_apply_of_notMem (fun g _ => g.allSites_back_subset_span ht) hxs]
    rintro ⟨g, hg, hxg⟩
    exact hxs g hg (g.zone_subset_span (by omega) hxg)

theorem pairSites_thereAll_subset (t : ℕ) : TeleportHop.pairSites (thereAll gs t) ⊆ zoneAll gs (t + 1) :=
  fun _ hi => by
    obtain ⟨g, hg, hi⟩ := mem_pairSites_flatMap.mp hi
    exact ⟨g, hg, g.pairSites_there_subset t hi⟩

theorem pairSites_backAll_subset (t : ℕ) : TeleportHop.pairSites (backAll gs t) ⊆ zoneAll gs t :=
  fun _ hi => by
    obtain ⟨g, hg, hi⟩ := mem_pairSites_flatMap.mp hi
    exact ⟨g, hg, g.pairSites_back_subset t hi⟩

include hgs in
/-- The backward chains invert the forward chains. -/
theorem sitePerm_backAll_eq_inv {t : ℕ} (ht : t < s) :
    sitePerm (backAll gs t) = (sitePerm (thereAll gs t))⁻¹ := by
  refine Equiv.ext fun i => ?_
  rw [Equiv.Perm.eq_inv_iff_eq]
  by_cases hi : ∃ g ∈ gs, i ∈ g.span
  · obtain ⟨g, hg, hi⟩ := hi
    have hfix : ∀ j ∉ g.span, sitePerm (g.back t) j = j := fun j hj =>
      sitePerm_apply_of_notMem fun hj' => hj (g.allSites_back_subset_span ht hj')
    have hmem := perm_apply_mem hfix hi
    rw [sitePerm_backAll_apply hgs ht hg hi, sitePerm_thereAll_apply hgs ht hg hmem,
      g.sitePerm_back_eq_inv]
    simp
  · simp only [not_exists, not_and] at hi
    rw [thereAll, backAll, sitePerm_flatMap_apply_of_notMem (fun g _ => g.allSites_back_subset_span ht) hi,
      sitePerm_flatMap_apply_of_notMem (fun g _ => g.allSites_there_subset_span ht) hi]

/-! ### The composite of the forward chains -/

/-- The permutation of sites of the forward chains of the sites `t - 1, …, 0`, the chain of
`t - 1` applied first. -/
def therePerm (gs : List (RegisterGate d N s)) : ℕ → Equiv.Perm (Fin N)
  | 0 => 1
  | t + 1 => therePerm gs t * sitePerm (thereAll gs t)

include hgs in
/-- The forward chains of the sites `t - 1, …, 0` move the site `a + u`, `u < t`, of the first
register to `a + 2L + u`, and fix the sites `a + j` with `t + 2L ≤ j`. -/
theorem therePerm_apply {g : RegisterGate d N s} (hg : g ∈ gs) :
    ∀ {t : ℕ}, t ≤ s →
      (∀ u < t, therePerm gs t (g.a + (u : Fin N)) = g.a + ((u + 2 * g.L : ℕ) : Fin N)) ∧
      ∀ j, t + 2 * g.L ≤ j → j < 2 * g.L + 2 * s →
        therePerm gs t (g.a + (j : Fin N)) = g.a + (j : Fin N)
  | 0, _ => ⟨fun u hu => absurd hu (Nat.not_lt_zero u), fun _ _ _ => rfl⟩
  | t + 1, ht => by
    obtain ⟨h1, h2⟩ := therePerm_apply hg (t := t) (by omega)
    have hspan : ∀ j < 2 * g.L + 2 * s, g.a + (j : Fin N) ∈ g.span := fun j hj => ⟨j, hj, rfl⟩
    refine ⟨fun u hu => ?_, fun j hj hjs => ?_⟩
    · rw [therePerm, Equiv.Perm.mul_apply,
        sitePerm_thereAll_apply hgs (by omega) hg (hspan u (by omega))]
      rcases (Nat.lt_succ_iff.mp hu).lt_or_eq with hu | rfl
      · rw [g.sitePerm_there_apply_of_lt (by omega) (by omega) (Or.inl hu), h1 u hu]
      · rw [g.sitePerm_there_apply_self, h2 _ le_rfl (by omega)]
    · rw [therePerm, Equiv.Perm.mul_apply,
        sitePerm_thereAll_apply hgs (by omega) hg (hspan j hjs),
        g.sitePerm_there_apply_of_lt (by omega) hjs (Or.inr (by omega)), h2 j (by omega) hjs]

include hgs in
/-- The forward chains of all the sites of the first register place it next to the second:
`π (sites t) = localSites t`. -/
theorem therePerm_comp_sites {g : RegisterGate d N s} (hg : g ∈ gs) :
    therePerm gs s ∘ g.sites = g.localSites := by
  funext t
  obtain ⟨h1, h2⟩ := therePerm_apply hgs hg (t := s) le_rfl
  simp only [Function.comp_apply, sites, offset, localSites]
  split_ifs with ht
  · rw [h1 _ ht, Nat.add_comm]
  · rw [h2 _ (by omega) (by omega)]
    congr 2
    omega

/-! ### The rounds -/

theorem _root_.MPSPreparation.TeleportHop.valid_nil : Valid ([] : List (TeleportHop N)) := trivial

variable [NeZero d]

/-- The rounds teleporting the sites `t - 1, …, 0` of the first registers, in this order. -/
noncomputable def thereRounds (gs : List (RegisterGate d N s))
    (hgs : gs.Pairwise fun g g' => Disjoint g.span g'.span) :
    (t : ℕ) → t ≤ s → List (MeasurementRound d N)
  | 0, _ => []
  | t + 1, ht => round [] (thereAll gs t) (valid_thereAll hgs (by omega)) ::
      thereRounds gs hgs t (by omega)

/-- The rounds teleporting the sites `0, …, t - 1` back, in this order. -/
noncomputable def backRounds (gs : List (RegisterGate d N s))
    (hgs : gs.Pairwise fun g g' => Disjoint g.span g'.span) :
    (t : ℕ) → t ≤ s → List (MeasurementRound d N)
  | 0, _ => []
  | t + 1, ht => backRounds gs hgs t (by omega) ++
      [round [] (backAll gs t) (valid_backAll hgs (by omega))]

/-- The rounds applying a layer of register gates: the forward teleportations, the circuit `Ls`
applying the gates `X` to the consecutive sites, and the backward teleportations.

Source: arXiv:2307.01696, paragraph "Tree-RG circuit with measurements". -/
noncomputable def rounds (Ls : List (Layer d N)) : List (MeasurementRound d N) :=
  thereRounds gs hgs s le_rfl ++ round Ls [] valid_nil :: backRounds gs hgs s le_rfl

theorem sum_depth_thereRounds : ∀ (t : ℕ) (ht : t ≤ s),
    ((thereRounds gs hgs t ht).map MeasurementRound.depth).sum = 2 * t
  | 0, _ => rfl
  | t + 1, ht => by
    rw [thereRounds, List.map_cons, List.sum_cons, sum_depth_thereRounds t, depth_round]
    simp only [List.length_nil]
    ring

theorem sum_depth_backRounds : ∀ (t : ℕ) (ht : t ≤ s),
    ((backRounds gs hgs t ht).map MeasurementRound.depth).sum = 2 * t
  | 0, _ => rfl
  | t + 1, ht => by
    rw [backRounds, List.map_append, List.sum_append, sum_depth_backRounds t]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, depth_round,
      List.length_nil]
    ring

/-- The rounds have depth `4s + K + 2` for a circuit `Ls` of `K` layers, whatever the distances
and the number of gates. -/
theorem sum_depth_rounds (Ls : List (Layer d N)) :
    ((rounds hgs Ls).map MeasurementRound.depth).sum = 4 * s + Ls.length + 2 := by
  rw [rounds, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
    sum_depth_thereRounds, sum_depth_backRounds, depth_round]
  ring

omit [NeZero d] in
/-- A round implementing a matrix is a sequence of rounds implementing it. -/
theorem _root_.MPSPreparation.MeasurementRound.IsImplementationOn.isRoundsImplementationOn
    {R : MeasurementRound d N} {E : Set (Cfg d N → ℂ)} {W : Matrix (Cfg d N) (Cfg d N) ℂ}
    (h : R.IsImplementationOn E W) : MeasurementRound.IsRoundsImplementationOn [R] E W := by
  intro v hv w hw
  obtain ⟨c, u, hu, rfl⟩ := h.exists_mem_outputs (Rs := []) hv hw
  rw [MeasurementRound.outputs_nil, Set.mem_singleton_iff] at hu
  exact ⟨c, by rw [hu]⟩

omit [NeZero d] in
/-- The permutation matrix of `therePerm`. -/
private theorem chainPerm_thereAll_mul (t : ℕ) :
    (cfgPerm (d := d) (therePerm gs t)).permMatrix ℂ * chainPerm (thereAll gs t) =
      (cfgPerm (therePerm gs (t + 1))).permMatrix ℂ := by
  rw [chainPerm, permMatrix_cfgPerm_mul_permMatrix_cfgPerm, therePerm]

theorem isRoundsImplementationOn_thereRounds : ∀ (t : ℕ) (ht : t ≤ s),
    MeasurementRound.IsRoundsImplementationOn (thereRounds gs hgs t ht)
      {v : Cfg d N → ℂ | IsZeroOn (zoneAll gs t) v}
        ((cfgPerm (therePerm gs t)).permMatrix ℂ) ∧
      ∀ v : Cfg d N → ℂ, IsZeroOn (zoneAll gs t) v →
        IsZeroOn (zoneAll gs 0) ((cfgPerm (therePerm gs t)).permMatrix ℂ *ᵥ v)
  | 0, _ => by
    refine ⟨?_, fun v hv => ?_⟩
    · simpa [thereRounds, therePerm, permMatrix_cfgPerm_one] using
        MeasurementRound.isRoundsImplementationOn_nil (d := d) (N := N)
          {v : Cfg d N → ℂ | IsZeroOn (zoneAll gs 0) v}
    · simpa [therePerm, permMatrix_cfgPerm_one] using hv
  | t + 1, ht => by
    obtain ⟨ih, ih'⟩ := isRoundsImplementationOn_thereRounds t (by omega)
    have h₁ := (isImplementationOn_round [] (valid_thereAll hgs (t := t) (by omega))
      (d := d)).isRoundsImplementationOn
    have hE : ∀ v ∈ {v : Cfg d N → ℂ | IsZeroOn (zoneAll gs (t + 1)) v},
        v ∈ {v | IsZeroOn (TeleportHop.pairSites (thereAll gs t)) (circuitOp [] *ᵥ v)} := fun v hv => by
      simpa [circuitOp] using (show IsZeroOn (zoneAll gs (t + 1)) v from hv).mono
        (pairSites_thereAll_subset t)
    have hmap : ∀ v ∈ {v : Cfg d N → ℂ | IsZeroOn (zoneAll gs (t + 1)) v},
        (chainPerm (thereAll gs t) * circuitOp []) *ᵥ v ∈ {v | IsZeroOn (zoneAll gs t) v} :=
      fun v hv => by
        simpa [circuitOp] using isZeroOn_chainPerm_thereAll hgs (by omega) hv
    refine ⟨?_, fun v hv => ?_⟩
    · have := (h₁.mono hE).append ih hmap
      simpa [thereRounds, circuitOp, chainPerm_thereAll_mul] using this
    · rw [← chainPerm_thereAll_mul, ← mulVec_mulVec]
      exact ih' _ (isZeroOn_chainPerm_thereAll hgs (by omega) hv)

omit [NeZero d] in
include hgs in
/-- The permutation of sites of the backward chains of the sites `0, …, t - 1`. -/
private theorem backRounds_perm {t : ℕ} (ht : t < s) :
    chainPerm (backAll gs t) * (cfgPerm (d := d) (therePerm gs t)⁻¹).permMatrix ℂ =
      (cfgPerm (therePerm gs (t + 1))⁻¹).permMatrix ℂ := by
  rw [chainPerm, permMatrix_cfgPerm_mul_permMatrix_cfgPerm, sitePerm_backAll_eq_inv hgs ht,
    therePerm, _root_.mul_inv_rev]

theorem isRoundsImplementationOn_backRounds : ∀ (t : ℕ) (ht : t ≤ s),
    MeasurementRound.IsRoundsImplementationOn (backRounds gs hgs t ht)
      {v : Cfg d N → ℂ | IsZeroOn (zoneAll gs 0) v}
        ((cfgPerm (therePerm gs t)⁻¹).permMatrix ℂ) ∧
      ∀ v : Cfg d N → ℂ, IsZeroOn (zoneAll gs 0) v →
        IsZeroOn (zoneAll gs t) ((cfgPerm (therePerm gs t)⁻¹).permMatrix ℂ *ᵥ v)
  | 0, _ => by
    refine ⟨?_, fun v hv => ?_⟩
    · simpa [backRounds, therePerm, permMatrix_cfgPerm_one] using
        MeasurementRound.isRoundsImplementationOn_nil (d := d) (N := N)
          {v : Cfg d N → ℂ | IsZeroOn (zoneAll gs 0) v}
    · simpa [therePerm, permMatrix_cfgPerm_one] using hv
  | t + 1, ht => by
    obtain ⟨ih, ih'⟩ := isRoundsImplementationOn_backRounds t (by omega)
    have h₁ := (isImplementationOn_round [] (valid_backAll hgs (t := t) (by omega))
      (d := d)).isRoundsImplementationOn
    have hE : ∀ v ∈ {v : Cfg d N → ℂ | IsZeroOn (zoneAll gs t) v},
        v ∈ {v | IsZeroOn (TeleportHop.pairSites (backAll gs t)) (circuitOp [] *ᵥ v)} := fun v hv => by
      simpa [circuitOp] using (show IsZeroOn (zoneAll gs t) v from hv).mono
        (pairSites_backAll_subset t)
    refine ⟨?_, fun v hv => ?_⟩
    · have := ih.append (h₁.mono hE) fun v hv => ih' v hv
      simpa [backRounds, circuitOp, backRounds_perm hgs (t := t) (by omega)] using this
    · rw [← backRounds_perm hgs (t := t) (by omega), ← mulVec_mulVec]
      exact isZeroOn_chainPerm_backAll hgs (by omega) (ih' v hv)

/-! ### The gates on the consecutive sites -/

/-- The gates `X` on the consecutive sites `a + 2L, …, a + 2L + 2s - 1` of every gate. -/
noncomputable def localProd (gs : List (RegisterGate d N s)) : Matrix (Cfg d N) (Cfg d N) ℂ :=
  (gs.map localOp).prod

omit [NeZero s] in
include hgs in
/-- The gates on the consecutive sites keep `|0⟩` at the zones `0`. -/
theorem isZeroOn_localProd_mulVec {v : Cfg d N → ℂ} (hv : IsZeroOn (zoneAll gs 0) v) :
    IsZeroOn (zoneAll gs 0) (localProd gs *ᵥ v) := by
  have : Std.Symm fun g g' : RegisterGate d N s => Disjoint g.span g'.span :=
    ⟨fun _ _ h => h.symm⟩
  refine hv.mulVec_of_mem_supportedOperators (T := {i | ∃ g ∈ gs, i ∈ Set.range g.localSites})
    ?_ (list_prod_mem_supportedOperators _ fun A hA => ?_)
  · rw [Set.disjoint_left]
    intro i hi hi'
    obtain ⟨g, hg, j, hj1, hj2, rfl⟩ := hi
    obtain ⟨g', hg', t, ht⟩ := hi'
    by_cases hgg : g = g'
    · subst hgg
      rw [localSites, g.add_eq_add_iff (by omega) (by omega)] at ht
      omega
    · exact Set.disjoint_left.mp (hgs.forall hg hg' hgg) (g.zone_subset_span (Nat.zero_le s)
        ⟨j, hj1, hj2, rfl⟩) (ht ▸ g'.localSites_mem_span t)
  · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hA
    refine supportedOperators_mono ?_ (embedOp_mem_supportedOperators g.localSites_injective g.X)
    exact fun i hi => ⟨g, hg, hi⟩

omit [NeZero d] in
include hgs in
/-- **The layer conjugated by the chains.** The backward chains, the gates on the consecutive
sites, and the forward chains compose to the product of the register gates. -/
theorem permMatrix_mul_localProd_mul_permMatrix :
    (cfgPerm (d := d) (therePerm gs s)⁻¹).permMatrix ℂ * localProd gs *
        (cfgPerm (therePerm gs s)).permMatrix ℂ = (gs.map op).prod := by
  set π := therePerm gs s
  have hPQ : (cfgPerm (d := d) π⁻¹).permMatrix ℂ * (cfgPerm π).permMatrix ℂ = 1 := by
    rw [permMatrix_cfgPerm_mul_permMatrix_cfgPerm, inv_mul_cancel, permMatrix_cfgPerm_one]
  have hQP : (cfgPerm (d := d) π).permMatrix ℂ * (cfgPerm π⁻¹).permMatrix ℂ = 1 := by
    rw [permMatrix_cfgPerm_mul_permMatrix_cfgPerm, mul_inv_cancel, permMatrix_cfgPerm_one]
  rw [localProd, mul_list_prod_mul_of_mul_eq_one hQP hPQ, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun g hg => ?_)
  have h := permMatrix_cfgPerm_mul_embedOp_mul (d := d) π⁻¹ g.localSites g.X
  rw [show (π⁻¹).symm = π from rfl] at h
  rw [Function.comp_apply, localOp, h, op]
  congr 1
  funext t
  have := congrFun (therePerm_comp_sites hgs hg) t
  simp only [Function.comp_apply] at this ⊢
  rw [← this]
  simp [π]

omit [NeZero s] in
/-- A vector has `|0⟩` at the zones `s` of all the gates exactly when it has `|0⟩` strictly
between the two registers of every gate. -/
theorem isZeroOn_zoneAll_iff {v : Cfg d N → ℂ} :
    IsZeroOn (zoneAll gs s) v ↔ ∀ g ∈ gs, IsZeroOn g.interior v :=
  ⟨fun h g hg => h.mono fun _ hi => ⟨g, hg, hi⟩,
    fun h y hy _ ⟨g, hg, hi⟩ => h g hg y hy _ hi⟩

/-- **A layer of register gates in constant depth with measurements.** For register gates on
pairwise disjoint stretches and a circuit `Ls` applying the gates `X` on the consecutive sites,
the rounds `rounds hgs Ls`, of depth `4s + K + 2` for `K` the number of layers of `Ls`
(`sum_depth_rounds`), implement the product of the register gates on the vectors with `|0⟩`
strictly between the two registers of every gate: whatever the outcomes, every output is a
scalar multiple of the product of the gates `X` at their registers applied to the input. No
outcome is post-selected.

Source: arXiv:2307.01696, paragraph "Tree-RG circuit with measurements" ("Isometries ... act on
a constant number of sites which, although spatially separated, can be teleported at
neighboring registers with a constant overhead ... Therefore every isometry ... takes constant
time using measurement"). -/
theorem isRoundsImplementationOn_rounds {Ls : List (Layer d N)}
    (hLs : circuitOp Ls = localProd gs) :
    MeasurementRound.IsRoundsImplementationOn (rounds hgs Ls)
      {v | ∀ g ∈ gs, IsZeroOn g.interior v} (gs.map op).prod := by
  obtain ⟨h₁, h₁'⟩ := isRoundsImplementationOn_thereRounds hgs s le_rfl
  obtain ⟨h₃, -⟩ := isRoundsImplementationOn_backRounds hgs s le_rfl
  have h₂ : MeasurementRound.IsRoundsImplementationOn [round Ls [] valid_nil]
      {v : Cfg d N → ℂ | IsZeroOn (zoneAll gs 0) v} (localProd gs) := by
    have := (isImplementationOn_round (d := d) Ls (valid_nil (N := N))).isRoundsImplementationOn
    rw [chainPerm_nil, Matrix.one_mul, hLs] at this
    exact this.mono fun v _ => fun _ _ _ h => h.elim
  have h₂₃ := h₂.append h₃ fun v hv => isZeroOn_localProd_mulVec hgs hv
  have := h₁.append h₂₃ h₁'
  rw [← permMatrix_mul_localProd_mul_permMatrix hgs]
  refine this.mono fun v hv => ?_
  exact isZeroOn_zoneAll_iff.mpr hv

omit [NeZero d] [NeZero s] in
include hgs in
/-- If every gate `X` is a product of at most `K` gates on neighbouring sites, the gates on the
consecutive sites form a circuit of depth `K`. -/
theorem isCircuitOn_localProd {K : ℕ} (hK : ∀ g ∈ gs, IsPairProduct d (s + s) K g.X) :
    IsCircuitOn {i | ∃ g ∈ gs, i ∈ g.span} K (localProd gs) := by
  induction gs with
  | nil =>
    simpa [localProd] using IsCircuitOn.one (d := d) (N := N)
      {i | ∃ g ∈ ([] : List (RegisterGate d N s)), i ∈ g.span} K
  | cons g gs ih =>
    rw [List.pairwise_cons] at hgs
    have h₁ := ((hK g List.mem_cons_self).isCircuitOn g.localSites_injective
      fun t t' h => g.localSites_succ t t' h).mono_set
        (show Set.range g.localSites ⊆ g.span by rintro _ ⟨t, rfl⟩; exact g.localSites_mem_span t)
    have h₂ := ih hgs.2 fun g' hg' => hK g' (List.mem_cons_of_mem _ hg')
    have hdisj : Disjoint g.span {i | ∃ g ∈ gs, i ∈ g.span} := by
      rw [Set.disjoint_left]
      rintro i hi ⟨g', hg', hi'⟩
      exact Set.disjoint_left.mp (hgs.1 g' hg') hi hi'
    refine (h₁.par hdisj h₂).mono_set fun i hi => ?_
    rcases hi with hi | ⟨g', hg', hi⟩
    · exact ⟨g, List.mem_cons_self, hi⟩
    · exact ⟨g', List.mem_cons_of_mem _ hg', hi⟩

include hgs in
/-- **A layer of register gates in depth `4s + K + 2` with measurements.** If every gate `X` of
a list of register gates on pairwise disjoint stretches is a product of at most `K` gates on
neighbouring sites, some sequence of measurement rounds of total depth `4s + K + 2` implements
the product of the register gates on the vectors with `|0⟩` strictly between the two registers
of every gate.

Source: arXiv:2307.01696, paragraph "Tree-RG circuit with measurements". -/
theorem exists_rounds {K : ℕ} (hK : ∀ g ∈ gs, IsPairProduct d (s + s) K g.X) :
    ∃ Rs : List (MeasurementRound d N), (Rs.map MeasurementRound.depth).sum = 4 * s + K + 2 ∧
      MeasurementRound.IsRoundsImplementationOn Rs {v | ∀ g ∈ gs, IsZeroOn g.interior v}
        (gs.map op).prod := by
  obtain ⟨Ls, hlen, -, hLs⟩ := isCircuitOn_localProd hgs hK
  exact ⟨rounds hgs Ls, by rw [sum_depth_rounds, hlen],
    isRoundsImplementationOn_rounds hgs hLs.symm⟩

end Layer

end RegisterGate

end MPSPreparation
