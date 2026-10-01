/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.TeleportationRound

/-!
# Teleportation chains between distant sites

The tree-RG circuit of arXiv:2307.01696, eq. (16), applies isometries to registers that are far
apart on the chain. The paragraph "Tree-RG circuit with measurements" observes that these
registers "can be teleported at neighboring registers with a constant overhead". This file
provides the chains of hops that do so, in the measurement-round model
(`MPSPreparation.MeasurementRound`):

* for any valid lists of hops `there` and `back` and any layer of gates `G`, the round
  teleporting along `there`, followed by the round applying `G` and teleporting along `back`,
  acts on every outcome as `P_back G P_there` up to a scalar
  (`MPSPreparation.TeleportHop.exists_eq_smul_of_mem_outputs_conj`); the two rounds have depth
  `2` and `3`, whatever the distances;
* the forward chain of `L` hops from `a` to `a + 2L` and the backward chain from `a + 2L` to
  `a`, whose permutations of sites are inverse to each other
  (`MPSPreparation.TeleportHop.sitePerm_backwardChain`), and which leave `|0⟩` at the sites
  `a, …, a + 2L - 1` when the sites `a + 1, …, a + 2L` carry `|0⟩`
  (`MPSPreparation.TeleportHop.isZeroOn_chainPerm_forwardChain`).

The gates between distant sites built from these chains are in
`TNLean.MPS.Preparation.LongRangeGates`.

## Main definitions

* `MPSPreparation.TeleportHop.sitePerm` — the permutation of sites of a list of hops.
* `MPSPreparation.TeleportHop.chainHop`, `MPSPreparation.TeleportHop.chainHopBack`,
  `MPSPreparation.TeleportHop.forwardChain`, `MPSPreparation.TeleportHop.backwardChain`.

## Main results

* `MPSPreparation.permMatrix_cfgPerm_mul_embedOp_mul` — relabelling the sites of an embedded
  operator.
* `MPSPreparation.TeleportHop.exists_eq_smul_of_mem_outputs_conj`.
* `MPSPreparation.TeleportHop.sitePerm_forwardChain`,
  `MPSPreparation.TeleportHop.sitePerm_backwardChain`,
  `MPSPreparation.TeleportHop.isZeroOn_chainPerm_forwardChain`.

## References

* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), eq. (16) and paragraph "Tree-RG circuit with
  measurements".
-/

open Matrix MPSTensor
open scoped BigOperators

namespace MPSPreparation

variable {d N : ℕ}

/-! ### Permutations of sites -/

theorem permMatrix_cfgPerm_mul_permMatrix_cfgPerm (π σ : Equiv.Perm (Fin N)) :
    (cfgPerm (d := d) π).permMatrix ℂ * (cfgPerm σ).permMatrix ℂ =
      (cfgPerm (π * σ)).permMatrix ℂ := by
  rw [← Matrix.permMatrix_mul]
  congr 1

theorem permMatrix_cfgPerm_one : (cfgPerm (d := d) (1 : Equiv.Perm (Fin N))).permMatrix ℂ = 1 := by
  have : cfgPerm (d := d) (1 : Equiv.Perm (Fin N)) = 1 := by ext x i; rfl
  rw [this, Matrix.permMatrix_one]

/-- **Relabelling the sites of an embedded operator.** Conjugating `X` at the sites `e` by the
permutation of configurations `x ↦ x ∘ σ` places `X` at the sites `σ ∘ e`. -/
theorem permMatrix_cfgPerm_mul_embedOp_mul {m : ℕ} (σ : Equiv.Perm (Fin N)) (e : Fin m → Fin N)
    (X : Matrix (Cfg d m) (Cfg d m) ℂ) :
    (cfgPerm σ).permMatrix ℂ * embedOp e X * (cfgPerm σ.symm).permMatrix ℂ =
      embedOp (σ ∘ e) X := by
  classical
  ext x y
  simp only [mul_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.sum_eq_single ((cfgPerm σ.symm).symm y), ite_eq_left (Equiv.apply_symm_apply _ _)]
  rotate_left
  · intro w _ hw
    rw [ite_eq_right fun h => hw (by rw [← h, Equiv.symm_apply_apply])]
  · simp
  rw [embedOp_apply, embedOp_apply]
  have hy : (cfgPerm σ.symm).symm y = y ∘ σ := by
    funext i; simp [cfgPerm]
  rw [hy]
  have hag : AgreeOff e (cfgPerm σ x) (y ∘ σ) ↔ AgreeOff (σ ∘ e) x y := by
    constructor
    · intro h i hi
      have := h (σ.symm i) fun j hj => hi j (by rw [Function.comp_apply, hj]; simp)
      simpa [cfgPerm] using this
    · intro h i hi
      exact h (σ i) fun j hj => hi j (σ.injective hj)
  by_cases h : AgreeOff (σ ∘ e) x y
  · rw [ite_eq_left (hag.mpr h), ite_eq_left h]; rfl
  · rw [ite_eq_right (fun h' => h (hag.mp h')), ite_eq_right h]

variable [NeZero d]

/-- Permuting the sites moves the sites carrying `|0⟩`. -/
theorem IsZeroOn.permMatrix_cfgPerm_mulVec_image {S : Set (Fin N)} {v : Cfg d N → ℂ}
    (h : IsZeroOn S v) (π : Equiv.Perm (Fin N)) :
    IsZeroOn (π '' S) ((cfgPerm π).permMatrix ℂ *ᵥ v) := by
  rintro y hy _ ⟨i, hi, rfl⟩
  rw [permMatrix_mulVec] at hy
  exact h _ hy i hi

private theorem isZeroOn_mulVec_of_finset {S : Finset (Fin N)} {v : Cfg d N → ℂ}
    (h : IsZeroOn (S : Set (Fin N)) v) {T : Set (Fin N)} (hST : Disjoint (S : Set (Fin N)) T)
    {A : Matrix (Cfg d N) (Cfg d N) ℂ} (hA : A ∈ supportedOperators d T) :
    IsZeroOn (S : Set (Fin N)) (A *ᵥ v) := by
  have hP : ∀ u : Cfg d N → ℂ, IsZeroOn (S : Set (Fin N)) u ↔ ctrlProj S 0 *ᵥ u = u := by
    intro u
    constructor
    · intro hu
      funext x
      rw [ctrlProj, mulVec_diagonal]
      by_cases hx : ∀ i ∈ S, x i = (0 : Cfg d N) i
      · rw [ite_eq_left hx, one_mul]
      · rw [ite_eq_right hx, zero_mul]
        by_contra h0
        exact hx fun i hi => hu x (Ne.symm h0) i hi
    · intro hu x hx i hi
      rw [← hu, ctrlProj, mulVec_diagonal] at hx
      by_contra hne
      exact hx (by rw [ite_eq_right fun h' => hne (h' i hi), zero_mul])
  have hc : Commute (ctrlProj S (0 : Cfg d N)) A :=
    commute_of_mem_supportedOperators hST (ctrlProj_mem_supportedOperators S 0) hA
  rw [hP] at h ⊢
  rw [mulVec_mulVec, hc.eq, ← mulVec_mulVec, h]

/-- An operator acting on sites outside `S` keeps `|0⟩` at the sites of `S`. -/
theorem IsZeroOn.mulVec_of_mem_supportedOperators {S : Set (Fin N)} {v : Cfg d N → ℂ}
    (h : IsZeroOn S v) {T : Set (Fin N)} (hST : Disjoint S T)
    {A : Matrix (Cfg d N) (Cfg d N) ℂ} (hA : A ∈ supportedOperators d T) :
    IsZeroOn S (A *ᵥ v) := by
  classical
  simpa using isZeroOn_mulVec_of_finset (S := S.toFinset) (by simpa using h)
    (by simpa using hST) hA

variable [NeZero N]

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

/-! ### Permutations of sites of a list of hops -/

/-- The permutation of sites of a list of hops: the product of the exchanges of the sites `c`
and `f`, the most recent leftmost. -/
def sitePerm : List (TeleportHop N) → Equiv.Perm (Fin N)
  | [] => 1
  | h :: hs => Equiv.swap h.c h.f * sitePerm hs

omit [NeZero d] in
theorem chainPerm_eq (hs : List (TeleportHop N)) :
    chainPerm (d := d) hs = (cfgPerm (sitePerm hs)).permMatrix ℂ := by
  induction hs with
  | nil => exact permMatrix_cfgPerm_one.symm
  | cons h hs ih =>
    rw [chainPerm, ih, swapPerm, permMatrix_cfgPerm_mul_permMatrix_cfgPerm, sitePerm]

/-! ### Two rounds around a layer of gates -/

/-- **Gates conjugated by teleportation.** Let `there` and `back` be valid lists of hops and `G`
a layer of gates, and let `v` carry `|0⟩` at the sites `e`, `f` of `there`, with `G P_there v`
carrying `|0⟩` at the sites `e`, `f` of `back`. Then every output of the round teleporting along
`there`, followed by the round applying `G` and teleporting along `back`, is a scalar multiple of
`P_back G P_there v`. The rounds have depth `2` and `3`.

Source: arXiv:2307.01696, paragraph "Tree-RG circuit with measurements". -/
theorem exists_eq_smul_of_mem_outputs_conj {there back : List (TeleportHop N)}
    (hthere : Valid there) (hback : Valid back) (G : Layer d N) {v : Cfg d N → ℂ}
    (hv : IsZeroOn (pairSites there) v)
    (hGv : IsZeroOn (pairSites back) (G.op *ᵥ (chainPerm there *ᵥ v)))
    {w : Cfg d N → ℂ}
    (hw : w ∈ MeasurementRound.outputs [round [] there hthere, round [G] back hback] v) :
    ∃ c : ℂ, w = c • ((chainPerm back * G.op * chainPerm there) *ᵥ v) := by
  have h₁ := isImplementationOn_round (d := d) [] hthere
  have h₂ := isImplementationOn_round [G] hback
  obtain ⟨c, u, hu, rfl⟩ := h₁.exists_mem_outputs (by simpa [circuitOp] using hv) hw
  have hGv' : (chainPerm there * circuitOp []) *ᵥ v ∈
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
  bond_k₁ := by rw [bond, add_natCast_succ]
  bond_k₂ := by rw [bond, add_natCast_succ]
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
  bond_k₁ := by rw [bond, add_natCast_succ, Set.pair_comm]
  bond_k₂ := by rw [bond, add_natCast_succ, Set.pair_comm]
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
  | cons h hs ih => rw [List.cons_append, pairSites, pairSites, ih, Set.union_assoc]

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
    simp only [After, sites, chainHop, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
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
    simp only [After, sites, chainHopBack, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
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
    pairSites (forwardChain a L hL) ⊆ {i | ∃ j, 1 ≤ j ∧ j ≤ 2 * L ∧ i = a + (j : Fin N)} := by
  induction L with
  | zero => simp [forwardChain, pairSites]
  | succ L ih =>
    rintro i ((rfl | rfl) | hi)
    · exact ⟨2 * L + 1, by omega, by omega, rfl⟩
    · exact ⟨2 * L + 2, by omega, by omega, rfl⟩
    · obtain ⟨j, hj1, hj2, rfl⟩ := ih (by omega) hi
      exact ⟨j, hj1, by omega, rfl⟩

/-- The sites `e` and `f` of the backward chain are the sites `a + j`, `j < 2L`. -/
theorem pairSites_backwardChain_subset (a : Fin N) (L : ℕ) (hL : 2 * L < N) :
    pairSites (backwardChain a L hL) ⊆
      ((Finset.range (2 * L)).image fun j : ℕ => a + (j : Fin N) : Finset (Fin N)) := by
  induction L with
  | zero => simp [backwardChain, pairSites]
  | succ L ih =>
    rw [backwardChain, pairSites_append]
    rintro i (hi | ((rfl | rfl) | hi))
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (ih (by omega) hi)
      exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by simp at hj; omega), rfl⟩
    · exact Finset.mem_image.mpr ⟨2 * L + 1, Finset.mem_range.mpr (by omega), rfl⟩
    · exact Finset.mem_image.mpr ⟨2 * L, Finset.mem_range.mpr (by omega), rfl⟩
    · simp [pairSites] at hi

theorem allSites_forwardChain_subset (a : Fin N) (L : ℕ) (hL : 2 * L < N) :
    allSites (forwardChain a L hL) ⊆ {i | ∃ j ≤ 2 * L, i = a + (j : Fin N)} := by
  intro i hi
  obtain ⟨h, hh, hi⟩ := mem_allSites.mp hi
  obtain ⟨k, hk, hk', rfl⟩ := mem_forwardChain hh
  simp only [sites, chainHop, Set.mem_insert_iff, Set.mem_singleton_iff] at hi
  rcases hi with rfl | rfl | rfl
  · exact ⟨2 * k, by omega, rfl⟩
  · exact ⟨2 * k + 1, by omega, rfl⟩
  · exact ⟨2 * k + 2, by omega, rfl⟩

/-- After the forward chain, a vector with `|0⟩` at the sites `a + j`, `1 ≤ j ≤ 2L`, has `|0⟩` at
the sites `a + j`, `j < 2L`. -/
theorem isZeroOn_chainPerm_forwardChain (a : Fin N) (L : ℕ) (hL : 2 * L < N)
    {v : Cfg d N → ℂ} (hv : IsZeroOn {i | ∃ j, 1 ≤ j ∧ j ≤ 2 * L ∧ i = a + (j : Fin N)} v) :
    IsZeroOn {i | ∃ j < 2 * L, i = a + (j : Fin N)} (chainPerm (forwardChain a L hL) *ᵥ v) := by
  induction L generalizing v with
  | zero => intro y _ i ⟨j, hj, _⟩; omega
  | succ L ih =>
    have hv' : IsZeroOn {i | ∃ j, 1 ≤ j ∧ j ≤ 2 * L ∧ i = a + (j : Fin N)} v :=
      hv.mono fun i ⟨j, h1, h2, hi⟩ => ⟨j, h1, by omega, hi⟩
    have hrest : IsZeroOn {a + ((2 * L + 1 : ℕ) : Fin N), a + ((2 * L + 2 : ℕ) : Fin N)} v :=
      hv.mono (by rintro i (rfl | rfl) <;> exact ⟨_, by omega, by omega, rfl⟩)
    have hrest' := hrest.chainPerm_mulVec (hs := forwardChain a L (by omega)) (by
      rw [Set.disjoint_left]
      rintro i hi hi'
      obtain ⟨j, hj, rfl⟩ := allSites_forwardChain_subset a L (by omega) hi'
      rcases hi with hi | hi
      · exact add_natCast_ne a (by omega) (by omega) (by omega) hi
      · exact add_natCast_ne a (by omega) (by omega) (by omega) hi)
    have hall : IsZeroOn ({i | ∃ j < 2 * L, i = a + (j : Fin N)} ∪
        {a + ((2 * L + 1 : ℕ) : Fin N), a + ((2 * L + 2 : ℕ) : Fin N)})
        (chainPerm (forwardChain a L (by omega)) *ᵥ v) :=
      fun y hy i hi => hi.elim (ih (by omega) hv' y hy i) (hrest' y hy i)
    rw [forwardChain, chainPerm, ← mulVec_mulVec, swapPerm]
    refine (hall.permMatrix_cfgPerm_mulVec_image _).mono ?_
    rintro i ⟨j, hj, rfl⟩
    simp only [chainHop]
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

end MPSPreparation
