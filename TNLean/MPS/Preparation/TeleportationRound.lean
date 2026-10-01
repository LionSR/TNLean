/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.QuditTeleportation

/-!
# Teleportation along chains of hops in one round

A list of hops (`MPSPreparation.TeleportHop`), the most recent first, is *valid* when every hop
`h` meets the hops `hs` before it only through its site `c`, which may be the site `f` of an
earlier hop: the sites `e` and `f` of `h` are not sites of `hs`, and its site `c` is not a site
`c` or `e` of `hs`. The hops then form chains `c₀ → f₀ = c₁ → f₁ = c₂ → ⋯`, any number of them.

The *teleportation round* of a valid list, after a given circuit, applies the circuit, the first
layers of all hops at once, the second layers of all hops at once, measures the sites `c` and `e`
of every hop, and corrects by the inverse of the single-site unitaries that the hops leave. On
the vectors with `|0⟩` at the sites `e` and `f` of every hop after the given circuit, it acts, for
every outcome, as `d^{-H}` times the permutation of sites `S_{h_1} ⋯ S_{h_H}`, `S_h` exchanging the
sites `c` and `f` of `h` (`MPSPreparation.TeleportHop.isImplementationOn_round`). The two layers
have depth `2` whatever the lengths of the chains: this is the constant-depth teleportation of
arXiv:2307.01696, paragraph "Tree-RG circuit with measurements".

## Main definitions

* `MPSPreparation.layerOfList` — the layer of gates on disjoint pairs given by a list.
* `MPSPreparation.TeleportHop.Valid`, `MPSPreparation.TeleportHop.pairSites`,
  `MPSPreparation.TeleportHop.chainPerm`.
* `MPSPreparation.TeleportHop.round`.

## Main results

* `MPSPreparation.TeleportHop.chainPre_mulVec` — the chains of hops before the correction.
* `MPSPreparation.TeleportHop.isImplementationOn_round`.

## References

* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), paragraph "Tree-RG circuit with measurements".
-/

open Matrix MPSTensor
open scoped BigOperators

namespace MPSPreparation

variable {d N : ℕ} [NeZero N]

/-! ### Layers given by lists -/

section LayerOfList

variable {ι : Type*} (l : List ι) (key : ι → Fin N) (G : ι → Matrix (Cfg d N) (Cfg d N) ℂ)
  (hl : l.Pairwise fun i j => Disjoint (bond (key i)) (bond (key j)))
  (hu : ∀ i ∈ l, G i ∈ unitary (Matrix (Cfg d N) (Cfg d N) ℂ))
  (hs : ∀ i ∈ l, G i ∈ supportedOperators d (bond (key i)))

private theorem key_mem_bond (k : Fin N) : k ∈ bond k := Or.inl rfl

include hl in
private theorem eq_of_key_eq {i j : ι} (hi : i ∈ l) (hj : j ∈ l) (h : key i = key j) : i = j := by
  by_contra hne
  have : Std.Symm fun i j : ι => Disjoint (bond (key i)) (bond (key j)) :=
    ⟨fun _ _ h => h.symm⟩
  exact Set.disjoint_left.mp (hl.forall hi hj hne) (key_mem_bond (key i)) (h ▸ key_mem_bond _)

/-- The gate of `layerOfList` on the pair `{k, k + 1}`. -/
noncomputable def layerOfListGate (k : Fin N) : Matrix (Cfg d N) (Cfg d N) ℂ := by
  classical
  exact if h : ∃ i ∈ l, key i = k then G h.choose else 1

include hl in
theorem layerOfListGate_key {i : ι} (hi : i ∈ l) : layerOfListGate l key G (key i) = G i := by
  classical
  have h : ∃ j ∈ l, key j = key i := ⟨i, hi, rfl⟩
  rw [layerOfListGate, dif_pos h]
  rw [eq_of_key_eq l key hl h.choose_spec.1 hi h.choose_spec.2]

/-- The layer of the gates `G i` on the pairs `{key i, key i + 1}` for `i` in the list `l`, the
pairs being pairwise disjoint. -/
noncomputable def layerOfList : Layer d N where
  bonds := by classical exact (l.map key).toFinset
  gate := layerOfListGate l key G
  gate_mem_unitary k hk := by
    classical
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hk)
    rw [layerOfListGate_key l key G hl hi]
    exact hu i hi
  gate_mem_supportedOperators k hk := by
    classical
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hk)
    rw [layerOfListGate_key l key G hl hi]
    exact hs i hi
  pairwiseDisjoint := by
    classical
    intro k hk k' hk' hkk'
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hk)
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hk')
    have : Std.Symm fun i j : ι => Disjoint (bond (key i)) (bond (key j)) :=
      ⟨fun _ _ h => h.symm⟩
    exact hl.forall hi hj fun h => hkk' (h ▸ rfl)

include hl in
/-- The operator of `layerOfList` is the product of its gates along the list. -/
theorem layerOfList_op : (layerOfList l key G hl hu hs).op = (l.map G).prod := by
  classical
  have hnodup : (l.map key).Nodup := by
    exact List.Pairwise.map _ (fun a b h hab =>
      Set.disjoint_left.mp h (key_mem_bond (key a)) (hab ▸ key_mem_bond (key b))) hl
  rw [Layer.op, Layer.partialOp]
  erw [Finset.noncommProd_toFinset (l.map key) (layerOfListGate l key G) _ hnodup]
  rw [List.map_map]
  exact congrArg List.prod (List.map_congr_left fun i hi => layerOfListGate_key l key G hl hi)

end LayerOfList

/-- A product of operators acting on `S` acts on `S`. -/
theorem list_prod_mem_supportedOperators {S : Set (Fin N)}
    (l : List (Matrix (Cfg d N) (Cfg d N) ℂ)) (hl : ∀ A ∈ l, A ∈ supportedOperators d S) :
    l.prod ∈ supportedOperators d S := by
  induction l with
  | nil => exact one_mem_supportedOperators S
  | cons A l ih =>
    rw [List.prod_cons]
    exact mul_mem_supportedOperators (hl A (List.mem_cons_self ..))
      (ih fun B hB => hl B (List.mem_cons_of_mem _ hB))

/-! ### Lists of hops -/

namespace TeleportHop

/-- The sites `c`, `e`, `f` of a hop. -/
def sites (h : TeleportHop N) : Set (Fin N) := {h.c, h.e, h.f}

/-- The sites of all hops of a list. -/
def allSites : List (TeleportHop N) → Set (Fin N)
  | [] => ∅
  | h :: hs => h.sites ∪ allSites hs

/-- The sites `e` and `f` of all hops of a list, which carry `|0⟩` before the round. -/
def pairSites : List (TeleportHop N) → Set (Fin N)
  | [] => ∅
  | h :: hs => {h.e, h.f} ∪ pairSites hs

/-- The sites `c` and `e` of all hops of a list, measured in the round. -/
def measuredSites : List (TeleportHop N) → Finset (Fin N)
  | [] => ∅
  | h :: hs => insert h.c (insert h.e (measuredSites hs))

/-- A list of hops, the most recent first, is *valid* when every hop meets the earlier ones only
through its site `c`, which is not a site `c` or `e` of an earlier hop. -/
def Valid : List (TeleportHop N) → Prop
  | [] => True
  | h :: hs => Valid hs ∧ h.e ∉ allSites hs ∧ h.f ∉ allSites hs ∧ ∀ h' ∈ hs, h.c ≠ h'.c ∧ h.c ≠ h'.e

theorem mem_allSites {hs : List (TeleportHop N)} {i : Fin N} :
    i ∈ allSites hs ↔ ∃ h ∈ hs, i ∈ h.sites := by
  induction hs with
  | nil => simp [allSites]
  | cons h hs ih => simp [allSites, ih]

theorem pairSites_subset_allSites (hs : List (TeleportHop N)) : pairSites hs ⊆ allSites hs := by
  induction hs with
  | nil => exact le_rfl
  | cons h hs ih =>
    refine Set.union_subset_union ?_ ih
    rintro i (rfl | rfl)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

theorem coe_measuredSites_subset_allSites (hs : List (TeleportHop N)) :
    (measuredSites hs : Set (Fin N)) ⊆ allSites hs := by
  induction hs with
  | nil => simp [measuredSites]
  | cons h hs ih =>
    intro i hi
    simp only [measuredSites, Finset.coe_insert, Set.mem_insert_iff] at hi
    rcases hi with rfl | rfl | hi
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inr (Or.inl rfl))
    · exact Or.inr (ih hi)

/-- The sites `c` and `e` of the hops of a valid list are not the sites `c`, `e`, `f` of a later
hop, except through its site `c`. -/
theorem disjoint_measuredSites {h : TeleportHop N} {hs : List (TeleportHop N)}
    (hv : Valid (h :: hs)) : Disjoint (measuredSites hs : Set (Fin N)) h.sites := by
  rw [Set.disjoint_right]
  rintro i (rfl | rfl | rfl) hi
  · obtain ⟨-, -, -, hc⟩ := hv
    induction hs with
    | nil => simp [measuredSites] at hi
    | cons h' hs ih =>
      simp only [measuredSites, Finset.coe_insert, Set.mem_insert_iff] at hi
      rcases hi with hi | hi | hi
      · exact (hc h' (List.mem_cons_self ..)).1 hi
      · exact (hc h' (List.mem_cons_self ..)).2 hi
      · exact ih hi fun h'' hh => hc h'' (List.mem_cons_of_mem _ hh)
  · exact hv.2.1 (coe_measuredSites_subset_allSites hs hi)
  · exact hv.2.2.1 (coe_measuredSites_subset_allSites hs hi)

/-! ### The layers of a list of hops -/

theorem pairwise_disjoint_one : ∀ {hs : List (TeleportHop N)}, Valid hs →
    hs.Pairwise fun h h' => Disjoint (bond h.k₁) (bond h'.k₁)
  | [], _ => List.Pairwise.nil
  | h :: hs, ⟨hv, he, hf, _⟩ => by
    refine List.Pairwise.cons (fun h' hh' => ?_) (pairwise_disjoint_one hv)
    rw [h.bond_k₁, h'.bond_k₁, Set.disjoint_left]
    rintro i (rfl | rfl) hi
    · exact he (mem_allSites.mpr ⟨h', hh', by simp only [sites, Set.mem_insert_iff, Set.mem_singleton_iff] at hi ⊢; tauto⟩)
    · exact hf (mem_allSites.mpr ⟨h', hh', by simp only [sites, Set.mem_insert_iff, Set.mem_singleton_iff] at hi ⊢; tauto⟩)

theorem pairwise_disjoint_two : ∀ {hs : List (TeleportHop N)}, Valid hs →
    hs.Pairwise fun h h' => Disjoint (bond h.k₂) (bond h'.k₂)
  | [], _ => List.Pairwise.nil
  | h :: hs, ⟨hv, he, _, hc⟩ => by
    refine List.Pairwise.cons (fun h' hh' => ?_) (pairwise_disjoint_two hv)
    rw [h.bond_k₂, h'.bond_k₂, Set.disjoint_left]
    rintro i (rfl | rfl) hi
    · rcases hi with hi | hi
      · exact (hc h' hh').1 hi
      · exact (hc h' hh').2 hi
    · exact he (mem_allSites.mpr ⟨h', hh', by simp only [sites, Set.mem_insert_iff, Set.mem_singleton_iff] at hi ⊢; tauto⟩)

variable [NeZero d]

/-- The first layer of a valid list of hops: the gates preparing the entangled pairs. -/
noncomputable def layerOne (hs : List (TeleportHop N)) (hv : Valid hs) : Layer d N :=
  layerOfList hs TeleportHop.k₁ TeleportHop.gate₁ (pairwise_disjoint_one hv)
    (fun h _ => h.gate₁_mem_unitary) fun h _ => h.bond_k₁ ▸ h.gate₁_mem_supportedOperators

/-- The second layer of a valid list of hops: the gates of the measurements in the basis of
maximally entangled pairs. -/
noncomputable def layerTwo (hs : List (TeleportHop N)) (hv : Valid hs) : Layer d N :=
  layerOfList hs TeleportHop.k₂ TeleportHop.gate₂ (pairwise_disjoint_two hv)
    (fun h _ => h.gate₂_mem_unitary) fun h _ => h.bond_k₂ ▸ h.gate₂_mem_supportedOperators

theorem layerOne_op (hs : List (TeleportHop N)) (hv : Valid hs) :
    (layerOne (d := d) hs hv).op = (hs.map TeleportHop.gate₁).prod :=
  layerOfList_op _ _ _ _ _ _

theorem layerTwo_op (hs : List (TeleportHop N)) (hv : Valid hs) :
    (layerTwo (d := d) hs hv).op = (hs.map TeleportHop.gate₂).prod :=
  layerOfList_op _ _ _ _ _ _

/-! ### Chains of hops before the correction -/

/-- The permutation of sites of a list of hops, as a matrix: the product of the exchanges of
the sites `c` and `f` of the hops, the most recent leftmost. -/
noncomputable def chainPerm : List (TeleportHop N) → Matrix (Cfg d N) (Cfg d N) ℂ
  | [] => 1
  | h :: hs => h.swapPerm.permMatrix ℂ * chainPerm hs

/-- The single-site unitaries left by a list of hops, for the outcome `z`. -/
noncomputable def chainFrame : List (TeleportHop N) → Cfg d N → Fin N → Matrix (Fin d) (Fin d) ℂ
  | [], _ => fun _ => 1
  | h :: hs, z => fun i => Function.update (chainFrame hs z) h.c 1 i * h.frame z i *
      Function.update (1 : Fin N → Matrix (Fin d) (Fin d) ℂ) h.f (chainFrame hs z h.c) i

/-- The operator of a list of hops before the correction, for the outcome `z`. -/
noncomputable def chainPre (hs : List (TeleportHop N)) (z : Cfg d N) :
    Matrix (Cfg d N) (Cfg d N) ℂ :=
  ctrlProj (measuredSites hs) z * (hs.map TeleportHop.gate₂).prod *
    (hs.map TeleportHop.gate₁).prod

theorem chainFrame_mem_unitary (hs : List (TeleportHop N)) (z : Cfg d N) (i : Fin N) :
    chainFrame hs z i ∈ unitary (Matrix (Fin d) (Fin d) ℂ) := by
  induction hs generalizing i with
  | nil => exact one_mem _
  | cons h hs ih =>
    refine Submonoid.mul_mem _ (Submonoid.mul_mem _ ?_ (h.frame_mem_unitary z i)) ?_
    · simp only [Function.update_apply]; split_ifs
      · exact one_mem _
      · exact ih i
    · simp only [Function.update_apply]; split_ifs
      · exact ih _
      · exact one_mem _

theorem chainFrame_of_notMem (hs : List (TeleportHop N)) (z : Cfg d N) {i : Fin N}
    (hi : i ∉ allSites hs) : chainFrame hs z i = 1 := by
  induction hs with
  | nil => rfl
  | cons h hs ih =>
    have hi' : i ∉ h.sites := fun h' => hi (Or.inl h')
    have hrest : i ∉ allSites hs := fun h' => hi (Or.inr h')
    simp only [sites, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hi'
    simp only [chainFrame, Function.update_of_ne hi'.1, Function.update_of_ne hi'.2.2,
      ih hrest, h.frame_of_ne z hi'.1 hi'.2.1 hi'.2.2, Pi.one_apply, mul_one]

theorem prod_gate₁_mem_supportedOperators (hs : List (TeleportHop N)) :
    (hs.map TeleportHop.gate₁).prod ∈ supportedOperators d (allSites hs) := by
  refine list_prod_mem_supportedOperators _ fun A hA => ?_
  obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hA
  refine supportedOperators_mono ?_ h.gate₁_mem_supportedOperators
  rintro i (rfl | rfl) <;> exact mem_allSites.mpr ⟨h, hh, by simp [sites]⟩

theorem prod_gate₂_mem_supportedOperators (hs : List (TeleportHop N)) :
    (hs.map TeleportHop.gate₂).prod ∈ supportedOperators d (allSites hs) := by
  refine list_prod_mem_supportedOperators _ fun A hA => ?_
  obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hA
  refine supportedOperators_mono ?_ h.gate₂_mem_supportedOperators
  rintro i (rfl | rfl) <;> exact mem_allSites.mpr ⟨h, hh, by simp [sites]⟩

theorem pre_mem_supportedOperators (h : TeleportHop N) (z : Cfg d N) :
    h.pre z ∈ supportedOperators d h.sites := by
  have hc : ({h.c} : Set (Fin N)) ⊆ h.sites := by simp [sites]
  have he : ({h.e} : Set (Fin N)) ⊆ h.sites := by simp [sites]
  refine mul_mem_supportedOperators (mul_mem_supportedOperators (mul_mem_supportedOperators
    ?_ ?_) ?_) ?_
  · exact supportedOperators_mono (by simpa using he) (ctrlProj_mem_supportedOperators _ z)
  · exact supportedOperators_mono (by simpa using hc) (ctrlProj_mem_supportedOperators _ z)
  · exact supportedOperators_mono (by rintro i (rfl | rfl) <;> simp [sites])
      h.gate₂_mem_supportedOperators
  · exact supportedOperators_mono (by rintro i (rfl | rfl) <;> simp [sites])
      h.gate₁_mem_supportedOperators

/-- One more hop factors off the operator of a valid list. -/
theorem chainPre_cons {h : TeleportHop N} {hs : List (TeleportHop N)} (hv : Valid (h :: hs))
    (z : Cfg d N) : chainPre (h :: hs) z = h.pre z * chainPre hs z := by
  have hdisj : Disjoint ({h.e, h.f} : Set (Fin N)) (allSites hs) := by
    rw [Set.disjoint_left]
    rintro i (rfl | rfl)
    · exact hv.2.1
    · exact hv.2.2.1
  have h1 : Commute (h.gate₁ (d := d)) (hs.map TeleportHop.gate₂).prod :=
    commute_of_mem_supportedOperators hdisj h.gate₁_mem_supportedOperators
      (prod_gate₂_mem_supportedOperators hs)
  have h2 : Commute (ctrlProj (measuredSites hs) z) (h.pre z) :=
    commute_of_mem_supportedOperators (disjoint_measuredSites hv)
      (ctrlProj_mem_supportedOperators _ z) (pre_mem_supportedOperators h z)
  simp only [chainPre, measuredSites, List.map_cons, List.prod_cons, ctrlProj_insert]
  calc ctrlProj (measuredSites hs) z * ctrlProj {h.e} z * ctrlProj {h.c} z *
        (h.gate₂ * (hs.map TeleportHop.gate₂).prod) * (h.gate₁ * (hs.map TeleportHop.gate₁).prod)
      = ctrlProj (measuredSites hs) z * h.pre z * (hs.map TeleportHop.gate₂).prod *
          (hs.map TeleportHop.gate₁).prod := by
        simp only [pre, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (hs.map TeleportHop.gate₂).prod, ← h1.eq, Matrix.mul_assoc]
    _ = h.pre z * (ctrlProj (measuredSites hs) z * (hs.map TeleportHop.gate₂).prod *
          (hs.map TeleportHop.gate₁).prod) := by
        rw [h2.eq]; simp only [Matrix.mul_assoc]

theorem _root_.MPSPreparation.IsZeroOn.chainPerm_mulVec {S : Set (Fin N)} {v : Cfg d N → ℂ} (hS : IsZeroOn S v)
    {hs : List (TeleportHop N)} (hdisj : Disjoint S (allSites hs)) :
    IsZeroOn S (chainPerm hs *ᵥ v) := by
  induction hs with
  | nil => simpa [chainPerm] using hS
  | cons h hs ih =>
    rw [chainPerm, ← mulVec_mulVec]
    refine (ih (hdisj.mono_right Set.subset_union_right)).permMatrix_cfgPerm_mulVec
      fun i hi => Equiv.swap_apply_of_ne_of_ne ?_ ?_
    · rintro rfl; exact Set.disjoint_left.mp hdisj hi (Or.inl (Or.inl rfl))
    · rintro rfl; exact Set.disjoint_left.mp hdisj hi (Or.inl (Or.inr (Or.inr rfl)))

/-- **Chains of hops before the correction.** For a valid list of `H` hops and a vector with
`|0⟩` at the sites `e` and `f` of every hop, the operator of the hops for the outcome `z` is
`d^{-H}` times the permutation of sites of the list followed by the single-site unitaries
`chainFrame hs z`.

Source: arXiv:2307.01696, paragraph "Tree-RG circuit with measurements" ("performing
simultaneous measurements"). -/
theorem chainPre_mulVec : ∀ {hs : List (TeleportHop N)}, Valid hs → ∀ (z : Cfg d N)
    {v : Cfg d N → ℂ}, IsZeroOn (pairSites hs) v →
    chainPre hs z *ᵥ v = ((d : ℂ) ^ hs.length)⁻¹ •
      (finKronecker (chainFrame hs z) *ᵥ (chainPerm hs *ᵥ v))
  | [], _, z, v, _ => by simp [chainPre, chainPerm, chainFrame, measuredSites]
  | h :: hs, hv, z, v, hz => by
    have hzhs : IsZeroOn (pairSites hs) v := hz.mono Set.subset_union_right
    have hef : Disjoint ({h.e, h.f} : Set (Fin N)) (allSites hs) :=
      Set.disjoint_left.mpr fun i hi => by
        rcases hi with rfl | rfl
        exacts [hv.2.1, hv.2.2.1]
    have hc : h.c ∉ ({h.e, h.f} : Set (Fin N)) := by
      rintro (h' | h')
      · exact h.c_ne_e h'
      · exact h.c_ne_f h'
    set g := chainFrame hs z
    set U := g h.c
    set w := chainPerm hs *ᵥ v
    have hge : g h.e = 1 := chainFrame_of_notMem hs z hv.2.1
    have hgf : g h.f = 1 := chainFrame_of_notMem hs z hv.2.2.1
    -- Split off the unitary at `c`.
    have hsplit : finKronecker g = finKronecker (Function.update g h.c 1) *
        finKronecker (Function.update 1 h.c U) := by
      rw [finKronecker_mul]
      congr 1
      funext i
      by_cases hi : i = h.c
      · subst hi; simp [U]
      · simp [Function.update_of_ne hi]
    have hcomm : Commute (h.pre z) (finKronecker (Function.update g h.c 1)) := by
      refine commute_of_mem_supportedOperators disjoint_compl_right
        (pre_mem_supportedOperators h z) (finKronecker_mem_supportedOperators fun i hi => ?_)
      simp only [Set.mem_compl_iff, not_not, sites, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hi
      rcases hi with rfl | rfl | rfl
      · exact Function.update_self ..
      · rw [Function.update_of_ne h.c_ne_e.symm, hge]
      · rw [Function.update_of_ne h.c_ne_f.symm, hgf]
    have hw : IsZeroOn {h.e, h.f} w :=
      (hz.mono Set.subset_union_left).chainPerm_mulVec hef
    have hw' : IsZeroOn {h.e, h.f} (finKronecker (Function.update 1 h.c U) *ᵥ w) :=
      hw.finKronecker_update_one_mulVec hc U
    have hswap : h.swapPerm.permMatrix ℂ * finKronecker (Function.update 1 h.c U) =
        finKronecker (Function.update 1 h.f U) * h.swapPerm.permMatrix ℂ := by
      rw [swapPerm, permMatrix_cfgPerm_mul_finKronecker]
      congr 2
      funext i
      rw [Equiv.symm_swap]
      by_cases hi : i = h.f
      · subst hi; simp
      · by_cases hi' : i = h.c
        · subst hi'
          rw [Equiv.swap_apply_left, Function.update_of_ne h.c_ne_f.symm,
            Function.update_of_ne hi]
          rfl
        · rw [Equiv.swap_apply_of_ne_of_ne hi' hi, Function.update_of_ne hi',
            Function.update_of_ne hi]
    have hframe : finKronecker (Function.update g h.c 1) * (finKronecker (h.frame z) *
        finKronecker (Function.update 1 h.f U)) = finKronecker (chainFrame (h :: hs) z) := by
      rw [finKronecker_mul, finKronecker_mul]
      congr 1
      funext i
      simp only [chainFrame, Matrix.mul_assoc]
      rfl
    rw [chainPre_cons hv, ← mulVec_mulVec, chainPre_mulVec hv.1 z hzhs, mulVec_smul, hsplit,
      ← mulVec_mulVec, mulVec_mulVec (M := h.pre z), hcomm.eq, ← mulVec_mulVec, h.pre_mulVec z hw',
      mulVec_smul, mulVec_mulVec (M := h.swapPerm.permMatrix ℂ), hswap, ← mulVec_mulVec,
      mulVec_mulVec (M := finKronecker (h.frame z)), mulVec_mulVec (M := finKronecker _), hframe, smul_smul,
      chainPerm, ← mulVec_mulVec, List.length_cons, pow_succ, mul_inv]

/-! ### The teleportation round -/

/-- The outcome string `m` on the sites of `S`, extended by `0` to a configuration. -/
def extendOutcome (S : Finset (Fin N)) (m : S → Fin d) : Cfg d N :=
  fun i => if hi : i ∈ S then m ⟨i, hi⟩ else 0

/-- The *teleportation round* of a valid list of hops after the circuit `pre`: the circuit `pre`,
the first layers of all hops, the second layers of all hops, the measurement of the sites `c` and
`e` of every hop, and the correction by the inverse of the single-site unitaries left by the hops.

Source: arXiv:2307.01696, paragraph "Tree-RG circuit with measurements" ("creating
nearest-neighbor entangled pairs, then performing simultaneous measurements, and correcting
(without postselection) based on the measurement outcomes"). -/
noncomputable def round (pre : List (Layer d N)) (hs : List (TeleportHop N)) (hv : Valid hs) :
    MeasurementRound d N where
  circuit := pre ++ [layerOne hs hv, layerTwo hs hv]
  measured := measuredSites hs
  correction m i := star (chainFrame hs (extendOutcome _ m) i)
  correction_mem_unitary _ _ := Unitary.star_mem (chainFrame_mem_unitary _ _ _)

/-- The teleportation round has depth `2` after the circuit `pre`, whatever the number and the
lengths of the chains. -/
theorem depth_round (pre : List (Layer d N)) (hs : List (TeleportHop N)) (hv : Valid hs) :
    (round pre hs hv).depth = pre.length + 2 := by
  simp [round, MeasurementRound.depth]

/-- **Teleportation in one round.** For a valid list of `H` hops, the teleportation round after
the circuit `pre` implements `P U` on the vectors `v` such that `U v` has `|0⟩` at the sites `e`
and `f` of every hop, `U` the circuit `pre` and `P` the permutation of sites of the hops; for
every outcome the scalar is `d^{-H}`. With `pre` empty, a register is moved along every chain of
hops, across any distance, in depth `2`.

Source: arXiv:2307.01696, paragraph "Tree-RG circuit with measurements" ("Isometries ... act on
a constant number of sites which, although spatially separated, can be teleported at
neighboring registers with a constant overhead"). -/
theorem isImplementationOn_round (pre : List (Layer d N)) {hs : List (TeleportHop N)}
    (hv : Valid hs) :
    (round pre hs hv).IsImplementationOn {v | IsZeroOn (pairSites hs) (circuitOp pre *ᵥ v)}
      (chainPerm hs * circuitOp pre) := by
  intro m
  refine ⟨((d : ℂ) ^ hs.length)⁻¹, fun v hv' => ?_⟩
  set z := extendOutcome (measuredSites hs) m
  have hproj : outcomeProj (measuredSites hs) m = ctrlProj (measuredSites hs) z :=
    outcomeProj_eq_ctrlProj _ _ _ fun i => by simp [z, extendOutcome]
  have hcirc : circuitOp (pre ++ [layerOne hs hv, layerTwo hs hv]) =
      (hs.map TeleportHop.gate₂).prod * (hs.map TeleportHop.gate₁).prod * circuitOp pre := by
    rw [circuitOp_append]
    simp [circuitOp, layerOne_op, layerTwo_op]
  have hkraus : (round pre hs hv).kraus m =
      finKronecker (fun i => star (chainFrame hs z i)) * chainPre hs z * circuitOp pre := by
    change finKronecker (fun i => star (chainFrame hs z i)) * outcomeProj (measuredSites hs) m *
      circuitOp (pre ++ [layerOne hs hv, layerTwo hs hv]) = _
    rw [hproj, hcirc, chainPre]
    simp only [Matrix.mul_assoc]
  have hstar : finKronecker (fun i => star (chainFrame hs z i)) *
      finKronecker (chainFrame hs z) = 1 := by
    rw [finKronecker_mul]
    simp only [Unitary.star_mul_self_of_mem (chainFrame_mem_unitary hs z _), finKronecker_one]
  rw [hkraus, ← mulVec_mulVec, ← mulVec_mulVec, chainPre_mulVec hv z hv', mulVec_smul,
    mulVec_mulVec, hstar, one_mulVec, mulVec_mulVec]

end TeleportHop

end MPSPreparation
