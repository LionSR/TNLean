/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.Channel.EncodedChannelPlacement

/-!
# Onsite channels as a product of independently placed site channels

A product onsite channel factors into its single-site operations in a definite order.
Each factor is the representation-independent lift of an actual one-site CPTP map.
These equalities hold on every chain operator and therefore retain correlations with
other sites. They allow physical-register implementations to certify each factor as
a free local operation without assuming a global onsite simulation identity.
-/

open Matrix
open scoped BigOperators Kronecker

namespace QuantumCircuit

variable {N q : ℕ}

/-- Select one spatial site as a one-site register. -/
def singletonSite (i : Fin N) : Fin 1 ↪ Fin N where
  toFun _ := i
  inj' _ _ _ := Subsingleton.elim _ _

@[simp] theorem singletonSite_apply (i : Fin N) (a : Fin 1) : singletonSite i a = i := rfl

@[simp] theorem range_singletonSite (i : Fin N) : Set.range (singletonSite i) = {i} := by
  ext j
  simp only [Set.mem_range, singletonSite_apply, Set.mem_singleton_iff]
  constructor
  · rintro ⟨_, rfl⟩; rfl
  · rintro rfl; exact ⟨0, rfl⟩

/-- Splitting a product matrix gives the products on the selected and complementary sites. -/
theorem registerMatrixSplit_rectKronecker {s : ℕ} (e : Fin s ↪ Fin N)
    (A : Fin N → Matrix (Fin q) (Fin q) ℂ) :
    registerMatrixSplit e (rectKronecker A) =
      rectKronecker (fun j => A (e j)) ⊗ₖ
        rectKronecker (fun j : {j // j ∉ Set.range e} => A j.val) :=
  reindex_rectKronecker_registerSplit e A

namespace OnsiteChannel

/-- Equal site maps define equal global maps, including on correlated inputs. -/
theorem map_congr (Φ Ψ : OnsiteChannel q q (Fin N))
    (h : ∀ i, Φ.siteMap i = Ψ.siteMap i) : Φ.map = Ψ.map := by
  apply LinearMap.ext
  intro X
  apply LinearMap.eqOn_span' _ (mem_supportedOperators_univ X)
  rintro _ ⟨A, _, rfl⟩
  simp only [map_rectKronecker, h]

/-- Apply an onsite channel only at the sites in a chosen finite set. -/
noncomputable def onSites (Φ : OnsiteChannel q q (Fin N)) (s : Finset (Fin N)) :
    OnsiteChannel q q (Fin N) :=
  ofSiteMaps (fun i => if i ∈ s then Φ.siteMap i else LinearMap.id) (fun i => by
    split_ifs
    · exact rectangularKrausMap_isKrausCPTP _ (Φ.sum_kraus i)
    · exact isKrausCPTP_id)

@[simp] theorem onSites_siteMap (Φ : OnsiteChannel q q (Fin N)) (s : Finset (Fin N))
    (i : Fin N) : (Φ.onSites s).siteMap i = if i ∈ s then Φ.siteMap i else LinearMap.id :=
  ofSiteMaps_siteMap _ _ _

/-- Restricting to all sites recovers the actual original map. -/
theorem onSites_univ_map (Φ : OnsiteChannel q q (Fin N)) :
    (Φ.onSites Finset.univ).map = Φ.map :=
  map_congr _ _ (fun i => by simp only [onSites_siteMap, Finset.mem_univ, ite_true])

/-- Restricting to no sites gives the identity. -/
theorem onSites_empty_map (Φ : OnsiteChannel q q (Fin N)) :
    (Φ.onSites ∅).map = LinearMap.id :=
  map_eq_id_of_siteMap_eq_id _ (fun i => by simp only [onSites_siteMap,
    Finset.notMem_empty, ite_false])

/-- Adding a new site composes its single-site factor with the previously selected map. -/
theorem onSites_insert_map (Φ : OnsiteChannel q q (Fin N)) (s : Finset (Fin N))
    {i : Fin N} (hi : i ∉ s) :
    (Φ.onSites (insert i s)).map = (Φ.onSites {i}).map ∘ₗ (Φ.onSites s).map := by
  rw [← comp_map]
  apply map_congr
  intro j
  simp only [comp, ofSiteMaps_siteMap, onSites_siteMap]
  by_cases hji : j = i
  · subst j
    simp only [Finset.mem_insert_self, ite_true, Finset.mem_singleton, ite_false, hi,
      LinearMap.comp_id]
  · by_cases hjs : j ∈ s <;>
      simp [Finset.mem_insert, Finset.mem_singleton, hji, hjs]

/-- Distinct single-site factors multiply to the channel on their set of sites. -/
theorem prod_onSites_singleton (Φ : OnsiteChannel q q (Fin N))
    (L : List (Fin N)) (hL : L.Nodup) :
    (L.map fun i => (Φ.onSites {i}).map).prod = (Φ.onSites L.toFinset).map := by
  induction L with
  | nil => simp only [List.map_nil, List.prod_nil, List.toFinset_nil,
      onSites_empty_map, Module.End.one_eq_id]
  | cons i L ih =>
    obtain ⟨hi, hL⟩ := List.nodup_cons.mp hL
    rw [List.map_cons, List.prod_cons, ih hL, List.toFinset_cons,
      onSites_insert_map Φ _ (by simpa only [List.mem_toFinset] using hi)]
    rfl

/-- The global onsite channel is a concrete ordered product of its single-site maps. -/
theorem map_eq_prod_onSites_singleton (Φ : OnsiteChannel q q (Fin N)) :
    Φ.map = ((List.finRange N).map fun i => (Φ.onSites {i}).map).prod := by
  rw [prod_onSites_singleton Φ _ (List.nodup_finRange N), List.toFinset_finRange,
    onSites_univ_map]

/-- A site's channel viewed on an explicit one-site register. -/
noncomputable def oneSite (Φ : OnsiteChannel q q (Fin N)) (i : Fin N) :
    OnsiteChannel q q (Fin 1) :=
  ofSiteMaps (fun _ => Φ.siteMap i) (fun _ =>
    rectangularKrausMap_isKrausCPTP _ (Φ.sum_kraus i))

@[simp] theorem oneSite_siteMap (Φ : OnsiteChannel q q (Fin N)) (i : Fin N) (j : Fin 1) :
    (Φ.oneSite i).siteMap j = Φ.siteMap i :=
  ofSiteMaps_siteMap (fun _ : Fin 1 => Φ.siteMap i) _ j

/-- A single-site factor is exactly the lift of its one-site channel, with the identity
on every other site; no assumption on input correlations is required. -/
theorem onSites_singleton_map_eq_lift (Φ : OnsiteChannel q q (Fin N)) (i : Fin N) :
    (Φ.onSites {i}).map = registerChannelLift (singletonSite i) (Φ.oneSite i).map := by
  apply LinearMap.ext
  intro X
  apply LinearMap.eqOn_span' _ (mem_supportedOperators_univ X)
  rintro _ ⟨A, _, rfl⟩
  apply (registerMatrixSplit (d := q) (singletonSite i)).injective
  rw [map_rectKronecker, registerMatrixSplit_channelLift,
    registerMatrixSplit_rectKronecker, registerMatrixSplit_rectKronecker,
    tensorMapIdLM_apply, tensorMapId_kronecker, map_rectKronecker]
  congr 1
  · congr 1
    funext j
    simp only [onSites_siteMap, singletonSite_apply, Finset.mem_singleton, ite_true,
      oneSite_siteMap]
  · congr 1
    funext j
    have hji : j.val ≠ i := by
      simpa only [range_singletonSite, Set.mem_singleton_iff] using j.property
    simp only [onSites_siteMap, Finset.mem_singleton, ite_eq_right hji, LinearMap.id_apply]

end OnsiteChannel

end QuantumCircuit
