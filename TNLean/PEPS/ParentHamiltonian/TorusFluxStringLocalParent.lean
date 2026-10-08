/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusGroupGaugeContraction
import TNLean.PEPS.TorusNativeFluxHolonomy
import TNLean.PEPS.GraphInsertedRegionSupport
import TNLean.PEPS.ParentHamiltonian.RegionParentHamiltonian

/-!
# Local parent constraints away from flux-string endpoints

An identity-holonomy plaquette admits a gauge supported on its four vertices
that removes all four internal insertions. Exterior and crossing insertions
remain arbitrary. Thus every complementary physical slice of the actual
inserted contraction lies in the original local PEPS range, and every positive
parent interaction with that kernel annihilates it. This includes the canonical
orthogonal parent projector. No equality of reduced densities is asserted.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Definition 6.13,
Lemma 6.14 and `eq:2d:move-strings`. The graph support theorem used here requires
both torus periods to be at least three. Virtual invariance suffices; the
representation need not be regular or unitary and no injectivity is required.

**Scope restriction (four-site regions on simple-graph tori):** See
`docs/paper-gaps/scp10_dual_flux_string_deformation.tex` for the distinction
from unrestricted source wording and arbitrary open-boundary geometries.
-/

noncomputable section
open scoped Matrix
namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "TV" => TorusVertex width height
local notation "TG" => torusGraph width height

private theorem mem_plaquette_iff (v w : TV) :
    w ∈ torusPlaquetteRegion v ↔
      (w.1 = v.1 ∨ w.1 = v.1 + 1) ∧ (w.2 = v.2 ∨ w.2 = v.2 + 1) := by
  simp [torusPlaquetteRegion, torusPlaquetteWalk, SimpleGraph.Walk.support, Prod.ext_iff]
  tauto

private theorem eq_left_of_mem_pair {n : ℕ} [NeZero n] [Fact (2 < n)] (a x : ZMod n)
    (hx : x = a ∨ x = a + 1) (hy : x + 1 = a ∨ x + 1 = a + 1) : x = a := by
  rcases hx with hx | rfl
  · exact hx
  · rcases hy with hy | hy
    · have htwo : (2 : ZMod n) = 0 := by
        simpa only [add_assoc, one_add_one_eq_two, add_eq_left] using hy
      have hd : n ∣ 2 := (ZMod.natCast_eq_zero_iff 2 n).mp htwo
      have := Nat.le_of_dvd (by decide : 0 < 2) hd
      have := Fact.out (p := 2 < n)
      omega
    · have hone : (1 : ZMod n) = 0 := by
        simpa only [add_eq_left] using hy
      simp at hone

variable {G : Type*} [Group G]

private def plaquetteGauge (p : TorusBondLabels width height G) (v w : TV) : G :=
  if w = (v.1 + 1, v.2) then (p.1 v)⁻¹
  else if w = (v.1, v.2 + 1) then p.2 v
  else if w = (v.1 + 1, v.2 + 1) then p.2 v * (p.1 (v.1, v.2 + 1))⁻¹
  else 1

/-- Identity native plaquette holonomy admits a gauge supported on its four
sites removing every internal horizontal and vertical bond. Source: SCP10,
Lemma 6.14 and `eq:2d:move-strings`. -/
theorem exists_torusBondGauge_plaquette_internal_eq_one
    (p : TorusBondLabels width height G) (v : TV)
    (hp : torusBondPlaquetteHolonomy p v = 1) :
    ∃ q : TV → G,
      (∀ w, w ∉ torusPlaquetteRegion v → q w = 1) ∧
      (∀ w, w ∈ torusPlaquetteRegion v → (w.1 + 1, w.2) ∈ torusPlaquetteRegion v →
        (torusBondGauge q p).1 w = 1) ∧
      (∀ w, w ∈ torusPlaquetteRegion v → (w.1, w.2 + 1) ∈ torusPlaquetteRegion v →
        (torusBondGauge q p).2 w = 1) := by
  refine ⟨plaquetteGauge p v, ?_, ?_, ?_⟩
  · intro w hw
    have hbr : w ≠ (v.1 + 1, v.2) := by
      rintro rfl
      exact hw ((mem_plaquette_iff _ _).mpr (by simp))
    have htl : w ≠ (v.1, v.2 + 1) := by
      rintro rfl
      exact hw ((mem_plaquette_iff _ _).mpr (by simp))
    have htr : w ≠ (v.1 + 1, v.2 + 1) := by
      rintro rfl
      exact hw ((mem_plaquette_iff _ _).mpr (by simp))
    simp [plaquetteGauge, hbr, htl, htr]
  · intro w hw hr
    obtain ⟨hx, hy⟩ := (mem_plaquette_iff _ _).mp hw
    have hx' := ((mem_plaquette_iff _ _).mp hr).1
    have he := eq_left_of_mem_pair v.1 w.1 hx hx'
    rcases w with ⟨x, y⟩
    dsimp only at he hy
    subst x
    rcases hy with rfl | rfl <;>
      simp [torusBondGauge, plaquetteGauge, Prod.ext_iff, mul_assoc]
  · intro w hw hu
    obtain ⟨hx, hy⟩ := (mem_plaquette_iff _ _).mp hw
    have hy' := ((mem_plaquette_iff _ _).mp hu).2
    have he := eq_left_of_mem_pair v.2 w.2 hy hy'
    rcases w with ⟨x, y⟩
    dsimp only at he hx
    subst y
    rcases hx with rfl | rfl
    · simp [torusBondGauge, plaquetteGauge, Prod.ext_iff]
    · simpa [torusBondGauge, plaquetteGauge, Prod.ext_iff, torusBondPlaquetteHolonomy,
        mul_assoc] using hp

variable {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ}

/-- Identity holonomy on a plaquette places every complementary physical slice
of the inserted state in the original plaquette ground space. This is a
support statement for the actual contraction, with arbitrary insertions away
from the plaquette. Source: SCP10, Lemma 6.14 and `eq:2d:move-strings`. -/
theorem torusBondNetwork_slice_mem_plaquetteGroundSpace_of_holonomy_eq_one
    (U : G →* Matrix V V ℂ) (a : V → V → V → V → Fin d → ℂ)
    (ha : ∀ g, siteMap a ∘ₗ torusLegRep U g = siteMap a)
    (p : TorusBondLabels width height G) (v : TV)
    (hp : torusBondPlaquetteHolonomy p v = 1)
    (τ : RegionPhysicalConfig (d := d) (Finset.univ \ torusPlaquetteRegion v)) :
    (fun σ ↦ torusBondNetwork
      (fun w c ↦ a c.1 c.2.1 c.2.2.1 c.2.2.2
        (assembleRegionσ (torusPlaquetteRegion v) σ τ w))
      (fun w ↦ U (p.1 w)) (fun w ↦ U (p.2 w))) ∈
      regionGroundSpace (groupBondTensor (torusNativeIncidentSite a)) (torusPlaquetteRegion v) := by
  obtain ⟨q, _, hqh, hqv⟩ := exists_torusBondGauge_plaquette_internal_eq_one p v hp
  let p' := torusBondGauge q p
  have heq (σ : TV → Fin d) :
      torusBondNetwork (fun w c ↦ a c.1 c.2.1 c.2.2.1 c.2.2.2 (σ w))
          (fun w ↦ U (p.1 w)) (fun w ↦ U (p.2 w)) =
        graphInsertedBondNetwork (torusGraphBondMatrix (fun w ↦ U (p'.1 w))
          (fun w ↦ U (p'.2 w))) (torusNativeIncidentSite a) σ := by
    rw [← torusBondNetwork_torusBondGauge U (fun _ ↦ a) (fun _ ↦ ha) σ q p]
    exact torusBondNetwork_eq_graphInsertedBondNetwork a _ _ σ
  simp_rw [heq]
  apply graphInsertedBondNetwork_slice_mem_regionGroundSpace_of_internal_eq_one
  intro e ht hh
  obtain ⟨w | w, rfl⟩ := torusEdgeEquiv.surjective e
  · change (torusRightEdge w).1.1 ∈ torusPlaquetteRegion v at ht
    change (torusRightEdge w).1.2 ∈ torusPlaquetteRegion v at hh
    change torusGraphBondMatrix _ _ (torusRightEdge w) = 1
    have hw : w ∈ torusPlaquetteRegion v ∧ (w.1 + 1, w.2) ∈ torusPlaquetteRegion v := by
      rcases Edge.ofAdj_endpoints (torusGraph_adj_right w.1 w.2) with h | h
      · exact ⟨by simpa only [torusRightEdge, h.1] using ht,
          by simpa only [torusRightEdge, h.2] using hh⟩
      · exact ⟨by simpa only [torusRightEdge, h.2] using hh,
          by simpa only [torusRightEdge, h.1] using ht⟩
    simp [p', hqh w hw.1 hw.2]
  · change (torusUpEdge w).1.1 ∈ torusPlaquetteRegion v at ht
    change (torusUpEdge w).1.2 ∈ torusPlaquetteRegion v at hh
    change torusGraphBondMatrix _ _ (torusUpEdge w) = 1
    have hw : w ∈ torusPlaquetteRegion v ∧ (w.1, w.2 + 1) ∈ torusPlaquetteRegion v := by
      rcases Edge.ofAdj_endpoints (torusGraph_adj_up w.1 w.2) with h | h
      · exact ⟨by simpa only [torusUpEdge, h.1] using ht,
          by simpa only [torusUpEdge, h.2] using hh⟩
      · exact ⟨by simpa only [torusUpEdge, h.2] using hh,
          by simpa only [torusUpEdge, h.1] using ht⟩
    simp [p', hqv w hw.1 hw.2]

/-- Every positive parent interaction with the actual plaquette PEPS kernel
annihilates an inserted state with identity plaquette holonomy. Source: SCP10,
Definition 6.13, Lemma 6.14 and `eq:2d:move-strings`. -/
theorem torusParent_annihilates_torusBondNetwork_of_holonomy_eq_one
    (U : G →* Matrix V V ℂ) (a : V → V → V → V → Fin d → ℂ)
    (ha : ∀ g, siteMap a ∘ₗ torusLegRep U g = siteMap a)
    (p : TorusBondLabels width height G) (v : TV)
    (hp : torusBondPlaquetteHolonomy p v = 1)
    (P : Matrix (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v))
      (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v)) ℂ)
    (hP : IsRegionParentInteraction (groupBondTensor (torusNativeIncidentSite a))
      (torusPlaquetteRegion v) P) :
    regionLocalTerm (torusPlaquetteRegion v) P *ᵥ
      (fun σ ↦ torusBondNetwork (fun w c ↦ a c.1 c.2.1 c.2.2.1 c.2.2.2 (σ w))
        (fun w ↦ U (p.1 w)) (fun w ↦ U (p.2 w))) = 0 := by
  apply (regionLocalTerm_mulVec_eq_zero_iff _ _ hP _).mpr
  exact torusBondNetwork_slice_mem_plaquetteGroundSpace_of_holonomy_eq_one U a ha p v hp

/-- The canonical orthogonal parent projector annihilates the same actual
inserted state whenever its plaquette holonomy is the identity. Source:
SCP10, Definition 6.13, Lemma 6.14 and the local parent construction. -/
theorem canonicalTorusParent_annihilates_torusBondNetwork_of_holonomy_eq_one
    (U : G →* Matrix V V ℂ) (a : V → V → V → V → Fin d → ℂ)
    (ha : ∀ g, siteMap a ∘ₗ torusLegRep U g = siteMap a)
    (p : TorusBondLabels width height G) (v : TV)
    (hp : torusBondPlaquetteHolonomy p v = 1) :
    regionLocalTerm (torusPlaquetteRegion v)
        (canonicalRegionParentInteraction (groupBondTensor (torusNativeIncidentSite a))
          (torusPlaquetteRegion v)) *ᵥ
      (fun σ ↦ torusBondNetwork (fun w c ↦ a c.1 c.2.1 c.2.2.1 c.2.2.2 (σ w))
        (fun w ↦ U (p.1 w)) (fun w ↦ U (p.2 w))) = 0 :=
  torusParent_annihilates_torusBondNetwork_of_holonomy_eq_one U a ha p v hp _
    (isRegionParentInteraction_canonical _ _)

/-- Zero signed plaquette curl of native powers implies annihilation by every
positive local parent interaction. For a dual path, the geometric endpoint
calculation supplies this premise at every nonendpoint plaquette. Source:
SCP10, Definition 6.13 and Lemma 6.14. -/
theorem torusParent_annihilates_torusBondNetwork_zpow_of_curl_eq_zero
    (U : G →* Matrix V V ℂ) (a : V → V → V → V → Fin d → ℂ)
    (ha : ∀ g, siteMap a ∘ₗ torusLegRep U g = siteMap a)
    (g : G) (h k : TV → ℤ) (v : TV)
    (hcurl : h (v.1, v.2 + 1) + k (v.1 + 1, v.2) - h v - k v = 0)
    (P : Matrix (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v))
      (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v)) ℂ)
    (hP : IsRegionParentInteraction (groupBondTensor (torusNativeIncidentSite a))
      (torusPlaquetteRegion v) P) :
    regionLocalTerm (torusPlaquetteRegion v) P *ᵥ
      (fun σ ↦ torusBondNetwork (fun w c ↦ a c.1 c.2.1 c.2.2.1 c.2.2.2 (σ w))
        (fun w ↦ U (g ^ h w)) (fun w ↦ U (g ^ k w))) = 0 := by
  apply torusParent_annihilates_torusBondNetwork_of_holonomy_eq_one U a ha
    (fun w ↦ g ^ h w, fun w ↦ g ^ k w) v _ P hP
  rw [torusBondPlaquetteHolonomy_zpow, hcurl, zpow_zero]

end TNLean.PEPS
