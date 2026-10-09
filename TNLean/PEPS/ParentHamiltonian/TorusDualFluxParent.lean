/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.TorusFluxStringLocalParent
import TNLean.PEPS.TorusDualFluxDetection

/-!
# Actual local parent annihilation away from dual-string endpoints

The endpoint formula supplies trivial plaquette holonomy at every other
plaquette. An explicit four-vertex gauge then removes its internal insertions,
which places every complementary physical slice in the untwisted local PEPS
range. The actual positive and canonical local parent interactions annihilate
the inserted state. This does not assert equality of all reduced densities.

Source: SCP10, arXiv:1001.3807, Definition 6.13 and Lemma 6.14,
lines 2181–2214. Both periods are at least three for the simple-graph parent.

**Scope restriction (canonical plaquette parents on simple-graph tori):** See
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
local notation "X" => TorusVertex width height
variable {G V : Type*} [Group G] [Fintype V] [DecidableEq V] {d : ℕ}

/-- Every actual positive plaquette parent term away from the two endpoints
annihilates the genuine inserted string state. The flatness premise is derived
from the path, with no gauge witness supplied. Source: SCP10, Lemma 6.14. -/
theorem torusDualFluxState_parent_annihilates_of_ne
    (U : G →* Matrix V V ℂ) (A : V → V → V → V → Fin d → ℂ)
    (hA : ∀ g, siteMap A ∘ₗ torusLegRep U g = siteMap A)
    (g : G) {a b : X} (p : TorusDualPath a b) (v : X) (hva : v ≠ a) (hvb : v ≠ b)
    (P : Matrix (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v))
      (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v)) ℂ)
    (hP : IsRegionParentInteraction (groupBondTensor (torusNativeIncidentSite A))
      (torusPlaquetteRegion v) P) :
    regionLocalTerm (torusPlaquetteRegion v) P *ᵥ
      torusDualFluxState U (fun _ => A) g p = 0 :=
  torusParent_annihilates_torusBondNetwork_of_holonomy_eq_one U A hA
    (torusDualFluxLabels g p) v
    (torusBondPlaquetteHolonomy_torusDualFluxLabels_of_ne g p v hva hvb) P hP

/-- The canonical orthogonal parent projector also annihilates the actual
string state at every nonendpoint plaquette. Source: SCP10, Lemma 6.14. -/
theorem torusDualFluxState_canonicalParent_annihilates_of_ne
    (U : G →* Matrix V V ℂ) (A : V → V → V → V → Fin d → ℂ)
    (hA : ∀ g, siteMap A ∘ₗ torusLegRep U g = siteMap A)
    (g : G) {a b : X} (p : TorusDualPath a b) (v : X) (hva : v ≠ a) (hvb : v ≠ b) :
    regionLocalTerm (torusPlaquetteRegion v)
        (canonicalRegionParentInteraction (groupBondTensor (torusNativeIncidentSite A))
          (torusPlaquetteRegion v)) *ᵥ torusDualFluxState U (fun _ => A) g p = 0 :=
  torusDualFluxState_parent_annihilates_of_ne U A hA g p v hva hvb _
    (isRegionParentInteraction_canonical _ _)

/-- Closed dual loops satisfy every canonical plaquette parent constraint,
including noncontractible loops; no vacuum-state equality is inferred.
Source: SCP10, Definition 5.6 and Lemma 6.14. -/
theorem torusDualFluxState_canonicalParent_annihilates_loop
    (U : G →* Matrix V V ℂ) (A : V → V → V → V → Fin d → ℂ)
    (hA : ∀ g, siteMap A ∘ₗ torusLegRep U g = siteMap A)
    (g : G) {a : X} (p : TorusDualPath a a) (v : X) :
    regionLocalTerm (torusPlaquetteRegion v)
        (canonicalRegionParentInteraction (groupBondTensor (torusNativeIncidentSite A))
          (torusPlaquetteRegion v)) *ᵥ torusDualFluxState U (fun _ => A) g p = 0 :=
  canonicalTorusParent_annihilates_torusBondNetwork_of_holonomy_eq_one U A hA
    (torusDualFluxLabels g p) v (torusBondPlaquetteHolonomy_torusDualFluxLabels_loop g p v)

end TNLean.PEPS
