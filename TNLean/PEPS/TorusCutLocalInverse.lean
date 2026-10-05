/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusCutPhysicalMap
import TNLean.PEPS.TorusMatchedBondRepresentation

/-!
# Local-inverse reduction of the four actual cut spaces

Local G-injective left inverses send every cut contraction, with exactly its
original correlated boundary tensor, to the corresponding contraction of
the local invariant projectors. The original site maps recover every such
vector. The same physical left inverse works for all four cuts, so the
intersection itself is identified with the image of the canonical intersection.

The action may vary from site to site. In particular, it can be the action
`torusMatchedLegRep Uh Uv v` from independent matching bond representations.
No regularity, isometry, homogeneous tensor, or parent-Hamiltonian
classification is assumed. These are the local-inverse steps in SCP10,
Theorem 5.5; the canonical coefficient-extraction and reverse closure
inclusion remain to be proved.
-/

open scoped Matrix

namespace TNLean.PEPS

variable {G V Phys : Type*} [Group G] [Fintype G] [Fintype V] [DecidableEq V]
attribute [local instance] Representation.invertibleFintypeCardComplex

/-- The original invariant site map recovers its tensor from the canonical
averaging tensor, for any specified local virtual action. -/
theorem physicalMapSite_representationAveragingSite
    (ρ : Representation ℂ G ((V × V × V × V) → ℂ))
    (a : V → V → V → V → Phys → ℂ)
    (hinv : ∀ g, siteMap a ∘ₗ ρ g = siteMap a) :
    physicalMapSite (LinearMap.toMatrix' (siteMap a)) (representationAveragingSite ρ) = a := by
  apply (physicalMapSite_eq_iff_siteMap_comp _ _ _).mpr
  rw [siteMap_representationAveragingSite]
  change Matrix.toLin' (LinearMap.toMatrix' (siteMap a)) ∘ₗ _ = siteMap a
  rw [Matrix.toLin'_toMatrix']
  exact LinearMap.ext (apply_averageMap_of_forall_comp_eq hinv)

variable [Fintype Phys]
variable {width height : ℕ} [NeZero width] [NeZero height]

omit [NeZero width] [NeZero height] in
/-- The actual matrix of a local G-injective left inverse, chosen independently
at every site. Its composition with each tensor is its local invariant projector. -/
theorem exists_sitewisePhysicalMap_to_representationAveragingSite
    (ρ : TorusVertex width height → Representation ℂ G ((V × V × V × V) → ℂ))
    (a : TorusVertex width height → V → V → V → V → Phys → ℂ)
    (ha : ∀ v, IsGInjective (ρ v) (siteMap (a v))) :
    ∃ F : TorusVertex width height → Matrix (V × V × V × V) Phys ℂ,
      ∀ v, physicalMapSite (F v) (a v) = representationAveragingSite (ρ v) := by
  classical
  have hlocal v := ((isGInjective_iff_exists_leftInverse _ _).mp (ha v)).2
  choose L hL using hlocal
  refine ⟨fun v ↦ LinearMap.toMatrix' (L v), fun v ↦ ?_⟩
  apply (physicalMapSite_eq_iff_siteMap_comp _ _ _).mpr
  rw [siteMap_representationAveragingSite]
  change Matrix.toLin' (LinearMap.toMatrix' (L v)) ∘ₗ siteMap (a v) = (ρ v).averageMap
  rw [Matrix.toLin'_toMatrix', hL]

/-- A single product of local left inverses works simultaneously for every
cut and every arbitrary correlated boundary tensor. -/
theorem exists_torusCutMap_localInverse
    (ρ : TorusVertex width height → Representation ℂ G ((V × V × V × V) → ℂ))
    (a : TorusVertex width height → V → V → V → V → Phys → ℂ)
    (ha : ∀ v, IsGInjective (ρ v) (siteMap (a v))) :
    ∃ F : TorusVertex width height → Matrix (V × V × V × V) Phys ℂ,
      ∀ c r M, torusSitewisePhysicalMap F (torusCutMap a c r M) =
        torusCutMap (fun v ↦ representationAveragingSite (ρ v)) c r M := by
  obtain ⟨F, hF⟩ := exists_sitewisePhysicalMap_to_representationAveragingSite ρ a ha
  refine ⟨F, fun c r M ↦ ?_⟩
  rw [torusSitewisePhysicalMap_torusCutMap]
  simp_rw [hF]

omit [Fintype Phys] in
/-- The original site maps recover a cut contraction from its canonical one,
without changing its boundary tensor. -/
theorem torusCutMap_recover_representationAveragingSite
    (ρ : TorusVertex width height → Representation ℂ G ((V × V × V × V) → ℂ))
    (a : TorusVertex width height → V → V → V → V → Phys → ℂ)
    (hinv : ∀ v g, siteMap (a v) ∘ₗ ρ v g = siteMap (a v))
    (c : ZMod width) (r : ZMod height)
    (M : TorusCutBoundaryConfig width height V → ℂ) :
    torusSitewisePhysicalMap (fun v ↦ LinearMap.toMatrix' (siteMap (a v)))
        (torusCutMap (fun v ↦ representationAveragingSite (ρ v)) c r M) =
      torusCutMap a c r M := by
  rw [torusSitewisePhysicalMap_torusCutMap]
  simp_rw [physicalMapSite_representationAveragingSite _ _ (hinv _)]

omit [Fintype Phys] in
/-- The actual intersection of four cut ranges is the image of the canonical
four-cut intersection under the original site maps. The proof uses the same
local left inverse on all four cuts; it does not infer that images commute
with intersection for arbitrary linear maps. Source: SCP10, Theorem 5.5. -/
theorem fourTorusCutSpace_eq_map_representationAveragingSite [Finite Phys]
    (ρ : TorusVertex 2 2 → Representation ℂ G ((V × V × V × V) → ℂ))
    (a : TorusVertex 2 2 → V → V → V → V → Phys → ℂ)
    (ha : ∀ v, IsGInjective (ρ v) (siteMap (a v))) :
    fourTorusCutSpace a =
      (fourTorusCutSpace (fun v ↦ representationAveragingSite (ρ v))).map
        (torusSitewisePhysicalMap (fun v ↦ LinearMap.toMatrix' (siteMap (a v)))) := by
  let := Fintype.ofFinite Phys
  obtain ⟨F, hF⟩ := exists_torusCutMap_localInverse ρ a ha
  have hR := torusCutMap_recover_representationAveragingSite ρ a (fun v ↦ (ha v).invariant)
  apply le_antisymm
  · intro ψ hψ
    have hcuts := (mem_fourTorusCutSpace_iff a ψ).mp hψ
    refine ⟨torusSitewisePhysicalMap F ψ, ?_, ?_⟩
    · apply (mem_fourTorusCutSpace_iff _ _).mpr
      intro c r
      obtain ⟨M, hM⟩ := hcuts c r
      have heq : torusCutMap a c r M = ψ := funext hM
      refine ⟨M, fun σ ↦ ?_⟩
      exact congrFun ((hF c r M).symm.trans (congrArg (torusSitewisePhysicalMap F) heq)) σ
    · obtain ⟨M, hM⟩ := hcuts 0 0
      have heq : torusCutMap a 0 0 M = ψ := funext hM
      rw [← heq, hF, hR]
  · rintro _ ⟨χ, hχ, rfl⟩
    apply (mem_fourTorusCutSpace_iff _ _).mpr
    intro c r
    obtain ⟨M, hM⟩ := (mem_fourTorusCutSpace_iff _ _).mp hχ c r
    have heq : torusCutMap (fun v ↦ representationAveragingSite (ρ v)) c r M = χ :=
      funext hM
    refine ⟨M, fun σ ↦ ?_⟩
    exact congrFun ((hR c r M).symm.trans (congrArg
      (torusSitewisePhysicalMap (fun v ↦ LinearMap.toMatrix' (siteMap (a v)))) heq)) σ

end TNLean.PEPS
