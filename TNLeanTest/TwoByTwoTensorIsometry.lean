/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TwoByTwoTensorIsometry
import TNLean.PEPS.RegularProjectorOpenRegion
import TNLean.PEPS.GInjectivePhysicalMap
import TNLean.PEPS.RegularTwoByTwoOriginalTensor

/-! # Four-site contraction: nonabelian groups and unused physical directions -/

noncomputable section
open TNLean.PEPS
open scoped BigOperators Matrix

namespace TwoByTwoTensorIsometryTest

private def extraPhysical {Y : Type*} [DecidableEq Y] : Matrix (Y ⊕ Unit) Y ℂ :=
  fun s η => match s with
    | Sum.inl σ => if σ = η then 1 else 0
    | Sum.inr _ => 0

private theorem extraPhysical_isIsometry {Y : Type*} [Fintype Y] [DecidableEq Y] :
    (extraPhysical (Y := Y)).IsIsometry := by
  ext η ξ
  simp [extraPhysical, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_sum_type, Matrix.one_apply, eq_comm]

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

private def paddedSite : (Fin 4 → G) → ((Fin 4 → G) ⊕ Unit) → ℂ :=
  regularPhysicalMapSite extraPhysical
    (fun η θ => regularLegProjector (Fin 4) θ η)

private theorem paddedSite_isGIsometric :
    IsGIsometric (regularLegRepresentation (Fin 4))
      (regularSiteMap (paddedSite (G := G))) := by
  rw [paddedSite, regularSiteMap_regularPhysicalMapSite]
  exact isGIsometric_regularLegProjector.comp_isometry _ extraPhysical_isIsometry

-- The unused direction is absent from every original fine-site column.
example (η : Fin 4 → G) : paddedSite η (Sum.inr ()) = 0 := by
  simp [paddedSite, regularPhysicalMapSite, extraPhysical]

-- It remains an actual zero physical coordinate after contracting the internal cycle.
example (α : Fin 4 → G × G) :
    twoByTwoTensor (fun _ => paddedSite) α (fun _ => Sum.inr ()) = 0 := by
  simp [twoByTwoTensor, paddedSite, regularPhysicalMapSite, extraPhysical]

-- The blocked physical map need not be surjective onto its ambient space.
example : ¬ Function.Surjective
    (regularSiteMap (twoByTwoSeparatedTensor (fun _ => paddedSite (G := G)))) := by
  intro h
  obtain ⟨x, hx⟩ := h (Pi.single (fun _ => Sum.inr ()) 1)
  have hcoord := congrFun hx (fun _ => Sum.inr ())
  change (∑ η, twoByTwoSeparatedTensor (fun _ => paddedSite (G := G)) η
    (fun _ => Sum.inr ()) * x η) = 1 at hcoord
  simp [twoByTwoSeparatedTensor, twoByTwoTensor, paddedSite,
    regularPhysicalMapSite, extraPhysical] at hcoord

-- The nonabelian permutation group S₃ is covered, with those unused directions.
example :
    IsGIsometric (regularLegRepresentation (G := Equiv.Perm (Fin 3)) (Fin 4 × Fin 2))
      (regularSiteMap (twoByTwoSeparatedTensor (fun _ => paddedSite))) :=
  isGIsometric_twoByTwoSeparatedTensor _ (fun _ => paddedSite_isGIsometric)

-- All site-dependent positive factors remain in the exact unnormalized Gram identity.
example {P : Type*} [Fintype P] (a : Fin 4 → (Fin 4 → G) → P → ℂ)
    (ha : ∀ i, IsGIsometric (regularLegRepresentation (Fin 4)) (regularSiteMap (a i))) :
    ∃ c : Fin 4 → ℝ, (∀ i, 0 < c i) ∧ ∀ α β : Fin 4 → G × G,
      (∑ σ, star (twoByTwoTensor a α σ) * twoByTwoTensor a β σ) =
        (∏ i, (c i : ℂ)) * ∑ g : G, if α = g • β then 1 else 0 :=
  exists_twoByTwoTensor_gram a ha

private abbrev S3 := Equiv.Perm (Fin 3)
private abbrev PaddedS3 := (Fin 4 → S3) ⊕ Unit
local instance : Fact (2 < 3) := ⟨by decide⟩

-- The complete fine 6×6 → coarse 3×3 theorem retains the padded physical
-- space and gives the exact canonical-state × normalized-Bell factorization.
example :
    let a : TorusVertex 6 6 → (Fin 4 → S3) → PaddedS3 → ℂ := fun _ => paddedSite
    ∃ c : TorusVertex 3 3 → ℝ, (∀ v, 0 < c v) ∧
      ∃ I : twoByTwoFinePhysicalSupport (width := 3) (height := 3) a →ₗᵢ[ℂ]
        EuclideanSpace ℂ
          (((v : TorusVertex 3 3) → IncidentEdge (torusGraph 3 3) v → S3) ×
            ((v : TorusVertex 3 3) → IncidentEdge (torusGraph 3 3) v → (Unit → S3))),
        I ⟨WithLp.toLp 2 (twoByTwoFineState (width := 3) (height := 3) a),
            twoByTwoFineState_mem_physicalSupport (width := 3) (height := 3) a⟩ =
          WithLp.toLp 2 (fun σ => (∏ v, (Real.sqrt (c v) : ℂ)) *
            (Real.sqrt (Fintype.card (Unit → S3) : ℝ) : ℂ) ^
              Fintype.card (Edge (torusGraph 3 3)) *
            graphBondNetwork (Γ := torusGraph 3 3)
              (graphAveragingSite (leftRegularMatrix S3)) σ.1 *
              regularGraphNormalizedBell (G := S3) (Γ := torusGraph 3 3) Unit σ.2) := by
  dsimp only
  obtain ⟨c, hc, I, _, hstate⟩ :=
    exists_regularTwoByTwoPhysicalSupportIsometry (width := 3) (height := 3)
      (fun _ => paddedSite (G := S3)) (fun _ => paddedSite_isGIsometric)
  exact ⟨c, hc, I, hstate⟩

-- Nonvanishing needed for normalization is derived, including padded S₃ sites.
example :
    twoByTwoFineState (width := 3) (height := 3) (fun _ => paddedSite (G := S3)) ≠ 0 :=
  paddedSite_isGIsometric.twoByTwoFineState_ne_zero

example :
    graphBondNetwork (torusIncidentFamily
      (fun _ : TorusVertex 3 3 => paddedSite (G := S3))) ≠ 0 :=
  paddedSite_isGIsometric.graphBondNetwork_torusIncidentFamily_ne_zero

-- Surplus registers preserve a genuinely padded nonabelian original tensor.
example (v : TorusVertex 3 3) :
    IsGIsometric (graphIncidentRepresentation (regularBundleMatrix (G := S3) Unit) v)
      (regularSiteMap (regularGraphSurplusSite Unit
        (torusIncidentFamily (fun _ : TorusVertex 3 3 => paddedSite (G := S3))) v)) := by
  apply isGIsometric_regularGraphSurplusSite
  intro w
  rw [← graphIncidentRepresentation_leftRegularMatrix]
  exact paddedSite_isGIsometric.isGIsometric_torusIncidentFamily w

-- The augmented contraction contains the original physical tensor itself,
-- with its unused directions, and a separate actual surplus Bell product.
example (σ : TorusVertex 3 3 → PaddedS3)
    (τ : (v : TorusVertex 3 3) → IncidentEdge (torusGraph 3 3) v → Unit → S3) :
    graphBondNetwork (regularGraphSurplusSite Unit
      (torusIncidentFamily (fun _ : TorusVertex 3 3 => paddedSite (G := S3))))
        (fun v => (σ v, τ v)) =
      graphBondNetwork (torusIncidentFamily (fun _ : TorusVertex 3 3 => paddedSite)) σ *
        regularGraphResidualBell Unit τ :=
  graphBondNetwork_regularGraphSurplusSite Unit _ σ τ

-- The complete normalized theorem has the same original padded S₃ tensor
-- on the coarse lattice. Fine and coarse nonvanishing are conclusions.
example :
    let a := paddedSite (G := S3)
    let ψ := WithLp.toLp 2 (twoByTwoFineState (width := 3) (height := 3) (fun _ => a))
    let χ := WithLp.toLp 2
      (graphBondNetwork (torusIncidentFamily (fun _ : TorusVertex 3 3 => a)))
    let ω := WithLp.toLp 2
      (regularGraphNormalizedBell (G := S3) (Γ := torusGraph 3 3) Unit)
    ψ ≠ 0 ∧ χ ≠ 0 ∧ ‖ω‖ = 1 ∧
      ∃ I : twoByTwoFinePhysicalSupport (width := 3) (height := 3) (fun _ => a) →ₗᵢ[ℂ]
        EuclideanSpace ℂ ((TorusVertex 3 3 → PaddedS3) ×
          ((v : TorusVertex 3 3) → IncidentEdge (torusGraph 3 3) v → Unit → S3)),
        I ((‖ψ‖ : ℂ)⁻¹ • ⟨ψ,
          twoByTwoFineState_mem_physicalSupport (width := 3) (height := 3) (fun _ => a)⟩) =
            physicalStateProduct ((‖χ‖ : ℂ)⁻¹ • χ) ω := by
  dsimp only
  obtain ⟨hψ, hχ, hω, _, _, _, _, _, I, _, _, hnormalized⟩ :=
    exists_regularTwoByTwoOriginalTensorIsometry (width := 3) (height := 3)
      (paddedSite (G := S3)) paddedSite_isGIsometric
  exact ⟨hψ, hχ, hω, I, hnormalized⟩

end TwoByTwoTensorIsometryTest

set_option linter.hashCommand false

/--
info: 'TNLean.PEPS.IsGIsometric.of_coordinateEquiv'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.IsGIsometric.of_coordinateEquiv

/--
info: 'TNLean.PEPS.sum_twoByTwoSiteLegs_compatible'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.sum_twoByTwoSiteLegs_compatible

/--
info: 'TNLean.PEPS.exists_twoByTwoTensor_gram'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.exists_twoByTwoTensor_gram

/--
info: 'TNLean.PEPS.isGIsometric_twoByTwoSeparatedTensor'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.isGIsometric_twoByTwoSeparatedTensor

/--
info: 'TNLean.PEPS.exists_regularTwoByTwoPhysicalSupportIsometry'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.exists_regularTwoByTwoPhysicalSupportIsometry

/--
info: 'TNLean.PEPS.IsGIsometric.exists_canonicalSupportEquiv'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.IsGIsometric.exists_canonicalSupportEquiv

/--
info: 'TNLean.PEPS.IsGIsometric.exists_torusCanonicalSupportEquiv'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.IsGIsometric.exists_torusCanonicalSupportEquiv

/--
info: 'TNLean.PEPS.IsGIsometric.twoByTwoFineState_ne_zero'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.IsGIsometric.twoByTwoFineState_ne_zero

/--
info: 'TNLean.PEPS.IsGIsometric.graphBondNetwork_torusIncidentFamily_ne_zero'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.IsGIsometric.graphBondNetwork_torusIncidentFamily_ne_zero

/--
info: 'TNLean.PEPS.isGIsometric_regularGraphSurplusSite'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.isGIsometric_regularGraphSurplusSite

/--
info: 'TNLean.PEPS.graphBondNetwork_regularGraphSurplusSite'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.graphBondNetwork_regularGraphSurplusSite

/--
info: 'TNLean.PEPS.exists_regularTwoByTwoOriginalTensorIsometry'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.exists_regularTwoByTwoOriginalTensorIsometry

/--
info: 'TNLean.PEPS.IsGIsometric.exists_physicalSupportTransport'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.IsGIsometric.exists_physicalSupportTransport

/--
info: 'TNLean.PEPS.exists_graphGIsometricPhysicalSupportTransport'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.exists_graphGIsometricPhysicalSupportTransport

/--
info: 'TNLean.PEPS.norm_physicalStateProduct'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.norm_physicalStateProduct

/--
info: 'TNLean.PEPS.norm_normalized_physicalState'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.norm_normalized_physicalState

/--
info: 'TNLean.PEPS.LinearIsometry.normalized_physicalStateProduct'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.LinearIsometry.normalized_physicalStateProduct
