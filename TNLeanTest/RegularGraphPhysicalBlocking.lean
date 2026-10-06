/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularGraphPhysicalBlocking

/-! # Physical support transport, unused physical directions, and axiom regressions -/

noncomputable section
open TNLean.PEPS
open scoped Matrix

namespace RegularGraphPhysicalBlockingTest

private def extraPhysical {Y : Type*} [DecidableEq Y] : Matrix (Y ⊕ Unit) Y ℂ :=
  fun s η => match s with
    | Sum.inl σ => if σ = η then 1 else 0
    | Sum.inr _ => 0

private theorem extraPhysical_isIsometry {Y : Type*} [Fintype Y] [DecidableEq Y] :
    (extraPhysical (Y := Y)).IsIsometry := by
  ext η ξ
  simp [extraPhysical, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_sum_type, Matrix.one_apply, eq_comm]

variable {G K V : Type*} [Group G] [Fintype G] [DecidableEq G]
  [Fintype K] [DecidableEq K] [Fintype V] [LinearOrder V]
  {Γ : SimpleGraph V} [DecidableRel Γ.Adj]

attribute [local instance] Representation.invertibleFintypeCardComplex

private theorem canonical_isGIsometric (v : V) :
    IsGIsometric (graphIncidentRepresentation (Γ := Γ) (regularBundleMatrix (G := G) K) v)
      (regularSiteMap (graphAveragingSite (regularBundleMatrix K) v)) := by
  refine ⟨isGInjective_graphAveragingSite _ _, 1, zero_lt_one, ?_⟩
  intro x hx y hy
  rw [regularSiteMap_graphAveragingSite,
    Representation.averageMap_id _ _ hx, Representation.averageMap_id _ _ hy]
  simp

private def paddedSite (v : V) :
    (IncidentEdge Γ v → G × (K → G)) →
      ((IncidentEdge Γ v → G × (K → G)) ⊕ Unit) → ℂ :=
  regularPhysicalMapSite extraPhysical (graphAveragingSite (regularBundleMatrix K) v)

private theorem padded_isGIsometric (v : V) :
    IsGIsometric (graphIncidentRepresentation (Γ := Γ) (regularBundleMatrix (G := G) K) v)
      (regularSiteMap (paddedSite (Γ := Γ) v)) := by
  rw [paddedSite, regularSiteMap_regularPhysicalMapSite]
  exact (canonical_isGIsometric v).comp_isometry _ extraPhysical_isIsometry

-- The unused physical direction is genuinely absent from every column.
example (v : V) (η : IncidentEdge Γ v → G × (K → G)) :
    paddedSite v η (Sum.inr ()) = 0 := by
  simp [paddedSite, regularPhysicalMapSite, extraPhysical]

-- Ambient surjectivity is false in this actual G-isometric family.
example (v : V) : ¬ Function.Surjective
    (regularSiteMap (paddedSite (G := G) (K := K) (Γ := Γ) v)) := by
  intro h
  obtain ⟨x, hx⟩ := h (Pi.single (Sum.inr ()) 1)
  have hcoord := congrFun hx (Sum.inr ())
  change (∑ η, paddedSite (G := G) (K := K) (Γ := Γ) v η (Sum.inr ()) * x η) = 1 at hcoord
  simp [paddedSite, regularPhysicalMapSite, extraPhysical] at hcoord

-- The capstone still supplies a norm-preserving physical operation.
open scoped Classical in
example :
    let a := paddedSite (G := G) (K := K) (Γ := Γ)
    ∃ c : V → ℝ, (∀ v, 0 < c v) ∧
      star (regularGraphPhysicalDisentangler K a c (graphBondNetwork a)) ⬝ᵥ
        regularGraphPhysicalDisentangler K a c (graphBondNetwork a) =
          star (graphBondNetwork a) ⬝ᵥ graphBondNetwork a := by
  classical
  dsimp only
  obtain ⟨c, hc, _, _, hnorm, _⟩ := exists_regularGraphPhysicalDisentangler K
    (paddedSite (G := G) (K := K) (Γ := Γ)) padded_isGIsometric
  exact ⟨c, hc, hnorm⟩

-- A nonabelian group and a genuine edge are covered with those unused directions.
open scoped Classical in
example :
    let a := paddedSite (G := Equiv.Perm (Fin 3)) (K := Unit)
      (Γ := (⊤ : SimpleGraph (Fin 2)))
    ∃ c : Fin 2 → ℝ, (∀ v, 0 < c v) ∧
      star (regularGraphPhysicalDisentangler Unit a c (graphBondNetwork a)) ⬝ᵥ
        regularGraphPhysicalDisentangler Unit a c (graphBondNetwork a) =
          star (graphBondNetwork a) ⬝ᵥ graphBondNetwork a := by
  classical
  dsimp only
  obtain ⟨c, hc, _, _, hnorm, _⟩ := exists_regularGraphPhysicalDisentangler Unit
    (paddedSite (G := Equiv.Perm (Fin 3)) (K := Unit)
      (Γ := (⊤ : SimpleGraph (Fin 2)))) padded_isGIsometric
  exact ⟨c, hc, hnorm⟩

end RegularGraphPhysicalBlockingTest

set_option linter.hashCommand false

/--
info: 'TNLean.PEPS.IsGIsometric.exists_accessibleCoordinates'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.IsGIsometric.exists_accessibleCoordinates

/--
info: 'TNLean.PEPS.graphBondNetwork_mem_range_productSiteMap'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.graphBondNetwork_mem_range_productSiteMap

/--
info: 'TNLean.PEPS.graphPhysicalProductMap_dotProduct_on_range'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.graphPhysicalProductMap_dotProduct_on_range

/--
info: 'TNLean.PEPS.exists_regularGraphPhysicalDisentangler'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.exists_regularGraphPhysicalDisentangler

/--
info: 'TNLean.PEPS.coordinateSupportIsometry'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.coordinateSupportIsometry

/--
info: 'TNLean.PEPS.exists_regularGraphPhysicalSupportIsometry'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.exists_regularGraphPhysicalSupportIsometry
