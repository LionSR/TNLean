/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Order.Filter.Basic
import TNLean.Algebra.CocycleRestriction

/-! # Native coboundary API with no local cohomology relation -/

open TNLean.Algebra
open scoped TNLean.Algebra.ScalarCohomology

variable {G : Type} [Group G]

-- No cocycle condition is required on the initial cochain or on the rephasing cochain.
example (ω : G × G → ℂˣ) (φ : G → ℂˣ) :
    groupCohomology.IsMulCoboundary₂
      ((fun p : G × G ↦ φ p.1 * φ p.2 * (φ (p.1 * p.2))⁻¹ * ω p) / ω) :=
  (isMulCoboundary₂_div_iff
    (fun p : G × G ↦ φ p.1 * φ p.2 * (φ (p.1 * p.2))⁻¹ * ω p) ω).mpr
      ⟨φ, fun _ _ ↦ rfl⟩

-- The cocycle proof for the first cochain is a conclusion, not a new premise.
example (ω η : G × G → ℂˣ) (hη : groupCohomology.IsMulCocycle₂ η)
    (hB : groupCohomology.IsMulCoboundary₂ (ω / η)) :
    groupCohomology.IsMulCocycle₂ ω :=
  isMulCocycle₂_of_isMulCoboundary₂_div hη hB

-- Only the cocycle being assigned an H² class needs a cocycle proof.
example (ω : G × G → ℂˣ) (hω : groupCohomology.IsMulCocycle₂ ω) :
    groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂ hω) = 0 ↔
      groupCohomology.IsMulCoboundary₂ ω :=
  H2π_eq_zero_iff_isMulCoboundary₂ hω

-- Commutator invariance requires commuting elements, but neither cochain must be a cocycle.
example (ω η : G × G → ℂˣ) (hB : groupCohomology.IsMulCoboundary₂ (ω / η))
    (g h : G) (hgh : g * h = h * g) :
    ScalarCocycle.commPhase ω g h = ScalarCocycle.commPhase η g h :=
  ScalarCocycle.commPhase_eq_of_isMulCoboundary₂_div hB hgh

-- Restriction acts on arbitrary cochains, not only those already carrying H² classes.
example {K : Type} [Group K] (ω η : G × G → ℂˣ)
    (hB : groupCohomology.IsMulCoboundary₂ (ω / η)) (f : K →* G) :
    groupCohomology.IsMulCoboundary₂ ((ω ∘ Prod.map f f) / (η ∘ Prod.map f f)) :=
  isMulCoboundary₂_div_comap hB f

-- Mathlib filter congruence transports the class/coboundary iff, including local witnesses.
section Eventually

variable {ι : Type*} {l : Filter ι}

example (ω η : ι → G × G → ℂˣ)
    (hω : ∀ i, groupCohomology.IsMulCocycle₂ (ω i))
    (hη : ∀ i, groupCohomology.IsMulCocycle₂ (η i))
    (h : ∀ᶠ i in l, groupCohomology.IsMulCoboundary₂ (ω i / η i)) :
    ∀ᶠ i in l, groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂ (hω i)) =
      groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂ (hη i)) := by
  apply (Filter.eventually_congr (.of_forall fun _ ↦
    H2π_eq_iff_isMulCoboundary₂_div _ _)).mpr
  exact h

example (ω η : ι → G × G → ℂˣ)
    (hω : ∀ i, groupCohomology.IsMulCocycle₂ (ω i))
    (hη : ∀ i, groupCohomology.IsMulCocycle₂ (η i))
    (h : ∀ᶠ i in l,
      groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂ (hω i)) =
        groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂ (hη i))) :
    ∀ᶠ i in l, groupCohomology.IsMulCoboundary₂ (ω i / η i) := by
  apply (Filter.eventually_congr (.of_forall fun _ ↦
    H2π_eq_iff_isMulCoboundary₂_div _ _)).mp
  exact h

example (ω η : ι → G × G → ℂˣ) (S : Set ι)
    (hω : ∀ i, ∀ _hi : i ∈ S, groupCohomology.IsMulCocycle₂ (ω i))
    (hη : ∀ i, groupCohomology.IsMulCocycle₂ (η i))
    (h : ∀ᶠ i in l, ∃ _hi : i ∈ S, groupCohomology.IsMulCoboundary₂ (ω i / η i)) :
    ∀ᶠ i in l, ∃ hi : i ∈ S,
      groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂ (hω i hi)) =
        groupCohomology.H2π _ (groupCohomology.cocyclesOfIsMulCocycle₂ (hη i)) := by
  exact (Filter.eventually_congr (.of_forall fun i ↦
    exists_congr fun hi ↦ H2π_eq_iff_isMulCoboundary₂_div (hω i hi) (hη i))).mpr h

end Eventually
