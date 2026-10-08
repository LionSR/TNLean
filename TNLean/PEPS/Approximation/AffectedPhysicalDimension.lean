/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.FamilyPhysicalReadout
import TNLean.PEPS.Approximation.AffectedOwners
import TNLean.PEPS.Approximation.LayoutOwnerMap

/-!
# Physical dimensions after the affected-party identifications

Relabelling owners preserves the actual selected memory. The two owner maps
used in the corrected-source decomposition therefore preserve the product of
the original affected physical dimensions, even when these dimensions differ
from party to party.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–151,
342–381 and 409–450.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-exterior-contraction; Theorem 5.2, lines 409–480.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-source-resource-affectedphysicaldimension-01
TNLean.PEPS.PairEffect.Layout.affectedOutputIso
Provenance-ID: 8769-source-resource-affectedphysicaldimension-02
TNLean.PEPS.PairEffect.Layout.restrictMapOwnerIso
Provenance-ID: 8769-source-resource-affectedphysicaldimension-03
TNLean.PEPS.PairEffect.Layout.restrict_mapOwner
Provenance-ID: 8769-source-resource-affectedphysicaldimension-04
TNLean.PEPS.PairEffect.affectedFamilyPhysicalBasis
Provenance-ID: 8769-source-resource-affectedphysicaldimension-05
TNLean.PEPS.PairEffect.finrank_affectedFamilyPhysicalLayout
-/


noncomputable section
namespace TNLean.PEPS.PairEffect.Layout
variable {P Q : Type}

/-- Selecting registers after an owner map is the owner map of the selected
original registers. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 342–364 and 409–450. -/
theorem restrict_mapOwner (f : P → Q) (g : Q → Bool) (a : Layout P) :
    restrict g (mapOwner f a) = mapOwner f (restrict (fun p ↦ g (f p)) a) := by
  simp [restrict, mapOwner, List.filter_map, Function.comp_def]

/-- The canonical isometry of the selected memories before and after relabelling.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–450. -/
def restrictMapOwnerIso (f : P → Q) (g : Q → Bool) (a : Layout P) :
    Mem (restrict (fun p ↦ g (f p)) a) ≃ₗᵢ[ℂ] Mem (restrict g (mapOwner f a)) :=
  (mapOwnerIso f _).trans (memCongr (restrict_mapOwner f g a).symm)

/-- The second owner map distinguishes exactly the original affected parties. -/
private theorem affectedOwner_isSome (A : P → Bool) (p : P) :
    (affectedOwner A p).isSome = A p := by
  cases h : A p <;> simp [affectedOwner, h]

/-- Either original side is isometric to the same side of the actual output
registers after both owner identifications. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 342–364 and 409–450. -/
def affectedOutputIso (A : P → Bool) (f : Bool → Bool) (a : Layout P) :
    Mem (restrict (fun p ↦ f (A p)) a) ≃ₗᵢ[ℂ]
      Mem (restrict f
        (mapOwner (fun p : Option {p // A p = true} ↦ p.isSome)
          (mapOwner (affectedOwner A) a))) :=
  let side := fun p : Option {p // A p = true} ↦ p.isSome
  let h : restrict (fun p ↦ f (side (affectedOwner A p))) a =
      restrict (fun p ↦ f (A p)) a := by
    congr 1
    funext p
    exact congrArg f (affectedOwner_isSome A p)
  (memCongr h.symm).trans
    ((restrictMapOwnerIso (affectedOwner A) (fun p ↦ f (side p)) a).trans
      (restrictMapOwnerIso side f (mapOwner (affectedOwner A) a)))

end TNLean.PEPS.PairEffect.Layout

namespace TNLean.PEPS.PairEffect
variable {P : Type} [DecidableEq P]

/-- The actual affected output memory has coordinates in the original local
physical dimensions. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 137–151 and 409–450. -/
def affectedFamilyPhysicalBasis (d : P → ℕ) (ps : List P)
    (hps : ps.Nodup) (hcover : ∀ p : P, p ∈ ps) (A : Finset P) :
    let mask := fun p ↦ decide (p ∈ A)
    OrthonormalBasis ((p : {p // p ∈ A}) → Fin (d p)) ℂ
      (Mem (Layout.restrict (fun p : Bool ↦ p)
        (Layout.mapOwner (fun p : Option {p // mask p = true} ↦ p.isSome)
          (Layout.mapOwner (affectedOwner mask) (familyPhysicalLayout d ps))))) :=
  (familyRestrictedPhysicalBasis d ps hps hcover A).map
    (Layout.affectedOutputIso (fun p ↦ decide (p ∈ A)) (fun p : Bool ↦ p)
      (familyPhysicalLayout d ps))

/-- The dimension of the actual twice-relabeled affected physical memory is
the product of the original affected local dimensions.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–151 and 356–381. -/
theorem finrank_affectedFamilyPhysicalLayout (d : P → ℕ) (ps : List P)
    (hps : ps.Nodup) (hcover : ∀ p : P, p ∈ ps) (A : Finset P) :
    let mask := fun p ↦ decide (p ∈ A)
    Module.finrank ℂ (Mem (Layout.restrict (fun p : Bool ↦ p)
      (Layout.mapOwner (fun p : Option {p // mask p = true} ↦ p.isSome)
        (Layout.mapOwner (affectedOwner mask) (familyPhysicalLayout d ps))))).carrier =
      ∏ p ∈ A, d p := by
  simpa only [Fintype.card_pi, Fintype.card_fin, Finset.prod_coe_sort] using
    Module.finrank_eq_card_basis (affectedFamilyPhysicalBasis d ps hps hcover A).toBasis

end TNLean.PEPS.PairEffect
