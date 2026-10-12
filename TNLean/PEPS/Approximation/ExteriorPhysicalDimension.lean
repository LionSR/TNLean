/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.AffectedPhysicalDimension

/-!
# Exterior physical coordinates after owner identification

The complement of the affected party set retains its original local physical
dimensions. Its canonical basis is transported into the actual exterior memory
after both owner identifications; no discarded dimension enters this basis.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–151,
342–381 and 409–450.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-exterior-contraction; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
-/


noncomputable section
namespace TNLean.PEPS.PairEffect
variable {P : Type} [Fintype P] [DecidableEq P]

/-- The exterior output memory has the original physical coordinates of the
complementary party set. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 137–151 and 409–450. -/
def exteriorFamilyPhysicalBasis (d : P → ℕ) (ps : List P)
    (hps : ps.Nodup) (hcover : ∀ p : P, p ∈ ps) (A : Finset P) :
    let mask := fun p ↦ decide (p ∈ A)
    OrthonormalBasis ((p : {p // p ∈ Aᶜ}) → Fin (d p)) ℂ
      (Mem (Layout.restrict (fun p : Bool ↦ !p)
        (Layout.mapOwner (fun p : Option {p // mask p = true} ↦ p.isSome)
          (Layout.mapOwner (affectedOwner mask) (familyPhysicalLayout d ps))))) := by
  let mask := fun p ↦ decide (p ∈ A)
  have h : Layout.restrict (fun p ↦ decide (p ∈ Aᶜ)) (familyPhysicalLayout d ps) =
      Layout.restrict (fun p ↦ !mask p) (familyPhysicalLayout d ps) := by
    congr 1
    funext p
    simp [mask]
  exact (familyRestrictedPhysicalBasis d ps hps hcover Aᶜ).map
    ((Layout.memCongr h).trans
      (Layout.affectedOutputIso mask (fun p : Bool ↦ !p) (familyPhysicalLayout d ps)))

/-- The actual exterior physical dimension is the product of the original local
physical dimensions outside the affected set. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 137–151 and 356–381. -/
theorem finrank_exteriorFamilyPhysicalLayout (d : P → ℕ) (ps : List P)
    (hps : ps.Nodup) (hcover : ∀ p : P, p ∈ ps) (A : Finset P) :
    let mask := fun p ↦ decide (p ∈ A)
    Module.finrank ℂ (Mem (Layout.restrict (fun p : Bool ↦ !p)
      (Layout.mapOwner (fun p : Option {p // mask p = true} ↦ p.isSome)
        (Layout.mapOwner (affectedOwner mask) (familyPhysicalLayout d ps))))).carrier =
      ∏ p ∈ Aᶜ, d p := by
  simpa only [Fintype.card_pi, Fintype.card_fin, Finset.prod_coe_sort] using
    Module.finrank_eq_card_basis (exteriorFamilyPhysicalBasis d ps hps hcover A).toBasis

end TNLean.PEPS.PairEffect
