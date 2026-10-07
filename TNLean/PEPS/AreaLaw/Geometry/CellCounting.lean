/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.FiniteDomain
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite counts for ambient neighborhoods and cut endpoints

These are auxiliary cardinality bounds for the dyadic-layer construction in
OpenAI, *A two-dimensional area law from a global spectral gap*, September 24,
2026, Section 11, source lines 143–210. They do not construct the dyadic layers
or establish their geometric separation. No connectedness of the domain or
its cut is required.

Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

/-
Source: September 24, 2026.
Manuscript:
  preprints/
  A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
  build/sections/10-geometry.tex
Labels: prop:two-families.
Independently formalized; no upstream Lean proof text reused.
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.card_ambientdilation_le
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.card_ambientDilation_le
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.boundaryendpoints
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.boundaryEndpoints
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.card_boundaryendpoints_le
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.card_boundaryEndpoints_le
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.dyadicchildren
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.dyadicChildren
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.card_dyadicchildren
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.card_dyadicChildren
-/

open scoped BigOperators

namespace TNLean.PEPS.AreaLaw.Geometry

/-- An ambient integer neighborhood has at most one square of side `2r+1`
per point of its defining set. Source: Section 11, lines 163–185, the count of
cells whose indices are within sup distance `C₀` of an occupied cell index. -/
theorem card_ambientDilation_le (T : Finset (ℤ × ℤ)) (r : ℕ) :
    (ambientDilation T r).card ≤ (2 * r + 1) ^ 2 * T.card := by
  unfold ambientDilation
  refine Finset.card_biUnion_le.trans ?_
  have h (a : ℤ) : (a + (r : ℤ) + 1 - (a - r)).toNat = 2 * r + 1 := by omega
  simp [Finset.product_eq_sprod, h, pow_two, Nat.mul_comm]

/-- The ambient integer endpoints of the unordered crossing edges.
Source: Section 11, Proposition `prop:two-families`, lines 103–109, and
lines 163–185. These are the source set `Z`, not an ambient boundary. -/
noncomputable def boundaryEndpoints (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) :
    Finset (ℤ × ℤ) := by
  classical
  exact ((edgeBoundary Λ A).biUnion Sym2.toFinset).image Subtype.val

/-- There are at most two endpoints per crossing edge, even when the boundary
is empty. Source: Section 11, lines 179–185, `|Z| ≤ 2b`, absorbed into the
numerical constant there. This does not assert the layer-cell bound. -/
theorem card_boundaryEndpoints_le (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) :
    (boundaryEndpoints Λ A).card ≤ 2 * (edgeBoundary Λ A).card := by
  classical
  unfold boundaryEndpoints
  refine Finset.card_image_le.trans (Finset.card_biUnion_le.trans ?_)
  calc
    ∑ a ∈ edgeBoundary Λ A, a.toFinset.card ≤ ∑ _ ∈ edgeBoundary Λ A, 2 := by
      refine Finset.sum_le_sum fun a _ ↦ ?_
      rw [Sym2.card_toFinset]
      split_ifs <;> omega
    _ = 2 * (edgeBoundary Λ A).card := by simp [Nat.mul_comm]

/-- Integer indices of the four dyadic children of a parent cell.
Source: area-law Section 11, dyadic cells, lines 157–181. -/
def dyadicChildren (P : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  (P ×ˢ (Finset.univ : Finset (Fin 2 × Fin 2))).image
    fun (z, a) ↦ (2 * z.1 + (a.1.val : ℤ), 2 * z.2 + (a.2.val : ℤ))

/-- Distinct dyadic parents have disjoint four-element child families.
Source: area-law Section 11, dyadic cells and layer counting, lines 157–181. -/
theorem card_dyadicChildren (P : Finset (ℤ × ℤ)) :
    (dyadicChildren P).card = 4 * P.card := by
  have hinj : Function.Injective
      (fun (za : (ℤ × ℤ) × (Fin 2 × Fin 2)) ↦
        (2 * za.1.1 + (za.2.1.val : ℤ), 2 * za.1.2 + (za.2.2.val : ℤ))) := by
    rintro ⟨z, a⟩ ⟨w, b⟩ h
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    dsimp at h₁ h₂
    have hz : z = w := Prod.ext (by omega) (by omega)
    have ha : a = b := Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
    exact Prod.ext hz ha
  rw [dyadicChildren, Finset.card_image_of_injective _ hinj, Finset.card_product]
  simp [Nat.mul_comm]


end TNLean.PEPS.AreaLaw.Geometry
