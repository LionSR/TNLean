/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusMatchedBondRepresentation
import TNLean.PEPS.TorusProjectorExtraction

/-!
# Coherent coefficient extraction for matching semi-regular torus bonds

The trace-dual pairing on each individual bond extracts one coefficient from
an arbitrary coherent sum of products of representation matrices. Bond
representations may differ, and the eight bonds of a two-by-two torus remain
separately labelled. Thus equality of vectors implies equality of all their
bond-label coefficients; it does not justify equating labels term by term
before the trace pairing has been applied.

This is the coefficient-uniqueness step required in SCP10, Theorem 5.5,
lines 1488–1513, using Lemma 4.6. The separate step expressing an arbitrary
four-cut vector in this bond-product span is not asserted here.
-/

open scoped BigOperators

namespace TNLean.PEPS

variable {G V : Type*} [Group G] [Fintype G] [Fintype V] [DecidableEq V]
variable {width height : ℕ} [NeZero width] [NeZero height]

/-- Independent group labels on every horizontal and vertical bond, including
parallel bonds in a two-by-two torus. -/
abbrev TorusBondLabels (width height : ℕ) (G : Type*) :=
  (TorusVertex width height → G) × (TorusVertex width height → G)

/-- The physical endpoint vector given by one representation matrix on each
actual bond. This has no averaging or contraction of physical indices. -/
def torusRepresentationBondProduct
    (Uh Uv : TorusVertex width height → G →* Matrix V V ℂ)
    (p : TorusBondLabels width height G)
    (σ : TorusVertex width height → V × V × V × V) : ℂ :=
  ∏ v, Uh v (p.1 v) (σ (v.1 + 1, v.2)).2.2.2 (σ v).2.1 *
    Uv v (p.2 v) (σ v).1 (σ (v.1, v.2 + 1)).2.2.1

/-- The product of the source's trace-dual functionals, using the matching
representation on each actual bond. -/
noncomputable def torusBondCoefficientExtraction
    (Uh Uv : TorusVertex width height → G →* Matrix V V ℂ)
    (p : TorusBondLabels width height G) :
    ((TorusVertex width height → V × V × V × V) → ℂ) →ₗ[ℂ] ℂ :=
  torusOutputBondPairing (fun v ↦ torusDeltaPairing (Uh v) (p.1 v))
    (fun v ↦ torusDeltaPairing (Uv v) (p.2 v))

open Classical in
/-- The simultaneous trace pairing distinguishes the complete bond-label
configuration. Semi-regularity is assumed on every individual bond. -/
theorem torusBondCoefficientExtraction_bondProduct
    (Uh Uv : TorusVertex width height → G →* Matrix V V ℂ)
    (hU : IsSemiRegularTorusBondFamily Uh Uv)
    (p q : TorusBondLabels width height G) :
    torusBondCoefficientExtraction Uh Uv p (torusRepresentationBondProduct Uh Uv q) =
      if p = q then 1 else 0 := by
  unfold torusBondCoefficientExtraction torusRepresentationBondProduct
  rw [torusOutputBondPairing_bondProduct]
  simp only [torusDeltaPairing_apply_rep _ (hU.1 _),
    torusDeltaPairing_apply_rep _ (hU.2 _), Finset.prod_mul_distrib,
    Fintype.prod_boole, ← funext_iff]
  by_cases h₁ : p.1 = q.1
  · by_cases h₂ : p.2 = q.2
    · simp [Prod.ext h₁ h₂]
    · have h : p ≠ q := fun h ↦ h₂ (congrArg Prod.snd h)
      simp [h₁, h₂, h]
  · have h : p ≠ q := fun h ↦ h₁ (congrArg Prod.fst h)
    simp [h₁, h]

/-- Trace-dual extraction returns the coefficient of a specified configuration
from a coherent sum, so cancellations between other labels cause no ambiguity. -/
theorem torusBondCoefficientExtraction_sum
    (Uh Uv : TorusVertex width height → G →* Matrix V V ℂ)
    (hU : IsSemiRegularTorusBondFamily Uh Uv)
    (c : TorusBondLabels width height G → ℂ) (p : TorusBondLabels width height G) :
    torusBondCoefficientExtraction Uh Uv p
        (∑ q, c q • torusRepresentationBondProduct Uh Uv q) = c p := by
  classical
  simp [map_sum, torusBondCoefficientExtraction_bondProduct Uh Uv hU]

omit [Fintype G] in
/-- Products of matching semi-regular bond matrices are linearly independent
as actual functions of the physical endpoint coordinates. -/
theorem linearIndependent_torusRepresentationBondProduct [Finite G]
    (Uh Uv : TorusVertex width height → G →* Matrix V V ℂ)
    (hU : IsSemiRegularTorusBondFamily Uh Uv) :
    LinearIndependent ℂ (torusRepresentationBondProduct Uh Uv) := by
  classical
  let := Fintype.ofFinite G
  apply Fintype.linearIndependent_iff.mpr
  intro c hc p
  have h := congrArg (torusBondCoefficientExtraction Uh Uv p) hc
  simpa only [torusBondCoefficientExtraction_sum Uh Uv hU, map_zero] using h

/-- Equality of arbitrary coherent bond-product sums is coefficient equality. -/
theorem sum_torusRepresentationBondProduct_eq_iff
    (Uh Uv : TorusVertex width height → G →* Matrix V V ℂ)
    (hU : IsSemiRegularTorusBondFamily Uh Uv)
    (c d : TorusBondLabels width height G → ℂ) :
    (∑ q, c q • torusRepresentationBondProduct Uh Uv q) =
        (∑ q, d q • torusRepresentationBondProduct Uh Uv q) ↔ c = d := by
  constructor
  · intro h
    funext p
    have hp := congrArg (torusBondCoefficientExtraction Uh Uv p) h
    simpa only [torusBondCoefficientExtraction_sum Uh Uv hU] using hp
  · rintro rfl
    rfl

omit [Fintype G] [Fintype V] [DecidableEq V] in
/-- The four relative labels produced by the source's local-inverse expansion
obey its nonabelian compatibility relation. Source: SCP10, Theorem 5.5. -/
theorem fourBlock_relativeLabel_compatibility (a b c d : G) :
    (d⁻¹ * b) * (b⁻¹ * a) = (d⁻¹ * c) * (c⁻¹ * a) := by
  simp only [mul_assoc, mul_inv_cancel_left]

omit [Fintype G] [Fintype V] [DecidableEq V] in
/-- After coefficient extraction forces equal horizontal and equal vertical
labels, the source's compatibility relation is precisely commutation. -/
theorem fourBlock_compatibility_commute {h₁ h₂ v₁ v₂ : G}
    (hcompat : v₂ * h₁ = h₂ * v₁) (hh : h₁ = h₂) (hv : v₁ = v₂) :
    Commute v₁ h₁ := by
  subst h₂
  subst v₂
  exact hcompat

omit [Group G] [Fintype V] [DecidableEq V] in
/-- The two-by-two network has eight independently labelled bonds. -/
theorem card_torusBondLabels_two :
    Fintype.card (TorusBondLabels 2 2 G) = Fintype.card G ^ 8 := by
  simp only [TorusBondLabels, TorusVertex, Fintype.card_prod, Fintype.card_fun, ZMod.card]
  ring

end TNLean.PEPS
