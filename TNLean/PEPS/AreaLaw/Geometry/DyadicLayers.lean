/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.CellCounting
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Translated dyadic neighborhoods and their layers

At nonnegative dyadic scales, coordinatewise floor indices describe the actual
half-open cells. Passing to parents preserves integer index neighborhoods,
which makes the enlarged occupied-cell unions nested. Their successive
set differences are finite unions of cells, with a count bounded uniformly
in the translation origin, scale, finite domain and cut.

These statements hold for every translation origin and every nonnegative
integer radius, including an empty endpoint set. Exhaustion of the plane,
closure-distance estimates, and the later two-family construction are separate
results; no such property is assumed here.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Section 11, source lines 151–185, the dyadic layers
  in the proof of `prop:two-families`.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The coordinatewise floor index in the translated half-open dyadic grid.
Source: area-law
Section 11, `prop:two-families`, lines 151–185. -/
noncomputable def dyadicCellIndex (o : ℝ × ℝ) (k : ℕ) (x : ℝ × ℝ) : ℤ × ℤ :=
  (⌊(x.1 - o.1) / (2 : ℝ) ^ k⌋, ⌊(x.2 - o.2) / (2 : ℝ) ^ k⌋)

/-- The coordinatewise integer parent of a dyadic cell index.
Source: area-law Section 11,
`prop:two-families`, lines 151–185. -/
def dyadicParent (z : ℤ × ℤ) : ℤ × ℤ := (z.1 / 2, z.2 / 2)

/-- The translated half-open square of side `2 ^ k`, at a nonnegative scale.
Source: area-law
Section 11, `prop:two-families`, lines 151–185. -/
def dyadicCell (o : ℝ × ℝ) (k : ℕ) (z : ℤ × ℤ) : Set (ℝ × ℝ) :=
  Set.Ico (o.1 + (2 : ℝ) ^ k * z.1) (o.1 + (2 : ℝ) ^ k * (z.1 + 1)) ×ˢ
    Set.Ico (o.2 + (2 : ℝ) ^ k * z.2) (o.2 + (2 : ℝ) ^ k * (z.2 + 1))

/-- Increasing the scale by one sends a cell index to its parent.
Source: area-law Section 11,
`prop:two-families`, lines 151–185. -/
theorem dyadicCellIndex_succ (o : ℝ × ℝ) (k : ℕ) (x : ℝ × ℝ) :
    dyadicCellIndex o (k + 1) x = dyadicParent (dyadicCellIndex o k x) := by
  have h (a : ℝ) : ⌊a / 2⌋ = ⌊a⌋ / 2 := Int.floor_div_natCast a 2
  simp only [dyadicCellIndex, dyadicParent, pow_succ, div_mul_eq_div_div, h]

/-- Every point belongs to exactly the half-open cell given by its floor index.
Source: area-law
Section 11, `prop:two-families`, lines 151–185. -/
theorem mem_dyadicCell_iff (o : ℝ × ℝ) (k : ℕ) (z : ℤ × ℤ) (x : ℝ × ℝ) :
    x ∈ dyadicCell o k z ↔ dyadicCellIndex o k x = z := by
  have h (t a : ℝ) (i : ℤ) :
      ⌊(t - a) / (2 : ℝ) ^ k⌋ = i ↔
        a + (2 : ℝ) ^ k * i ≤ t ∧ t < a + (2 : ℝ) ^ k * (i + 1) := by
    rw [Int.floor_eq_iff, le_div_iff₀ (pow_pos zero_lt_two k),
      div_lt_iff₀ (pow_pos zero_lt_two k), le_sub_iff_add_le, sub_lt_iff_lt_add]
    simp only [mul_comm, add_comm]
  simp only [dyadicCell, Set.mem_prod, Set.mem_Ico, dyadicCellIndex, Prod.ext_iff, h]

/-- Passing to dyadic parents preserves an integer coordinate-distance bound.
Source: area-law
Section 11, `prop:two-families`, lines 151–185. -/
theorem dyadicParent_abs_sub_le (u v : ℤ × ℤ) (C : ℕ)
    (h : |u.1 - v.1| ≤ (C : ℤ) ∧ |u.2 - v.2| ≤ (C : ℤ)) :
    |(dyadicParent u).1 - (dyadicParent v).1| ≤ (C : ℤ) ∧
      |(dyadicParent u).2 - (dyadicParent v).2| ≤ (C : ℤ) := by
  simp only [dyadicParent, abs_le] at h ⊢
  omega

private theorem mem_ambientDilation_iff (T : Finset (ℤ × ℤ)) (C : ℕ) (u : ℤ × ℤ) :
    u ∈ ambientDilation T C ↔
      ∃ v ∈ T, |u.1 - v.1| ≤ (C : ℤ) ∧ |u.2 - v.2| ≤ (C : ℤ) := by
  have h (a b : ℤ) :
      (a - C ≤ b ∧ b ≤ a + C) ↔ (-((C : ℤ)) ≤ b - a ∧ b - a ≤ C) := by omega
  simp only [ambientDilation, Finset.mem_biUnion, Finset.product_eq_sprod,
    Finset.mem_product, Finset.mem_Icc, abs_le, h]

/-- The parent of a nearby index lies near the parent image with the same radius.
Source: area-law
Section 11, `prop:two-families`, lines 151–185. -/
theorem dyadicParent_mem_ambientDilation_image {T : Finset (ℤ × ℤ)} {C : ℕ}
    {u : ℤ × ℤ} (h : u ∈ ambientDilation T C) :
    dyadicParent u ∈ ambientDilation (T.image dyadicParent) C := by
  rw [mem_ambientDilation_iff] at h ⊢
  obtain ⟨v, hv, huv⟩ := h
  exact ⟨dyadicParent v, Finset.mem_image.mpr ⟨v, hv, rfl⟩,
    dyadicParent_abs_sub_le u v C huv⟩

/-- The dyadic indices of the cells occupied by a finite set of integer points.
Source: area-law
Section 11, `prop:two-families`, lines 151–185. -/
noncomputable def occupiedCellIndices (o : ℝ × ℝ) (k : ℕ) (Z : Finset (ℤ × ℤ)) :
    Finset (ℤ × ℤ) :=
  Z.image fun z ↦ dyadicCellIndex o k ((z.1 : ℝ), (z.2 : ℝ))

/-- Occupied indices at the next scale are exactly the parent image.
Source: area-law Section 11,
`prop:two-families`, lines 151–185. -/
theorem occupiedCellIndices_succ (o : ℝ × ℝ) (k : ℕ) (Z : Finset (ℤ × ℤ)) :
    occupiedCellIndices o (k + 1) Z = (occupiedCellIndices o k Z).image dyadicParent := by
  simp only [occupiedCellIndices, Finset.image_image, dyadicCellIndex_succ, Function.comp_def]

/-- The union of cells whose indices are within the specified integer radius of an occupied index.
Source: area-law Section 11, `prop:two-families`, lines 151–185. -/
noncomputable def dyadicNeighborhood (o : ℝ × ℝ) (k : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) : Set (ℝ × ℝ) :=
  ⋃ z ∈ ambientDilation (occupiedCellIndices o k Z) C, dyadicCell o k z

/-- A point belongs to the dyadic neighborhood exactly when its index belongs to the enlarged
occupied set.
Source: area-law Section 11, `prop:two-families`, lines 151–185. -/
theorem mem_dyadicNeighborhood_iff (o : ℝ × ℝ) (k : ℕ) (Z : Finset (ℤ × ℤ))
    (C : ℕ) (x : ℝ × ℝ) :
    x ∈ dyadicNeighborhood o k Z C ↔
      dyadicCellIndex o k x ∈ ambientDilation (occupiedCellIndices o k Z) C := by
  simp [dyadicNeighborhood, mem_dyadicCell_iff]

/-- The actual dyadic neighborhoods are nested at every nonnegative scale.
Source: area-law Section
11, `prop:two-families`, lines 151–185. -/
theorem dyadicNeighborhood_subset_succ (o : ℝ × ℝ) (k : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) :
    dyadicNeighborhood o k Z C ⊆ dyadicNeighborhood o (k + 1) Z C := by
  intro x hx
  rw [mem_dyadicNeighborhood_iff] at hx ⊢
  rw [dyadicCellIndex_succ, occupiedCellIndices_succ]
  exact dyadicParent_mem_ambientDilation_image hx

/-- An integer index is a dyadic child precisely when its parent is in the given set.
Source: area-
law Section 11, `prop:two-families`, lines 151–185. -/
theorem mem_dyadicChildren_iff (P : Finset (ℤ × ℤ)) (u : ℤ × ℤ) :
    u ∈ dyadicChildren P ↔ dyadicParent u ∈ P := by
  constructor
  · intro h
    obtain ⟨⟨z, a⟩, hza, rfl⟩ := Finset.mem_image.mp h
    have hp (j : ℤ) (a : Fin 2) : (2 * j + (a.val : ℤ)) / 2 = j := by omega
    simpa only [dyadicParent, hp] using (Finset.mem_product.mp hza).1
  · intro h
    let a : Fin 2 × Fin 2 :=
      (⟨(u.1 % 2).toNat, by omega⟩, ⟨(u.2 % 2).toNat, by omega⟩)
    refine Finset.mem_image.mpr
      ⟨(dyadicParent u, a), Finset.mem_product.mpr ⟨h, Finset.mem_univ _⟩, ?_⟩
    apply Prod.ext <;> dsimp [dyadicParent, a] <;> omega

/-- The indices at the finer scale of the cells in the difference of successive neighborhoods.
Source: area-law Section 11, `prop:two-families`, lines 151–185. -/
noncomputable def dyadicLayerIndices (o : ℝ × ℝ) (k : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) : Finset (ℤ × ℤ) :=
  dyadicChildren (ambientDilation (occupiedCellIndices o (k + 1) Z) C) \
    ambientDilation (occupiedCellIndices o k Z) C

/-- The actual planar difference of successive dyadic neighborhoods.
Source: area-law Section 11,
`prop:two-families`, lines 151–185. -/
noncomputable def dyadicLayer (o : ℝ × ℝ) (k : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) : Set (ℝ × ℝ) :=
  dyadicNeighborhood o (k + 1) Z C \ dyadicNeighborhood o k Z C

/-- A dyadic layer is exactly the union of its indexed half-open cells.
Source: area-law Section
11, `prop:two-families`, lines 151–185. -/
theorem dyadicLayer_eq_iUnion (o : ℝ × ℝ) (k : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ) :
    dyadicLayer o k Z C = ⋃ z ∈ dyadicLayerIndices o k Z C, dyadicCell o k z := by
  ext x
  simp [dyadicLayer, dyadicLayerIndices, mem_dyadicNeighborhood_iff,
    mem_dyadicCell_iff, mem_dyadicChildren_iff, dyadicCellIndex_succ]

/-- The layer-cell count is bounded uniformly in the scale and translation origin.
Source: area-law
Section 11, `prop:two-families`, lines 151–185. -/
theorem card_dyadicLayerIndices_le (o : ℝ × ℝ) (k : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) :
    (dyadicLayerIndices o k Z C).card ≤ 4 * (2 * C + 1) ^ 2 * Z.card := by
  calc
    (dyadicLayerIndices o k Z C).card ≤
        (dyadicChildren (ambientDilation (occupiedCellIndices o (k + 1) Z) C)).card :=
      Finset.card_le_card Finset.sdiff_subset
    _ = 4 * (ambientDilation (occupiedCellIndices o (k + 1) Z) C).card :=
      card_dyadicChildren _
    _ ≤ 4 * ((2 * C + 1) ^ 2 * (occupiedCellIndices o (k + 1) Z).card) :=
      Nat.mul_le_mul_left 4 (card_ambientDilation_le _ _)
    _ ≤ 4 * ((2 * C + 1) ^ 2 * Z.card) :=
      Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left _ Finset.card_image_le)
    _ = 4 * (2 * C + 1) ^ 2 * Z.card := (Nat.mul_assoc _ _ _).symm

/-- The layer-cell count is at most eight times the squared neighborhood width times the crossing-
edge count.
Source: area-law Section 11, `prop:two-families`, lines 151–185. -/
theorem card_dyadicLayerIndices_boundary_le (o : ℝ × ℝ) (k : ℕ)
    (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (C : ℕ) :
    (dyadicLayerIndices o k (boundaryEndpoints Λ A) C).card ≤
      8 * (2 * C + 1) ^ 2 * (edgeBoundary Λ A).card := by
  have h := card_dyadicLayerIndices_le o k (boundaryEndpoints Λ A) C
  calc
    (dyadicLayerIndices o k (boundaryEndpoints Λ A) C).card ≤
        4 * (2 * C + 1) ^ 2 * (boundaryEndpoints Λ A).card := h
    _ ≤ 4 * (2 * C + 1) ^ 2 * (2 * (edgeBoundary Λ A).card) :=
      Nat.mul_le_mul_left _ (card_boundaryEndpoints_le Λ A)
    _ = 8 * (2 * C + 1) ^ 2 * (edgeBoundary Λ A).card := by ring

end TNLean.PEPS.AreaLaw.Geometry
