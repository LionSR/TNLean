/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.DyadicLayers

/-!
# Fine-cell subdivision of dyadic layers

A coarse half-open dyadic cell is the disjoint union of its fine cells.
The exact subdivision and cardinality formulas apply to the actual layers
defined by the endpoint neighborhoods, including empty layers.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Section 11, `geometry:belt-count`, lines 200–237.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript:
  preprints/
  A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
  build/
  sections/
  10-geometry.tex
Labels: geometry:belt-count.
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.dyadicancestor
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.dyadicAncestor
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.dyadicrefinement
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.dyadicRefinement
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.mem_dyadicrefinement_iff
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.mem_dyadicRefinement_iff
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.card_dyadicrefinement
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.card_dyadicRefinement
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.dyadiccellindex_of_le
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.dyadicCellIndex_of_le
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.finelayerindices
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.fineLayerIndices
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.dyadiclayer_eq_iunion_fine
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.dyadicLayer_eq_iUnion_fine
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.card_finelayerindices
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.card_fineLayerIndices
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.card_finelayerindices_le
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.card_fineLayerIndices_le
Provenance-ID: 8758-tnlean.peps.arealaw.geometry.card_finelayerindices_boundary_le
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.card_fineLayerIndices_boundary_le
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The coarse ancestor of a fine dyadic cell index after the given number
of scales. Source: area-law Section 11, `geometry:belt-count`, lines 200–228. -/
def dyadicAncestor (depth : ℕ) (u : ℤ × ℤ) : ℤ × ℤ :=
  (u.1 / (2 : ℤ) ^ depth, u.2 / (2 : ℤ) ^ depth)

private def refinementIndex (depth : ℕ)
    (za : (ℤ × ℤ) × (Fin (2 ^ depth) × Fin (2 ^ depth))) : ℤ × ℤ :=
  ((2 : ℤ) ^ depth * za.1.1 + za.2.1.val,
    (2 : ℤ) ^ depth * za.1.2 + za.2.2.val)

private theorem dyadicAncestor_refinementIndex (depth : ℕ)
    (z : ℤ × ℤ) (a : Fin (2 ^ depth) × Fin (2 ^ depth)) :
    dyadicAncestor depth (refinementIndex depth (z, a)) = z := by
  have h (i : ℤ) (j : Fin (2 ^ depth)) :
      ((2 : ℤ) ^ depth * i + (j.val : ℤ)) / (2 : ℤ) ^ depth = i := by
    rw [Int.mul_add_ediv_left _ _ (pow_ne_zero _ (by norm_num))]
    rw [Int.ediv_eq_zero_of_lt (Int.natCast_nonneg _) (by exact_mod_cast j.isLt)]
    exact add_zero _
  exact Prod.ext (h z.1 a.1) (h z.2 a.2)

/-- All fine indices subdividing a finite set of coarse dyadic cells.
Source: area-law Section 11, `geometry:belt-count`, lines 200–228. -/
def dyadicRefinement (P : Finset (ℤ × ℤ)) (depth : ℕ) : Finset (ℤ × ℤ) :=
  (P ×ˢ (Finset.univ : Finset (Fin (2 ^ depth) × Fin (2 ^ depth)))).image
    (refinementIndex depth)

/-- Refinement membership is exactly membership of the coarse ancestor.
Source: area-law Section 11, `geometry:belt-count`, lines 200–228. -/
theorem mem_dyadicRefinement_iff (P : Finset (ℤ × ℤ)) (depth : ℕ) (u : ℤ × ℤ) :
    u ∈ dyadicRefinement P depth ↔ dyadicAncestor depth u ∈ P := by
  constructor
  · intro hu
    obtain ⟨⟨z, a⟩, hza, rfl⟩ := Finset.mem_image.mp hu
    rw [dyadicAncestor_refinementIndex]
    exact (Finset.mem_product.mp hza).1
  · intro hu
    have hp : 0 < (2 : ℤ) ^ depth := pow_pos (by norm_num) depth
    let a : Fin (2 ^ depth) × Fin (2 ^ depth) :=
      (⟨(u.1 % (2 : ℤ) ^ depth).toNat,
        (Int.toNat_lt (Int.emod_nonneg _ hp.ne')).mpr
          (by exact_mod_cast Int.emod_lt_of_pos u.1 hp)⟩,
        ⟨(u.2 % (2 : ℤ) ^ depth).toNat,
        (Int.toNat_lt (Int.emod_nonneg _ hp.ne')).mpr
          (by exact_mod_cast Int.emod_lt_of_pos u.2 hp)⟩)
    refine Finset.mem_image.mpr
      ⟨(dyadicAncestor depth u, a), Finset.mem_product.mpr ⟨hu, Finset.mem_univ _⟩, ?_⟩
    apply Prod.ext <;> dsimp [refinementIndex, dyadicAncestor, a]
    all_goals
      rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hp.ne'), Int.mul_ediv_add_emod]

/-- Each coarse dyadic cell has exactly four to the refinement depth fine cells.
Source: area-law Section 11, `geometry:belt-count`, lines 200–228. -/
theorem card_dyadicRefinement (P : Finset (ℤ × ℤ)) (depth : ℕ) :
    (dyadicRefinement P depth).card = 4 ^ depth * P.card := by
  have hinj : Function.Injective (refinementIndex depth) := by
    rintro ⟨z, a⟩ ⟨w, b⟩ h
    have hz : z = w := by
      simpa only [dyadicAncestor_refinementIndex] using congrArg (dyadicAncestor depth) h
    subst w
    have ha : a = b := by
      apply Prod.ext
      · apply Fin.ext
        have h₁ := congrArg Prod.fst h
        dsimp [refinementIndex] at h₁
        omega
      · apply Fin.ext
        have h₂ := congrArg Prod.snd h
        dsimp [refinementIndex] at h₂
        omega
    exact Prod.ext rfl ha
  rw [dyadicRefinement, Finset.card_image_of_injective _ hinj, Finset.card_product]
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  rw [← mul_pow]
  norm_num [Nat.mul_comm]

/-- Fine point indices map to their coarse point indices under dyadic ancestry.
Source: area-law Section 11, `geometry:belt-count`, lines 200–228. -/
theorem dyadicCellIndex_of_le (o : ℝ × ℝ) (ℓ k : ℕ) (x : ℝ × ℝ) (hℓk : ℓ ≤ k) :
    dyadicAncestor (k - ℓ) (dyadicCellIndex o ℓ x) = dyadicCellIndex o k x := by
  have h (a : ℝ) : ⌊a / (2 : ℝ) ^ (k - ℓ)⌋ = ⌊a⌋ / (2 : ℤ) ^ (k - ℓ) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using Int.floor_div_natCast a (2 ^ (k - ℓ))
  conv_rhs => rw [← Nat.add_sub_of_le hℓk]
  simp only [dyadicAncestor, dyadicCellIndex, pow_add, div_mul_eq_div_div, h]

/-- The actual fine-cell indices of a dyadic layer when the fine scale is no
larger than its layer scale.
Source: area-law Section 11, `geometry:belt-count`, lines 200–228. -/
noncomputable def fineLayerIndices (o : ℝ × ℝ) (k ℓ : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) : Finset (ℤ × ℤ) :=
  dyadicRefinement (dyadicLayerIndices o k Z C) (k - ℓ)

/-- Subdivision gives an exact fine-cell union of the actual dyadic layer.
Source: area-law Section 11, `geometry:belt-count`, lines 200–228. -/
theorem dyadicLayer_eq_iUnion_fine (o : ℝ × ℝ) (k ℓ : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (hℓk : ℓ ≤ k) :
    dyadicLayer o k Z C = ⋃ u ∈ fineLayerIndices o k ℓ Z C, dyadicCell o ℓ u := by
  ext x
  simp [dyadicLayer_eq_iUnion, fineLayerIndices, mem_dyadicCell_iff,
    mem_dyadicRefinement_iff, dyadicCellIndex_of_le o ℓ k x hℓk]

/-- Exact fine-cell cardinality, including empty index sets and depth zero.
Source: area-law Section 11, `geometry:belt-count`, lines 200–228. -/
theorem card_fineLayerIndices (o : ℝ × ℝ) (k ℓ : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ) :
    (fineLayerIndices o k ℓ Z C).card =
      4 ^ (k - ℓ) * (dyadicLayerIndices o k Z C).card :=
  card_dyadicRefinement _ _

/-- The number of fine layer cells is bounded by the endpoint count times
the squared ratio of cell sides.
Source: area-law Section 11, `geometry:belt-count`, lines 200–228. -/
theorem card_fineLayerIndices_le (o : ℝ × ℝ) (k ℓ : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) :
    (fineLayerIndices o k ℓ Z C).card ≤
      4 * (2 * C + 1) ^ 2 * Z.card * 4 ^ (k - ℓ) := by
  rw [card_fineLayerIndices]
  calc
    4 ^ (k - ℓ) * (dyadicLayerIndices o k Z C).card ≤
        4 ^ (k - ℓ) * (4 * (2 * C + 1) ^ 2 * Z.card) :=
      Nat.mul_le_mul_left _ (card_dyadicLayerIndices_le o k Z C)
    _ = 4 * (2 * C + 1) ^ 2 * Z.card * 4 ^ (k - ℓ) := by ring

/-- The number of fine cells in a cut layer is bounded by eight times the
squared neighborhood width, the crossing-edge count, and the squared ratio
of cell sides. Source: area-law Section 11, `geometry:belt-count`, lines 200–228. -/
theorem card_fineLayerIndices_boundary_le (o : ℝ × ℝ) (k ℓ : ℕ)
    (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (C : ℕ) :
    (fineLayerIndices o k ℓ (boundaryEndpoints Λ A) C).card ≤
      8 * (2 * C + 1) ^ 2 * (edgeBoundary Λ A).card * 4 ^ (k - ℓ) := by
  rw [card_fineLayerIndices]
  calc
    4 ^ (k - ℓ) * (dyadicLayerIndices o k (boundaryEndpoints Λ A) C).card ≤
        4 ^ (k - ℓ) * (8 * (2 * C + 1) ^ 2 * (edgeBoundary Λ A).card) :=
      Nat.mul_le_mul_left _ (card_dyadicLayerIndices_boundary_le o k Λ A C)
    _ = 8 * (2 * C + 1) ^ 2 * (edgeBoundary Λ A).card * 4 ^ (k - ℓ) := by ring

end TNLean.PEPS.AreaLaw.Geometry
