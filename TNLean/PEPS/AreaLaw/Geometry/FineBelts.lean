/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.DyadicRefinement
import TNLean.PEPS.AreaLaw.Geometry.DyadicScales
import TNLean.PEPS.AreaLaw.Geometry.SparseBelts
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Sparse belts in dyadic layers

Finite averaging selects vertical and horizontal residue classes among
the fine cells of each actual dyadic layer. Combining the exact cell count
with the rounded source scales gives decay with an explicit constant.
The estimate does not require an entropy inequality or an assumed partition.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Section 11, `geometry:belt-count`, lines 200–237.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

private theorem dyadic_scale_ratio (ℓ k p : ℕ) (hℓk : ℓ ≤ k) (hℓp : ℓ ≤ p) :
    (4 : ℝ) ^ (k - ℓ) / (2 : ℝ) ^ (p - ℓ) =
      (2 : ℝ) ^ (2 * (k : ℝ) - (p : ℝ) - (ℓ : ℝ)) := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul,
    ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_sub (by norm_num)]
  congr 1
  push_cast
  rw [Nat.cast_sub hℓk, Nat.cast_sub hℓp]
  ring

/-- The layer-to-pitch and layer-to-fine ratios give geometric decay with
rounding factor four. Source: Section 11, `geometry:belt-count`, lines 220–228. -/
theorem dyadicScale_ratio_le (k : ℕ) :
    (4 : ℝ) ^ (k - fineScaleIndex k) /
        (2 : ℝ) ^ (pitchScaleIndex k - fineScaleIndex k) ≤
      4 * (2 : ℝ) ^ (-(Exponents.geometryDelta : ℝ) * (k : ℝ) / 2) := by
  rw [dyadic_scale_ratio _ _ _ (fineScaleIndex_le k)
    ((fineScaleIndex_le k).trans (le_pitchScaleIndex k))]
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (layerScale_exponent_le k)
  calc
    _ ≤ (2 : ℝ) ^ (2 - (Exponents.geometryDelta : ℝ) * (k : ℝ) / 2) := h
    _ = _ := by
      rw [show (2 : ℝ) - (Exponents.geometryDelta : ℝ) * (k : ℝ) / 2 =
        2 + (-(Exponents.geometryDelta : ℝ) * (k : ℝ) / 2) by ring,
        Real.rpow_add (by norm_num)]
      norm_num

/-- Indices selected by one vertical or horizontal residue class.
Source: area-law Section 11, `geometry:belt-count`, lines 212–228. -/
def beltCellIndices (F : Finset (ℤ × ℤ)) (m : ℕ) (a b : Fin m) : Finset (ℤ × ℤ) :=
  F.filter fun z ↦ z.1 % (m : ℤ) = (a.val : ℤ) ∨ z.2 % (m : ℤ) = (b.val : ℤ)

/-- Finite residue averaging selects sparse belt cells from an actual refined layer.
The combinatorial bound holds at all indices; the physical fine-cell union uses
`ℓ ≤ k`. Source: area-law Section 11, `geometry:belt-count`, lines 220–228. -/
theorem exists_fine_belt_shift (o : ℝ × ℝ) (k ℓ p : ℕ)
    (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (C : ℕ) :
    ∃ a b : Fin (2 ^ (p - ℓ)),
      2 ^ (p - ℓ) *
          (beltCellIndices (fineLayerIndices o k ℓ (boundaryEndpoints Λ A) C)
            (2 ^ (p - ℓ)) a b).card ≤
        16 * (2 * C + 1) ^ 2 * (edgeBoundary Λ A).card * 4 ^ (k - ℓ) := by
  obtain ⟨a, b, hab⟩ := exists_sparse_belt_shift
    (fineLayerIndices o k ℓ (boundaryEndpoints Λ A) C)
    (2 ^ (p - ℓ)) (pow_pos (by norm_num) _)
  refine ⟨a, b, hab.trans ?_⟩
  calc
    2 * (fineLayerIndices o k ℓ (boundaryEndpoints Λ A) C).card ≤
        2 * (8 * (2 * C + 1) ^ 2 * (edgeBoundary Λ A).card * 4 ^ (k - ℓ)) :=
      Nat.mul_le_mul_left 2 (card_fineLayerIndices_boundary_le o k ℓ Λ A C)
    _ = _ := by ring

/-- The source sparse-belt estimate, with an explicit uniform constant and
both floor losses accounted for. Source: area-law Section 11,
`geometry:belt-count`, lines 220–228. -/
theorem exists_sparse_dyadic_belt_shift (o : ℝ × ℝ) (k : ℕ)
    (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (C : ℕ) :
    ∃ a b : Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k)),
      ((beltCellIndices (fineLayerIndices o k (fineScaleIndex k)
          (boundaryEndpoints Λ A) C) (2 ^ (pitchScaleIndex k - fineScaleIndex k))
        a b).card : ℝ) ≤
      64 * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card *
        (2 : ℝ) ^ (-(Exponents.geometryDelta : ℝ) * (k : ℝ) / 2) := by
  obtain ⟨a, b, hab⟩ := exists_fine_belt_shift o k (fineScaleIndex k)
    (pitchScaleIndex k) Λ A C
  refine ⟨a, b, ?_⟩
  let ℓ := fineScaleIndex k
  let p := pitchScaleIndex k
  let F := fineLayerIndices o k ℓ (boundaryEndpoints Λ A) C
  let B := beltCellIndices F (2 ^ (p - ℓ)) a b
  let coeff : ℝ := 16 * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card
  have hreal : (2 : ℝ) ^ (p - ℓ) * (B.card : ℝ) ≤ coeff * (4 : ℝ) ^ (k - ℓ) := by
    dsimp [coeff, B, F, ℓ, p]
    exact_mod_cast hab
  have hcount : (B.card : ℝ) ≤ coeff *
      ((4 : ℝ) ^ (k - ℓ) / (2 : ℝ) ^ (p - ℓ)) := by
    rw [← mul_div_assoc]
    exact (le_div_iff₀ (pow_pos zero_lt_two _)).mpr
      (by simpa only [mul_comm] using hreal)
  calc
    _ ≤ coeff * ((4 : ℝ) ^ (k - ℓ) / (2 : ℝ) ^ (p - ℓ)) := hcount
    _ ≤ coeff * (4 * (2 : ℝ) ^ (-(Exponents.geometryDelta : ℝ) * (k : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left (dyadicScale_ratio_le k) (by dsimp [coeff]; positivity)
    _ = _ := by dsimp [coeff]; ring

end TNLean.PEPS.AreaLaw.Geometry
