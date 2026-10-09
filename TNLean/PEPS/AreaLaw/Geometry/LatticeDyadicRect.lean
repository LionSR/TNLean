/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.BufferedRectangles
import TNLean.PEPS.AreaLaw.Geometry.CappedDyadicPartition
import TNLean.PEPS.AreaLaw.Geometry.TemplateClearance

/-!
# Integer rectangles of lattice dyadic squares

The origin-zero dyadic lattice square at scale k is an integer rectangle
of side length 2^k, including squares with negative coordinates. Its physical
intersection is the existing rectangle region.

Source: OpenAI, A two-dimensional area law from a global spectral gap,
September 24, 2026, Lemma 9.4, 08-scanner.tex, lines 641–649,
at openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
These independently written manuscript proofs are extracted unchanged from
TemplateSafeRectangles.lean.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The integer rectangle of a lattice dyadic cell, with closed integer
endpoints. Source: Lemma 9.4, the maximal contained dyadic square covering. -/
def latticeDyadicRect (k : ℕ) (z : ℤ × ℤ) : IntRect where
  x₀ := z.1 * (2 : ℤ) ^ k
  x₁ := z.1 * (2 : ℤ) ^ k + (2 : ℤ) ^ k - 1
  y₀ := z.2 * (2 : ℤ) ^ k
  y₁ := z.2 * (2 : ℤ) ^ k + (2 : ℤ) ^ k - 1
  hx := by
    have : 0 < (2 : ℤ) ^ k := by positivity
    omega
  hy := by
    have : 0 < (2 : ℤ) ^ k := by positivity
    omega

/-- The rectangle preserves every lattice point, including negative coordinates.
Source: Lemma 9.4, lines 641–649. -/
@[simp] theorem toFinset_latticeDyadicRect (k : ℕ) (z : ℤ × ℤ) :
    (latticeDyadicRect k z).toFinset = latticeDyadicCell k z := by
  rw [latticeDyadicCell_eq_Icc_product]
  rfl

/-- Rectangle size counts sites along an axis, so a side-`2^k` cell has size
exactly `2^k`, rather than its coordinate diameter `2^k - 1`. -/
@[simp] theorem size_latticeDyadicRect (k : ℕ) (z : ℤ × ℤ) :
    (latticeDyadicRect k z).size = 2 ^ k := by
  have h (a : ℤ) : (a + (2 : ℤ) ^ k - 1 + 1 - a).toNat = 2 ^ k := by
    have he : a + (2 : ℤ) ^ k - 1 + 1 - a = (2 : ℤ) ^ k := by omega
    rw [he, Int.toNat_pow_of_nonneg (by norm_num)]
    rfl
  simp only [IntRect.size, latticeDyadicRect, h, max_self]

/-- Physical intersections use the same native rectangle region as the safe-box
entropy interface; no ambient sites outside the domain are added. -/
theorem rectRegion_latticeDyadicRect {Λ : Finset (ℤ × ℤ)}
    (A : Finset (Site Λ)) (k : ℕ) (z : ℤ × ℤ) :
    rectRegion A (latticeDyadicRect k z) = A.filter (fun x ↦ x.1 ∈ latticeDyadicCell k z) := by
  simp only [rectRegion, toFinset_latticeDyadicRect]

end TNLean.PEPS.AreaLaw.Geometry
