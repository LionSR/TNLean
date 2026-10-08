/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.DyadicLayers

/-!
# Exhaustion by translated dyadic neighborhoods

For a nonempty finite endpoint set and an integer radius at least two,
the enlarged occupied-cell neighborhoods exhaust the plane. The origin is
arbitrary. The proof uses an explicit Archimedean bound for the four translated
coordinates; it does not assume exhaustion or invoke a spectral hypothesis.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `prop:two-families`, lines 151–177.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The enlarged occupied-cell neighborhoods exhaust the plane for a nonempty
finite set. Source: area-law Section 11, `prop:two-families`, lines 151–177.
The origin is arbitrary; the source radius assumption is retained. -/
theorem exists_mem_dyadicNeighborhood (o : ℝ × ℝ) (Z : Finset (ℤ × ℤ))
    (C : ℕ) (hZ : Z.Nonempty) (hC : 2 ≤ C) (x : ℝ × ℝ) :
    ∃ k : ℕ, x ∈ dyadicNeighborhood o k Z C := by
  obtain ⟨z, hz⟩ := hZ
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt
    (|x.1 - o.1| + |x.2 - o.2| + |(z.1 : ℝ) - o.1| + |(z.2 : ℝ) - o.2|)
    (by norm_num : (1 : ℝ) < 2)
  have hp : 0 < (2 : ℝ) ^ k := pow_pos zero_lt_two k
  have floor_bounds (a : ℝ) (ha : |a| < (2 : ℝ) ^ k) :
      -1 ≤ ⌊a / (2 : ℝ) ^ k⌋ ∧ ⌊a / (2 : ℝ) ^ k⌋ ≤ 0 := by
    obtain ⟨ha₀, ha₁⟩ := abs_lt.mp ha
    have hlo : (-1 : ℝ) ≤ a / (2 : ℝ) ^ k :=
      (le_div_iff₀ hp).mpr (by linarith)
    have hhi : a / (2 : ℝ) ^ k < (1 : ℝ) :=
      (div_lt_iff₀ hp).mpr (by linarith)
    refine ⟨Int.le_floor.mpr (by simpa using hlo), ?_⟩
    have hf : ⌊a / (2 : ℝ) ^ k⌋ < (1 : ℤ) :=
      Int.floor_lt.mpr (by simpa using hhi)
    omega
  have hb : |x.1 - o.1| < (2 : ℝ) ^ k ∧ |x.2 - o.2| < (2 : ℝ) ^ k ∧
      |(z.1 : ℝ) - o.1| < (2 : ℝ) ^ k ∧ |(z.2 : ℝ) - o.2| < (2 : ℝ) ^ k := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [abs_nonneg (x.1 - o.1), abs_nonneg (x.2 - o.2),
      abs_nonneg ((z.1 : ℝ) - o.1), abs_nonneg ((z.2 : ℝ) - o.2)]
  have hx₁ := floor_bounds (x.1 - o.1) hb.1
  have hx₂ := floor_bounds (x.2 - o.2) hb.2.1
  have hz₁ := floor_bounds ((z.1 : ℝ) - o.1) hb.2.2.1
  have hz₂ := floor_bounds ((z.2 : ℝ) - o.2) hb.2.2.2
  refine ⟨k, ?_⟩
  rw [mem_dyadicNeighborhood_iff]
  simp only [ambientDilation, Finset.mem_biUnion, Finset.product_eq_sprod,
    Finset.mem_product, Finset.mem_Icc]
  refine ⟨dyadicCellIndex o k ((z.1 : ℝ), (z.2 : ℝ)), ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
  · simp only [dyadicCellIndex]
    constructor <;> constructor <;> omega

/-- The union of the enlarged occupied-cell neighborhoods is the whole plane.
Source: area-law Section 11, `prop:two-families`, lines 151–177. -/
theorem iUnion_dyadicNeighborhood_eq_univ (o : ℝ × ℝ) (Z : Finset (ℤ × ℤ))
    (C : ℕ) (hZ : Z.Nonempty) (hC : 2 ≤ C) :
    (⋃ k : ℕ, dyadicNeighborhood o k Z C) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact Set.mem_iUnion.mpr (exists_mem_dyadicNeighborhood o Z C hZ hC x)

end TNLean.PEPS.AreaLaw.Geometry
