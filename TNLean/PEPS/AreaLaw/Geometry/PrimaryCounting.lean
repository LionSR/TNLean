/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.PrimaryRegions

/-!
# Number of primary birth regions in one layer

The primary indices are exactly those open pitch interiors that meet the
actual dyadic layer. They form a finite set at every scale. When the cell
side is no greater than the pitch, each cell meets at most four pitch
interiors. Thus the number of primary indices is at most four times the
layer-cell count, uniformly in the origin and selected shifts.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, lines 212–218 and 237–238, in the proof
of `prop:two-families`. Source revision:
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

private def shiftedPitchOrigin (o : ℝ × ℝ) (ℓ : ℕ) (a b : ℤ) : ℝ × ℝ :=
  (o.1 + (2 : ℝ) ^ ℓ * a, o.2 + (2 : ℝ) ^ ℓ * b)

private def pitchCornerBox (o : ℝ × ℝ) (k ℓ p : ℕ) (a b : ℤ) (z : ℤ × ℤ) :
    Finset (ℤ × ℤ) :=
  let o' := shiftedPitchOrigin o ℓ a b
  let q := dyadicCellIndex o' p (o.1 + (2 : ℝ) ^ k * z.1, o.2 + (2 : ℝ) ^ k * z.2)
  let u := dyadicCellIndex o' p
    (o.1 + (2 : ℝ) ^ k * (z.1 + 1), o.2 + (2 : ℝ) ^ k * (z.2 + 1))
  (Finset.Icc q.1 u.1).product (Finset.Icc q.2 u.2)

/-- The finite set of primary indices, selected by nonempty intersection of the actual
layer with the open pitch interior. Source: area-law Section 11, lines 212–218 and 237–238. -/
def primaryPitchIndices (o : ℝ × ℝ) (k ℓ p : ℕ) (Z : Finset (ℤ × ℤ))
    (C : ℕ) (a b : ℤ) : Finset (ℤ × ℤ) := by
  classical
  exact ((dyadicLayerIndices o k Z C).biUnion (pitchCornerBox o k ℓ p a b)).filter
    (fun j ↦ (dyadicLayer o k Z C ∩ pitchInterior o ℓ p a b j).Nonempty)

private theorem pitchInterior_subset_shiftedCell (o : ℝ × ℝ) (ℓ p : ℕ)
    (a b : ℤ) (j : ℤ × ℤ) :
    pitchInterior o ℓ p a b j ⊆ dyadicCell (shiftedPitchOrigin o ℓ a b) p j := by
  intro x hx
  dsimp [pitchInterior, dyadicCell, shiftedPitchOrigin] at hx ⊢
  have ht : 0 ≤ (2 : ℝ) ^ ℓ := pow_nonneg zero_le_two ℓ
  exact ⟨⟨(le_add_of_nonneg_right ht).trans hx.1.1.le,
    by simpa only [mul_add, mul_one, add_assoc] using hx.1.2⟩,
    ⟨(le_add_of_nonneg_right ht).trans hx.2.1.le,
    by simpa only [mul_add, mul_one, add_assoc] using hx.2.2⟩⟩

private theorem coordinate_pitch_index_bounds {o o' r s x : ℝ} {z : ℤ}
    (hs : 0 < s) (hx : x ∈ Set.Ico (o + r * z) (o + r * (z + 1))) :
    ⌊(o + r * z - o') / s⌋ ≤ ⌊(x - o') / s⌋ ∧
      ⌊(x - o') / s⌋ ≤ ⌊(o + r * (z + 1) - o') / s⌋ :=
  ⟨Int.floor_mono (div_le_div_of_nonneg_right (sub_le_sub_right hx.1 o') hs.le),
    Int.floor_mono (div_le_div_of_nonneg_right (sub_le_sub_right hx.2.le o') hs.le)⟩

private theorem mem_pitchCornerBox_of_intersection (o : ℝ × ℝ) (k ℓ p : ℕ)
    (a b : ℤ) (j z : ℤ × ℤ) (x : ℝ × ℝ)
    (hx : x ∈ dyadicCell o k z) (hy : x ∈ pitchInterior o ℓ p a b j) :
    j ∈ pitchCornerBox o k ℓ p a b z := by
  have hj := (mem_dyadicCell_iff (shiftedPitchOrigin o ℓ a b) p j x).mp
    (pitchInterior_subset_shiftedCell o ℓ p a b j hy)
  rw [← hj]
  apply Finset.mem_product.mpr
  exact ⟨Finset.mem_Icc.mpr (coordinate_pitch_index_bounds (pow_pos zero_lt_two p) hx.1),
    Finset.mem_Icc.mpr (coordinate_pitch_index_bounds (pow_pos zero_lt_two p) hx.2)⟩

/-- A primary index is retained precisely when its open pitch interior meets the actual layer.
This equivalence holds at every scale. Source: area-law Section 11, lines 212–218 and 237–238. -/
theorem mem_primaryPitchIndices_iff (o : ℝ × ℝ) (k ℓ p : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (a b : ℤ) (j : ℤ × ℤ) :
    j ∈ primaryPitchIndices o k ℓ p Z C a b ↔
      (dyadicLayer o k Z C ∩ pitchInterior o ℓ p a b j).Nonempty := by
  classical
  simp only [primaryPitchIndices, Finset.mem_filter]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_, h⟩
    obtain ⟨x, hx, hy⟩ := h
    rw [dyadicLayer_eq_iUnion] at hx
    obtain ⟨z, hz, hx⟩ := Set.mem_iUnion₂.mp hx
    exact Finset.mem_biUnion.mpr
      ⟨z, hz, mem_pitchCornerBox_of_intersection o k ℓ p a b j z x hx hy⟩

private theorem card_floor_interval_le_two {x y : ℝ} (h : y ≤ x + 1) :
    (Finset.Icc ⌊x⌋ ⌊y⌋).card ≤ 2 := by
  have hf := Int.floor_mono h
  rw [Int.floor_add_one] at hf
  rw [Int.card_Icc]
  omega

private theorem card_pitchCornerBox_le (o : ℝ × ℝ) (k ℓ p : ℕ)
    (a b : ℤ) (z : ℤ × ℤ) (hkp : k ≤ p) :
    (pitchCornerBox o k ℓ p a b z).card ≤ 4 := by
  have hr : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ p := pow_le_pow_right₀ (by norm_num) hkp
  have hs : 0 < (2 : ℝ) ^ p := pow_pos zero_lt_two p
  have hc (v v' : ℝ) (i : ℤ) :
      (Finset.Icc ⌊(v + (2 : ℝ) ^ k * i - v') / (2 : ℝ) ^ p⌋
        ⌊(v + (2 : ℝ) ^ k * (i + 1) - v') / (2 : ℝ) ^ p⌋).card ≤ 2 := by
    apply card_floor_interval_le_two
    apply (div_le_iff₀ hs).mpr
    rw [add_mul, div_mul_cancel₀ _ hs.ne']
    nlinarith
  dsimp [pitchCornerBox, dyadicCellIndex]
  rw [Finset.card_product]
  exact Nat.mul_le_mul (hc _ _ _) (hc _ _ _)

/-- When the layer-cell side does not exceed the pitch, there are at most four primary
indices per layer cell. Source: area-law Section 11, lines 237–238. -/
theorem card_primaryPitchIndices_le (o : ℝ × ℝ) (k ℓ p : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (a b : ℤ) (hkp : k ≤ p) :
    (primaryPitchIndices o k ℓ p Z C a b).card ≤
      4 * (dyadicLayerIndices o k Z C).card := by
  classical
  unfold primaryPitchIndices
  calc
    _ ≤ ((dyadicLayerIndices o k Z C).biUnion (pitchCornerBox o k ℓ p a b)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ ∑ z ∈ dyadicLayerIndices o k Z C, (pitchCornerBox o k ℓ p a b z).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _z ∈ dyadicLayerIndices o k Z C, 4 :=
      Finset.sum_le_sum (fun z _ ↦ card_pitchCornerBox_le o k ℓ p a b z hkp)
    _ = 4 * (dyadicLayerIndices o k Z C).card := by simp [Nat.mul_comm]

/-- The actual number of primary indices is uniformly bounded by the physical cut boundary.
Source: area-law Section 11, lines 237–238. -/
theorem card_primaryPitchIndices_boundary_le (o : ℝ × ℝ) (k ℓ p : ℕ)
    (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (C : ℕ) (a b : ℤ) (hkp : k ≤ p) :
    (primaryPitchIndices o k ℓ p (boundaryEndpoints Λ A) C a b).card ≤
      32 * (2 * C + 1) ^ 2 * (edgeBoundary Λ A).card := by
  calc
    _ ≤ 4 * (dyadicLayerIndices o k (boundaryEndpoints Λ A) C).card :=
      card_primaryPitchIndices_le o k ℓ p (boundaryEndpoints Λ A) C a b hkp
    _ ≤ 4 * (8 * (2 * C + 1) ^ 2 * (edgeBoundary Λ A).card) :=
      Nat.mul_le_mul_left 4 (card_dyadicLayerIndices_boundary_le o k Λ A C)
    _ = 32 * (2 * C + 1) ^ 2 * (edgeBoundary Λ A).card := by ring

end TNLean.PEPS.AreaLaw.Geometry
