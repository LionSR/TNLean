/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.NonbeltPrimaries

/-!
# Fine-cell decomposition of primary birth regions

A primary birth region is the finite union of the closed actual non-belt fine
cells with its shifted pitch index. This equality includes empty layers,
non-retained identifiers and equal fine and pitch scales. The primary keeps
one identifier even when its pieces are disconnected.

The fine exponent is at most the layer and pitch exponents. No lower bound on
the layer, dilation width or endpoint count is needed. Boundary points enter
through closure of the layer–pitch intersection, rather than an assignment to
an open pitch region.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `prop:two-families`, lines 212–218 and 299–323.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

private theorem fine_coordinate_pitch_index {o t s x : ℝ}
    (m : ℕ) (a : Fin m) (z j : ℤ) (ht : 0 < t) (hs : s = t * m)
    (hx : x ∈ Set.Ico (o + t * z) (o + t * (z + 1)))
    (hy : x ∈ Set.Ioo (o + t * a.val + s * j + t)
      (o + t * a.val + s * j + s)) :
    (z - a.val) / (m : ℤ) = j ∧ z % (m : ℤ) ≠ (a.val : ℤ) := by
  rw [hs] at hy
  have hlo : (a.val : ℝ) + (m : ℝ) * j + 1 < (z : ℝ) + 1 := by
    apply (mul_lt_mul_iff_right₀ ht).mp
    nlinarith only [hx.2, hy.1]
  have hhi : (z : ℝ) < (a.val : ℝ) + (m : ℝ) * j + m := by
    apply (mul_lt_mul_iff_right₀ ht).mp
    nlinarith only [hx.1, hy.2]
  have hlo' : (a.val : ℤ) + (m : ℤ) * j + 1 ≤ z := by
    have h : (a.val : ℤ) + (m : ℤ) * j + 1 < z + 1 := by exact_mod_cast hlo
    omega
  have hhi' : z < (a.val : ℤ) + (m : ℤ) * j + m := by exact_mod_cast hhi
  have hm : (0 : ℤ) < m := by exact_mod_cast (show 0 < m by omega)
  let r : ℤ := z - a.val - (m : ℤ) * j
  have hrlo : 0 < r := by dsimp [r]; omega
  have hrhi : r < m := by dsimp [r]; omega
  have hqr := (Int.ediv_emod_unique (a := z - a.val) (b := m) (r := r) (q := j) hm).mpr
    ⟨by dsimp [r]; ring, hrlo.le, hrhi⟩
  have ha : (a.val : ℤ) % (m : ℤ) = a.val :=
    Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast a.isLt)
  refine ⟨hqr.1, ?_⟩
  intro he
  have hrzero := Int.emod_eq_emod_iff_emod_sub_eq_zero.mp (he.trans ha.symm)
  rw [hqr.2] at hrzero
  omega

/-- A primary birth region is the finite union of the closed actual non-belt fine
cells with its shifted pitch index, including empty regions and equal fine and pitch scales.
Source: area-law Section 11, `prop:two-families`, lines 212–218 and 299–323. -/
theorem primaryBirthRegion_eq_iUnion_nonbeltCell_closure
    (o : ℝ × ℝ) (k ℓ p : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
    (a b : Fin (2 ^ (p - ℓ))) (J : ℤ × ℤ) (hℓk : ℓ ≤ k) (hℓp : ℓ ≤ p) :
    primaryBirthRegion o k ℓ p Z C a.val b.val J =
      ⋃ z ∈ (fineLayerIndices o k ℓ Z C).filter (fun z ↦
        z ∉ beltCellIndices (fineLayerIndices o k ℓ Z C) (2 ^ (p - ℓ)) a b ∧
          nonbeltPitchIndex ℓ p a.val b.val z = J), closure (dyadicCell o ℓ z) := by
  classical
  apply Set.Subset.antisymm
  · change closure (dyadicLayer o k Z C ∩ pitchInterior o ℓ p a.val b.val J) ⊆ _
    apply closure_minimal
    · intro x hx
      rcases hx with ⟨hLayer, hPitch⟩
      rw [dyadicLayer_eq_iUnion_fine o k ℓ Z C hℓk] at hLayer
      obtain ⟨z, hz, hcell⟩ := Set.mem_iUnion₂.mp hLayer
      have hs : (2 : ℝ) ^ p = (2 : ℝ) ^ ℓ * (2 ^ (p - ℓ) : ℕ) := by
        push_cast
        rw [← pow_add, Nat.add_sub_of_le hℓp]
      rw [dyadicCell] at hcell
      dsimp only [pitchInterior] at hPitch
      have h₁ := fine_coordinate_pitch_index (2 ^ (p - ℓ)) a z.1 J.1
        (pow_pos zero_lt_two ℓ) hs hcell.1 hPitch.1
      have h₂ := fine_coordinate_pitch_index (2 ^ (p - ℓ)) b z.2 J.2
        (pow_pos zero_lt_two ℓ) hs hcell.2 hPitch.2
      have hnot : z ∉ beltCellIndices (fineLayerIndices o k ℓ Z C)
          (2 ^ (p - ℓ)) a b := by
        simp only [beltCellIndices, Finset.mem_filter]
        rintro ⟨_, hres⟩
        exact hres.elim h₁.2 h₂.2
      have hindex : nonbeltPitchIndex ℓ p a.val b.val z = J := by
        apply Prod.ext
        · change (z.1 - a.val) / (2 : ℤ) ^ (p - ℓ) = J.1
          simpa only [Nat.cast_pow, Nat.cast_ofNat] using h₁.1
        · change (z.2 - b.val) / (2 : ℤ) ^ (p - ℓ) = J.2
          simpa only [Nat.cast_pow, Nat.cast_ofNat] using h₂.1
      exact Set.mem_iUnion₂.mpr
        ⟨z, Finset.mem_filter.mpr ⟨hz, hnot, hindex⟩, subset_closure hcell⟩
    · exact isClosed_biUnion_finset (fun _ _ ↦ isClosed_closure)
  · intro x hx
    obtain ⟨z, hz, hcell⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨hz, hnot, hindex⟩ := Finset.mem_filter.mp hz
    have h := closure_nonbeltCell_subset_primaryBirthRegion o k ℓ p Z C a b z
      hℓk hℓp hz hnot hcell
    simpa only [hindex] using h

end TNLean.PEPS.AreaLaw.Geometry
