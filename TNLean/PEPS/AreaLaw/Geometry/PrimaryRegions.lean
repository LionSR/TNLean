/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.DistanceLayers
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Primary birth regions between periodic belts

The open squares between the periodic belts are intersected with an actual
dyadic layer. Their closures are the primary birth regions. Each such region
has diameter at most the belt pitch, and two different regions in the same
layer are separated by at least the belt width. All distances are measured
in the sup metric on the plane.

The shifts are integer representatives of the selected residue classes.
The definitions also cover an empty intersection without an additional
nonemptiness assumption.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:primary-pieces`, lines 212–218
and 237–249. Source revision:
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The open square between consecutive horizontal and vertical belts.
Source: area-law Section 11, lines 212–218. -/
def pitchInterior (o : ℝ × ℝ) (ℓ p : ℕ) (a b : ℤ) (j : ℤ × ℤ) : Set (ℝ × ℝ) :=
  Set.Ioo (o.1 + (2 : ℝ) ^ ℓ * a + (2 : ℝ) ^ p * j.1 + (2 : ℝ) ^ ℓ)
      (o.1 + (2 : ℝ) ^ ℓ * a + (2 : ℝ) ^ p * j.1 + (2 : ℝ) ^ p) ×ˢ
    Set.Ioo (o.2 + (2 : ℝ) ^ ℓ * b + (2 : ℝ) ^ p * j.2 + (2 : ℝ) ^ ℓ)
      (o.2 + (2 : ℝ) ^ ℓ * b + (2 : ℝ) ^ p * j.2 + (2 : ℝ) ^ p)

/-- A closed fragment of one layer cell in a pitch interior.
Source: area-law Section 11, `geometry:primary-pieces`, lines 239–246. -/
def primaryFragment (o : ℝ × ℝ) (k ℓ p : ℕ) (a b : ℤ) (j z : ℤ × ℤ) :
    Set (ℝ × ℝ) :=
  closure (dyadicCell o k z ∩ pitchInterior o ℓ p a b j)

/-- Exactly those layer cells whose intersections with the pitch interior are nonempty.
Source: area-law Section 11, `geometry:primary-pieces`, lines 239–246. -/
def primaryFragmentIndices (o : ℝ × ℝ) (k ℓ p : ℕ) (Z : Finset (ℤ × ℤ))
    (C : ℕ) (a b : ℤ) (j : ℤ × ℤ) : Finset (ℤ × ℤ) := by
  classical
  exact (dyadicLayerIndices o k Z C).filter
    (fun z ↦ (dyadicCell o k z ∩ pitchInterior o ℓ p a b j).Nonempty)

/-- The closure of the part of an actual layer lying between the selected belts.
Source: area-law Section 11, lines 215–218 and `geometry:primary-pieces`, lines 239–249. -/
def primaryBirthRegion (o : ℝ × ℝ) (k ℓ p : ℕ) (Z : Finset (ℤ × ℤ))
    (C : ℕ) (a b : ℤ) (j : ℤ × ℤ) : Set (ℝ × ℝ) :=
  closure (dyadicLayer o k Z C ∩ pitchInterior o ℓ p a b j)

private theorem closure_pitchInterior_subset (o : ℝ × ℝ) (ℓ p : ℕ)
    (a b : ℤ) (j : ℤ × ℤ) :
    closure (pitchInterior o ℓ p a b j) ⊆
      Set.Icc (o.1 + (2 : ℝ) ^ ℓ * a + (2 : ℝ) ^ p * j.1 + (2 : ℝ) ^ ℓ)
        (o.1 + (2 : ℝ) ^ ℓ * a + (2 : ℝ) ^ p * j.1 + (2 : ℝ) ^ p) ×ˢ
      Set.Icc (o.2 + (2 : ℝ) ^ ℓ * b + (2 : ℝ) ^ p * j.2 + (2 : ℝ) ^ ℓ)
        (o.2 + (2 : ℝ) ^ ℓ * b + (2 : ℝ) ^ p * j.2 + (2 : ℝ) ^ p) := by
  apply closure_minimal _ (isClosed_Icc.prod isClosed_Icc)
  intro x hx
  exact ⟨⟨hx.1.1.le, hx.1.2.le⟩, ⟨hx.2.1.le, hx.2.2.le⟩⟩

/-- A primary birth region lies in the closure of its pitch interior.
Source: area-law Section 11, `geometry:primary-pieces`, lines 239–246. -/
theorem primaryBirthRegion_subset_closure_pitchInterior (o : ℝ × ℝ) (k ℓ p : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (a b : ℤ) (j : ℤ × ℤ) :
    primaryBirthRegion o k ℓ p Z C a b j ⊆ closure (pitchInterior o ℓ p a b j) :=
  closure_mono Set.inter_subset_right

private theorem interval_abs_sub_le {v t s x y : ℝ} (ht : 0 ≤ t)
    (hx : x ∈ Set.Icc (v + t) (v + s)) (hy : y ∈ Set.Icc (v + t) (v + s)) :
    |x - y| ≤ s := by
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- Any two points of a primary birth region are at sup distance at most the belt pitch.
Source: area-law Section 11, `geometry:primary-pieces`, lines 243–246. -/
theorem primaryBirthRegion_dist_le (o : ℝ × ℝ) (k ℓ p : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (a b : ℤ) (j : ℤ × ℤ) (x y : ℝ × ℝ)
    (hx : x ∈ primaryBirthRegion o k ℓ p Z C a b j)
    (hy : y ∈ primaryBirthRegion o k ℓ p Z C a b j) :
    dist x y ≤ (2 : ℝ) ^ p := by
  have hx' := closure_pitchInterior_subset o ℓ p a b j
    (primaryBirthRegion_subset_closure_pitchInterior o k ℓ p Z C a b j hx)
  have hy' := closure_pitchInterior_subset o ℓ p a b j
    (primaryBirthRegion_subset_closure_pitchInterior o k ℓ p Z C a b j hy)
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_le_iff]
  exact ⟨interval_abs_sub_le (pow_nonneg (by norm_num) ℓ) hx'.1 hy'.1,
    interval_abs_sub_le (pow_nonneg (by norm_num) ℓ) hx'.2 hy'.2⟩

/-- The sup diameter of a primary birth region is at most the belt pitch.
Source: area-law Section 11, `geometry:primary-pieces`, lines 243–246. -/
theorem primaryBirthRegion_diam_le (o : ℝ × ℝ) (k ℓ p : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (a b : ℤ) (j : ℤ × ℤ) :
    Metric.diam (primaryBirthRegion o k ℓ p Z C a b j) ≤ (2 : ℝ) ^ p :=
  Metric.diam_le_of_forall_dist_le (pow_nonneg (by norm_num) p)
    (fun x hx y hy ↦ primaryBirthRegion_dist_le o k ℓ p Z C a b j x y hx hy)

private theorem interval_abs_sub_ge {v t s x y : ℝ} {i j : ℤ}
    (hs : 0 ≤ s) (hij : i ≠ j)
    (hx : x ∈ Set.Icc (v + s * i + t) (v + s * i + s))
    (hy : y ∈ Set.Icc (v + s * j + t) (v + s * j + s)) :
    t ≤ |x - y| := by
  have step {i j : ℤ} (hij : i < j) : s * (i : ℝ) + s ≤ s * (j : ℝ) := by
    have h : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast (show i + 1 ≤ j by omega)
    nlinarith [mul_le_mul_of_nonneg_left h hs]
  rcases lt_or_gt_of_ne hij with hij | hij
  · calc
      t ≤ y - x := by linarith [hx.2, hy.1, step hij]
      _ ≤ |x - y| := by simpa only [abs_sub_comm] using le_abs_self (y - x)
  · calc
      t ≤ x - y := by linarith [hy.2, hx.1, step hij]
      _ ≤ |x - y| := le_abs_self _

/-- Distinct primary birth regions in one layer are separated by at least one belt width.
Source: area-law Section 11, `geometry:primary-pieces`, lines 246–249. -/
theorem primaryBirthRegion_dist_separation (o : ℝ × ℝ) (k ℓ p : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (a b : ℤ) (i j : ℤ × ℤ) (hij : i ≠ j)
    (x y : ℝ × ℝ) (hx : x ∈ primaryBirthRegion o k ℓ p Z C a b i)
    (hy : y ∈ primaryBirthRegion o k ℓ p Z C a b j) :
    (2 : ℝ) ^ ℓ ≤ dist x y := by
  have hx' := closure_pitchInterior_subset o ℓ p a b i
    (primaryBirthRegion_subset_closure_pitchInterior o k ℓ p Z C a b i hx)
  have hy' := closure_pitchInterior_subset o ℓ p a b j
    (primaryBirthRegion_subset_closure_pitchInterior o k ℓ p Z C a b j hy)
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  by_cases h : i.1 = j.1
  · have h' : i.2 ≠ j.2 := fun he ↦ hij (Prod.ext h he)
    exact (interval_abs_sub_ge (pow_nonneg (by norm_num) p) h' hx'.2 hy'.2).trans
      (le_max_right _ _)
  · exact (interval_abs_sub_ge (pow_nonneg (by norm_num) p) h hx'.1 hy'.1).trans
      (le_max_left _ _)

private theorem coordinate_fragment_index_bounds {o v t r s x : ℝ} {z : ℤ} {N : ℕ}
    (hr : 0 < r) (ht : 0 ≤ t) (hs : s = r * N)
    (hx : x ∈ Set.Ico (o + r * z) (o + r * (z + 1)))
    (hy : x ∈ Set.Ioo (v + t) (v + s)) :
    Int.floor ((v - o) / r) ≤ z ∧ z ≤ Int.floor ((v - o) / r) + N := by
  constructor
  · apply Int.floor_le_iff.mpr
    apply (div_lt_iff₀ hr).mpr
    linarith [hx.2, hy.1]
  · have hz : (z : ℝ) ≤ (x - o) / r :=
      (le_div_iff₀ hr).mpr (by linarith [hx.1])
    have hu : (x - o) / r < (v - o) / r + N := by
      apply (div_lt_iff₀ hr).mpr
      rw [add_mul, div_mul_cancel₀ _ hr.ne']
      linarith [hy.2]
    have h := Int.le_floor.mpr (hz.trans hu.le)
    simpa only [Int.floor_add_natCast] using h

/-- The number of nonempty fragments is at most the square of the sum of the
pitch-to-cell ratio and two, uniformly in the layer, origin and selected shifts.
Source: area-law Section 11, `geometry:primary-pieces`, lines 239–246. -/
theorem card_primaryFragmentIndices_le (o : ℝ × ℝ) (k ℓ p : ℕ)
    (Z : Finset (ℤ × ℤ)) (C : ℕ) (a b : ℤ) (j : ℤ × ℤ) (hkp : k ≤ p) :
    (primaryFragmentIndices o k ℓ p Z C a b j).card ≤ (2 ^ (p - k) + 2) ^ 2 := by
  classical
  let N : ℕ := 2 ^ (p - k)
  let q : ℤ × ℤ :=
    (Int.floor ((o.1 + (2 : ℝ) ^ ℓ * a + (2 : ℝ) ^ p * j.1 - o.1) / (2 : ℝ) ^ k),
      Int.floor ((o.2 + (2 : ℝ) ^ ℓ * b + (2 : ℝ) ^ p * j.2 - o.2) / (2 : ℝ) ^ k))
  have hs : (2 : ℝ) ^ p = (2 : ℝ) ^ k * (N : ℝ) := by
    dsimp [N]
    push_cast
    rw [← pow_add, Nat.add_sub_of_le hkp]
  have hsub : primaryFragmentIndices o k ℓ p Z C a b j ⊆
      (Finset.Icc q.1 (q.1 + (N : ℤ))).product (Finset.Icc q.2 (q.2 + (N : ℤ))) := by
    intro z hz
    obtain ⟨_, x, hx, hy⟩ := Finset.mem_filter.mp hz
    change x ∈ Set.Ico _ _ ×ˢ Set.Ico _ _ at hx
    change x ∈ Set.Ioo _ _ ×ˢ Set.Ioo _ _ at hy
    have h₁ := coordinate_fragment_index_bounds (pow_pos zero_lt_two k)
      (pow_nonneg zero_le_two ℓ) hs hx.1 hy.1
    have h₂ := coordinate_fragment_index_bounds (pow_pos zero_lt_two k)
      (pow_nonneg zero_le_two ℓ) hs hx.2 hy.2
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr h₁, Finset.mem_Icc.mpr h₂⟩
  have hcard (v : ℤ) : (Finset.Icc v (v + (N : ℤ))).card = N + 1 := by
    rw [Int.card_Icc]
    have hN : 0 ≤ (N : ℤ) := Int.natCast_nonneg N
    omega
  calc
    (primaryFragmentIndices o k ℓ p Z C a b j).card ≤
        ((Finset.Icc q.1 (q.1 + (N : ℤ))).product
          (Finset.Icc q.2 (q.2 + (N : ℤ)))).card := Finset.card_le_card hsub
    _ = (N + 1) ^ 2 := by
      rw [Finset.product_eq_sprod, Finset.card_product, hcard, hcard, pow_two]
    _ ≤ (N + 2) ^ 2 := by gcongr; omega

end TNLean.PEPS.AreaLaw.Geometry
