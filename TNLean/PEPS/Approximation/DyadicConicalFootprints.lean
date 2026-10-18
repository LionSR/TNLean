/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Topology.LocallyConstant.Basic
import TNLean.PEPS.Approximation.DyadicChamberSampling
import TNLean.PEPS.Approximation.DyadicFootprintTemplates

/-!
# An explicit footprint ratio near a mark

The small-patch covers of a point treatment need a footprint ratio `ν` such that every footprint
of radius `ν t` meets at most two labels of the sampled guide outside the inner holes of radius
`ε₀ t`. The source takes `ν` from the compactness observation over the finitely many templates
near a mark. This file proves the two-owner condition at the explicit ratio
`pointTreatmentRatio ε₀ = min(ε₀, 1) / 20000`, for every template and every reading after a
generic displacement:

* the templates are conical about the mark in units of `t`, with walls on lines whose normals
  lie in `wallNormals`; such a guide is locally constant off the lines through the mark with
  these normals (`eventually_eq_of_not_isWallDirection`);
* in the cone `|w.2| ≤ w.1` the guide is a function of the slope `w.2 / w.1`, and the slopes of
  the wall directions there are multiples of `1/1000` (`le_abs_sub_of_mem_wallSlopes`); four
  isometric charts carry every point into this cone (`exists_isWallChart`);
* three nearby points far from the mark lie in a window of slopes of length below `1/1000`, which
  meets at most one wall slope, so they carry at most two labels
  (`eq_or_eq_or_eq_of_conical`); two nearby labels just outside the treated square are separated
  by one wall, which meets the rim of the square at a point approached by both labels
  (`exists_wall_near_of_conical`);
* hence, for a reading after a generic displacement, three labels in a footprint force a true
  vertex within `ε₀` of a footprint point: the mark itself when it is not treated, and a point of
  the rim of the treated square when it is (`hasTwoOwnerFootprints_reading_pointTreated`,
  `hasTwoOwnerFootprints_reading_footprintTemplate`).

The bound is crude: it uses only the slopes of the wall directions, not the actual layout of the
bands.

Distances are ambient sup distances: `ℝ × ℝ` carries the maximum metric.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), §7, `06-geometry.tex`: the walls of the guides
  (lines 69–80, 142–221), the straight-ray charts (lines 301–302), the point treatment (lines
  330–338), the compactness observation (lines 447–479) and the point covers (lines 481–505).
-/

open Set Metric Filter Topology

namespace TNLean.PEPS.Approximation

/-! ### Walls on lines through a point -/

/-- Rescaling the argument about a point keeps a set lying locally in lines so, with the same
normals. -/
theorem IsLocallyInLines.preimage_affine {𝒩 Z : Set (ℝ × ℝ)} (h : IsLocallyInLines 𝒩 Z)
    (c : ℝ × ℝ) {a : ℝ} (ha : a ≠ 0) : IsLocallyInLines 𝒩 ((fun u => c + a • u) ⁻¹' Z) :=
  fun p => by
  obtain ⟨U, hU, F, hF, h𝒩, hs⟩ := h (c + a • p)
  refine ⟨(fun u => c + a • u) ⁻¹' U,
    (by fun_prop : Continuous fun u : ℝ × ℝ => c + a • u).continuousAt.preimage_mem_nhds hU,
    (fun L => (L.1, (L.2 - (L.1.1 * c.1 + L.1.2 * c.2)) / a)) '' F, hF.image _, ?_, ?_⟩
  · rintro _ ⟨L, hL, rfl⟩
    exact h𝒩 L hL
  · rintro q ⟨hqZ, hqU⟩
    obtain ⟨L, hL, hm⟩ := mem_iUnion₂.1 (hs ⟨hqZ, hqU⟩)
    refine mem_iUnion₂.2 ⟨_, mem_image_of_mem _ hL, ?_⟩
    simp only [normalLine, mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul] at hm ⊢
    rw [eq_div_iff ha]
    linear_combination hm

/-- Composing with an affine map of nonzero ratio keeps the walls on lines with the same
normals. -/
theorem HasLineWalls.comp_affine {𝒩 : Set (ℝ × ℝ)} {ι : Sort*} {f : ℝ × ℝ → ι}
    (h : HasLineWalls 𝒩 f) (c : ℝ × ℝ) {a : ℝ} (ha : a ≠ 0) :
    HasLineWalls 𝒩 fun u => f (c + a • u) := by
  obtain ⟨Z, hZ, hl⟩ := h
  exact ⟨_, hZ.preimage_affine c ha, fun q hq =>
    ((by fun_prop : Continuous fun u : ℝ × ℝ => c + a • u).tendsto q).eventually (hl _ hq)⟩

/-- There are finitely many wall normals. -/
theorem finite_wallNormals : wallNormals.Finite := by
  have hT : wallThresholds.Finite := by simp [wallThresholds]
  refine (hT.biUnion fun t _ =>
    Set.toFinite ({(t, 1000), (-t, 1000), (1000, t), (1000, -t)} : Set (ℝ × ℝ))).subset ?_
  rintro N ⟨t, ht, h⟩
  exact mem_biUnion ht (by rcases h with rfl | rfl | rfl | rfl <;> simp)

/-! ### Wall directions -/

/-- The vector `w` lies on a line through the origin with normal in `wallNormals`: a direction
of the walls of the guides near a mark.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:142–221, 301–302`. -/
def IsWallDirection (w : ℝ × ℝ) : Prop := ∃ N ∈ wallNormals, N.1 * w.1 + N.2 * w.2 = 0

/-- The wall directions, by threshold. -/
theorem isWallDirection_iff {w : ℝ × ℝ} : IsWallDirection w ↔ ∃ t ∈ wallThresholds,
    t * w.1 + 1000 * w.2 = 0 ∨ -t * w.1 + 1000 * w.2 = 0 ∨ 1000 * w.1 + t * w.2 = 0 ∨
      1000 * w.1 + -t * w.2 = 0 := by
  constructor
  · rintro ⟨N, ⟨t, ht, rfl | rfl | rfl | rfl⟩, h⟩
    exacts [⟨t, ht, Or.inl h⟩, ⟨t, ht, Or.inr (Or.inl h)⟩, ⟨t, ht, Or.inr (Or.inr (Or.inl h))⟩,
      ⟨t, ht, Or.inr (Or.inr (Or.inr h))⟩]
  · rintro ⟨t, ht, h | h | h | h⟩
    exacts [⟨_, ⟨t, ht, Or.inl rfl⟩, h⟩, ⟨_, ⟨t, ht, Or.inr (Or.inl rfl)⟩, h⟩,
      ⟨_, ⟨t, ht, Or.inr (Or.inr (Or.inl rfl))⟩, h⟩,
      ⟨_, ⟨t, ht, Or.inr (Or.inr (Or.inr rfl))⟩, h⟩]

/-- Wall directions are invariant under nonzero scalings. -/
theorem isWallDirection_smul_iff {a : ℝ} (ha : a ≠ 0) {w : ℝ × ℝ} :
    IsWallDirection (a • w) ↔ IsWallDirection w := by
  simp only [IsWallDirection, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  refine exists_congr fun N => and_congr_right fun _ => ?_
  rw [show N.1 * (a * w.1) + N.2 * (a * w.2) = a * (N.1 * w.1 + N.2 * w.2) by ring,
    mul_eq_zero, or_iff_right ha]

/-- The wall thresholds are integers of absolute value at most `8`. -/
theorem wallThresholds_bound {t : ℝ} (ht : t ∈ wallThresholds) :
    ∃ k : ℤ, t = k ∧ |t| ≤ 8 := by
  simp only [wallThresholds, mem_insert_iff, mem_singleton_iff] at ht
  have h8 : |t| ≤ 8 := by
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [abs_le]
  refine ⟨⌊t⌋, ?_, h8⟩
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- The slopes `m`, `|m| < 3`, of the wall directions `(1, m)`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:142–221`. -/
def wallSlopes : Set ℝ := {m | |m| < 3 ∧ IsWallDirection (1, m)}

/-- The wall slopes are multiples `k / 1000` with `|k| ≤ 8`. -/
theorem exists_int_of_mem_wallSlopes {m : ℝ} (hm : m ∈ wallSlopes) :
    ∃ k : ℤ, 1000 * m = k ∧ |(k : ℝ)| ≤ 8 := by
  obtain ⟨hm3, hw⟩ := hm
  obtain ⟨t, ht, h⟩ := isWallDirection_iff.1 hw
  obtain ⟨k, rfl, hk⟩ := wallThresholds_bound ht
  simp only [mul_one] at h
  have hb : |(k : ℝ) * m| < 1000 := by
    rw [abs_mul]; nlinarith [abs_nonneg (k : ℝ), abs_nonneg m]
  rw [abs_lt] at hb
  rcases h with h | h | h | h
  · exact ⟨-k, by push_cast; linarith, by rwa [Int.cast_neg, abs_neg]⟩
  · exact ⟨k, by linarith, hk⟩
  · exact absurd h (by nlinarith)
  · exact absurd h (by nlinarith)

/-- The wall slopes are at most `1/100` in absolute value. -/
theorem abs_le_of_mem_wallSlopes {m : ℝ} (hm : m ∈ wallSlopes) : |m| ≤ 1 / 100 := by
  obtain ⟨k, hk, hk8⟩ := exists_int_of_mem_wallSlopes hm
  have : |1000 * m| ≤ 8 := by rw [hk]; exact hk8
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1000)] at this
  linarith

/-- **Distinct wall slopes differ by at least `1/1000`.**

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:142–221`. -/
theorem le_abs_sub_of_mem_wallSlopes {m m' : ℝ} (hm : m ∈ wallSlopes) (hm' : m' ∈ wallSlopes)
    (hne : m ≠ m') : 1 / 1000 ≤ |m - m'| := by
  obtain ⟨k, hk, -⟩ := exists_int_of_mem_wallSlopes hm
  obtain ⟨k', hk', -⟩ := exists_int_of_mem_wallSlopes hm'
  have hkk : k ≠ k' := fun h => hne (by
    have : (1000 : ℝ) * m = 1000 * m' := by rw [hk, hk', h]
    linarith)
  have h1 : (1 : ℝ) ≤ |(k : ℝ) - k'| := by
    rw [← Int.cast_sub, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs (sub_ne_zero.2 hkk)
  have : |(k : ℝ) - k'| = 1000 * |m - m'| := by
    rw [← hk, ← hk', ← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1000)]
  linarith

/-! ### Slopes off the walls -/

section Slopes

variable {κ : Type*} {φ : ℝ → κ}

/-- A function on the slopes locally constant off the wall slopes is constant on every interval
in `(-3, 3)` without wall slopes. -/
theorem eq_of_forall_notMem_wallSlopes
    (hloc : ∀ m, |m| < 3 → m ∉ wallSlopes → ∀ᶠ m' in 𝓝 m, φ m' = φ m) {a b : ℝ} (hab : a ≤ b)
    (ha : -3 < a) (hb : b < 3) (hno : ∀ m ∈ Icc a b, m ∉ wallSlopes) : φ a = φ b := by
  have : PreconnectedSpace (Icc a b) := Subtype.preconnectedSpace isPreconnected_Icc
  have hlc : IsLocallyConstant fun m : Icc a b => φ m := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro m
    have hm3 : |(m : ℝ)| < 3 := abs_lt.2 ⟨by linarith [m.2.1], by linarith [m.2.2]⟩
    exact continuous_subtype_val.continuousAt.eventually (hloc m hm3 (hno m m.2))
  exact hlc.apply_eq_of_preconnectedSpace ⟨a, le_rfl, hab⟩ ⟨b, hab, le_rfl⟩

/-- Two slopes within `1/1000`, off the wall slopes and with different values, have a wall slope
strictly between them; the value is constant from each of them up to that slope.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:447–479`. -/
theorem exists_wallSlope_between
    (hloc : ∀ m, |m| < 3 → m ∉ wallSlopes → ∀ᶠ m' in 𝓝 m, φ m' = φ m) {m₁ m₂ : ℝ}
    (h₁ : |m₁| ≤ 2) (h₂ : |m₂| ≤ 2) (h₁' : m₁ ∉ wallSlopes) (h₂' : m₂ ∉ wallSlopes)
    (h₁₂ : |m₁ - m₂| < 1 / 1000) (hne : φ m₁ ≠ φ m₂) :
    ∃ β ∈ wallSlopes, (m₁ < β ∧ β < m₂ ∨ m₂ < β ∧ β < m₁) ∧
      (∀ m, (m₁ ≤ m ∧ m < β ∨ β < m ∧ m ≤ m₁) → φ m = φ m₁ ∧ m ∉ wallSlopes) ∧
      ∀ m, (m₂ ≤ m ∧ m < β ∨ β < m ∧ m ≤ m₂) → φ m = φ m₂ ∧ m ∉ wallSlopes := by
  rw [abs_le] at h₁ h₂
  rw [abs_lt] at h₁₂
  -- a wall slope in the closed interval between the two slopes
  have hex : ∃ β ∈ wallSlopes, min m₁ m₂ ≤ β ∧ β ≤ max m₁ m₂ := by
    by_contra hc
    push Not at hc
    have h := eq_of_forall_notMem_wallSlopes hloc (min_le_max (a := m₁) (b := m₂))
      (lt_min (by linarith) (by linarith)) (max_lt (by linarith) (by linarith))
      fun m hm hmB => absurd hm.2 (not_le.2 (hc m hmB hm.1))
    rcases le_total m₁ m₂ with h' | h'
    · rw [min_eq_left h', max_eq_right h'] at h; exact hne h
    · rw [min_eq_right h', max_eq_left h'] at h; exact hne h.symm
  obtain ⟨β, hβ, hβ₁, hβ₂⟩ := hex
  -- it is the only wall slope within `1/1000` of both
  have huniq : ∀ b ∈ wallSlopes, min m₁ m₂ ≤ b → b ≤ max m₁ m₂ → b = β := by
    intro b hb hb₁ hb₂
    by_contra hbβ
    have := le_abs_sub_of_mem_wallSlopes hb hβ hbβ
    rw [le_abs] at this
    rcases le_total m₁ m₂ with h' | h' <;>
      simp only [min_eq_left, min_eq_right, max_eq_left, max_eq_right, h'] at hβ₁ hβ₂ hb₁ hb₂ <;>
      rcases this with h | h <;> linarith
  have hne₁ : β ≠ m₁ := fun h => h₁' (h ▸ hβ)
  have hne₂ : β ≠ m₂ := fun h => h₂' (h ▸ hβ)
  have side (m₀ : ℝ) (hm₀ : m₀ = m₁ ∨ m₀ = m₂) (m : ℝ)
      (hm : m₀ ≤ m ∧ m < β ∨ β < m ∧ m ≤ m₀) : φ m = φ m₀ ∧ m ∉ wallSlopes := by
    have h0lo : min m₁ m₂ ≤ m₀ := by
      rcases hm₀ with rfl | rfl
      exacts [min_le_left _ _, min_le_right _ _]
    have h0hi : m₀ ≤ max m₁ m₂ := by
      rcases hm₀ with rfl | rfl
      exacts [le_max_left _ _, le_max_right _ _]
    have hlo : min m₁ m₂ ≤ min m₀ m := le_min h0lo (by rcases hm with hm | hm <;> linarith)
    have hhi : max m₀ m ≤ max m₁ m₂ := max_le h0hi (by rcases hm with hm | hm <;> linarith)
    have hno : ∀ b ∈ Icc (min m₀ m) (max m₀ m), b ∉ wallSlopes := by
      intro b hb hbB
      have := huniq b hbB (hlo.trans hb.1) (hb.2.trans hhi)
      subst this
      rcases hm with hm | hm
      · rw [min_eq_left hm.1, max_eq_right hm.1] at hb; linarith [hb.2]
      · rw [min_eq_right hm.2, max_eq_left hm.2] at hb; linarith [hb.1]
    have hrange : -3 < min m₁ m₂ ∧ max m₁ m₂ < 3 :=
      ⟨lt_min (by linarith) (by linarith), max_lt (by linarith) (by linarith)⟩
    have h := eq_of_forall_notMem_wallSlopes hloc min_le_max (by linarith [hlo, hrange.1])
      (by linarith [hhi, hrange.2]) hno
    have hmm : m ∈ Icc (min m₀ m) (max m₀ m) := ⟨min_le_right _ _, le_max_right _ _⟩
    refine ⟨?_, hno m hmm⟩
    rcases hm with hm | hm
    · rw [min_eq_left hm.1, max_eq_right hm.1] at h; exact h.symm
    · rw [min_eq_right hm.2, max_eq_left hm.2] at h; exact h
  refine ⟨β, hβ, ?_, side m₁ (Or.inl rfl), side m₂ (Or.inr rfl)⟩
  rcases le_total m₁ m₂ with h' | h'
  · rw [min_eq_left h'] at hβ₁; rw [max_eq_right h'] at hβ₂
    exact Or.inl ⟨lt_of_le_of_ne hβ₁ (Ne.symm hne₁), lt_of_le_of_ne hβ₂ hne₂⟩
  · rw [min_eq_right h'] at hβ₁; rw [max_eq_left h'] at hβ₂
    exact Or.inr ⟨lt_of_le_of_ne hβ₁ (Ne.symm hne₂), lt_of_le_of_ne hβ₂ hne₁⟩

/-- Three slopes within `1/1000` of each other, off the wall slopes, carry at most two values.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:447–479`. -/
theorem eq_or_eq_or_eq_of_slopes
    (hloc : ∀ m, |m| < 3 → m ∉ wallSlopes → ∀ᶠ m' in 𝓝 m, φ m' = φ m) {m₁ m₂ m₃ : ℝ}
    (h₁ : |m₁| ≤ 2) (h₂ : |m₂| ≤ 2) (h₃ : |m₃| ≤ 2) (h₁' : m₁ ∉ wallSlopes)
    (h₂' : m₂ ∉ wallSlopes) (h₃' : m₃ ∉ wallSlopes) (h₁₂ : |m₁ - m₂| < 1 / 1000)
    (h₁₃ : |m₁ - m₃| < 1 / 1000) (h₂₃ : |m₂ - m₃| < 1 / 1000) :
    φ m₁ = φ m₂ ∨ φ m₁ = φ m₃ ∨ φ m₂ = φ m₃ := by
  by_contra hc
  push Not at hc
  obtain ⟨n12, n13, n23⟩ := hc
  obtain ⟨β, hβ, hb, -, -⟩ := exists_wallSlope_between hloc h₁ h₂ h₁' h₂' h₁₂ n12
  obtain ⟨β', hβ', hb', -, -⟩ := exists_wallSlope_between hloc h₁ h₃ h₁' h₃' h₁₃ n13
  obtain ⟨β'', hβ'', hb'', -, -⟩ := exists_wallSlope_between hloc h₂ h₃ h₂' h₃' h₂₃ n23
  rw [abs_lt] at h₁₂ h₁₃ h₂₃
  have e1 : β' = β := by
    by_contra h
    have := le_abs_sub_of_mem_wallSlopes hβ' hβ h
    rw [le_abs] at this
    rcases hb with hb | hb <;> rcases hb' with hb' | hb' <;> rcases this with h | h <;> linarith
  have e2 : β'' = β := by
    by_contra h
    have := le_abs_sub_of_mem_wallSlopes hβ'' hβ h
    rw [le_abs] at this
    rcases hb with hb | hb <;> rcases hb'' with hb'' | hb'' <;> rcases this with h | h <;>
      linarith
  subst e1 e2
  rcases hb with hb | hb <;> rcases hb' with hb' | hb' <;> rcases hb'' with hb'' | hb'' <;>
    linarith

end Slopes

/-! ### Charts about the coordinate axes -/

/-- A chart of the plane exchanging the four cones about the coordinate axes: an involutive
linear isometry of the sup metric that maps wall directions to wall directions.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:142–221, 301–302`. -/
structure IsWallChart (L : ℝ × ℝ → ℝ × ℝ) : Prop where
  invol : ∀ w, L (L w) = w
  map_smul : ∀ (a : ℝ) (w : ℝ × ℝ), L (a • w) = a • L w
  dist_eq : ∀ w w', dist (L w) (L w') = dist w w'
  wall : ∀ w, IsWallDirection w → IsWallDirection (L w)
  continuous : Continuous L

namespace IsWallChart

variable {L : ℝ × ℝ → ℝ × ℝ}

/-- A chart fixes the origin. -/
theorem map_zero (hL : IsWallChart L) : L 0 = 0 := by
  simpa using hL.map_smul 0 0

/-- A chart preserves the sup norm. -/
theorem norm_eq (hL : IsWallChart L) (w : ℝ × ℝ) : ‖L w‖ = ‖w‖ := by
  rw [← dist_zero_right, ← hL.map_zero, hL.dist_eq, dist_zero_right]

/-- A chart preserves the wall directions. -/
theorem wall_iff (hL : IsWallChart L) (w : ℝ × ℝ) : IsWallDirection (L w) ↔ IsWallDirection w :=
  ⟨fun h => hL.invol w ▸ hL.wall _ h, hL.wall w⟩

end IsWallChart

/-- **Every point lies in a chart of the cone about the positive first axis.** For every `w`
there is a chart `L` with `|(L w).2| ≤ (L w).1`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:301–302`. -/
theorem exists_isWallChart (w : ℝ × ℝ) : ∃ L, IsWallChart L ∧ |(L w).2| ≤ (L w).1 := by
  have dist_neg_fst (a b : ℝ × ℝ) : dist ((-a.1, a.2) : ℝ × ℝ) (-b.1, b.2) = dist a b := by
    simp only [Prod.dist_eq, Real.dist_eq, show -a.1 - -b.1 = -(a.1 - b.1) by ring, abs_neg]
  have dist_swap (a b : ℝ × ℝ) : dist ((a.2, a.1) : ℝ × ℝ) (b.2, b.1) = dist a b := by
    simp only [Prod.dist_eq, max_comm]
  have dist_negswap (a b : ℝ × ℝ) : dist ((-a.2, -a.1) : ℝ × ℝ) (-b.2, -b.1) = dist a b := by
    simp only [Prod.dist_eq, Real.dist_eq, show -a.2 - -b.2 = -(a.2 - b.2) by ring,
      show -a.1 - -b.1 = -(a.1 - b.1) by ring, abs_neg, max_comm]
  rcases le_total |w.2| |w.1| with h | h
  · rcases le_total 0 w.1 with h0 | h0
    · refine ⟨id, ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ h => h, continuous_id⟩, ?_⟩
      simpa [abs_of_nonneg h0] using h
    · refine ⟨fun a => (-a.1, a.2), ⟨fun _ => by simp, fun _ _ => by simp [Prod.smul_mk],
        dist_neg_fst, fun a ha => ?_, by fun_prop⟩, ?_⟩
      · obtain ⟨t, ht, h | h | h | h⟩ := isWallDirection_iff.1 ha <;>
          refine isWallDirection_iff.2 ⟨t, ht, ?_⟩ <;> simp only
        exacts [Or.inr (Or.inl (by linarith)), Or.inl (by linarith),
          Or.inr (Or.inr (Or.inr (by linarith))), Or.inr (Or.inr (Or.inl (by linarith)))]
      · simpa [abs_of_nonpos h0] using h
  · rcases le_total 0 w.2 with h0 | h0
    · refine ⟨fun a => (a.2, a.1), ⟨fun _ => rfl, fun _ _ => by simp [Prod.smul_mk],
        dist_swap, fun a ha => ?_, by fun_prop⟩, ?_⟩
      · obtain ⟨t, ht, h | h | h | h⟩ := isWallDirection_iff.1 ha <;>
          refine isWallDirection_iff.2 ⟨t, ht, ?_⟩ <;> simp only
        exacts [Or.inr (Or.inr (Or.inl (by linarith))), Or.inr (Or.inr (Or.inr (by linarith))),
          Or.inl (by linarith), Or.inr (Or.inl (by linarith))]
      · simpa [abs_of_nonneg h0] using h
    · refine ⟨fun a => (-a.2, -a.1), ⟨fun _ => by simp, fun _ _ => by simp [Prod.smul_mk],
        dist_negswap, fun a ha => ?_, by fun_prop⟩, ?_⟩
      · obtain ⟨t, ht, h | h | h | h⟩ := isWallDirection_iff.1 ha <;>
          refine isWallDirection_iff.2 ⟨t, ht, ?_⟩ <;> simp only
        exacts [Or.inr (Or.inr (Or.inl (by linarith))), Or.inr (Or.inr (Or.inr (by linarith))),
          Or.inl (by linarith), Or.inr (Or.inl (by linarith))]
      · simpa [abs_of_nonpos h0] using h

/-! ### Conical guides with walls on lines -/

section Conical

variable {κ : Type*} {G : ℝ × ℝ → κ} {R : ℝ}

/-- **A conical guide with walls on lines is locally constant off the wall directions.** Let `G`
be constant along the rays from the origin in the open square of radius `R`, with walls on lines
with normals in `wallNormals`. Then `G` is locally constant at every point of that square off
the lines through the origin with these normals: the ray through such a point meets each wall
line near it in at most one point, and the constancy near a nearby point of the ray scales back.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:69–72, 301–302, 486–488`. -/
theorem eventually_eq_of_not_isWallDirection
    (hcon : ∀ (w : ℝ × ℝ) (a : ℝ), 0 < a → ‖w‖ < R → ‖a • w‖ < R → G (a • w) = G w)
    (hw : HasLineWalls wallNormals G) {y : ℝ × ℝ} (hy : ‖y‖ < R) (hny : ¬ IsWallDirection y) :
    ∀ᶠ y' in 𝓝 y, G y' = G y := by
  obtain ⟨Z, hZ, hl⟩ := hw
  obtain ⟨U, hU, F, hF, h𝒩, hs⟩ := hZ y
  -- the scalings `a` with `a • y ∈ U` and `‖a • y‖ < R` form a neighborhood of `1`
  have hcont : Continuous fun a : ℝ => a • y := continuous_id.smul continuous_const
  have hU' : ∀ᶠ a in 𝓝 (1 : ℝ), a • y ∈ U ∧ ‖a • y‖ < R ∧ 0 < a := by
    have h1 : ∀ᶠ a in 𝓝 (1 : ℝ), a • y ∈ U := (hcont.tendsto 1).eventually (by simpa using hU)
    have h2 : ∀ᶠ a in 𝓝 (1 : ℝ), ‖a • y‖ < R :=
      (hcont.norm.tendsto 1).eventually_lt_const (by simpa using hy)
    filter_upwards [h1, h2, lt_mem_nhds one_pos] with a h1 h2 h3 using ⟨h1, h2, h3⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1 hU'
  -- a scaling avoiding the finitely many wall lines near `y`
  let bad : Set ℝ := (fun L : (ℝ × ℝ) × ℝ => L.2 / (L.1.1 * y.1 + L.1.2 * y.2)) '' F
  have hbad : bad.Finite := hF.image _
  obtain ⟨a, ha, hab⟩ :=
    (Set.Ioo_infinite (a := 1 - ρ) (b := 1 + ρ) (by linarith)).exists_notMem_finite hbad
  have hda : dist a 1 < ρ := by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ha.1, ha.2]
  obtain ⟨haU, haR, ha0⟩ := hball hda
  have hnZ : a • y ∉ Z := by
    intro hz
    obtain ⟨L, hL, hm⟩ := mem_iUnion₂.1 (hs ⟨hz, haU⟩)
    have hN : L.1.1 * y.1 + L.1.2 * y.2 ≠ 0 := fun h0 => hny ⟨L.1, h𝒩 L hL, h0⟩
    refine hab ⟨L, hL, ?_⟩
    simp only [normalLine, mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hm
    rw [div_eq_iff hN, ← hm]
    ring
  have hloc := hl _ hnZ
  have hsc : ∀ᶠ y' in 𝓝 y, G (a • y') = G (a • y) :=
    ((continuous_const_smul a).tendsto y).eventually hloc
  have hn1 : ∀ᶠ y' in 𝓝 y, ‖y'‖ < R :=
    continuous_norm.continuousAt.eventually (isOpen_Iio.mem_nhds hy)
  have hn2 : ∀ᶠ y' in 𝓝 y, ‖a • y'‖ < R :=
    (continuous_const_smul a).norm.continuousAt.eventually (isOpen_Iio.mem_nhds haR)
  filter_upwards [hsc, hn1, hn2] with y' h1 h2 h3
  rw [← hcon y' a ha0 h2 h3, h1, hcon y a ha0 hy haR]

end Conical

section Cone

variable {κ : Type*} {G : ℝ × ℝ → κ}

/-- In the cone `|w.2| ≤ w.1` the sup norm is the first coordinate. -/
theorem norm_eq_fst_of_abs_snd_le {w : ℝ × ℝ} (h : |w.2| ≤ w.1) : ‖w‖ = w.1 := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ((abs_nonneg _).trans h),
    max_eq_left h]

/-- A point within `D` of a point of the cone `|w₁.2| ≤ w₁.1` with `3 D < w₁.1` lies in the
cone `|w.2| ≤ 2 w.1`, with first coordinate at least `w₁.1 - D`. -/
theorem cone_of_dist_le {w₁ w : ℝ × ℝ} {D : ℝ} (hE : |w₁.2| ≤ w₁.1) (hD : 3 * D < w₁.1)
    (h : dist w₁ w ≤ D) : w₁.1 - D ≤ w.1 ∧ 0 < w.1 ∧ |w.2| ≤ 2 * w.1 := by
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_le_iff] at h
  have hD0 : 0 ≤ D := (abs_nonneg _).trans h.1
  obtain ⟨h1, h2⟩ := h
  rw [abs_le] at h1 h2 hE ⊢
  refine ⟨by linarith, by linarith, by constructor <;> linarith⟩

/-- Slopes of nearby points of the cone `|b.2| ≤ 2 b.1` differ by at most `3 D / a.1`. -/
theorem abs_slope_sub_le {a b : ℝ × ℝ} {D : ℝ} (ha : 0 < a.1) (hb : 0 < b.1)
    (hb2 : |b.2| ≤ 2 * b.1) (hab : dist a b ≤ D) : |a.2 / a.1 - b.2 / b.1| ≤ 3 * D / a.1 := by
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_le_iff] at hab
  have hm : |b.2 / b.1| ≤ 2 := by rw [abs_div, abs_of_pos hb, div_le_iff₀ hb]; exact hb2
  have e : a.2 / a.1 - b.2 / b.1 = ((a.2 - b.2) - b.2 / b.1 * (a.1 - b.1)) / a.1 := by
    field_simp
    ring
  rw [e, abs_div, abs_of_pos ha]
  refine div_le_div_of_nonneg_right ?_ ha.le
  calc |(a.2 - b.2) - b.2 / b.1 * (a.1 - b.1)| ≤ |a.2 - b.2| + |b.2 / b.1 * (a.1 - b.1)| :=
        abs_sub _ _
    _ ≤ D + 2 * D := by
        rw [abs_mul]
        gcongr
        · exact hab.2
        · nlinarith [abs_nonneg (b.2 / b.1), abs_nonneg (a.1 - b.1), hab.1]
    _ = 3 * D := by ring

variable (hcon : ∀ (w : ℝ × ℝ) (a : ℝ), 0 < a → ‖w‖ < 4 → ‖a • w‖ < 4 → G (a • w) = G w)
  (hloc : ∀ y : ℝ × ℝ, ‖y‖ < 4 → ¬ IsWallDirection y → ∀ᶠ y' in 𝓝 y, G y' = G y)

include hcon in
/-- In the cone `|w.2| ≤ 2 w.1`, a conical guide takes its value on the slope `w.2 / w.1`. -/
theorem eq_slope {w : ℝ × ℝ} (h0 : 0 < w.1) (h2 : |w.2| ≤ 2 * w.1) (hw : ‖w‖ < 4) :
    G w = G (1, w.2 / w.1) := by
  have hm : |w.2 / w.1| ≤ 2 := by rw [abs_div, abs_of_pos h0, div_le_iff₀ h0]; exact h2
  have e : w = w.1 • ((1 : ℝ), w.2 / w.1) := by
    ext <;> simp [smul_eq_mul, mul_div_cancel₀ _ h0.ne']
  have hn : ‖((1 : ℝ), w.2 / w.1)‖ < 4 := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, abs_one]
    exact max_lt (by norm_num) (by linarith)
  conv_lhs => rw [e]
  exact hcon _ _ h0 hn (e ▸ hw)

/-- The slope of a point off the wall directions is not a wall slope. -/
theorem slope_notMem_wallSlopes {w : ℝ × ℝ} (h0 : 0 < w.1) (hw : ¬ IsWallDirection w) :
    w.2 / w.1 ∉ wallSlopes := fun hm => hw (by
  have e : w = w.1 • ((1 : ℝ), w.2 / w.1) := by
    ext <;> simp [smul_eq_mul, mul_div_cancel₀ _ h0.ne']
  rw [e, isWallDirection_smul_iff h0.ne']
  exact hm.2)

include hloc in
/-- The values of a conical guide on the slopes are locally constant off the wall slopes. -/
theorem slope_eventually_eq : ∀ m : ℝ, |m| < 3 → m ∉ wallSlopes →
    ∀ᶠ m' in 𝓝 m, G (1, m') = G (1, m) := by
  intro m hm hmB
  have hn : ‖((1 : ℝ), m)‖ < 4 := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, abs_one]
    exact max_lt (by norm_num) (by linarith)
  have hc : Continuous fun m' : ℝ => ((1 : ℝ), m') := by fun_prop
  exact (hc.tendsto m).eventually (hloc _ hn fun h => hmB ⟨hm, h⟩)

include hcon hloc in
/-- **Three nearby values in a cone.** Three points off the wall directions, the first in the
cone `|w₁.2| ≤ w₁.1` with `ρ ≤ w₁.1`, pairwise within `D` with `3001 D < ρ`, carry at most two
values of a conical guide. -/
theorem eq_or_eq_or_eq_of_cone {w₁ w₂ w₃ : ℝ × ℝ} {ρ D : ℝ} (hE : |w₁.2| ≤ w₁.1)
    (hρ : ρ ≤ w₁.1) (hD : 3001 * D < ρ) (h12 : dist w₁ w₂ ≤ D) (h13 : dist w₁ w₃ ≤ D)
    (h23 : dist w₂ w₃ ≤ D) (hn₁ : ‖w₁‖ < 4) (hn₂ : ‖w₂‖ < 4) (hn₃ : ‖w₃‖ < 4)
    (hw₁ : ¬ IsWallDirection w₁) (hw₂ : ¬ IsWallDirection w₂) (hw₃ : ¬ IsWallDirection w₃) :
    G w₁ = G w₂ ∨ G w₁ = G w₃ ∨ G w₂ = G w₃ := by
  have hD0 : 0 ≤ D := dist_nonneg.trans h12
  obtain ⟨a₂, p₂, c₂⟩ := cone_of_dist_le hE (by linarith) h12
  obtain ⟨a₃, p₃, c₃⟩ := cone_of_dist_le hE (by linarith) h13
  have p₁ : 0 < w₁.1 := by linarith
  have c₁ : |w₁.2| ≤ 2 * w₁.1 := by linarith
  have sl {w : ℝ × ℝ} (h0 : 0 < w.1) (h2 : |w.2| ≤ 2 * w.1) : |w.2 / w.1| ≤ 2 := by
    rw [abs_div, abs_of_pos h0, div_le_iff₀ h0]; exact h2
  have small {a b : ℝ × ℝ} (ha : 0 < a.1) (ha' : w₁.1 - D ≤ a.1) (hb : 0 < b.1)
      (hb2 : |b.2| ≤ 2 * b.1) (hab : dist a b ≤ D) : |a.2 / a.1 - b.2 / b.1| < 1 / 1000 := by
    refine (abs_slope_sub_le ha hb hb2 hab).trans_lt ?_
    rw [div_lt_iff₀ ha]
    linarith
  rw [eq_slope hcon p₁ c₁ hn₁, eq_slope hcon p₂ c₂ hn₂, eq_slope hcon p₃ c₃ hn₃]
  exact eq_or_eq_or_eq_of_slopes (slope_eventually_eq hloc) (sl p₁ c₁) (sl p₂ c₂) (sl p₃ c₃)
    (slope_notMem_wallSlopes p₁ hw₁) (slope_notMem_wallSlopes p₂ hw₂)
    (slope_notMem_wallSlopes p₃ hw₃) (small p₁ (by linarith) p₂ c₂ h12)
    (small p₁ (by linarith) p₃ c₃ h13) (small p₂ a₂ p₃ c₃ h23)

include hcon in
/-- Points just outside the unit square near the wall direction `(1, β)`, on the side of a slope
`m₀` with no wall slope in between, carry the value of `m₀`. -/
theorem exists_near_wallSlope {m₀ β : ℝ}
    (hside : ∀ m, (m₀ ≤ m ∧ m < β ∨ β < m ∧ m ≤ m₀) →
      G (1, m) = G (1, m₀) ∧ m ∉ wallSlopes)
    (hb : m₀ < β ∨ β < m₀) (hm₀ : |m₀| ≤ 2) (hmβ : |m₀ - β| ≤ 1) (hβ : |β| ≤ 1) {τ : ℝ}
    (hτ : 0 < τ) : ∃ y : ℝ × ℝ, dist y (1, β) < τ ∧ 1 < ‖y‖ ∧ ‖y‖ < 3 ∧
      ¬ IsWallDirection y ∧ G y = G (1, m₀) := by
  set s := min 1 (τ / 8) with hs
  set τ' := min 1 τ / 8 with hτ'
  have hs0 : 0 < s := lt_min one_pos (by positivity)
  have hs1 : s ≤ 1 := min_le_left _ _
  have hsτ : s ≤ τ / 8 := min_le_right _ _
  have hτ'0 : 0 < τ' := by positivity
  have hτ'1 : τ' ≤ 1 / 8 := by have := min_le_left 1 τ; linarith
  have hτ'τ : τ' ≤ τ / 8 := by have := min_le_right 1 τ; linarith
  set m := β + s * (m₀ - β) with hm
  have hmside : m₀ ≤ m ∧ m < β ∨ β < m ∧ m ≤ m₀ := by
    rcases hb with hb | hb
    · left; constructor <;> nlinarith
    · right; constructor <;> nlinarith
  obtain ⟨hGm, hmB⟩ := hside m hmside
  have hm2 : |m| ≤ 2 := by
    rw [abs_le] at hm₀ hβ ⊢
    rcases hmside with h | h <;> constructor <;> linarith [h.1, h.2]
  have hn1 : ‖((1 : ℝ), m)‖ = max 1 |m| := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, abs_one]
  refine ⟨(1 + τ') • ((1 : ℝ), m), ?_, ?_, ?_, ?_, ?_⟩
  · rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    simp only [Prod.smul_mk, smul_eq_mul, mul_one]
    refine max_lt ?_ ?_
    · rw [show 1 + τ' - 1 = τ' by ring, abs_of_pos hτ'0]; linarith
    · have e : (1 + τ') * m - β = s * (m₀ - β) + τ' * m := by rw [hm]; ring
      rw [e]
      calc |s * (m₀ - β) + τ' * m| ≤ |s * (m₀ - β)| + |τ' * m| := abs_add_le _ _
        _ ≤ s * 1 + τ' * 2 := by
          rw [abs_mul, abs_mul, abs_of_pos hs0, abs_of_pos hτ'0]
          gcongr
        _ < τ := by linarith
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith), hn1]
    nlinarith [le_max_left 1 |m|]
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith), hn1]
    have : max 1 |m| ≤ 2 := max_le (by norm_num) hm2
    nlinarith [le_max_left 1 |m|]
  · rw [isWallDirection_smul_iff (by linarith)]
    exact fun h => hmB ⟨by linarith, h⟩
  · have hn : ‖((1 : ℝ), m)‖ < 4 := by rw [hn1]; exact max_lt (by norm_num) (by linarith)
    have hn' : ‖(1 + τ') • ((1 : ℝ), m)‖ < 4 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith), hn1]
      have : max 1 |m| ≤ 2 := max_le (by norm_num) hm2
      nlinarith
    rw [hcon _ _ (by linarith) hn hn', hGm]

include hcon hloc in
/-- **Two nearby values just outside the unit square in a cone.** Let `w₁` lie in the cone
`|w₁.2| ≤ w₁.1` with `1 ≤ w₁.1 ≤ 1 + D`, `3001 D < 1`, let `w₂` lie within `D` of it, both off the
wall directions, with different values of a conical guide. Then there is a point `z` of the
boundary of the unit square within `5 D` of `w₁`, on a wall direction between them, such that
points just outside the unit square arbitrarily near `z` carry each of the two values. -/
theorem exists_wall_near_of_cone {w₁ w₂ : ℝ × ℝ} {D : ℝ} (hE : |w₁.2| ≤ w₁.1) (h1 : 1 ≤ w₁.1)
    (h1' : w₁.1 ≤ 1 + D) (hD : 3001 * D < 1) (h12 : dist w₁ w₂ ≤ D) (hn₁ : ‖w₁‖ < 4)
    (hn₂ : ‖w₂‖ < 4) (hw₁ : ¬ IsWallDirection w₁) (hw₂ : ¬ IsWallDirection w₂)
    (hne : G w₁ ≠ G w₂) :
    ∃ z : ℝ × ℝ, ‖z‖ = 1 ∧ dist w₁ z ≤ 5 * D ∧
      (∀ τ > 0, ∃ y : ℝ × ℝ, dist y z < τ ∧ 1 < ‖y‖ ∧ ‖y‖ < 3 ∧ ¬ IsWallDirection y ∧
        G y = G w₁) ∧
      ∀ τ > 0, ∃ y : ℝ × ℝ, dist y z < τ ∧ 1 < ‖y‖ ∧ ‖y‖ < 3 ∧ ¬ IsWallDirection y ∧
        G y = G w₂ := by
  have hD0 : 0 ≤ D := dist_nonneg.trans h12
  obtain ⟨a₂, p₂, c₂⟩ := cone_of_dist_le hE (by linarith) h12
  have p₁ : 0 < w₁.1 := by linarith
  have c₁ : |w₁.2| ≤ 2 * w₁.1 := by linarith
  have sl {w : ℝ × ℝ} (h0 : 0 < w.1) (h2 : |w.2| ≤ 2 * w.1) : |w.2 / w.1| ≤ 2 := by
    rw [abs_div, abs_of_pos h0, div_le_iff₀ h0]; exact h2
  have hm₁ : |w₁.2 / w₁.1| ≤ 1 := by rw [abs_div, abs_of_pos p₁, div_le_iff₀ p₁]; linarith
  have hdm : |w₁.2 / w₁.1 - w₂.2 / w₂.1| ≤ 3 * D := by
    refine (abs_slope_sub_le p₁ p₂ c₂ h12).trans ?_
    rw [div_le_iff₀ p₁]; nlinarith
  have e₁ := eq_slope hcon p₁ c₁ hn₁
  have e₂ := eq_slope hcon p₂ c₂ hn₂
  rw [e₁, e₂] at hne ⊢
  obtain ⟨β, hβ, hb, hs₁, hs₂⟩ := exists_wallSlope_between (slope_eventually_eq hloc)
    (sl p₁ c₁) (sl p₂ c₂) (slope_notMem_wallSlopes p₁ hw₁) (slope_notMem_wallSlopes p₂ hw₂)
    (by linarith) hne
  have hβ1 := abs_le_of_mem_wallSlopes hβ
  have hb₁ : |w₁.2 / w₁.1 - β| ≤ 3 * D := by
    rw [abs_le] at hdm ⊢; rcases hb with hb | hb <;> constructor <;> linarith
  have hb₂ : |w₂.2 / w₂.1 - β| ≤ 3 * D := by
    rw [abs_le] at hdm ⊢; rcases hb with hb | hb <;> constructor <;> linarith
  refine ⟨((1 : ℝ), β), ?_, ?_,
    fun τ hτ => exists_near_wallSlope hcon hs₁ (hb.imp (fun h => h.1) fun h => h.2)
      (sl p₁ c₁) (by linarith) (by linarith) hτ,
    fun τ hτ => exists_near_wallSlope hcon hs₂ (hb.symm.imp (fun h => h.1) fun h => h.2)
      (sl p₂ c₂) (by linarith) (by linarith) hτ⟩
  · rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, abs_one]
    exact max_eq_left (by linarith)
  · rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    refine max_le (by rw [abs_le]; constructor <;> linarith) ?_
    have e : w₁.2 - β = w₁.1 * (w₁.2 / w₁.1 - β) + (w₁.1 - 1) * β := by
      field_simp
      ring
    rw [e]
    calc |w₁.1 * (w₁.2 / w₁.1 - β) + (w₁.1 - 1) * β|
        ≤ |w₁.1 * (w₁.2 / w₁.1 - β)| + |(w₁.1 - 1) * β| := abs_add_le _ _
      _ ≤ (1 + D) * (3 * D) + D * 1 := by
          rw [abs_mul, abs_mul, abs_of_pos p₁, abs_of_nonneg (by linarith : 0 ≤ w₁.1 - 1)]
          gcongr
          · linarith
          · linarith
      _ ≤ 5 * D := by nlinarith

end Cone

/-! ### Conical guides in every chart -/

section Ambient

variable {κ : Type*} {G : ℝ × ℝ → κ}
  (hcon : ∀ (w : ℝ × ℝ) (a : ℝ), 0 < a → ‖w‖ < 4 → ‖a • w‖ < 4 → G (a • w) = G w)
  (hloc : ∀ y : ℝ × ℝ, ‖y‖ < 4 → ¬ IsWallDirection y → ∀ᶠ y' in 𝓝 y, G y' = G y)

include hcon in
/-- A conical guide read through a chart is conical. -/
theorem IsWallChart.conical {L : ℝ × ℝ → ℝ × ℝ} (hL : IsWallChart L) :
    ∀ (w : ℝ × ℝ) (a : ℝ), 0 < a → ‖w‖ < 4 → ‖a • w‖ < 4 → G (L (a • w)) = G (L w) := by
  intro w a ha hw haw
  rw [hL.map_smul]
  exact hcon _ _ ha (by rwa [hL.norm_eq]) (by rwa [← hL.map_smul, hL.norm_eq])

include hloc in
/-- A guide locally constant off the wall directions stays so when read through a chart. -/
theorem IsWallChart.eventually_eq {L : ℝ × ℝ → ℝ × ℝ} (hL : IsWallChart L) :
    ∀ y : ℝ × ℝ, ‖y‖ < 4 → ¬ IsWallDirection y → ∀ᶠ y' in 𝓝 y, G (L y') = G (L y) := by
  intro y hy hny
  exact (hL.continuous.tendsto y).eventually
    (hloc _ (by rwa [hL.norm_eq]) (by rwa [hL.wall_iff]))

include hcon hloc in
/-- **Three nearby values of a conical guide.** Three points off the wall directions, pairwise
within `D`, with `‖w₁‖ ≥ ρ > 3001 D`, carry at most two values of a conical guide with walls on
lines.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:447–479, 486–491`. -/
theorem eq_or_eq_or_eq_of_conical {w₁ w₂ w₃ : ℝ × ℝ} {ρ D : ℝ} (hρ : ρ ≤ ‖w₁‖)
    (hD : 3001 * D < ρ) (h12 : dist w₁ w₂ ≤ D) (h13 : dist w₁ w₃ ≤ D) (h23 : dist w₂ w₃ ≤ D)
    (hn₁ : ‖w₁‖ < 4) (hn₂ : ‖w₂‖ < 4) (hn₃ : ‖w₃‖ < 4) (hw₁ : ¬ IsWallDirection w₁)
    (hw₂ : ¬ IsWallDirection w₂) (hw₃ : ¬ IsWallDirection w₃) :
    G w₁ = G w₂ ∨ G w₁ = G w₃ ∨ G w₂ = G w₃ := by
  obtain ⟨L, hL, hE⟩ := exists_isWallChart w₁
  have h := eq_or_eq_or_eq_of_cone (G := fun w => G (L w)) (w₂ := L w₂) (w₃ := L w₃)
    (hL.conical hcon) (hL.eventually_eq hloc) hE
    (by rwa [← norm_eq_fst_of_abs_snd_le hE, hL.norm_eq]) hD (by rwa [hL.dist_eq])
    (by rwa [hL.dist_eq]) (by rwa [hL.dist_eq]) (by rwa [hL.norm_eq]) (by rwa [hL.norm_eq])
    (by rwa [hL.norm_eq]) (by rwa [hL.wall_iff]) (by rwa [hL.wall_iff]) (by rwa [hL.wall_iff])
  simpa only [hL.invol] using h

include hcon hloc in
/-- **Two nearby values of a conical guide just outside the unit square.** Let
`1 ≤ ‖w₁‖ ≤ 1 + D` with `3001 D < 1` and `dist w₁ w₂ ≤ D`, both off the wall directions, carry
different values of a conical guide with walls on lines. Then a point `z` of the boundary of the
unit square within `5 D` of `w₁` is approached from outside the unit square by points of either
value.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:109–111, 330–338, 447–479`. -/
theorem exists_wall_near_of_conical {w₁ w₂ : ℝ × ℝ} {D : ℝ} (h1 : 1 ≤ ‖w₁‖)
    (h1' : ‖w₁‖ ≤ 1 + D) (hD : 3001 * D < 1) (h12 : dist w₁ w₂ ≤ D) (hn₁ : ‖w₁‖ < 4)
    (hn₂ : ‖w₂‖ < 4) (hw₁ : ¬ IsWallDirection w₁) (hw₂ : ¬ IsWallDirection w₂)
    (hne : G w₁ ≠ G w₂) :
    ∃ z : ℝ × ℝ, ‖z‖ = 1 ∧ dist w₁ z ≤ 5 * D ∧
      (∀ τ > 0, ∃ y : ℝ × ℝ, dist y z < τ ∧ 1 < ‖y‖ ∧ ‖y‖ < 3 ∧ ¬ IsWallDirection y ∧
        G y = G w₁) ∧
      ∀ τ > 0, ∃ y : ℝ × ℝ, dist y z < τ ∧ 1 < ‖y‖ ∧ ‖y‖ < 3 ∧ ¬ IsWallDirection y ∧
        G y = G w₂ := by
  obtain ⟨L, hL, hE⟩ := exists_isWallChart w₁
  have hn : ‖L w₁‖ = (L w₁).1 := norm_eq_fst_of_abs_snd_le hE
  obtain ⟨z, hz, hdz, hy₁, hy₂⟩ := exists_wall_near_of_cone (G := fun w => G (L w))
    (w₂ := L w₂) (hL.conical hcon) (hL.eventually_eq hloc) hE (by rwa [← hn, hL.norm_eq])
    (by rwa [← hn, hL.norm_eq]) hD (by rwa [hL.dist_eq]) (by rwa [hL.norm_eq])
    (by rwa [hL.norm_eq]) (by rwa [hL.wall_iff]) (by rwa [hL.wall_iff])
    (by simpa only [hL.invol] using hne)
  have back {w : ℝ × ℝ} (hy : ∀ τ > 0, ∃ y : ℝ × ℝ, dist y z < τ ∧ 1 < ‖y‖ ∧ ‖y‖ < 3 ∧
      ¬ IsWallDirection y ∧ G (L y) = G (L (L w))) :
      ∀ τ > 0, ∃ y : ℝ × ℝ, dist y (L z) < τ ∧ 1 < ‖y‖ ∧ ‖y‖ < 3 ∧ ¬ IsWallDirection y ∧
        G y = G w := by
    intro τ hτ
    obtain ⟨y, h1, h2, h3, h4, h5⟩ := hy τ hτ
    refine ⟨L y, by rwa [hL.dist_eq], by rwa [hL.norm_eq], by rwa [hL.norm_eq],
      by rwa [hL.wall_iff], by rwa [hL.invol] at h5⟩
  refine ⟨L z, by rwa [hL.norm_eq], ?_, back hy₁, back hy₂⟩
  calc dist w₁ (L z) = dist (L (L w₁)) (L z) := by rw [hL.invol]
    _ = dist (L w₁) z := hL.dist_eq _ _
    _ ≤ 5 * D := hdz

end Ambient

/-! ### The two-owner condition near a mark -/

/-- After a generic displacement every point leaves the wall directions at once.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:73–77`. -/
theorem IsGenericDisplacement.eventually_not_isWallDirection {v : ℝ × ℝ}
    (hv : IsGenericDisplacement v) (u : ℝ × ℝ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ¬ IsWallDirection (u + ε • v) := by
  have h : ∀ N ∈ wallNormals, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      N.1 * (u + ε • v).1 + N.2 * (u + ε • v).2 ≠ 0 := by
    intro N hN
    have e (ε : ℝ) : N.1 * (u + ε • v).1 + N.2 * (u + ε • v).2 =
        (N.1 * u.1 + N.2 * u.2) + ε * (N.1 * v.1 + N.2 * v.2) := by
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    by_cases h0 : N.1 * u.1 + N.2 * u.2 = 0
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      rw [e, h0, zero_add]
      exact mul_ne_zero hε.ne' (hv N hN)
    · have hc : Continuous fun ε : ℝ => (N.1 * u.1 + N.2 * u.2) + ε * (N.1 * v.1 + N.2 * v.2) :=
        by fun_prop
      have := (hc.tendsto 0).eventually (isOpen_ne.mem_nhds (by simpa using h0))
      filter_upwards [nhdsWithin_le_nhds this] with ε hε
      rw [e]; exact hε
  filter_upwards [(finite_wallNormals.eventually_all).2 h] with ε hε
  rintro ⟨N, hN, h0⟩
  exact hε N hN h0

/-- A reading of a labelling that is constant near a point takes that value at the point.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:71–77`. -/
theorem IsDisplacedReading.eq_of_eventually_const {X ι : Type*} [AddCommGroup X] [Module ℝ X]
    [TopologicalSpace X] [ContinuousAdd X] [ContinuousSMul ℝ X] {T F : X → ι} {v : X}
    (hT : IsDisplacedReading T F v) {y : X} {c : ι} (h : ∀ᶠ q in 𝓝 y, F q = c) : T y = c := by
  obtain ⟨ε, e₁, e₂⟩ := ((hT y).and ((tendsto_add_smul_nhdsGT y v).eventually h)).exists
  rw [e₁, e₂]

/-- **The explicit footprint ratio near a mark.** The ratio `min(ε₀, 1) / 20000`, in place of
the compactness minimum of the source over the templates near a mark. Three labels of a template
within a footprint lie in a window of slopes of length below `1/1000` at distance at least
`min(ε₀, 1)` from the mark, up to the displacement.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:447–479, 481–505, 559–563`. -/
noncomputable def pointTreatmentRatio (ε₀ : ℝ) : ℝ := min ε₀ 1 / 20000

/-- The footprint ratio near a mark is positive.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:559–563`. -/
theorem pointTreatmentRatio_pos {ε₀ : ℝ} (hε : 0 < ε₀) : 0 < pointTreatmentRatio ε₀ := by
  unfold pointTreatmentRatio; have := lt_min hε one_pos; positivity

/-- The footprint ratio near a mark is at most `1/20000`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:481–505`. -/
theorem pointTreatmentRatio_le (ε₀ : ℝ) : pointTreatmentRatio ε₀ ≤ 1 / 20000 := by
  unfold pointTreatmentRatio; have := min_le_right ε₀ 1; linarith

/-- **The two-owner condition of a conical guide near a mark, at an explicit footprint radius.**
Let `G` be constant along the rays from the origin in the open square of radius `4`, and locally
constant there off the wall directions. Let `T` be a reading, after a generic displacement, of
the relabelling by `π` of `G` point treated on the unit square, or of `G` itself. Then `T` has
the two-owner condition with working set the closed square of radius `2`, holes of radius `ε₀`
at its true vertices within `3`, and every footprint radius `δ ≤ min(ε₀, 1) / 20000`.

The wall slopes are multiples of `1/1000`, so three labels in a footprint far from the origin
straddle at most one wall; if the origin is untreated it is a true vertex, and if it is treated a
label of the treated square meets two labels across one wall at a true vertex of the rim.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:447–479, 481–505`. -/
theorem hasTwoOwnerFootprints_reading_pointTreated {κ ι : Type*} {G : ℝ × ℝ → κ}
    (hcon : ∀ (w : ℝ × ℝ) (a : ℝ), 0 < a → ‖w‖ < 4 → ‖a • w‖ < 4 → G (a • w) = G w)
    (hloc : ∀ y : ℝ × ℝ, ‖y‖ < 4 → ¬ IsWallDirection y → ∀ᶠ y' in 𝓝 y, G y' = G y)
    (π : κ → ι) (P : Option κ) {v : ℝ × ℝ} (hv : IsGenericDisplacement v) {T : ℝ × ℝ → ι}
    (hT : IsDisplacedReading T (fun u => π (pointTreated 0 1 P G u)) v) {ε₀ δ : ℝ}
    (hε : 0 < ε₀) (hδ : δ ≤ pointTreatmentRatio ε₀) :
    HasTwoOwnerFootprints T (closedBall 0 2)
      {u | u ∈ closedBall (0 : ℝ × ℝ) 3 ∧ IsTrueVertex T u} ε₀ δ := by
  intro x u₁ u₂ u₃ h₁ h₂ h₃
  by_contra hne
  push Not at hne
  obtain ⟨n12, n13, n23⟩ := hne
  set l := pointTreatmentRatio ε₀ with hl
  have hl0 : 0 < l := pointTreatmentRatio_pos hε
  have hlε : 20000 * l ≤ ε₀ := by
    rw [hl, pointTreatmentRatio]; have := min_le_left ε₀ 1; linarith
  have hl1 : 20000 * l ≤ 1 := by
    rw [hl, pointTreatmentRatio]; have := min_le_right ε₀ 1; linarith
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (0 : ℝ × ℝ) + ε • v ∈ ball 0 l :=
    tendsto_add_smul_nhdsGT 0 v (ball_mem_nhds 0 hl0)
  obtain ⟨ε, e₁, e₂, e₃, e₄, g₁, g₂, g₃⟩ := ((hT u₁).and ((hT u₂).and ((hT u₃).and (hsmall.and
    ((hv.eventually_not_isWallDirection u₁).and ((hv.eventually_not_isWallDirection u₂).and
      (hv.eventually_not_isWallDirection u₃))))))).exists
  rw [zero_add, mem_ball, dist_zero_right] at e₄
  set w₁ := u₁ + ε • v
  set w₂ := u₂ + ε • v
  set w₃ := u₃ + ε • v
  -- distances
  have hd (u : ℝ × ℝ) : dist u (u + ε • v) < l := by
    rw [dist_comm, dist_eq_norm, add_sub_cancel_left]; exact e₄
  have hx {u : ℝ × ℝ} (hu : u ∈ (closedBall x δ ∩ closedBall 0 2) \
      ⋃ h ∈ {u | u ∈ closedBall (0 : ℝ × ℝ) 3 ∧ IsTrueVertex T u}, ball h ε₀) :
      dist u x ≤ δ ∧ ‖u‖ ≤ 2 :=
    ⟨hu.1.1, by simpa [mem_closedBall, dist_zero_right] using hu.1.2⟩
  have hw {u u' : ℝ × ℝ}
      (hu : u ∈ (closedBall x δ ∩ closedBall 0 2) \
        ⋃ h ∈ {u | u ∈ closedBall (0 : ℝ × ℝ) 3 ∧ IsTrueVertex T u}, ball h ε₀)
      (hu' : u' ∈ (closedBall x δ ∩ closedBall 0 2) \
        ⋃ h ∈ {u | u ∈ closedBall (0 : ℝ × ℝ) 3 ∧ IsTrueVertex T u}, ball h ε₀) :
      dist (u + ε • v) (u' + ε • v) ≤ 2 * l := by
    rw [dist_add_right]
    linarith [dist_triangle u x u', dist_comm x u', (hx hu).1, (hx hu').1]
  have d12 := hw h₁ h₂
  have d13 := hw h₁ h₃
  have d23 := hw h₂ h₃
  have hn {u : ℝ × ℝ}
      (hu : u ∈ (closedBall x δ ∩ closedBall 0 2) \
        ⋃ h ∈ {u | u ∈ closedBall (0 : ℝ × ℝ) 3 ∧ IsTrueVertex T u}, ball h ε₀) :
      ‖u + ε • v‖ < 4 := by
    have := norm_add_le u (ε • v); linarith [(hx hu).2]
  have hn₁ := hn h₁
  have hn₂ := hn h₂
  have hn₃ := hn h₃
  -- a footprint point within `ε₀` of a true vertex within `3` is in a hole
  have hhole {u z : ℝ × ℝ}
      (hu : u ∈ (closedBall x δ ∩ closedBall 0 2) \
        ⋃ h ∈ {u | u ∈ closedBall (0 : ℝ × ℝ) 3 ∧ IsTrueVertex T u}, ball h ε₀)
      (hz : ‖z‖ ≤ 3) (htv : IsTrueVertex T z) (hdz : dist u z < ε₀) : False :=
    hu.2 (mem_biUnion ⟨by rwa [mem_closedBall, dist_zero_right], htv⟩ hdz)
  -- the reading at points near which the guide is locally constant
  have hGread {y : ℝ × ℝ} (hy : ‖y‖ < 4) (hny : ¬ IsWallDirection y)
      (hF : ∀ᶠ q in 𝓝 y, pointTreated 0 1 P G q = G q) : T y = π (G y) :=
    hT.eq_of_eventually_const ((hF.and (hloc y hy hny)).mono fun q hq => by
      simp only [hq.1, hq.2])
  cases P with
  | none =>
    have hP : ∀ q, pointTreated 0 1 none G q = G q := fun _ => rfl
    simp only [hP] at e₁ e₂ e₃
    rw [e₁, e₂] at n12; rw [e₁, e₃] at n13; rw [e₂, e₃] at n23
    -- the origin is a true vertex
    have hcl {w : ℝ × ℝ} (hw4 : ‖w‖ < 4) (hnw : ¬ IsWallDirection w) :
        (0 : ℝ × ℝ) ∈ closure (T ⁻¹' {π (G w)}) := by
      rw [Metric.mem_closure_iff]
      intro τ hτ
      set a := min 1 (τ / (2 * (‖w‖ + 1))) with ha
      have ha0 : 0 < a := lt_min one_pos (by positivity)
      have ha1 : a ≤ 1 := min_le_left _ _
      have haτ : a ≤ τ / (2 * (‖w‖ + 1)) := min_le_right _ _
      have hnorm : ‖a • w‖ = a * ‖w‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha0]
      have hay : ‖a • w‖ < 4 := by rw [hnorm]; nlinarith [norm_nonneg w]
      have hnay : ¬ IsWallDirection (a • w) := by rwa [isWallDirection_smul_iff ha0.ne']
      refine ⟨a • w, ?_, ?_⟩
      · rw [mem_preimage, mem_singleton_iff, hGread hay hnay (Eventually.of_forall hP),
          hcon w a ha0 hw4 hay]
      · rw [dist_zero_left, hnorm]
        have h2 : a * (2 * (‖w‖ + 1)) ≤ τ := (le_div_iff₀ (by positivity)).1 haτ
        nlinarith [norm_nonneg w]
    have htv : IsTrueVertex T 0 :=
      ⟨_, _, _, n12, n13, n23, hcl hn₁ g₁, hcl hn₂ g₂, hcl hn₃ g₃⟩
    have hfar : ε₀ ≤ ‖u₁‖ := by
      by_contra h
      exact hhole h₁ (by norm_num) htv (by rw [dist_zero_right]; linarith)
    have h1 : ε₀ - l ≤ ‖w₁‖ := by
      have := norm_sub_norm_le u₁ (-(ε • v))
      rw [sub_neg_eq_add, norm_neg] at this
      linarith
    rcases eq_or_eq_or_eq_of_conical hcon hloc h1 (D := 2 * l) (by linarith) d12 d13 d23 hn₁ hn₂
      hn₃ g₁ g₂ g₃ with h | h | h
    · exact n12 (congrArg π h)
    · exact n13 (congrArg π h)
    · exact n23 (congrArg π h)
  | some P₀ =>
    beta_reduce at e₁ e₂ e₃
    have hin {q : ℝ × ℝ} (hq : q ∈ ball (0 : ℝ × ℝ) 1) : pointTreated 0 1 (some P₀) G q = P₀ :=
      homogenize_of_mem hq
    have hout {q : ℝ × ℝ} (hq : q ∉ ball (0 : ℝ × ℝ) 1) :
        pointTreated 0 1 (some P₀) G q = G q :=
      homogenize_of_notMem hq
    have hone {q : ℝ × ℝ} (hq : q ∉ ball (0 : ℝ × ℝ) 1) : 1 ≤ ‖q‖ := by
      simpa [mem_ball, dist_zero_right] using hq
    -- the case of one treated point
    have key {ua ub uc : ℝ × ℝ}
        (ha : ua ∈ (closedBall x δ ∩ closedBall 0 2) \
          ⋃ h ∈ {u | u ∈ closedBall (0 : ℝ × ℝ) 3 ∧ IsTrueVertex T u}, ball h ε₀)
        (hba : ua + ε • v ∉ ball (0 : ℝ × ℝ) 1) (hbb : ub + ε • v ∉ ball (0 : ℝ × ℝ) 1)
        (hbc : uc + ε • v ∈ ball (0 : ℝ × ℝ) 1)
        (dab : dist (ua + ε • v) (ub + ε • v) ≤ 2 * l)
        (dac : dist (ua + ε • v) (uc + ε • v) ≤ 2 * l) (hna : ‖ua + ε • v‖ < 4)
        (hnb : ‖ub + ε • v‖ < 4) (ga : ¬ IsWallDirection (ua + ε • v))
        (gb : ¬ IsWallDirection (ub + ε • v)) (nab : π (G (ua + ε • v)) ≠ π (G (ub + ε • v)))
        (nac : π (G (ua + ε • v)) ≠ π P₀) (nbc : π (G (ub + ε • v)) ≠ π P₀) : False := by
      have h1 := hone hba
      have h1' : ‖ua + ε • v‖ ≤ 1 + 2 * l := by
        have := norm_le_norm_add_norm_sub' (ua + ε • v) (uc + ε • v)
        rw [← dist_eq_norm] at this
        rw [mem_ball, dist_zero_right] at hbc
        linarith
      obtain ⟨z, hz, hdz, hy₁, hy₂⟩ := exists_wall_near_of_conical hcon hloc h1 h1'
        (by linarith) dab hna hnb ga gb fun h => nab (congrArg π h)
      have hcl {w : ℝ × ℝ} (hy : ∀ τ > 0, ∃ y : ℝ × ℝ, dist y z < τ ∧ 1 < ‖y‖ ∧ ‖y‖ < 3 ∧
          ¬ IsWallDirection y ∧ G y = G w) : z ∈ closure (T ⁻¹' {π (G w)}) := by
        rw [Metric.mem_closure_iff]
        intro τ hτ
        obtain ⟨y, hyz, hy1, hy3, hny, hGy⟩ := hy τ hτ
        have hev : ∀ᶠ q in 𝓝 y, pointTreated 0 1 (some P₀) G q = G q := by
          have : ∀ᶠ q in 𝓝 y, 1 < ‖q‖ :=
            continuous_norm.continuousAt.eventually (lt_mem_nhds hy1)
          filter_upwards [this] with q hq
          exact hout (by rw [mem_ball, dist_zero_right]; linarith)
        refine ⟨y, ?_, by rwa [dist_comm]⟩
        rw [mem_preimage, mem_singleton_iff, hGread (by linarith) hny hev, hGy]
      have hclP : z ∈ closure (T ⁻¹' {π P₀}) := by
        rw [Metric.mem_closure_iff]
        intro τ hτ
        set s := min (1 / 2) (τ / 2) with hs
        have hs0 : 0 < s := lt_min (by norm_num) (by positivity)
        have hs1 : s ≤ 1 / 2 := min_le_left _ _
        have hsτ : s ≤ τ / 2 := min_le_right _ _
        have hyin : (1 - s) • z ∈ ball (0 : ℝ × ℝ) 1 := by
          rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith),
            hz]
          linarith
        refine ⟨(1 - s) • z, ?_, ?_⟩
        · rw [mem_preimage, mem_singleton_iff]
          exact hT.eq_of_eventually_const (Filter.eventually_of_mem (isOpen_ball.mem_nhds hyin)
            fun q hq => by simp only [hin hq])
        · rw [dist_eq_norm, show z - (1 - s) • z = s • z by rw [sub_smul, one_smul]; abel,
            norm_smul, Real.norm_eq_abs, abs_of_pos hs0, hz]
          linarith
      have htv : IsTrueVertex T z := ⟨_, _, _, nab, nac, nbc, hcl hy₁, hcl hy₂, hclP⟩
      refine hhole ha (by rw [hz]; norm_num) htv ?_
      linarith [dist_triangle ua (ua + ε • v) z, hd ua]
    by_cases b₁ : w₁ ∈ ball (0 : ℝ × ℝ) 1 <;> by_cases b₂ : w₂ ∈ ball (0 : ℝ × ℝ) 1 <;>
      by_cases b₃ : w₃ ∈ ball (0 : ℝ × ℝ) 1
    · exact n12 (by rw [e₁, e₂, hin b₁, hin b₂])
    · exact n12 (by rw [e₁, e₂, hin b₁, hin b₂])
    · exact n13 (by rw [e₁, e₃, hin b₁, hin b₃])
    · rw [e₁, e₂, hin b₁, hout b₂] at n12
      rw [e₁, e₃, hin b₁, hout b₃] at n13
      rw [e₂, e₃, hout b₂, hout b₃] at n23
      rw [dist_comm] at d12 d13
      exact key h₂ b₂ b₃ b₁ d23 d12 hn₂ hn₃ g₂ g₃ n23 (Ne.symm n12) (Ne.symm n13)
    · exact n23 (by rw [e₂, e₃, hin b₂, hin b₃])
    · rw [e₁, e₂, hout b₁, hin b₂] at n12
      rw [e₁, e₃, hout b₁, hout b₃] at n13
      rw [e₂, e₃, hin b₂, hout b₃] at n23
      exact key h₁ b₁ b₃ b₂ d13 d12 hn₁ hn₃ g₁ g₃ n13 n12 (Ne.symm n23)
    · rw [e₁, e₂, hout b₁, hout b₂] at n12
      rw [e₁, e₃, hout b₁, hin b₃] at n13
      rw [e₂, e₃, hout b₂, hin b₃] at n23
      exact key h₁ b₁ b₂ b₃ d12 d13 hn₁ hn₂ g₁ g₂ n12 n13 n23
    · rw [e₁, e₂, hout b₁, hout b₂] at n12
      rw [e₁, e₃, hout b₁, hout b₃] at n13
      rw [e₂, e₃, hout b₂, hout b₃] at n23
      rcases eq_or_eq_or_eq_of_conical hcon hloc (hone b₁) (D := 2 * l) (by linarith) d12 d13
        d23 hn₁ hn₂ hn₃ g₁ g₂ g₃ with h | h | h
      · exact n12 (congrArg π h)
      · exact n13 (congrArg π h)
      · exact n23 (congrArg π h)

/-- **The two-owner condition of the templates near a mark, at an explicit footprint radius.**
Every reading after a generic displacement of a template of the point treatment has the two-owner
condition with working set the closed square of radius `2`, holes of radius `ε₀` at its true
vertices within `3`, and every footprint radius `δ ≤ pointTreatmentRatio ε₀`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:447–479, 481–505`. -/
theorem hasTwoOwnerFootprints_reading_footprintTemplate (i : TemplateIndex) {v : ℝ × ℝ}
    (hv : IsGenericDisplacement v) {T : ℝ × ℝ → BlockSlot 1}
    (hT : IsDisplacedReading T (footprintTemplate i) v) {ε₀ δ : ℝ} (hε : 0 < ε₀)
    (hδ : δ ≤ pointTreatmentRatio ε₀) :
    HasTwoOwnerFootprints T (closedBall 0 2)
      {u | u ∈ closedBall (0 : ℝ × ℝ) 3 ∧ IsTrueVertex T u} ε₀ δ := by
  set c := i.2.1.1
  have hR : IsConicalAt referenceRepainting.guide c := by
    intro w a b ha hb haw hbw
    have := isConicalAt_blockGuide (blockSlot 1) i.2.1.2 w a b ha hb haw hbw
    simpa only [referenceRepainting, blockBaseline, blockCorner, Int.cast_zero, mul_zero,
      Prod.mk_zero_zero, add_zero] using this
  have hc := RepaintingBaseline.IsUnmodifiedGuide.isConicalAt _ rfl i.2.1.2 hR i.1.2
  have hcon : ∀ (w : ℝ × ℝ) (a : ℝ), 0 < a → ‖w‖ < 4 → ‖a • w‖ < 4 →
      i.1.1 (c + (1 / 32 : ℝ) • (a • w)) = i.1.1 (c + (1 / 32 : ℝ) • w) := by
    intro w a ha hw haw
    rw [smul_smul]
    refine hc w _ _ (by positivity) (by norm_num) ?_ ?_
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha] at haw
      nlinarith
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
      linarith
  have h0 : HasLineWalls wallNormals i.1.1 :=
    i.1.2.hasLineWalls _ ((hasLineWalls_blockGuide 1 (blockSlot 1)).comp_add _)
  have hw : HasLineWalls wallNormals fun u => i.1.1 (c + (1 / 32 : ℝ) • u) :=
    h0.comp_affine c (by norm_num)
  exact hasTwoOwnerFootprints_reading_pointTreated (G := fun u => i.1.1 (c + (1 / 32 : ℝ) • u))
    hcon (fun y hy hny => eventually_eq_of_not_isWallDirection hcon hw hy hny) i.2.2.2 i.2.2.1
    hv hT hε hδ

end TNLean.PEPS.Approximation
