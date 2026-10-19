/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicWallSlopes

/-!
# Conical guides with walls on lines

A guide near a mark is, in units of `t`, constant along the rays from the mark, with walls on
lines whose normals lie in `wallNormals`. This file shows:

* such a guide is locally constant off the wall directions
  (`eventually_eq_of_not_isWallDirection`);
* four isometric charts, exchanging or reversing the coordinate axes, carry every point into the
  cone `|w.2| ≤ w.1` (`exists_isWallChart`), where the guide is a function of the slope;
* three nearby points far from the mark carry at most two values
  (`eq_or_eq_or_eq_of_conical`), and two nearby values just outside the unit square are separated
  by one wall direction meeting the boundary of the square at a point approached from outside by
  both values (`exists_wall_near_of_conical`).

Distances are ambient sup distances: `ℝ × ℝ` carries the maximum metric.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), §7, `06-geometry.tex`: the walls of the guides
  (lines 69–80, 142–221), the straight-ray charts (lines 301–302), the point treatment (lines
  330–338), the compactness observation (lines 447–479) and the point covers (lines 481–505).
-/

open Set Metric Filter Topology

namespace TNLean.PEPS.Approximation

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

end TNLean.PEPS.Approximation
