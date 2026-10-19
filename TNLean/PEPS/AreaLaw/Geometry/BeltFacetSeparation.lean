/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Tactic.LinearCombination
import TNLean.PEPS.AreaLaw.Geometry.BirthSeparationAngular

/-!
# Explicit separation of polygons cut out by belt facets

A *belt facet* is a closed half-plane `a x₁ + b x₂ ≤ n` with integer level whose
normal is an axis vector, or a diagonal vector `(±1, ±1)` with even level. These
are the facets of the rescaled local patterns compared in the birth-separation
lemma: the lines have the four allowed slopes, and any two lines that are not
parallel meet in an integer point.

The compactness step of the manuscript (a positive minimum over a finite list of
rescaled patterns) is replaced here by an explicit constant. If a point `z`
violates every facet of a family by at most `ε < 1/7` in the facet values, then
some point `w` within sup distance `3ε` of `z` satisfies all of them. Either two
nearly tight facets with distinct directions meet in an integer point near `z`,
and every facet value at that integer point is an integer smaller than `1`; or
every nearly tight facet is parallel to one violated facet, and a translation
normal to that facet repairs all of them at once.

Applied to `x ∈ P` and `y ∈ Q`, with `ε = 2‖x - y‖`, this gives a common point
of `P` and `Q` within `7‖x - y‖` of both points. Hence two such polygons have
points at distance less than `birthSeparationConstant = 1/28` only together
inside an open quarter-square about a common point. At an integer common point
the angular estimate then holds.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:birth-separation`, lines 616–645,
with the quarter mesh and the four slopes of `geometry:initial-stars`,
lines 352–359.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-! ### Belt facets -/

/-- A facet `a x₁ + b x₂ ≤ n` of the normalized belt arrangement: an axis
normal at any integer level, or a diagonal normal at an even level.
Source: area-law Section 11, `geometry:initial-stars`, lines 352–359. -/
def IsBeltFacet (f : ℤ × ℤ × ℤ) : Prop :=
  ((f.1 = 1 ∨ f.1 = -1) ∧ f.2.1 = 0) ∨ (f.1 = 0 ∧ (f.2.1 = 1 ∨ f.2.1 = -1)) ∨
    ((f.1 = 1 ∨ f.1 = -1) ∧ (f.2.1 = 1 ∨ f.2.1 = -1) ∧ Even f.2.2)

private theorem isBeltFacet_det_dvd {f g : ℤ × ℤ × ℤ} (hf : IsBeltFacet f)
    (hg : IsBeltFacet g) (hdet : f.1 * g.2.1 - g.1 * f.2.1 ≠ 0) :
    (f.1 * g.2.1 - g.1 * f.2.1) ∣ (f.2.2 * g.2.1 - g.2.2 * f.2.1) ∧
      (f.1 * g.2.1 - g.1 * f.2.1) ∣ (f.1 * g.2.2 - g.1 * f.2.2) := by
  obtain ⟨a, b, n⟩ := f
  obtain ⟨a', b', n'⟩ := g
  simp only [IsBeltFacet] at hf hg hdet ⊢
  rcases hf with ⟨ha | ha, hb⟩ | ⟨ha, hb | hb⟩ | ⟨ha | ha, hb | hb, r, hr⟩ <;>
    rcases hg with ⟨ha' | ha', hb'⟩ | ⟨ha', hb' | hb'⟩ | ⟨ha' | ha', hb' | hb', r', hr'⟩ <;>
    subst_vars <;> (try norm_num at hdet ⊢) <;> omega

/-- Two lines of the normalized belt arrangement that are not parallel meet in
an integer point.
Source: area-law Section 11, `geometry:initial-stars`, lines 352–359. -/
theorem exists_int_eq_of_isBeltFacet {f g : ℤ × ℤ × ℤ} (hf : IsBeltFacet f)
    (hg : IsBeltFacet g) (hdet : f.1 * g.2.1 - g.1 * f.2.1 ≠ 0) {z : ℝ × ℝ}
    (hzf : (f.1 : ℝ) * z.1 + f.2.1 * z.2 = f.2.2)
    (hzg : (g.1 : ℝ) * z.1 + g.2.1 * z.2 = g.2.2) :
    ∃ i j : ℤ, z = ((i : ℝ), (j : ℝ)) := by
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := isBeltFacet_det_dvd hf hg hdet
  obtain ⟨a, b, n⟩ := f
  obtain ⟨a', b', n'⟩ := g
  simp only at hdet hzf hzg hp hq
  have hD : ((a * b' - a' * b : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hdet
  have e₁ : ((a * b' - a' * b : ℤ) : ℝ) * z.1 = ((n * b' - n' * b : ℤ) : ℝ) := by
    push_cast; linear_combination (b' : ℝ) * hzf - (b : ℝ) * hzg
  have e₂ : ((a * b' - a' * b : ℤ) : ℝ) * z.2 = ((a * n' - a' * n : ℤ) : ℝ) := by
    push_cast; linear_combination (a : ℝ) * hzg - (a' : ℝ) * hzf
  refine ⟨p, q, Prod.ext (mul_left_cancel₀ hD ?_) (mul_left_cancel₀ hD ?_)⟩
  · rw [e₁, hp]; push_cast; ring
  · rw [e₂, hq]; push_cast; ring

/-- The two normal coefficients of a belt facet have absolute values summing to at most `2`. -/
theorem isBeltFacet_abs {f : ℤ × ℤ × ℤ} (hf : IsBeltFacet f) :
    |f.1| + |f.2.1| ≤ 2 := by
  rcases hf with ⟨ha | ha, hb⟩ | ⟨ha, hb | hb⟩ | ⟨ha | ha, hb | hb, -⟩ <;>
    simp [ha, hb]

/-- The normal vector of a belt facet is nonzero. -/
theorem isBeltFacet_ne_zero {f : ℤ × ℤ × ℤ} (hf : IsBeltFacet f) :
    ((f.1 : ℝ), (f.2.1 : ℝ)) ≠ 0 := by
  intro h
  have h₁ : (f.1 : ℝ) = 0 := congrArg Prod.fst h
  have h₂ : (f.2.1 : ℝ) = 0 := congrArg Prod.snd h
  norm_cast at h₁ h₂
  rcases hf with ⟨ha | ha, hb⟩ | ⟨ha, hb | hb⟩ | ⟨ha | ha, hb | hb, -⟩ <;> omega

/-- The two normal coefficients of a belt facet are `0` or `±1`, and not both
`0`, so their squares sum to at least `1`. -/
private theorem isBeltFacet_coeffs {f : ℤ × ℤ × ℤ} (hf : IsBeltFacet f) :
    |(f.1 : ℝ)| ≤ 1 ∧ |(f.2.1 : ℝ)| ≤ 1 ∧ 1 ≤ (f.1 : ℝ) ^ 2 + (f.2.1 : ℝ) ^ 2 := by
  rcases hf with ⟨ha | ha, hb⟩ | ⟨ha, hb | hb⟩ | ⟨ha | ha, hb | hb, -⟩ <;>
    simp [ha, hb]

/-- Two belt facets with parallel lines have equal or opposite normals. -/
private theorem isBeltFacet_parallel {f g : ℤ × ℤ × ℤ} (hf : IsBeltFacet f)
    (hg : IsBeltFacet g) (hdet : f.1 * g.2.1 - g.1 * f.2.1 = 0) :
    (g.1 = f.1 ∧ g.2.1 = f.2.1) ∨ (g.1 = -f.1 ∧ g.2.1 = -f.2.1) := by
  obtain ⟨a, b, n⟩ := f
  obtain ⟨a', b', n'⟩ := g
  simp only [IsBeltFacet] at hf hg hdet ⊢
  rcases hf with ⟨ha | ha, hb⟩ | ⟨ha, hb | hb⟩ | ⟨ha | ha, hb | hb, -⟩ <;>
    rcases hg with ⟨ha' | ha', hb'⟩ | ⟨ha', hb' | hb'⟩ | ⟨ha' | ha', hb' | hb', -⟩ <;>
    subst_vars <;> omega

/-- The facet functional of a belt facet is `2`-Lipschitz for the sup norm. -/
theorem abs_isBeltFacet_sub_le {f : ℤ × ℤ × ℤ} (hf : IsBeltFacet f) (z w : ℝ × ℝ) :
    |((f.1 : ℝ) * z.1 + f.2.1 * z.2) - (f.1 * w.1 + f.2.1 * w.2)| ≤ 2 * ‖z - w‖ := by
  obtain ⟨ha, hb, -⟩ := isBeltFacet_coeffs hf
  have h₁ : |z.1 - w.1| ≤ ‖z - w‖ := by simpa using norm_fst_le (z - w)
  have h₂ : |z.2 - w.2| ≤ ‖z - w‖ := by simpa using norm_snd_le (z - w)
  calc |((f.1 : ℝ) * z.1 + f.2.1 * z.2) - (f.1 * w.1 + f.2.1 * w.2)|
      = |(f.1 : ℝ) * (z.1 - w.1) + f.2.1 * (z.2 - w.2)| := by congr 1; ring
    _ ≤ |(f.1 : ℝ)| * |z.1 - w.1| + |(f.2.1 : ℝ)| * |z.2 - w.2| := by
      rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ 1 * ‖z - w‖ + 1 * ‖z - w‖ := by gcongr
    _ = 2 * ‖z - w‖ := by ring

private theorem int_le_of_lt_add_one {n n' : ℤ} (h : (n : ℝ) < n' + 1) : (n : ℝ) ≤ n' := by
  have h' : n < n' + 1 := by exact_mod_cast h
  exact_mod_cast Int.lt_add_one_iff.mp h'

/-- An integer facet value below `n + 1` is at most `n`. -/
private theorem int_facet_le {a b n i j : ℤ}
    (h : (a : ℝ) * i + b * j < n + 1) : (a : ℝ) * i + b * j ≤ n := by
  have h' : a * i + b * j < n + 1 := by exact_mod_cast h
  exact_mod_cast (show a * i + b * j ≤ n by omega)

private theorem abs_mul_sub_mul_le {p q r s : ℝ} (hp : |p| ≤ 1) (hq : |q| ≤ 1) :
    |p * r - q * s| ≤ |r| + |s| :=
  calc |p * r - q * s| ≤ |p * r| + |q * s| := abs_sub _ _
    _ = |p| * |r| + |q| * |s| := by rw [abs_mul, abs_mul]
    _ ≤ 1 * |r| + 1 * |s| := by gcongr
    _ = |r| + |s| := by ring

/-- The closed polygon cut out by a set of facets `a x₁ + b x₂ ≤ n`.
Source: area-law Section 11, `geometry:birth-separation`, lines 597–615. -/
def facetPolygon (S : Set (ℤ × ℤ × ℤ)) : Set (ℝ × ℝ) :=
  ⋂ f ∈ S, intHalfPlane f.1 f.2.1 f.2.2

theorem mem_facetPolygon {S : Set (ℤ × ℤ × ℤ)} {z : ℝ × ℝ} :
    z ∈ facetPolygon S ↔ ∀ f ∈ S, (f.1 : ℝ) * z.1 + f.2.1 * z.2 ≤ f.2.2 := by
  simp [facetPolygon, intHalfPlane]

theorem facetPolygon_union (S T : Set (ℤ × ℤ × ℤ)) :
    facetPolygon (S ∪ T) = facetPolygon S ∩ facetPolygon T :=
  Set.biInter_union S T _

theorem facetPolygon_range {ι : Type*} (F : ι → ℤ × ℤ × ℤ) :
    facetPolygon (Set.range F) = ⋂ i, intHalfPlane (F i).1 (F i).2.1 (F i).2.2 :=
  Set.biInter_range

/-! ### Repairing small facet violations -/

/-- **Explicit error bound for belt facets.** If a point violates each facet of
a set of belt facets by at most `ε`, with `0 ≤ ε` and `7ε < 1`, then the facet
polygon contains a point within sup distance `3ε`.
Source: area-law Section 11, `geometry:birth-separation`, lines 616–625, made
explicit with the quarter mesh of `geometry:initial-stars`, lines 352–359. -/
theorem exists_mem_facetPolygon_of_le_add {S : Set (ℤ × ℤ × ℤ)}
    (hS : ∀ f ∈ S, IsBeltFacet f) {ε : ℝ} (hε₀ : 0 ≤ ε) (hε : 7 * ε < 1) {z : ℝ × ℝ}
    (hz : ∀ f ∈ S, (f.1 : ℝ) * z.1 + f.2.1 * z.2 ≤ f.2.2 + ε) :
    ∃ w ∈ facetPolygon S, ‖z - w‖ ≤ 3 * ε := by
  simp only [mem_facetPolygon]
  by_cases hall : ∀ f ∈ S, (f.1 : ℝ) * z.1 + f.2.1 * z.2 ≤ f.2.2
  · exact ⟨z, hall, by simpa using hε₀⟩
  push Not at hall
  obtain ⟨⟨a, b, n⟩, hfS, hfz⟩ := hall
  have hf := hS _ hfS
  have hfε := hz _ hfS
  simp only at hfz hfε
  obtain ⟨ha, hb, hab⟩ := isBeltFacet_coeffs hf
  simp only at ha hb hab
  by_cases hnp : ∃ g ∈ S, (g.2.2 : ℝ) - 2 * ε < g.1 * z.1 + g.2.1 * z.2 ∧
      a * g.2.1 - g.1 * b ≠ 0
  · -- two nearly tight facets with distinct directions: their integer meeting point
    obtain ⟨⟨a', b', n'⟩, hgS, hgz, hdet⟩ := hnp
    have hg := hS _ hgS
    have hgε := hz _ hgS
    simp only at hgz hdet hgε
    obtain ⟨ha', hb', -⟩ := isBeltFacet_coeffs hg
    simp only at ha' hb'
    set r₁ : ℝ := a * z.1 + b * z.2 - n
    set r₂ : ℝ := a' * z.1 + b' * z.2 - n'
    set D : ℝ := a * b' - a' * b
    have hDz : ((a * b' - a' * b : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hdet
    have hD : D ≠ 0 := by simpa [D] using hDz
    have hD1 : 1 ≤ |D| := by
      have : (1 : ℤ) ≤ |a * b' - a' * b| := Int.one_le_abs hdet
      have : (1 : ℝ) ≤ |((a * b' - a' * b : ℤ) : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast this
      simpa [D] using this
    set v : ℝ × ℝ := (z.1 - (b' * r₁ - b * r₂) / D, z.2 - (a * r₂ - a' * r₁) / D)
    have hv₁ : (a : ℝ) * v.1 + b * v.2 = n := by
      have e : (a : ℝ) * (b' * r₁ - b * r₂) + b * (a * r₂ - a' * r₁) = D * r₁ := by
        simp only [D]; ring
      have : (a : ℝ) * v.1 + b * v.2 =
          a * z.1 + b * z.2 - (a * (b' * r₁ - b * r₂) + b * (a * r₂ - a' * r₁)) / D := by
        simp only [v]; ring
      rw [this, e, mul_div_cancel_left₀ _ hD]; simp only [r₁]; ring
    have hv₂ : (a' : ℝ) * v.1 + b' * v.2 = n' := by
      have e : (a' : ℝ) * (b' * r₁ - b * r₂) + b' * (a * r₂ - a' * r₁) = D * r₂ := by
        simp only [D]; ring
      have : (a' : ℝ) * v.1 + b' * v.2 =
          a' * z.1 + b' * z.2 - (a' * (b' * r₁ - b * r₂) + b' * (a * r₂ - a' * r₁)) / D := by
        simp only [v]; ring
      rw [this, e, mul_div_cancel_left₀ _ hD]; simp only [r₂]; ring
    obtain ⟨i, j, hij⟩ := exists_int_eq_of_isBeltFacet hf hg hdet hv₁ hv₂
    have hdiv {x : ℝ} : |x / D| ≤ |x| := by
      rw [abs_div]; exact div_le_self (abs_nonneg _) hD1
    have hr₁ : 0 < r₁ := by simp only [r₁]; linarith
    have hr : |r₁| + |r₂| ≤ 3 * ε := by
      have : |r₂| ≤ 2 * ε := abs_le.mpr ⟨by simp only [r₂]; linarith, by simp only [r₂]; linarith⟩
      have : r₁ ≤ ε := by simp only [r₁]; linarith
      rw [abs_of_pos hr₁]; linarith
    have hzv : ‖z - v‖ ≤ 3 * ε := by
      rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, max_le_iff]
      simp only [v, Prod.fst_sub, Prod.snd_sub, sub_sub_cancel]
      exact ⟨(hdiv.trans (abs_mul_sub_mul_le hb' hb)).trans hr,
        (hdiv.trans ((abs_mul_sub_mul_le ha ha').trans_eq (add_comm _ _))).trans hr⟩
    refine ⟨v, fun g hg ↦ ?_, hzv⟩
    have hlip := (abs_le.mp (abs_isBeltFacet_sub_le (hS g hg) v z)).2
    have key : (g.1 : ℝ) * v.1 + g.2.1 * v.2 < g.2.2 + 1 := by
      have := hz g hg; rw [norm_sub_rev] at hlip; linarith
    rw [hij] at key ⊢
    exact int_facet_le key
  · -- every nearly tight facet is parallel to the violated one: translate normally
    push Not at hnp
    set c : ℝ := a * z.1 + b * z.2 - n with hc
    set m : ℝ := (a : ℝ) ^ 2 + b ^ 2
    have hm : 0 < m := by linarith
    have hc0 : 0 < c := by linarith
    set w : ℝ × ℝ := (z.1 - c / m * a, z.2 - c / m * b)
    have hval : (a : ℝ) * w.1 + b * w.2 = n := by
      have : c / m * m = c := div_mul_cancel₀ c hm.ne'
      simp only [w, m] at this ⊢
      linear_combination hc - this
    have hzw : ‖z - w‖ ≤ ε := by
      have hcm : 0 ≤ c / m := by positivity
      have hcm' : c / m ≤ ε := (div_le_self hc0.le (by linarith)).trans (by linarith)
      rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, max_le_iff]
      simp only [w, Prod.fst_sub, Prod.snd_sub, sub_sub_cancel, abs_mul, abs_of_nonneg hcm]
      exact ⟨(mul_le_of_le_one_right hcm ha).trans hcm', (mul_le_of_le_one_right hcm hb).trans hcm'⟩
    refine ⟨w, fun g hg ↦ ?_, hzw.trans (by linarith)⟩
    obtain ⟨a', b', n'⟩ := g
    have hgε := hz _ hg
    simp only at hgε ⊢
    by_cases hnear : (n' : ℝ) - 2 * ε < a' * z.1 + b' * z.2
    · rcases isBeltFacet_parallel hf (hS _ hg) (hnp _ hg hnear) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [hval]; exact int_le_of_lt_add_one (by linarith)
      · push_cast at hgε ⊢
        have := int_le_of_lt_add_one (n := -n) (n' := n') (by push_cast; linarith)
        push_cast at this; linarith
    · have hlip := (abs_le.mp (abs_isBeltFacet_sub_le (hS _ hg) w z)).2
      rw [norm_sub_rev] at hlip
      simp only at hlip
      linarith

/-! ### The explicit separation constant -/

/-- **The birth-separation constant** `c₂ = 1/28`, in the normalized units of
the compared local patterns. Two points of two polygons cut out by belt facets
that are closer than this constant lie together in an open quarter-square
about a common point of the polygons. It replaces the positive minimum over the
finite list of rescaled patterns.
Source: area-law Section 11, `geometry:birth-separation`, lines 616–625. -/
def birthSeparationConstant : ℝ := 1 / 28

theorem birthSeparationConstant_pos : 0 < birthSeparationConstant := by
  norm_num [birthSeparationConstant]

theorem birthSeparationConstant_le_quarter : birthSeparationConstant ≤ 1 / 4 := by
  norm_num [birthSeparationConstant]

theorem birthSeparationConstant_le_one : birthSeparationConstant ≤ 1 :=
  birthSeparationConstant_le_quarter.trans (by norm_num)

/-- Two integer points within sup distance `1/4` coincide. -/
theorem eq_of_norm_sub_intPoint_le_quarter {i j i' j' : ℤ}
    (h : ‖((i : ℝ), (j : ℝ)) - ((i' : ℝ), (j' : ℝ))‖ ≤ 1 / 4) : i = i' ∧ j = j' := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, max_le_iff] at h
  simp only [Prod.fst_sub, Prod.snd_sub] at h
  obtain ⟨h₁, h₂⟩ := h
  have a₁ : |((i - i' : ℤ) : ℝ)| < 1 := by push_cast; linarith
  have a₂ : |((j - j' : ℤ) : ℝ)| < 1 := by push_cast; linarith
  rw [← Int.cast_abs] at a₁ a₂
  have b₁ : |i - i'| < 1 := by exact_mod_cast a₁
  have b₂ : |j - j'| < 1 := by exact_mod_cast a₂
  have c₁ := abs_lt.mp b₁
  have c₂ := abs_lt.mp b₂
  omega

/-- **A common point near two close points.** If `x` and `y` lie in two polygons
cut out by belt facets and `‖x - y‖ < 1/28`, then the polygons have a common
point within sup distance `1/4` of both `x` and `y`.
Source: area-law Section 11, `geometry:birth-separation`, lines 616–625. -/
theorem exists_mem_facetPolygon_inter_of_norm_sub_lt {S T : Set (ℤ × ℤ × ℤ)}
    (hS : ∀ f ∈ S, IsBeltFacet f) (hT : ∀ f ∈ T, IsBeltFacet f) {x y : ℝ × ℝ}
    (hx : x ∈ facetPolygon S) (hy : y ∈ facetPolygon T)
    (hxy : ‖x - y‖ < birthSeparationConstant) :
    ∃ q ∈ facetPolygon S ∩ facetPolygon T, ‖x - q‖ < 1 / 4 ∧ ‖y - q‖ < 1 / 4 := by
  have hδ : ‖x - y‖ < 1 / 28 := hxy
  have hδ0 := norm_nonneg (x - y)
  obtain ⟨w, hw, hxw⟩ := exists_mem_facetPolygon_of_le_add (S := S ∪ T)
    (fun f hf ↦ hf.elim (hS f) (hT f)) (ε := 2 * ‖x - y‖) (by positivity) (by linarith)
    (z := x) fun f hf ↦ by
      rcases hf with hf | hf
      · linarith [mem_facetPolygon.mp hx f hf]
      · linarith [(abs_le.mp (abs_isBeltFacet_sub_le (hT f hf) x y)).2,
          mem_facetPolygon.mp hy f hf]
  rw [facetPolygon_union] at hw
  refine ⟨w, hw, by linarith, ?_⟩
  calc ‖y - w‖ ≤ ‖y - x‖ + ‖x - w‖ := norm_sub_le_norm_sub_add_norm_sub y x w
    _ < 1 / 4 := by rw [norm_sub_rev]; linarith

/-- **Explicit contact dichotomy for belt polygons.** Let two polygons cut out by
belt facets meet only in integer points. Then each pair of their points is at
distance at least `birthSeparationConstant = 1/28`, or lies in the open
quarter-square about a common point `q` of the two polygons, where the angular
estimate `‖x - y‖ ≥ ‖y - q‖ / 2` holds.
Source: area-law Section 11, `geometry:birth-separation`, lines 616–645. -/
theorem facetPolygon_contact_dichotomy {S T : Set (ℤ × ℤ × ℤ)}
    (hS : ∀ f ∈ S, IsBeltFacet f) (hT : ∀ f ∈ T, IsBeltFacet f)
    (hST : ∀ z ∈ facetPolygon S, z ∈ facetPolygon T → ∃ i j : ℤ, z = ((i : ℝ), (j : ℝ)))
    {x y : ℝ × ℝ} (hx : x ∈ facetPolygon S) (hy : y ∈ facetPolygon T) :
    birthSeparationConstant ≤ ‖x - y‖ ∨ ∃ q ∈ facetPolygon S ∩ facetPolygon T,
      ‖x - q‖ < 1 / 4 ∧ ‖y - q‖ < 1 / 4 ∧ ‖y - q‖ / 2 ≤ ‖x - y‖ := by
  refine (le_or_gt _ _).imp id fun hxy ↦ ?_
  obtain ⟨q, hq, hxq, hyq⟩ := exists_mem_facetPolygon_inter_of_norm_sub_lt hS hT hx hy hxy
  refine ⟨q, hq, hxq, hyq, ?_⟩
  obtain ⟨i, j, rfl⟩ := hST q hq.1 hq.2
  have hsec {U : Set (ℤ × ℤ × ℤ)} (hU : ∀ f ∈ U, IsBeltFacet f) :
      IsQuarterSectorial ((i : ℝ), (j : ℝ)) (facetPolygon U) :=
    .iInter fun f ↦ .iInter fun hf ↦ isQuarterSectorial_intHalfPlane (isBeltFacet_abs (hU f hf)) i j
  have hcontact : ∀ z ∈ facetPolygon S, z ∈ facetPolygon T →
      ‖z - ((i : ℝ), (j : ℝ))‖ ≤ 1 / 4 → z = ((i : ℝ), (j : ℝ)) := by
    intro z hzS hzT hz
    obtain ⟨i', j', rfl⟩ := hST z hzS hzT
    obtain ⟨rfl, rfl⟩ := eq_of_norm_sub_intPoint_le_quarter hz
    rfl
  have := half_max_le_norm_sub_of_isQuarterSectorial (hsec hS) (hsec hT) hcontact hx hy
    hxq.le hyq.le
  linarith [le_max_right ‖x - ((i : ℝ), (j : ℝ))‖ ‖y - ((i : ℝ), (j : ℝ))‖]

end TNLean.PEPS.AreaLaw.Geometry
