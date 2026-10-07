/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.Templates
import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

/-!
# Supporting slabs of allowed template polygons

The actual triangle and rectangle constructors determine their convex hulls
through supporting slabs with the four allowed normal directions. The reverse
inclusion uses barycentric coordinates and orthogonal side coordinates.

These are original proofs from the geometry used in Lemma 9.4 of the
September 24, 2026 area-law manuscript. No upstream Lean proof text is reused.
-/

/-
Source: September 24, 2026; scanner:templates (Lemma 9.4).
Revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original formalization; no upstream Lean proof text reused.
Provenance-ID: 8754-tnlean.peps.arealaw.geometry.templatepolygon.vertices
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.TemplatePolygon.vertices
Provenance-ID: 8754-tnlean.peps.arealaw.geometry.templatepolygon.region_eq_convexhull_vertices
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.TemplatePolygon.region_eq_convexHull_vertices
Provenance-ID: 8754-tnlean.peps.arealaw.geometry.templatepolygon.mem_region_iff_normal_bounds
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.TemplatePolygon.mem_region_iff_normal_bounds
Provenance-ID: 8754-tnlean.peps.arealaw.geometry.templatepolygon.exists_four_strip_bounds
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.TemplatePolygon.exists_four_strip_bounds
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The real vertices appearing in the actual polygon constructor. -/
def TemplatePolygon.vertices : TemplatePolygon → Set (ℝ × ℝ)
  | .triangle a b c _ _ _ _ => {a, b, c}
  | .rectangle a u v _ _ _ _ _ => {a, a + u, a + u + v, a + v}

/-- The region is the convex hull of its actual vertices. -/
theorem TemplatePolygon.region_eq_convexHull_vertices (P : TemplatePolygon) :
    P.region = convexHull ℝ P.vertices := by
  cases P <;> rfl

private def planeDot (u p : ℝ × ℝ) : ℝ := u.1 * p.1 + u.2 * p.2

private def planeCross (u v : ℝ × ℝ) : ℝ := u.1 * v.2 - u.2 * v.1

private theorem allowed_perpendicular {u : ℝ × ℝ} (hu : IsAllowedSlope u) :
    IsAllowedSlope (-u.2, u.1) := by
  rcases hu with h | h | h | h <;> simp_all [IsAllowedSlope]

private theorem ratio_nonneg_of_between {x d : ℝ}
    (h : min 0 d ≤ x ∧ x ≤ max 0 d) : 0 ≤ x / d := by
  by_cases hd : 0 ≤ d
  · rw [min_eq_left hd, max_eq_right hd] at h
    exact div_nonneg h.1 hd
  · have hd' : d ≤ 0 := le_of_not_ge hd
    rw [min_eq_right hd', max_eq_left hd'] at h
    exact div_nonneg_of_nonpos h.2 hd'

private theorem side_bounds {S : Set (ℝ × ℝ)} {p a b : ℝ × ℝ}
    (h : ∀ u : ℝ × ℝ, IsAllowedSlope u → ∀ l r : ℝ,
      (∀ q ∈ S, l ≤ planeDot u q ∧ planeDot u q ≤ r) →
        l ≤ planeDot u p ∧ planeDot u p ≤ r)
    (hab : IsAllowedSlope (b - a)) {l r : ℝ}
    (hs : ∀ q ∈ S, l ≤ planeCross (b - a) (q - a) ∧
      planeCross (b - a) (q - a) ≤ r) :
    l ≤ planeCross (b - a) (p - a) ∧ planeCross (b - a) (p - a) ≤ r := by
  let u : ℝ × ℝ := (-(b.2 - a.2), b.1 - a.1)
  have hu : IsAllowedSlope u := allowed_perpendicular hab
  have hp := h u hu (l + planeDot u a) (r + planeDot u a) (by
    intro q hq
    have hq' := hs q hq
    dsimp [u, planeDot, planeCross] at hq' ⊢
    constructor <;> nlinarith only [hq'.1, hq'.2])
  dsimp [u, planeDot, planeCross] at hp ⊢
  constructor <;> nlinarith only [hp.1, hp.2]

private theorem triangle_mem_of_normal_bounds (a b c p : ℝ × ℝ)
    (hd : planeCross (b - a) (c - a) ≠ 0)
    (hab : IsAllowedSlope (b - a)) (hbc : IsAllowedSlope (c - b))
    (hca : IsAllowedSlope (a - c))
    (h : ∀ u : ℝ × ℝ, IsAllowedSlope u → ∀ l r : ℝ,
      (∀ q ∈ ({a, b, c} : Set (ℝ × ℝ)), l ≤ planeDot u q ∧ planeDot u q ≤ r) →
        l ≤ planeDot u p ∧ planeDot u p ≤ r) :
    p ∈ convexHull ℝ ({a, b, c} : Set (ℝ × ℝ)) := by
  let d := planeCross (b - a) (c - a)
  let α := planeCross (a - c) (p - c) / d
  let β := planeCross (b - a) (p - a) / d
  let γ := planeCross (c - b) (p - b) / d
  have hside (x y : ℝ × ℝ) (hxy : IsAllowedSlope (y - x))
      (hv : ∀ q ∈ ({a, b, c} : Set (ℝ × ℝ)),
        planeCross (y - x) (q - x) = 0 ∨ planeCross (y - x) (q - x) = d) :
      0 ≤ planeCross (y - x) (p - x) / d := by
    apply ratio_nonneg_of_between
    apply side_bounds h hxy
    intro q hq
    rcases hv q hq with hq' | hq'
    · rw [hq']
      exact ⟨min_le_left _ _, le_max_left _ _⟩
    · rw [hq']
      exact ⟨min_le_right _ _, le_max_right _ _⟩
  have hα : 0 ≤ α := by
    apply hside c a hca
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl
    · left
      dsimp [planeCross]
      ring
    · right
      dsimp [d, planeCross]
      ring
    · left
      simp [planeCross]
  have hβ : 0 ≤ β := by
    apply hside a b hab
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl
    · left
      simp [planeCross]
    · left
      dsimp [planeCross]
      ring
    · exact Or.inr rfl
  have hγ : 0 ≤ γ := by
    apply hside b c hbc
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl
    · right
      dsimp [d, planeCross]
      ring
    · left
      simp [planeCross]
    · left
      dsimp [planeCross]
      ring
  have hd' : d ≠ 0 := hd
  have hsum : γ + α + β = 1 := by
    dsimp [α, β, γ]
    field_simp [hd']
    dsimp [d, planeCross]
    ring
  have hpoint : γ • a + α • b + β • c = p := by
    ext <;> simp [α, β, γ]
    all_goals
      field_simp [hd']
      dsimp [d, planeCross]
      ring
  apply mem_convexHull_of_exists_fintype ![γ, α, β] ![a, b, c]
  · intro i
    fin_cases i
    · exact hγ
    · exact hα
    · exact hβ
  · simpa [Fin.sum_univ_succ, add_assoc] using hsum
  · intro i
    fin_cases i <;> simp
  · simpa [Fin.sum_univ_succ, add_assoc] using hpoint

private theorem planeDot_self_pos {u : ℝ × ℝ} (hu : u ≠ 0) :
    0 < planeDot u u := by
  by_contra h
  have hle : u.1 * u.1 + u.2 * u.2 ≤ 0 := le_of_not_gt h
  have h₁ : u.1 = 0 := by nlinarith [sq_nonneg u.2, sq_nonneg u.1]
  have h₂ : u.2 = 0 := by nlinarith [sq_nonneg u.1, sq_nonneg u.2]
  exact hu (Prod.ext h₁ h₂)

private theorem cross_ne_zero_of_orthogonal {u v : ℝ × ℝ}
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : planeDot u v = 0) : planeCross u v ≠ 0 := by
  have hpos := mul_pos (planeDot_self_pos hu) (planeDot_self_pos hv)
  have hid : planeCross u v ^ 2 + planeDot u v ^ 2 = planeDot u u * planeDot v v := by
    dsimp [planeCross, planeDot]
    ring
  intro hzero
  rw [hzero, huv] at hid
  have hid' : 0 = planeDot u u * planeDot v v := by
    simpa only [zero_pow, zero_add] using hid
  exact (ne_of_gt hpos) hid'.symm

private theorem basis_reconstruct (a u v p : ℝ × ℝ) (hd : planeCross u v ≠ 0) :
    a + (planeCross (p - a) v / planeCross u v) • u +
      (planeCross u (p - a) / planeCross u v) • v = p := by
  ext <;> simp
  all_goals
    field_simp [hd]
    dsimp [planeCross]
    ring

private theorem rectangle_mem_of_normal_bounds (a u v p : ℝ × ℝ)
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : planeDot u v = 0)
    (hus : IsAllowedSlope u) (hvs : IsAllowedSlope v)
    (h : ∀ w : ℝ × ℝ, IsAllowedSlope w → ∀ l r : ℝ,
      (∀ q ∈ ({a, a + u, a + u + v, a + v} : Set (ℝ × ℝ)),
        l ≤ planeDot w q ∧ planeDot w q ≤ r) →
          l ≤ planeDot w p ∧ planeDot w p ≤ r) :
    p ∈ convexHull ℝ ({a, a + u, a + u + v, a + v} : Set (ℝ × ℝ)) := by
  have hu' := planeDot_self_pos hu
  have hv' := planeDot_self_pos hv
  have hd := cross_ne_zero_of_orthogonal hu hv huv
  let α := planeCross (p - a) v / planeCross u v
  let β := planeCross u (p - a) / planeCross u v
  have hp : a + α • u + β • v = p := basis_reconstruct a u v p hd
  have hpu : planeDot u (p - a) = α * planeDot u u := by
    rw [← hp]
    dsimp [planeDot] at huv ⊢
    linear_combination β * huv
  have hpv : planeDot v (p - a) = β * planeDot v v := by
    rw [← hp]
    dsimp [planeDot] at huv ⊢
    linear_combination α * huv
  have hU : 0 ≤ planeDot u (p - a) ∧ planeDot u (p - a) ≤ planeDot u u := by
    have hb := h u hus (planeDot u a) (planeDot u a + planeDot u u) (by
      intro q hq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl | rfl | rfl <;>
        dsimp [planeDot] at * <;> constructor <;> nlinarith only [hu', huv])
    dsimp [planeDot] at hb ⊢
    constructor <;> nlinarith only [hb.1, hb.2]
  have hV : 0 ≤ planeDot v (p - a) ∧ planeDot v (p - a) ≤ planeDot v v := by
    have hb := h v hvs (planeDot v a) (planeDot v a + planeDot v v) (by
      intro q hq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl | rfl | rfl <;>
        dsimp [planeDot] at * <;> constructor <;> nlinarith only [hv', huv])
    dsimp [planeDot] at hb ⊢
    constructor <;> nlinarith only [hb.1, hb.2]
  rw [hpu] at hU
  rw [hpv] at hV
  have hα₀ : 0 ≤ α := (mul_le_mul_right hu').mp (by simpa using hU.1)
  have hα₁ : α ≤ 1 := (mul_le_mul_right hu').mp (by simpa using hU.2)
  have hβ₀ : 0 ≤ β := (mul_le_mul_right hv').mp (by simpa using hV.1)
  have hβ₁ : β ≤ 1 := (mul_le_mul_right hv').mp (by simpa using hV.2)
  have hαc : 0 ≤ 1 - α := sub_nonneg.mpr hα₁
  have hβc : 0 ≤ 1 - β := sub_nonneg.mpr hβ₁
  have hpoint : ((1 - α) * (1 - β)) • a + (α * (1 - β)) • (a + u) +
      (α * β) • (a + u + v) + ((1 - α) * β) • (a + v) = p := by
    rw [← hp]
    ext <;> simp <;> ring
  apply mem_convexHull_of_exists_fintype
    ![(1 - α) * (1 - β), α * (1 - β), α * β, (1 - α) * β]
    ![a, a + u, a + u + v, a + v]
  · intro i
    fin_cases i
    · exact mul_nonneg hαc hβc
    · exact mul_nonneg hα₀ hβc
    · exact mul_nonneg hα₀ hβ₀
    · exact mul_nonneg hαc hβ₀
  · simp [Fin.sum_univ_succ]
    ring
  · intro i
    fin_cases i <;> simp
  · simpa [Fin.sum_univ_succ, add_assoc] using hpoint

/-- An allowed triangle or rectangle is exactly the intersection of all closed
supporting slabs with allowed normal directions. This is derived from the real
convex-hull constructors, not supplied as an extra template assumption. -/
theorem TemplatePolygon.mem_region_iff_normal_bounds (P : TemplatePolygon) (p : ℝ × ℝ) :
    p ∈ P.region ↔ ∀ u : ℝ × ℝ, IsAllowedSlope u → ∀ l r : ℝ,
      (∀ q ∈ P.vertices, l ≤ u.1 * q.1 + u.2 * q.2 ∧ u.1 * q.1 + u.2 * q.2 ≤ r) →
        l ≤ u.1 * p.1 + u.2 * p.2 ∧ u.1 * p.1 + u.2 * p.2 ≤ r := by
  constructor
  · intro hp u _ l r hv
    let f : (ℝ × ℝ) →ₗ[ℝ] ℝ :=
      u.1 • LinearMap.fst ℝ ℝ ℝ + u.2 • LinearMap.snd ℝ ℝ ℝ
    have hc : Convex ℝ {q : ℝ × ℝ | l ≤ u.1 * q.1 + u.2 * q.2 ∧
        u.1 * q.1 + u.2 * q.2 ≤ r} := by
      change Convex ℝ (f ⁻¹' Set.Icc l r)
      exact (convex_Icc l r).linear_preimage f
    rw [P.region_eq_convexHull_vertices] at hp
    exact convexHull_min hv hc hp
  · intro h
    cases P with
    | triangle a b c hd hab hbc hca =>
      exact triangle_mem_of_normal_bounds a b c p hd hab hbc hca h
    | rectangle a u v hu hv huv hus hvs =>
      exact rectangle_mem_of_normal_bounds a u v p hu hv huv hus hvs h

private theorem finite_form_bounds {S : Set (ℝ × ℝ)} (hs : S.Finite) (hne : S.Nonempty)
    (f : (ℝ × ℝ) → ℝ) : ∃ l r : ℝ,
      (∃ a ∈ S, f a = l) ∧ (∃ b ∈ S, f b = r) ∧
        ∀ q ∈ S, l ≤ f q ∧ f q ≤ r := by
  classical
  let V := hs.toFinset.image f
  have hV : V.Nonempty := (hs.toFinset_nonempty.mpr hne).image f
  refine ⟨V.min' hV, V.max' hV, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hfa⟩ := Finset.mem_image.mp (Finset.min'_mem V hV)
    exact ⟨a, hs.mem_toFinset.mp ha, hfa⟩
  · obtain ⟨b, hb, hfb⟩ := Finset.mem_image.mp (Finset.max'_mem V hV)
    exact ⟨b, hs.mem_toFinset.mp hb, hfb⟩
  · intro q hq
    have hq' : f q ∈ V := Finset.mem_image.mpr ⟨q, hs.mem_toFinset.mpr hq, rfl⟩
    exact ⟨Finset.min'_le _ _ hq', Finset.le_max' _ _ hq'⟩

private theorem scaled_between {a b x c l r : ℝ} (hx : a ≤ x ∧ x ≤ b)
    (ha : l ≤ c * a ∧ c * a ≤ r) (hb : l ≤ c * b ∧ c * b ≤ r) :
    l ≤ c * x ∧ c * x ≤ r := by
  by_cases hc : 0 ≤ c
  · exact ⟨ha.1.trans (mul_le_mul_of_nonneg_left hx.1 hc),
      (mul_le_mul_of_nonneg_left hx.2 hc).trans hb.2⟩
  · have hc' : c ≤ 0 := le_of_not_ge hc
    exact ⟨hb.1.trans (mul_le_mul_of_nonpos_left hx.2 hc'),
      (mul_le_mul_of_nonpos_left hx.1 hc').trans ha.2⟩

/-- The actual polygon admits eight real bounds for the four forms `x`, `y`,
`x+y`, and `x-y`. No half-plane description is assumed in the model. -/
theorem TemplatePolygon.exists_four_strip_bounds (P : TemplatePolygon) :
    ∃ lx ux ly uy ls us ld ud : ℝ, ∀ p : ℝ × ℝ,
      p ∈ P.region ↔ (lx ≤ p.1 ∧ p.1 ≤ ux) ∧ (ly ≤ p.2 ∧ p.2 ≤ uy) ∧
        (ls ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ us) ∧ (ld ≤ p.1 - p.2 ∧ p.1 - p.2 ≤ ud) := by
  have hf : P.vertices.Finite := by
    cases P <;> simp only [TemplatePolygon.vertices] <;> exact Set.toFinite _
  have hn : P.vertices.Nonempty := by cases P <;> exact Set.insert_nonempty _ _
  obtain ⟨lx, ux, hlx, hux, hx⟩ := finite_form_bounds hf hn (fun q ↦ q.1)
  obtain ⟨ly, uy, hly, huy, hy⟩ := finite_form_bounds hf hn (fun q ↦ q.2)
  obtain ⟨ls, us, hls, hus, hs⟩ := finite_form_bounds hf hn (fun q ↦ q.1 + q.2)
  obtain ⟨ld, ud, hld, hud, hd⟩ := finite_form_bounds hf hn (fun q ↦ q.1 - q.2)
  refine ⟨lx, ux, ly, uy, ls, us, ld, ud, fun p ↦ ?_⟩
  rw [P.mem_region_iff_normal_bounds]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using h (1, 0) (by simp [IsAllowedSlope]) lx ux (by simpa using hx)
    · simpa using h (0, 1) (by simp [IsAllowedSlope]) ly uy (by simpa using hy)
    · simpa using h (1, 1) (by simp [IsAllowedSlope]) ls us (by simpa using hs)
    · simpa [sub_eq_add_neg] using
        h (1, -1) (by simp [IsAllowedSlope]) ld ud (by simpa [sub_eq_add_neg] using hd)
  · rintro ⟨hpx, hpy, hps, hpd⟩ u hu l r hv
    have transfer (f : (ℝ × ℝ) → ℝ) (lo hi : ℝ)
        (hlo : ∃ a ∈ P.vertices, f a = lo) (hhi : ∃ b ∈ P.vertices, f b = hi)
        (hfp : lo ≤ f p ∧ f p ≤ hi) (c : ℝ)
        (hfc : ∀ q ∈ P.vertices, l ≤ c * f q ∧ c * f q ≤ r) :
        l ≤ c * f p ∧ c * f p ≤ r := by
      obtain ⟨a, ha, hfa⟩ := hlo
      obtain ⟨b, hb, hfb⟩ := hhi
      have ha' := hfc a ha
      have hb' := hfc b hb
      rw [hfa] at ha'
      rw [hfb] at hb'
      exact scaled_between hfp ha' hb'
    rcases hu with hu | hu | hu | hu
    · have ht := transfer (fun q ↦ q.2) ly uy hly huy hpy u.2 (by simpa [hu] using hv)
      simpa [hu] using ht
    · have ht := transfer (fun q ↦ q.1) lx ux hlx hux hpx u.1 (by simpa [hu] using hv)
      simpa [hu] using ht
    · have ht := transfer (fun q ↦ q.1 + q.2) ls us hls hus hps u.1
        (by simpa [← hu, mul_add] using hv)
      simpa [← hu, mul_add] using ht
    · have hu' : u.2 = -u.1 := by linarith
      have ht := transfer (fun q ↦ q.1 - q.2) ld ud hld hud hpd u.1
        (by simpa [hu', mul_sub, sub_eq_add_neg] using hv)
      simpa [hu', mul_sub, sub_eq_add_neg] using ht

end TNLean.PEPS.AreaLaw.Geometry
