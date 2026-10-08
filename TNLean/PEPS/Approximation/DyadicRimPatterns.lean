/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicUnmodifiedVertices

/-!
# Rim patterns of the point treatment

Before a large-scale elementary operation, every involved guide is homogenized on the treated
squares of radius `t` about the marked grid corners. A true vertex of such a temporary guide is an
old true vertex off the closed treated squares, or a point of a treated rim at which two labels
other than the homogenizing one meet. The source observes that such a rim point lies on a ray of
the unmodified guide, that the possible rim points form a finite pattern after scaling by `t`,
and chooses `ε₀` small compared with their separations, so that the outer holes are disjoint in
the temporary guides too. This file proves:

* off the grid lines and off the curves `x = k`, `k ∈ {-6, …, 1}`, of the bands of the four edges
  of the repainted square, every unmodified guide of a repainting is constant near each point;
* the rim pattern about a grid corner `v` at radius `t`: on each side of the rim of the sup square
  of radius `t` about `v`, the thirteen points at offset `j t / 1000`, `|j| ≤ 6`, from the midpoint
  of the side. It is finite, its points lie on the rim, and distinct points are at sup distance at
  least `t / 1000`. It contains the rim points of the grid lines through `v` and of the rays of
  both edges of the square meeting at `v`;
* for `2 t < n`, every point of the rim about a grid corner at which an unmodified guide of the
  repainting of a block has two distinct incident labels lies in that rim pattern;
* for `20 t < n`, the true vertices of the guide homogenized on the treated squares about finitely
  many grid corners are pairwise at sup distance at least `t / 1000`, so the closed outer hole
  squares of radius `2 ε₀ t` about them are disjoint once `ε₀ < 1/4000`.

Distances are ambient sup distances: `ℝ × ℝ` carries the maximum metric.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), §7, `06-geometry.tex`: the edge construction
  (lines 142–241), the separation of unmodified true vertices (lines 321–326), the point treatment
  (lines 330–338), and the choice of `K₀` and `ε₀` (lines 341–351).
-/

namespace TNLean.PEPS.Approximation

open Set Metric Filter Topology SquareEdge

/-! ### Locally constant guides -/

/-- A normal word is constant near every point other than its interfaces. -/
theorem bandWord_eventually_eq {ι : Type*} (c : ι) (l : List (ℝ × ι)) {x₀ : ℝ}
    (h : ∀ q ∈ l, x₀ ≠ q.1) : ∀ᶠ x in 𝓝 x₀, bandWord c l x = bandWord c l x₀ := by
  induction l generalizing c with
  | nil => exact Eventually.of_forall fun _ => rfl
  | cons q rest ih =>
    obtain ⟨t, l'⟩ := q
    simp only [List.mem_cons, forall_eq_or_imp] at h
    rcases lt_or_gt_of_ne h.1 with hlt | hgt
    · filter_upwards [Iio_mem_nhds hlt] with x (hx : x < t)
      simp [bandWord, hx, hlt]
    · filter_upwards [Ioi_mem_nhds hgt, ih l' h.2] with x (hx : t < x) hx'
      simp only [bandWord, not_lt.2 hx.le, not_lt.2 hgt.le, ite_false]
      exact hx'

/-- The interface curves `x = k`, `k ∈ {-6, …, 1}`, of the bands of the four edges of `[0, n] ^ 2`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:155–220`. -/
def edgeCurves (n : ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ e : SquareEdge, ∃ k : ℤ, -6 ≤ k ∧ k ≤ 1 ∧ 0 < e.par p ∧ e.par p < n ∧
    e.nor n p = k * bandWidth n (e.par p)}

section Words

variable {ι : Type*} {A B C : ι}

private theorem ne_of_forall_int {x₀ : ℝ} (hx : ∀ k : ℤ, -6 ≤ k → k ≤ 1 → x₀ ≠ k) :
    x₀ ≠ -6 ∧ x₀ ≠ -5 ∧ x₀ ≠ -4 ∧ x₀ ≠ -3 ∧ x₀ ≠ -2 ∧ x₀ ≠ -1 ∧ x₀ ≠ 0 ∧ x₀ ≠ 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hx (-6) le_rfl (by norm_num)
  · simpa using hx (-5) (by norm_num) (by norm_num)
  · simpa using hx (-4) (by norm_num) (by norm_num)
  · simpa using hx (-3) (by norm_num) (by norm_num)
  · simpa using hx (-2) (by norm_num) (by norm_num)
  · simpa using hx (-1) (by norm_num) (by norm_num)
  · simpa using hx 0 (by norm_num) (by norm_num)
  · simpa using hx 1 (by norm_num) le_rfl

/-- A main word is constant near every point other than the integers from `-6` to `1`. -/
theorem mainWords_eventually_eq {W : ℝ → ι} (hW : W ∈ mainWords A B C) {x₀ : ℝ}
    (hx : ∀ k : ℤ, -6 ≤ k → k ≤ 1 → x₀ ≠ k) : ∀ᶠ x in 𝓝 x₀, W x = W x₀ := by
  obtain ⟨m6, m5, m4, m3, -, -, m0, m1⟩ := ne_of_forall_int hx
  simp only [mainWords, mem_insert_iff, mem_singleton_iff] at hW
  rcases hW with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact bandWord_eventually_eq _ _ (by simp_all)

/-- An auxiliary word is constant near every point other than the integers from `-6` to `-1`. -/
theorem auxWords_eventually_eq {W : ℝ → ι} (hW : W ∈ auxWords A B C) {x₀ : ℝ}
    (hx : ∀ k : ℤ, -6 ≤ k → k ≤ 1 → x₀ ≠ k) : ∀ᶠ x in 𝓝 x₀, W x = W x₀ := by
  obtain ⟨m6, m5, m4, m3, m2, m1, -, -⟩ := ne_of_forall_int hx
  simp only [auxWords, mem_insert_iff, mem_singleton_iff] at hW
  rcases hW with rfl | rfl | rfl | rfl | rfl <;> exact bandWord_eventually_eq _ _ (by simp_all)

end Words

/-- **A band update off the curves.** If `W` is constant near every point other than the integers
from `-6` to `1` and has the matching end values, and the guide `g` is constant near `p` and equals
the matching labels near the curves `x = -8` and `x = 2`, then replacing the band `-8 < x < 2` of
`g` by `W` gives a guide constant near every point off the endpoints of the edge and off the curves
`x = k`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:227–241, 321–326`. -/
theorem eventually_bandUpdate_eq {ι : Type*} {n : ℝ} (hn : 0 < n) {e : SquareEdge}
    {W : ℝ → ι} {g : ℝ × ℝ → ι} {p : ℝ × ℝ}
    (hW : ∀ x₀ : ℝ, (∀ k : ℤ, -6 ≤ k → k ≤ 1 → x₀ ≠ k) → ∀ᶠ x in 𝓝 x₀, W x = W x₀)
    {c₁ c₂ : ι} (hlo : ∀ x ∈ Ioo (-8 : ℝ) (-7), W x = c₁) (hhi : ∀ x ∈ Ioo (1 : ℝ) 2, W x = c₂)
    (h0 : p ≠ e.point n 0 0) (h1 : p ≠ e.point n n 0) (hc : p ∉ edgeCurves n)
    (hg : ∀ᶠ q in 𝓝 p, g q = g p)
    (hlow : 0 < e.par p → e.par p < n → e.nor n p = -8 * bandWidth n (e.par p) →
      g =ᶠ[𝓝 p] fun _ => c₁)
    (hup : 0 < e.par p → e.par p < n → e.nor n p = 2 * bandWidth n (e.par p) →
      g =ᶠ[𝓝 p] fun _ => c₂) :
    ∀ᶠ q in 𝓝 p, bandUpdate n e W g q = bandUpdate n e W g p := by
  by_cases hb : p ∈ edgeBand n e (-8) 2
  · obtain ⟨s1, s2, -, -⟩ := id hb
    have hw := bandWidth_pos s1 s2
    have hx : ∀ k : ℤ, -6 ≤ k → k ≤ 1 → bandCoord n e p ≠ k := by
      intro k hk1 hk2 hk
      refine hc ⟨e, k, hk1, hk2, s1, s2, ?_⟩
      rw [← hk, bandCoord, div_mul_cancel₀ _ hw.ne']
    filter_upwards [(isOpen_edgeBand n e _ _).mem_nhds hb,
      (continuousAt_bandCoord s1 s2).eventually (hW _ hx)] with q hq hq'
    rw [bandUpdate_of_mem hq, bandUpdate_of_mem hb]
    exact hq'
  by_cases hcb : p ∈ closedEdgeBand n e (-8) 2
  · have hs0 : 0 < e.par p :=
      lt_of_le_of_ne hcb.1 fun h => h0 (eq_point_zero_of_mem_closedEdgeBand hn.le hcb h.symm)
    have hsn : e.par p < n :=
      lt_of_le_of_ne hcb.2.1 fun h => h1 (eq_point_end_of_mem_closedEdgeBand hn.le hcb h)
    have hw := bandWidth_pos hs0 hsn
    have hct := continuousAt_bandCoord hs0 hsn
    have hd : e.nor n p = -8 * bandWidth n (e.par p) ∨ e.nor n p = 2 * bandWidth n (e.par p) := by
      by_contra h
      push Not at h
      exact hb ⟨hs0, hsn, lt_of_le_of_ne hcb.2.2.1 (Ne.symm h.1), lt_of_le_of_ne hcb.2.2.2 h.2⟩
    rw [bandUpdate_of_notMem hb]
    rcases hd with hd | hd
    · have hx : bandCoord n e p < -7 := by
        rw [bandCoord, hd, mul_div_assoc, div_self hw.ne']
        norm_num
      have hgc := hlow hs0 hsn hd
      rw [hgc.self_of_nhds]
      filter_upwards [hgc, hct.eventually (Iio_mem_nhds hx)] with q hq (hq' : _ < _)
      by_cases hqb : q ∈ edgeBand n e (-8) 2
      · rw [bandUpdate_of_mem hqb]
        exact hlo _ ⟨(mem_edgeBand_iff_bandCoord.1 hqb).2.2.1, hq'⟩
      · rw [bandUpdate_of_notMem hqb]
        exact hq
    · have hx : 1 < bandCoord n e p := by
        rw [bandCoord, hd, mul_div_assoc, div_self hw.ne']
        norm_num
      have hgc := hup hs0 hsn hd
      rw [hgc.self_of_nhds]
      filter_upwards [hgc, hct.eventually (Ioi_mem_nhds hx)] with q hq (hq' : _ < _)
      by_cases hqb : q ∈ edgeBand n e (-8) 2
      · rw [bandUpdate_of_mem hqb]
        exact hhi _ ⟨hq', (mem_edgeBand_iff_bandCoord.1 hqb).2.2.2⟩
      · rw [bandUpdate_of_notMem hqb]
        exact hq
  · rw [bandUpdate_of_notMem hb]
    filter_upwards [(isClosed_closedEdgeBand n e _ _).isOpen_compl.mem_nhds hcb, hg] with q hq hq'
    rw [bandUpdate_of_notMem fun h => hq (edgeBand_subset_closedEdgeBand _ _ _ _ h), hq']

namespace RepaintingBaseline

variable {ι : Type*} (R : RepaintingBaseline ι)

/-- Off the corners and off the curves `x = 1` of the four bands, the guide after the central
birth is constant near every point where the starting guide is.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:155–160, 321–326`. -/
theorem eventually_centralGuide_eq {p : ℝ × ℝ} (hp : ¬ IsSquareCorner R.n p)
    (hc : p ∉ edgeCurves R.n) (hg : ∀ᶠ q in 𝓝 p, R.guide q = R.guide p) :
    ∀ᶠ q in 𝓝 p, R.centralGuide q = R.centralGuide p := by
  by_cases hcl : p ∈ closure (centralRegion R.n)
  · by_cases hmem : p ∈ centralRegion R.n
    · filter_upwards [(isOpen_centralRegion _).mem_nhds hmem] with q hq
      rw [R.centralGuide_of_mem hq, R.centralGuide_of_mem hmem]
    · exfalso
      have hS := mem_openSquare_of_mem_closure_centralRegion hcl hp
      have hle : ∀ e : SquareEdge, bandWidth R.n (e.par p) ≤ e.nor R.n p := fun e =>
        closure_minimal (fun q hq => (hq.2.2.2.2 e).le)
          (isClosed_le ((continuous_bandWidth _).comp e.continuous_par) (e.continuous_nor _)) hcl
      obtain ⟨h1, h2, h3, h4⟩ := mem_openSquare.1 hS
      have : ¬ ∀ e : SquareEdge, bandWidth R.n (e.par p) < e.nor R.n p :=
        fun h => hmem ⟨h1, h2, h3, h4, h⟩
      push Not at this
      obtain ⟨e, he⟩ := this
      obtain ⟨s1, s2, -⟩ := par_nor_of_mem_openSquare hS e
      exact hc ⟨e, 1, by norm_num, le_rfl, s1, s2, by push_cast; linarith [hle e]⟩
  · filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hcl, hg] with q hq hq'
    rw [R.centralGuide_of_notMem fun h => hq (subset_closure h),
      R.centralGuide_of_notMem fun h => hcl (subset_closure h), hq']

/-- Off the corners and the curves, every completed guide is constant near every point where the
starting guide is. -/
theorem eventually_completedGuide_eq (E : List SquareEdge) {p : ℝ × ℝ}
    (hp : ¬ IsSquareCorner R.n p) (hc : p ∉ edgeCurves R.n)
    (hg : ∀ᶠ q in 𝓝 p, R.guide q = R.guide p) :
    ∀ᶠ q in 𝓝 p, R.completedGuide E q = R.completedGuide E p := by
  induction E with
  | nil => exact R.eventually_centralGuide_eq hp hc hg
  | cons e E ih =>
    have hW := mainWords_props (A := R.oldLabel) (B := R.finalLabel) (C := R.nbrLabel e)
      (W := mainWordFive R.finalLabel (R.nbrLabel e)) (by simp [mainWords])
    exact eventually_bandUpdate_eq R.n_pos
      (fun _ hx => mainWords_eventually_eq (A := R.oldLabel) (B := R.finalLabel)
        (C := R.nbrLabel e) (by simp [mainWords]) hx)
      hW.2.1 hW.2.2 (fun h => hp (h ▸ isSquareCorner_point_zero _ e))
      (fun h => hp (h ▸ isSquareCorner_point_end _ e)) hc ih
      (fun h1 h2 hd => R.eventually_completedGuide_nbrLabel E h1 h2 hd)
      (fun h1 h2 hd => R.eventually_completedGuide_finalLabel E h1 h2 hd)

/-- **Unmodified guides off the curves.** Off the four corners and the interface curves, every
unmodified guide is constant near every point where the starting guide is.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:155–241, 321–326`. -/
theorem IsUnmodifiedGuide.eventually_eq {g : ℝ × ℝ → ι} (h : R.IsUnmodifiedGuide g)
    {p : ℝ × ℝ} (hp : ¬ IsSquareCorner R.n p) (hc : p ∉ edgeCurves R.n)
    (hg : ∀ᶠ q in 𝓝 p, R.guide q = R.guide p) : ∀ᶠ q in 𝓝 p, g q = g p := by
  have c0 (e : SquareEdge) : p ≠ e.point R.n 0 0 := fun h => hp (h ▸ isSquareCorner_point_zero _ e)
  have cn (e : SquareEdge) : p ≠ e.point R.n R.n 0 := fun h =>
    hp (h ▸ isSquareCorner_point_end _ e)
  rcases h with rfl | rfl | ⟨E, rfl⟩ | ⟨E, e, W, hW, rfl⟩ | ⟨e, W, hW, rfl⟩
  · exact hg
  · exact R.eventually_centralGuide_eq hp hc hg
  · exact R.eventually_completedGuide_eq E hp hc hg
  · have hW' := mainWords_props hW
    exact eventually_bandUpdate_eq R.n_pos (fun _ hx => mainWords_eventually_eq hW hx) hW'.2.1
      hW'.2.2 (c0 e) (cn e) hc (R.eventually_completedGuide_eq E hp hc hg)
      (fun h1 h2 hd => R.eventually_completedGuide_nbrLabel E h1 h2 hd)
      (fun h1 h2 hd => R.eventually_completedGuide_finalLabel E h1 h2 hd)
  · have hW' := auxWords_props hW
    exact eventually_bandUpdate_eq R.n_pos (fun _ hx => auxWords_eventually_eq hW hx) hW'.2.1
      hW'.2.2 (c0 e) (cn e) hc (Eventually.of_forall fun _ => rfl)
      (fun _ _ _ => Eventually.of_forall fun _ => rfl)
      (fun _ _ _ => Eventually.of_forall fun _ => rfl)

end RepaintingBaseline

/-! ### The rim pattern about a grid corner -/

/-- The rim pattern about `v` at radius `t`: on each side of the rim of the sup square of radius
`t` about `v`, the thirteen points at offset `j t / 1000`, `|j| ≤ 6`, from the midpoint of the
side. In units of `t` it is one fixed finite set.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:344–349`. -/
def rimPattern (v : ℝ × ℝ) (t : ℝ) : Set (ℝ × ℝ) :=
  {c | ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∃ j : ℤ, |j| ≤ 6 ∧
    (c = v + (σ * t, j * t / 1000) ∨ c = v + (j * t / 1000, σ * t))}

/-- The rim pattern is finite.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:346–347`. -/
theorem rimPattern_finite (v : ℝ × ℝ) (t : ℝ) : (rimPattern v t).Finite := by
  let f : ℝ × ℤ × Bool → ℝ × ℝ := fun x =>
    if x.2.2 then v + (x.1 * t, x.2.1 * t / 1000) else v + (x.2.1 * t / 1000, x.1 * t)
  refine (((Set.toFinite ({1, -1} : Set ℝ)).prod
    ((Set.finite_Icc (-6 : ℤ) 6).prod Set.finite_univ)).image f).subset ?_
  rintro c ⟨σ, hσ, j, hj, hc | hc⟩
  · exact ⟨(σ, j, true), ⟨hσ, abs_le.1 hj, trivial⟩, by simp [f, hc]⟩
  · exact ⟨(σ, j, false), ⟨hσ, abs_le.1 hj, trivial⟩, by simp [f, hc]⟩

private theorem abs_int_cast_le_six {j : ℤ} (hj : |j| ≤ 6) : |(j : ℝ)| ≤ 6 := by
  have : ((|j| : ℤ) : ℝ) ≤ 6 := by exact_mod_cast hj
  rwa [Int.cast_abs] at this

/-- The points of the rim pattern lie on the rim: at sup distance `t` from its center.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:344–347`. -/
theorem dist_of_mem_rimPattern {v c : ℝ × ℝ} {t : ℝ} (ht : 0 ≤ t) (hc : c ∈ rimPattern v t) :
    dist c v = t := by
  obtain ⟨σ, hσ, j, hj, rfl | rfl⟩ := hc <;>
  · have hj' := abs_int_cast_le_six hj
    have hjt : |(j : ℝ) * t / 1000| ≤ t := by
      rw [abs_div, abs_mul, abs_of_nonneg ht, abs_of_pos (by norm_num : (0 : ℝ) < 1000)]
      nlinarith [abs_nonneg (j : ℝ)]
    have hσt : |σ * t| = t := by rcases hσ with rfl | rfl <;> simp [abs_of_nonneg ht]
    rw [dist_comm, dist_self_add_right, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, hσt]
    first | exact max_eq_left hjt | exact max_eq_right hjt

private theorem sep_same {σ σ' t : ℝ} (ht : 0 < t) (hσ : σ = 1 ∨ σ = -1) (hσ' : σ' = 1 ∨ σ' = -1)
    {j j' : ℤ} (hne : σ ≠ σ' ∨ j ≠ j') :
    t / 1000 ≤ max |σ * t - σ' * t| |j * t / 1000 - j' * t / 1000| := by
  rcases hne with hne | hne
  · refine le_max_of_le_left ?_
    rcases hσ with rfl | rfl <;> rcases hσ' with rfl | rfl
    · exact absurd rfl hne
    · rw [show (1 : ℝ) * t - -1 * t = 2 * t by ring, abs_of_pos (by linarith)]; linarith
    · rw [show (-1 : ℝ) * t - 1 * t = -(2 * t) by ring, abs_neg, abs_of_pos (by linarith)]
      linarith
    · exact absurd rfl hne
  · refine le_max_of_le_right ?_
    have h1 : (1 : ℝ) ≤ |(j : ℝ) - j'| := by
      have := Int.one_le_abs (sub_ne_zero.2 hne)
      have : ((1 : ℤ) : ℝ) ≤ ((|j - j'| : ℤ) : ℝ) := by exact_mod_cast this
      simpa [Int.cast_abs] using this
    rw [show (j : ℝ) * t / 1000 - j' * t / 1000 = (j - j') * (t / 1000) by ring, abs_mul,
      abs_of_pos (by positivity : 0 < t / 1000)]
    nlinarith

private theorem sep_cross {σ t : ℝ} (ht : 0 < t) (hσ : σ = 1 ∨ σ = -1) {j : ℤ} (hj : |j| ≤ 6) :
    t / 1000 ≤ |σ * t - j * t / 1000| := by
  have hj' := abs_le.1 (abs_int_cast_le_six hj)
  rcases hσ with rfl | rfl
  · rw [abs_of_pos (by nlinarith)]; nlinarith
  · rw [abs_of_neg (by nlinarith)]; nlinarith

/-- **Separation of the rim pattern.** Distinct points of the rim pattern at radius `t > 0` are
at sup distance at least `t / 1000`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:346–351`. -/
theorem le_dist_of_mem_rimPattern {v c c' : ℝ × ℝ} {t : ℝ} (ht : 0 < t) (hc : c ∈ rimPattern v t)
    (hc' : c' ∈ rimPattern v t) (hne : c ≠ c') : t / 1000 ≤ dist c c' := by
  obtain ⟨σ, hσ, j, hj, rfl | rfl⟩ := hc <;> obtain ⟨σ', hσ', j', hj', rfl | rfl⟩ := hc' <;>
    rw [dist_add_left, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  · refine sep_same ht hσ hσ' ?_
    by_contra h
    push Not at h
    exact hne (by rw [h.1, h.2])
  · exact le_max_of_le_left (sep_cross ht hσ hj')
  · refine le_max_of_le_left ?_
    rw [abs_sub_comm]
    exact sep_cross ht hσ' hj
  · rw [max_comm]
    refine sep_same ht hσ hσ' ?_
    by_contra h
    push Not at h
    exact hne (by rw [h.1, h.2])

/-! ### Rim points of the unmodified guides -/

/-- An integer multiple of `n > 0` of absolute value less than `n` is zero. -/
private theorem int_eq_zero_of_abs_lt {n : ℝ} (hn : 0 < n) {m : ℤ} (h : |n * m| < n) : m = 0 := by
  rw [abs_mul, abs_of_pos hn] at h
  have : |(m : ℝ)| < 1 := by nlinarith [abs_nonneg (m : ℝ)]
  rwa [← Int.cast_abs, ← Int.cast_one, Int.cast_lt, Int.abs_lt_one_iff] at this

/-- **Grid lines meet the rim in the pattern.** For `2 t < n`, a point of a grid line at sup
distance `t` from a grid corner lies in the rim pattern of that corner: the grid line is one of
the two through the corner, and the point is the midpoint of a side of the rim.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:321–322, 344–347`. -/
theorem mem_rimPattern_of_grid {n t : ℝ} (hn : 0 < n) (htn : 2 * t < n)
    {Q : ℤ × ℤ} {c : ℝ × ℝ} (hc : dist c (blockCorner n Q) = t)
    (hgrid : (∃ a : ℤ, c.1 = n * a) ∨ ∃ b : ℤ, c.2 = n * b) :
    c ∈ rimPattern (blockCorner n Q) t := by
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq] at hc
  simp only [blockCorner] at hc ⊢
  rcases hgrid with ⟨a, ha⟩ | ⟨b, hb⟩
  · have h1 : |c.1 - n * Q.1| ≤ t := hc ▸ le_max_left _ _
    have ha' : a = Q.1 := by
      have := int_eq_zero_of_abs_lt hn (m := a - Q.1) (by push_cast; rw [mul_sub, ← ha]; linarith)
      omega
    have hc1 : c.1 - n * Q.1 = 0 := by rw [ha, ha']; ring
    rw [hc1, abs_zero, max_eq_right (abs_nonneg _)] at hc
    refine ⟨if 0 ≤ c.2 - n * Q.2 then 1 else -1, by split_ifs <;> simp, 0, by simp, Or.inr ?_⟩
    ext
    · simp; linarith
    · split_ifs with h
      · rw [abs_of_nonneg h] at hc; simp; linarith
      · rw [abs_of_neg (not_le.1 h)] at hc; simp; linarith
  · have h2 : |c.2 - n * Q.2| ≤ t := hc ▸ le_max_right _ _
    have hb' : b = Q.2 := by
      have := int_eq_zero_of_abs_lt hn (m := b - Q.2) (by push_cast; rw [mul_sub, ← hb]; linarith)
      omega
    have hc2 : c.2 - n * Q.2 = 0 := by rw [hb, hb']; ring
    rw [hc2, abs_zero, max_eq_left (abs_nonneg _)] at hc
    refine ⟨if 0 ≤ c.1 - n * Q.1 then 1 else -1, by split_ifs <;> simp, 0, by simp, Or.inl ?_⟩
    ext
    · split_ifs with h
      · rw [abs_of_nonneg h] at hc; simp; linarith
      · rw [abs_of_neg (not_le.1 h)] at hc; simp; linarith
    · simp; linarith

/-- **Rays of both edges at a corner meet the rim in the pattern.** For `2 t < n`, a point at sup
distance `t` from a grid corner on an interface curve `x = k`, `k ∈ {-6, …, 1}`, of an edge of the
repainted block lies in the rim pattern of that corner: the corner is an endpoint of the edge, the
point has parallel distance `t` from it and normal coordinate `k t / 1000`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:301–302, 344–347`. -/
theorem mem_rimPattern_of_curve {n t : ℝ} (hn : 0 < n) (htn : 2 * t < n)
    {S Q : ℤ × ℤ} {c : ℝ × ℝ} (hc : dist c (blockCorner n Q) = t)
    (hcurve : c - blockCorner n S ∈ edgeCurves n) : c ∈ rimPattern (blockCorner n Q) t := by
  obtain ⟨e, k, hk1, hk2, s1, s2, hd⟩ := hcurve
  set o := blockCorner n S
  set v := blockCorner n Q
  have hdist : dist (c - o) (v - o) = t := by rw [dist_sub_right]; exact hc
  obtain ⟨ms, md, hms, hmd⟩ : ∃ ms md : ℤ, e.par (v - o) = n * ms ∧ e.nor n (v - o) = n * md := by
    cases e <;> simp only [par, nor, v, o, blockCorner, Prod.fst_sub, Prod.snd_sub]
    · exact ⟨Q.1 - S.1, Q.2 - S.2, by push_cast; ring, by push_cast; ring⟩
    · exact ⟨Q.2 - S.2, 1 - (Q.1 - S.1), by push_cast; ring, by push_cast; ring⟩
    · exact ⟨Q.1 - S.1, 1 - (Q.2 - S.2), by push_cast; ring, by push_cast; ring⟩
    · exact ⟨Q.2 - S.2, Q.1 - S.1, by push_cast; ring, by push_cast; ring⟩
  set s := e.par (c - o)
  set d := e.nor n (c - o)
  rw [dist_eq n e, hms, hmd] at hdist
  have hs1 : |s - n * ms| ≤ t := hdist ▸ le_max_left _ _
  have hs2 : |d - n * md| ≤ t := hdist ▸ le_max_right _ _
  have hw0 := bandWidth_pos s1 s2
  have hwl := bandWidth_le_left n s
  have hwr := bandWidth_le_right n s
  have hk : |(k : ℝ)| ≤ 6 := by
    have h1 : (-6 : ℝ) ≤ k := by exact_mod_cast hk1
    have h2 : (k : ℝ) ≤ 1 := by exact_mod_cast hk2
    rw [abs_le]; constructor <;> linarith
  have hdw : |d| ≤ 6 * bandWidth n s := by
    rw [hd, abs_mul, abs_of_pos hw0]
    exact mul_le_mul_of_nonneg_right hk hw0.le
  have hmd0 : md = 0 := by
    refine int_eq_zero_of_abs_lt hn ?_
    have := abs_sub_abs_le_abs_sub (n * md : ℝ) d
    rw [abs_sub_comm] at this
    linarith
  subst hmd0
  simp only [Int.cast_zero, mul_zero, sub_zero] at hs2 hdist
  rw [abs_le] at hs1
  obtain ⟨hs1a, hs1b⟩ := hs1
  have hms0 : -1 < ms := by
    have : (-1 : ℝ) < ms := by nlinarith
    exact_mod_cast this
  have hms1 : ms < 2 := by
    have : (ms : ℝ) < 2 := by nlinarith
    exact_mod_cast this
  have hkj : |-k| ≤ 6 := by rw [abs_neg]; exact abs_le.2 ⟨by omega, by omega⟩
  have hkk : |k| ≤ 6 := abs_le.2 ⟨by omega, by omega⟩
  have hp : c - o = e.point n s d := (point_par_nor n e (c - o)).symm
  have hu := point_par_nor n e (v - o)
  rw [hms, hmd] at hu
  rcases (show ms = 0 ∨ ms = 1 by omega) with rfl | rfl
  · -- the first endpoint of `e`
    simp only [Int.cast_zero, mul_zero, sub_zero] at hu hs1b hdist
    have hhalf : s ≤ n / 2 := by linarith
    have hw : bandWidth n s = s / 1000 := bandWidth_of_le_half hhalf
    have hds : |d| < s := by rw [hw] at hdw; linarith
    rw [abs_of_pos s1, max_eq_left hds.le] at hdist
    have hd' : d = k * (t / 1000) := by rw [hd, hw, hdist]
    have hc' : c = v + (e.point n t (k * (t / 1000)) - e.point n 0 0) := by
      rw [← hd', ← hdist, ← hp, hu]; abel
    rw [hc']
    cases e
    · exact ⟨1, Or.inl rfl, k, hkk, Or.inl (Prod.ext (by simp [point]) (by simp [point]; ring))⟩
    · exact ⟨1, Or.inl rfl, -k, hkj, Or.inr (Prod.ext (by simp [point]; ring) (by simp [point]))⟩
    · exact ⟨1, Or.inl rfl, -k, hkj, Or.inl (Prod.ext (by simp [point]) (by simp [point]; ring))⟩
    · exact ⟨1, Or.inl rfl, k, hkk, Or.inr (Prod.ext (by simp [point]; ring) (by simp [point]))⟩
  · -- the second endpoint of `e`
    simp only [Int.cast_one, mul_one, Int.cast_zero, mul_zero] at hu hs1a hdist
    have hhalf : n / 2 ≤ s := by linarith
    have hw : bandWidth n s = (n - s) / 1000 := bandWidth_of_half_le hhalf
    have hds : |d| < n - s := by rw [hw] at hdw; linarith
    rw [abs_sub_comm, abs_of_pos (by linarith : 0 < n - s), max_eq_left hds.le] at hdist
    have hd' : d = k * (t / 1000) := by rw [hd, hw, hdist]
    have hs' : s = n - t := by linarith
    have hc' : c = v + (e.point n (n - t) (k * (t / 1000)) - e.point n n 0) := by
      rw [← hd', ← hs', ← hp, hu]; abel
    rw [hc']
    cases e
    · exact ⟨-1, Or.inr rfl, k, hkk, Or.inl (Prod.ext (by simp [point]) (by simp [point]; ring))⟩
    · exact ⟨-1, Or.inr rfl, -k, hkj,
        Or.inr (Prod.ext (by simp [point]; ring) (by simp [point]))⟩
    · exact ⟨-1, Or.inr rfl, -k, hkj,
        Or.inl (Prod.ext (by simp [point]) (by simp [point]; ring))⟩
    · exact ⟨-1, Or.inr rfl, k, hkk, Or.inr (Prod.ext (by simp [point]; ring) (by simp [point]))⟩

/-- **Rim points of the unmodified guides lie in the rim pattern.** Let `2 t < n`. In the
repainting of a block, every point at sup distance `t` from a grid corner at which an unmodified
guide, placed on the block, has two distinct incident labels lies in the rim pattern of that
corner. So the points of a treated rim where a true vertex of a temporary guide can occur form a
finite pattern after scaling by `t`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:321–326, 344–347`. -/
theorem mem_rimPattern_of_incidentLabels {ι : Type*} {n t : ℝ} (hn : 0 < n) (htn : 2 * t < n)
    {lab : ℤ × ℤ → ι} {S : ℤ × ℤ} {B : ι} {g : ℝ × ℝ → ι}
    (hg : (blockBaseline hn lab S B).IsUnmodifiedGuide g) (Q : ℤ × ℤ) {c : ℝ × ℝ}
    (hc : dist c (blockCorner n Q) = t) {l₁ l₂ : ι} (h12 : l₁ ≠ l₂)
    (h1 : l₁ ∈ incidentLabels (shiftGuide (blockCorner n S) g) c)
    (h2 : l₂ ∈ incidentLabels (shiftGuide (blockCorner n S) g) c) :
    c ∈ rimPattern (blockCorner n Q) t := by
  set o := blockCorner n S
  by_cases hgrid : (∃ a : ℤ, c.1 = n * a) ∨ ∃ b : ℤ, c.2 = n * b
  · exact mem_rimPattern_of_grid hn htn hc hgrid
  by_cases hcur : c - o ∈ edgeCurves n
  · exact mem_rimPattern_of_curve hn htn hc hcur
  exfalso
  push Not at hgrid
  obtain ⟨hg1, hg2⟩ := hgrid
  have hblock : ∀ᶠ q in 𝓝 c, blockGuide n lab q = blockGuide n lab c := by
    filter_upwards [continuous_fst.continuousAt.eventually (floor_div_eventually_eq hn hg1),
      continuous_snd.continuousAt.eventually (floor_div_eventually_eq hn hg2)] with q hq1 hq2
    simp only [blockGuide, blockIndex, hq1, hq2]
  have hb : ∀ᶠ q in 𝓝 (c - o), (blockBaseline hn lab S B).guide q =
      (blockBaseline hn lab S B).guide (c - o) := by
    have hT : Tendsto (fun q => q + o) (𝓝 (c - o)) (𝓝 c) := by
      have h : Continuous fun q : ℝ × ℝ => q + o := continuous_id.add continuous_const
      simpa using h.tendsto (c - o)
    filter_upwards [hT.eventually hblock] with q hq
    change blockGuide n lab (q + o) = blockGuide n lab (c - o + o)
    rw [hq, sub_add_cancel]
  have hcorner : ¬ IsSquareCorner n (c - o) := by
    intro h
    rcases h with h | h | h | h <;> rw [sub_eq_iff_eq_add] at h <;> simp only [o, blockCorner] at h
    · exact hg1 S.1 (by rw [h]; simp)
    · exact hg1 (S.1 + 1) (by rw [h]; push_cast; simp; ring)
    · exact hg1 S.1 (by rw [h]; simp)
    · exact hg1 (S.1 + 1) (by rw [h]; push_cast; simp; ring)
  have hconst := RepaintingBaseline.IsUnmodifiedGuide.eventually_eq _ hg hcorner hcur hb
  have hT : Tendsto (fun q => q - o) (𝓝 c) (𝓝 (c - o)) :=
    (continuous_id.sub continuous_const).tendsto c
  have hconst' : ∀ᶠ q in 𝓝 c, shiftGuide o g q ∈ ({shiftGuide o g c} : Set ι) :=
    hT.eventually hconst
  have hsub := incidentLabels_subset (f := shiftGuide o g) (s := {shiftGuide o g c}) hconst'
    fun _ hq => hq
  exact h12 ((hsub h1).trans (hsub h2).symm)

/-! ### Disjoint outer holes in the temporary guides -/

/-- **True vertices of a temporary guide.** Let `2 t < n`. A true vertex of an unmodified guide of
the repainting of a block, homogenized to any label on the open squares of radius `t` about
finitely many grid corners, is a grid corner or a point of the rim pattern of one of these
corners.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:330–338, 341–347`. -/
theorem isTrueVertex_homogenize_cases {ι : Type*} {n t : ℝ} (hn : 0 < n) (htn : 2 * t < n)
    {lab : ℤ × ℤ → ι} {S : ℤ × ℤ} {B : ι} {g : ℝ × ℝ → ι}
    (hg : (blockBaseline hn lab S B).IsUnmodifiedGuide g) (M : Finset (ℤ × ℤ)) (P : ι)
    {c : ℝ × ℝ} (h : IsTrueVertex (homogenize (⋃ Q ∈ M, ball (blockCorner n Q) t) P
      (shiftGuide (blockCorner n S) g)) c) :
    (∃ Q : ℤ × ℤ, c = blockCorner n Q) ∨ ∃ Q ∈ M, c ∈ rimPattern (blockCorner n Q) t := by
  have hU : IsOpen (⋃ Q ∈ M, ball (blockCorner n Q) t) := isOpen_biUnion fun _ _ => isOpen_ball
  rcases h.of_homogenize hU with ⟨-, hv⟩ | ⟨hfr, l₁, l₂, h12, -, -, h1, h2⟩
  · exact Or.inl (hv.eq_blockCorner_of_isUnmodifiedGuide hn hg)
  · right
    rw [hU.frontier_eq] at hfr
    obtain ⟨hcl, hnot⟩ := hfr
    rw [M.closure_biUnion] at hcl
    simp only [mem_iUnion] at hcl hnot
    obtain ⟨Q, hQ, hcQ⟩ := hcl
    have hle : dist c (blockCorner n Q) ≤ t := closure_ball_subset_closedBall hcQ
    have hge : t ≤ dist c (blockCorner n Q) := le_of_not_gt fun h => hnot ⟨Q, hQ, h⟩
    exact ⟨Q, hQ, mem_rimPattern_of_incidentLabels hn htn hg Q (le_antisymm hle hge) h12 h1 h2⟩

/-- **Separation of the true vertices of a temporary guide.** For `20 t < n`, distinct true
vertices of an unmodified guide of the repainting of a block, homogenized on the open squares of
radius `t` about finitely many grid corners, are at sup distance at least `t / 1000`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:341–351`. -/
theorem le_dist_of_isTrueVertex_homogenize {ι : Type*} {n t : ℝ} (hn : 0 < n) (ht : 0 < t)
    (htn : 20 * t < n) {lab : ℤ × ℤ → ι} {S : ℤ × ℤ} {B : ι} {g : ℝ × ℝ → ι}
    (hg : (blockBaseline hn lab S B).IsUnmodifiedGuide g) (M : Finset (ℤ × ℤ)) (P : ι)
    {c₁ c₂ : ℝ × ℝ}
    (h₁ : IsTrueVertex (homogenize (⋃ Q ∈ M, ball (blockCorner n Q) t) P
      (shiftGuide (blockCorner n S) g)) c₁)
    (h₂ : IsTrueVertex (homogenize (⋃ Q ∈ M, ball (blockCorner n Q) t) P
      (shiftGuide (blockCorner n S) g)) c₂) (hne : c₁ ≠ c₂) :
    t / 1000 ≤ dist c₁ c₂ := by
  have h2t : 2 * t < n := by linarith
  rcases isTrueVertex_homogenize_cases hn h2t hg M P h₁ with ⟨Q₁, rfl⟩ | ⟨Q₁, -, hc₁⟩ <;>
    rcases isTrueVertex_homogenize_cases hn h2t hg M P h₂ with ⟨Q₂, rfl⟩ | ⟨Q₂, -, hc₂⟩
  · have := le_dist_blockCorner_of_ne hn (fun h : Q₁ = Q₂ => hne (by rw [h]))
    linarith
  · have hd := dist_of_mem_rimPattern ht.le hc₂
    by_cases h : Q₁ = Q₂
    · subst h
      rw [dist_comm, hd]
      linarith
    · have := le_dist_blockCorner_of_ne hn h
      have := dist_triangle (blockCorner n Q₁) c₂ (blockCorner n Q₂)
      linarith
  · have hd := dist_of_mem_rimPattern ht.le hc₁
    by_cases h : Q₁ = Q₂
    · subst h
      rw [hd]
      linarith
    · have := le_dist_blockCorner_of_ne hn h
      have := dist_triangle (blockCorner n Q₁) c₁ (blockCorner n Q₂)
      rw [dist_comm] at hd
      linarith
  · by_cases h : Q₁ = Q₂
    · subst h
      exact le_dist_of_mem_rimPattern ht hc₁ hc₂ hne
    · have hd₁ := dist_of_mem_rimPattern ht.le hc₁
      have hd₂ := dist_of_mem_rimPattern ht.le hc₂
      have := le_dist_blockCorner_of_ne hn h
      have := dist_triangle4 (blockCorner n Q₁) c₁ c₂ (blockCorner n Q₂)
      rw [dist_comm] at hd₁
      linarith

/-- **Disjoint outer holes in the temporary guides.** For `20 t < n` and `ε₀ < 1/4000`, the
closed outer hole squares, of radius `2 ε₀ t`, about distinct true vertices of a temporary guide
of the point treatment are disjoint.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:347–351`. -/
theorem homogenize_outerHoles_disjoint {ι : Type*} {n t ε₀ : ℝ} (hn : 0 < n) (ht : 0 < t)
    (htn : 20 * t < n) (hε : ε₀ < 1 / 4000) {lab : ℤ × ℤ → ι} {S : ℤ × ℤ} {B : ι}
    {g : ℝ × ℝ → ι} (hg : (blockBaseline hn lab S B).IsUnmodifiedGuide g) (M : Finset (ℤ × ℤ))
    (P : ι) {c₁ c₂ : ℝ × ℝ}
    (h₁ : IsTrueVertex (homogenize (⋃ Q ∈ M, ball (blockCorner n Q) t) P
      (shiftGuide (blockCorner n S) g)) c₁)
    (h₂ : IsTrueVertex (homogenize (⋃ Q ∈ M, ball (blockCorner n Q) t) P
      (shiftGuide (blockCorner n S) g)) c₂) (hne : c₁ ≠ c₂) :
    Disjoint (closedBall c₁ (2 * ε₀ * t)) (closedBall c₂ (2 * ε₀ * t)) := by
  have := le_dist_of_isTrueVertex_homogenize hn ht htn hg M P h₁ h₂ hne
  exact closedBall_disjoint_closedBall (by nlinarith)

end TNLean.PEPS.Approximation
