/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicSmallPatchCovers

/-!
# True vertices of the unmodified guides of a repainting

The guides of a large-scale repainting before any point treatment are the starting block guide,
the guide after the central birth, the guides after completed edges, and the main and auxiliary
guides along an edge, which replace the band `-8 < x < 2` of the edge by a normal word. The
auxiliary words include the word left on the auxiliary sheet by the lens exchange, to which the
point treatment of the exchange is removed before that sheet is retired. The source
observes that all true vertices of these guides are separated on scale `n`: the baseline vertices
are grid corners, the band interfaces are disjoint except at their endpoints, and the bends at
`s = n/2` have only two incident labels. This file proves:

* a normal word takes at most two values near every point, the value there and the value just
  below;
* replacing the band of an edge by a word whose ends match the labels across the band boundary
  keeps at most two labels near every point other than the endpoints of the edge;
* the guide after the central birth has at most two labels near every point other than the four
  corners of the square at which the starting guide has at most two;
* hence every true vertex of every unmodified guide of the repainting of a block is a grid corner,
  and for `n > 20 t` the closed tenfold enlargement of the treated square about a grid corner
  contains no true vertex of these guides other than its center. This is the clause of the choice
  of `K₀` that the enlargements contain no other unmodified true vertex.

Distances are ambient sup distances: `ℝ × ℝ` carries the maximum metric.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), §7, `06-geometry.tex`: the edge construction
  (lines 142–241), the separation of unmodified true vertices (lines 321–326), and the choice of
  `K₀` (lines 341–343).
-/

namespace TNLean.PEPS.Approximation

open Set Metric Filter Topology SquareEdge

/-! ### Normal words near a point -/

/-- A normal word is constant just below every point and from the point on. -/
theorem bandWord_eventually_step {ι : Type*} (c : ι) (l : List (ℝ × ι)) (x₀ : ℝ) :
    ∃ P, ∀ᶠ x in 𝓝 x₀,
      (x < x₀ → bandWord c l x = P) ∧ (x₀ ≤ x → bandWord c l x = bandWord c l x₀) := by
  induction l generalizing c with
  | nil => exact ⟨c, Eventually.of_forall fun _ => ⟨fun _ => rfl, fun _ => rfl⟩⟩
  | cons q rest ih =>
    obtain ⟨t, l'⟩ := q
    obtain ⟨P', h'⟩ := ih l'
    rcases lt_trichotomy x₀ t with h | rfl | h
    · refine ⟨c, ?_⟩
      filter_upwards [Iio_mem_nhds h] with x (hx : x < t)
      simp [bandWord, hx, h]
    · refine ⟨c, ?_⟩
      filter_upwards [h'] with x hx
      refine ⟨fun hlt => by simp [bandWord, hlt], fun hle => ?_⟩
      simp only [bandWord, not_lt.2 hle, lt_irrefl, ite_false]
      exact hx.2 hle
    · refine ⟨P', ?_⟩
      filter_upwards [Ioi_mem_nhds h, h'] with x (hx : t < x) hx'
      simp only [bandWord, not_lt.2 hx.le, not_lt.2 h.le, ite_false]
      exact hx'

/-- **A normal word takes at most two values near every point.**

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:161–170, 321–326`. -/
theorem bandWord_eventually_mem {ι : Type*} (c : ι) (l : List (ℝ × ι)) (x₀ : ℝ) :
    ∃ P, ∀ᶠ x in 𝓝 x₀, bandWord c l x ∈ ({P, bandWord c l x₀} : Set ι) := by
  obtain ⟨P, h⟩ := bandWord_eventually_step c l x₀
  refine ⟨P, ?_⟩
  filter_upwards [h] with x hx
  rcases lt_or_ge x x₀ with hlt | hge
  · exact Or.inl (hx.1 hlt)
  · exact Or.inr (hx.2 hge)

/-! ### Band coordinates near a point -/

/-- The normal ratio is continuous off the endpoints of the parallel span. -/
theorem continuousAt_bandCoord {n : ℝ} {e : SquareEdge} {p : ℝ × ℝ} (h1 : 0 < e.par p)
    (h2 : e.par p < n) : ContinuousAt (bandCoord n e) p :=
  (e.continuous_nor n).continuousAt.div
    ((continuous_bandWidth n).comp e.continuous_par).continuousAt (bandWidth_pos h1 h2).ne'

/-- A point of a closed band with parallel coordinate `0` is the first endpoint of the edge. -/
theorem eq_point_zero_of_mem_closedEdgeBand {n : ℝ} (hn : 0 ≤ n) {e : SquareEdge} {α β : ℝ}
    {p : ℝ × ℝ} (hp : p ∈ closedEdgeBand n e α β) (hs : e.par p = 0) : p = e.point n 0 0 := by
  obtain ⟨-, -, h3, h4⟩ := hp
  have hw : bandWidth n (e.par p) = 0 := by simp [bandWidth, hs, hn]
  rw [hw, mul_zero] at h3 h4
  rw [← point_par_nor n e p, hs, le_antisymm h4 h3]

/-- A point of a closed band with parallel coordinate `n` is the second endpoint of the edge. -/
theorem eq_point_end_of_mem_closedEdgeBand {n : ℝ} (hn : 0 ≤ n) {e : SquareEdge} {α β : ℝ}
    {p : ℝ × ℝ} (hp : p ∈ closedEdgeBand n e α β) (hs : e.par p = n) : p = e.point n n 0 := by
  obtain ⟨-, -, h3, h4⟩ := hp
  have hw : bandWidth n (e.par p) = 0 := by simp [bandWidth, hs, hn]
  rw [hw, mul_zero] at h3 h4
  rw [← point_par_nor n e p, hs, le_antisymm h4 h3]

/-! ### Replacing a band by a word -/

/-- **Two labels near a point after a band update.** Let `W` take at most two values near every
point, the value `c₁` on `-8 < x < -7` and `c₂` on `1 < x < 2`, and let the guide `g` have at most
two labels near `p`, equal `c₁` near the curve `x = -8` and `c₂` near the curve `x = 2`. Then
replacing the band `-8 < x < 2` of `g` by the word `W` leaves at most two labels near every point
other than the two endpoints of the edge.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:227–241, 321–326`. -/
theorem hasTwoLabelsNear_bandUpdate {ι : Type*} {n : ℝ} (hn : 0 < n) {e : SquareEdge} {W : ℝ → ι}
    {g : ℝ × ℝ → ι} {p : ℝ × ℝ} (hW : ∀ x₀, ∃ P, ∀ᶠ x in 𝓝 x₀, W x ∈ ({P, W x₀} : Set ι))
    {c₁ c₂ : ι} (hlo : ∀ x ∈ Ioo (-8 : ℝ) (-7), W x = c₁) (hhi : ∀ x ∈ Ioo (1 : ℝ) 2, W x = c₂)
    (h0 : p ≠ e.point n 0 0) (h1 : p ≠ e.point n n 0) (hg : HasTwoLabelsNear g p)
    (hlow : 0 < e.par p → e.par p < n → e.nor n p = -8 * bandWidth n (e.par p) →
      g =ᶠ[𝓝 p] fun _ => c₁)
    (hup : 0 < e.par p → e.par p < n → e.nor n p = 2 * bandWidth n (e.par p) →
      g =ᶠ[𝓝 p] fun _ => c₂) :
    HasTwoLabelsNear (bandUpdate n e W g) p := by
  by_cases hb : p ∈ edgeBand n e (-8) 2
  · obtain ⟨s1, s2, -, -⟩ := id hb
    obtain ⟨P, hP⟩ := hW (bandCoord n e p)
    refine ⟨P, W (bandCoord n e p), ?_⟩
    filter_upwards [(isOpen_edgeBand n e _ _).mem_nhds hb,
      (continuousAt_bandCoord s1 s2).eventually hP] with q hq hq'
    rw [bandUpdate_of_mem hq]
    exact hq'
  by_cases hcb : p ∈ closedEdgeBand n e (-8) 2
  · have hs0 : 0 < e.par p :=
      lt_of_le_of_ne hcb.1 fun h => h0 (eq_point_zero_of_mem_closedEdgeBand hn.le hcb h.symm)
    have hsn : e.par p < n :=
      lt_of_le_of_ne hcb.2.1 fun h => h1 (eq_point_end_of_mem_closedEdgeBand hn.le hcb h)
    have hw := bandWidth_pos hs0 hsn
    have hc := continuousAt_bandCoord hs0 hsn
    have hd : e.nor n p = -8 * bandWidth n (e.par p) ∨ e.nor n p = 2 * bandWidth n (e.par p) := by
      by_contra h
      push Not at h
      exact hb ⟨hs0, hsn, lt_of_le_of_ne hcb.2.2.1 (Ne.symm h.1), lt_of_le_of_ne hcb.2.2.2 h.2⟩
    rcases hd with hd | hd
    · have hx : bandCoord n e p < -7 := by
        rw [bandCoord, hd, mul_div_assoc, div_self hw.ne']
        norm_num
      refine hasTwoLabelsNear_of_eventuallyEq_const (c := c₁) ?_
      filter_upwards [hlow hs0 hsn hd, hc.eventually (Iio_mem_nhds hx)] with q hq (hq' : _ < _)
      by_cases hqb : q ∈ edgeBand n e (-8) 2
      · rw [bandUpdate_of_mem hqb]
        exact hlo _ ⟨(mem_edgeBand_iff_bandCoord.1 hqb).2.2.1, hq'⟩
      · rw [bandUpdate_of_notMem hqb]
        exact hq
    · have hx : 1 < bandCoord n e p := by
        rw [bandCoord, hd, mul_div_assoc, div_self hw.ne']
        norm_num
      refine hasTwoLabelsNear_of_eventuallyEq_const (c := c₂) ?_
      filter_upwards [hup hs0 hsn hd, hc.eventually (Ioi_mem_nhds hx)] with q hq (hq' : _ < _)
      by_cases hqb : q ∈ edgeBand n e (-8) 2
      · rw [bandUpdate_of_mem hqb]
        exact hhi _ ⟨hq', (mem_edgeBand_iff_bandCoord.1 hqb).2.2.2⟩
      · rw [bandUpdate_of_notMem hqb]
        exact hq
  · refine hg.congr ?_
    filter_upwards [(isClosed_closedEdgeBand n e _ _).isOpen_compl.mem_nhds hcb] with q hq
    rw [bandUpdate_of_notMem fun h => hq (edgeBand_subset_closedEdgeBand _ _ _ _ h)]

/-! ### The central region near the boundary of the square -/

/-- The four corners of the square `[0, n] ^ 2`. -/
def IsSquareCorner (n : ℝ) (p : ℝ × ℝ) : Prop :=
  p = (0, 0) ∨ p = (n, 0) ∨ p = (0, n) ∨ p = (n, n)

/-- The first endpoint of an edge is a corner of the square. -/
theorem isSquareCorner_point_zero (n : ℝ) (e : SquareEdge) : IsSquareCorner n (e.point n 0 0) := by
  cases e <;> simp [IsSquareCorner, point]

/-- The second endpoint of an edge is a corner of the square. -/
theorem isSquareCorner_point_end (n : ℝ) (e : SquareEdge) : IsSquareCorner n (e.point n n 0) := by
  cases e <;> simp [IsSquareCorner, point]

/-- The open square is open. -/
theorem isOpen_openSquare (n : ℝ) : IsOpen (openSquare n) := isOpen_Ioo.prod isOpen_Ioo

/-- The central region is open. -/
theorem isOpen_centralRegion (n : ℝ) : IsOpen (centralRegion n) := by
  have h : centralRegion n = openSquare n ∩ ⋂ e : SquareEdge,
      {p | bandWidth n (e.par p) < e.nor n p} := by
    ext p
    simp only [centralRegion, openSquare, mem_inter_iff, mem_prod, mem_Ioo, mem_iInter,
      mem_ofPred_eq]
    tauto
  rw [h]
  exact (isOpen_openSquare n).inter (isOpen_iInter_of_finite fun e =>
    isOpen_lt ((continuous_bandWidth n).comp e.continuous_par) (e.continuous_nor n))

/-- A point of the closed square that is neither in the open square nor a corner lies on the
open segment of one edge. -/
theorem exists_edge_of_mem_closedSquare {n : ℝ} {p : ℝ × ℝ} (hp : p ∈ closedSquare n)
    (hpo : p ∉ openSquare n) (hc : ¬ IsSquareCorner n p) :
    ∃ e : SquareEdge, e.nor n p = 0 ∧ 0 < e.par p ∧ e.par p < n := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_closedSquare.1 hp
  rw [mem_openSquare] at hpo
  obtain ⟨x, y⟩ := p
  simp only at h1 h2 h3 h4 hpo
  have hc' : ¬ ((x = 0 ∨ x = n) ∧ (y = 0 ∨ y = n)) := by
    rintro ⟨hx | hx, hy | hy⟩ <;> rw [hx, hy] at hc <;> simp [IsSquareCorner] at hc
  rcases eq_or_lt_of_le h1 with hx0 | hx0
  · refine ⟨.left, by simp [nor, ← hx0], lt_of_le_of_ne h3 ?_, lt_of_le_of_ne h4 ?_⟩ <;>
      intro h <;> exact hc' ⟨Or.inl hx0.symm, by simp only [par] at h; tauto⟩
  rcases eq_or_lt_of_le h2 with hxn | hxn
  · refine ⟨.right, by simp [nor, hxn], lt_of_le_of_ne h3 ?_, lt_of_le_of_ne h4 ?_⟩ <;>
      intro h <;> exact hc' ⟨Or.inr hxn, by simp only [par] at h; tauto⟩
  rcases eq_or_lt_of_le h3 with hy0 | hy0
  · exact ⟨.bottom, by simp [nor, ← hy0], hx0, hxn⟩
  rcases eq_or_lt_of_le h4 with hyn | hyn
  · exact ⟨.top, by simp [nor, hyn], hx0, hxn⟩
  exact absurd ⟨hx0, hxn, hy0, hyn⟩ hpo

/-- **The closed central region meets the boundary of the square only at its corners.**

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:157–159`. -/
theorem mem_openSquare_of_mem_closure_centralRegion {n : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ closure (centralRegion n)) (hc : ¬ IsSquareCorner n p) : p ∈ openSquare n := by
  have hS : p ∈ closedSquare n := closure_minimal
    ((centralRegion_subset_openSquare n).trans (openSquare_subset_closedSquare n))
    (isClosed_Icc.prod isClosed_Icc) hp
  by_contra ho
  obtain ⟨e, hd, hs0, hsn⟩ := exists_edge_of_mem_closedSquare hS ho hc
  have hV : {q : ℝ × ℝ | e.nor n q < bandWidth n (e.par q)} ∈ 𝓝 p :=
    (isOpen_lt (e.continuous_nor n) ((continuous_bandWidth n).comp e.continuous_par)).mem_nhds
      (by simp only [mem_ofPred_eq, hd]; exact bandWidth_pos hs0 hsn)
  obtain ⟨q, hqV, hq⟩ := mem_closure_iff_nhds.1 hp _ hV
  exact lt_asymm hqV (hq.2.2.2.2 e)

/-- A point of the curve `x = 2` of the band of an edge lies in the central region.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:155–160, 227–236`. -/
theorem mem_centralRegion_of_nor_eq_two_mul {n : ℝ} {e : SquareEdge} {p : ℝ × ℝ}
    (h1 : 0 < e.par p) (h2 : e.par p < n) (hd : e.nor n p = 2 * bandWidth n (e.par p)) :
    p ∈ centralRegion n := by
  have hw := bandWidth_pos h1 h2
  have a1 := bandWidth_le_left n p.1
  have a2 := bandWidth_le_right n p.1
  have b1 := bandWidth_le_left n p.2
  have b2 := bandWidth_le_right n p.2
  refine ⟨?_, ?_, ?_, ?_, fun e' => ?_⟩ <;> cases e <;> (try cases e') <;>
    simp only [par, nor] at * <;> linarith

/-- A point of the curve `x = 2` of the band of an edge lies off the closed bands `-8 ≤ x ≤ 2` of
the other edges.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:227–236`. -/
theorem notMem_closedEdgeBand_of_nor_eq_two_mul {n : ℝ} {e e' : SquareEdge} (he : e' ≠ e)
    {p : ℝ × ℝ} (h1 : 0 < e.par p) (h2 : e.par p < n)
    (hd : e.nor n p = 2 * bandWidth n (e.par p)) : p ∉ closedEdgeBand n e' (-8) 2 := by
  rintro ⟨c1, c2, c3, c4⟩
  have hw := bandWidth_pos h1 h2
  have a1 := bandWidth_le_left n p.1
  have a2 := bandWidth_le_right n p.1
  have b1 := bandWidth_le_left n p.2
  have b2 := bandWidth_le_right n p.2
  cases e <;> cases e' <;> simp only [par, nor, ne_eq, not_true_eq_false] at * <;> linarith

/-- The normal words of the main sheet along an edge: the starting word and the words before and
after its main births and deaths.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:160–165, 207–220`. -/
def mainWords {ι : Type*} (A B C : ι) : Set (ℝ → ι) :=
  {edgeStartWord A B C, mainWordOne A B C, mainWordTwo A B C, mainWordThree B C, mainWordFour B C,
    mainWordFive B C}

/-- The normal word `C | A | B | C` at interfaces `-3, -2, -1` of the auxiliary sheet after the
lens exchange: the auxiliary word `eq:geometry-aux-word` with the lens `-7 < x < -7/2` replaced by
the main sheet's `C`. The point treatment of the exchange is removed by changing to it, before the
auxiliary sheet is retired.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:193–214, 334–338`. -/
noncomputable def auxWordExchanged {ι : Type*} (A B C : ι) : ℝ → ι :=
  bandWord C [(-3, A), (-2, B), (-1, C)]

/-- The normal words of the auxiliary sheet along an edge: the uniform word, the words after its
three births, and the word after the lens exchange.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:187–214`. -/
def auxWords {ι : Type*} (A B C : ι) : Set (ℝ → ι) :=
  {bandWord C [], auxWordOne B C, auxWordTwo A B C, auxWord A B C, auxWordExchanged A B C}

section Words

variable {ι : Type*} {A B C : ι}

/-- A main word takes at most two values near every point, is `C` on `-8 < x < -7` and `B` on
`1 < x < 2`. -/
theorem mainWords_props {W : ℝ → ι} (hW : W ∈ mainWords A B C) :
    (∀ x₀, ∃ P, ∀ᶠ x in 𝓝 x₀, W x ∈ ({P, W x₀} : Set ι)) ∧
      (∀ x ∈ Ioo (-8 : ℝ) (-7), W x = C) ∧ ∀ x ∈ Ioo (1 : ℝ) 2, W x = B := by
  simp only [mainWords, mem_insert_iff, mem_singleton_iff] at hW
  rcases hW with rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨bandWord_eventually_mem _ _, fun x ⟨h1, h2⟩ => ?_, fun x ⟨h1, h2⟩ => ?_⟩ <;>
    simp only [edgeStartWord, mainWordOne, mainWordTwo, mainWordThree, mainWordFour,
      mainWordFive, bandWord] <;>
    split_ifs <;> first | rfl | (exfalso; linarith)

/-- An auxiliary word takes at most two values near every point and is `C` on `-8 < x < -7` and
on `1 < x < 2`. -/
theorem auxWords_props {W : ℝ → ι} (hW : W ∈ auxWords A B C) :
    (∀ x₀, ∃ P, ∀ᶠ x in 𝓝 x₀, W x ∈ ({P, W x₀} : Set ι)) ∧
      (∀ x ∈ Ioo (-8 : ℝ) (-7), W x = C) ∧ ∀ x ∈ Ioo (1 : ℝ) 2, W x = C := by
  simp only [auxWords, mem_insert_iff, mem_singleton_iff] at hW
  rcases hW with rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨bandWord_eventually_mem _ _, fun x ⟨h1, h2⟩ => ?_, fun x ⟨h1, h2⟩ => ?_⟩ <;>
    simp only [auxWordOne, auxWordTwo, auxWord, auxWordExchanged, bandWord] <;>
    split_ifs <;> first | rfl | (exfalso; linarith)

/-- Every main word is a normal word `bandWord c l`. -/
theorem exists_eq_bandWord_of_mem_mainWords {W : ℝ → ι} (hW : W ∈ mainWords A B C) :
    ∃ c l, W = bandWord c l := by
  simp only [mainWords, mem_insert_iff, mem_singleton_iff] at hW
  rcases hW with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩

/-- Every auxiliary word is a normal word `bandWord c l`. -/
theorem exists_eq_bandWord_of_mem_auxWords {W : ℝ → ι} (hW : W ∈ auxWords A B C) :
    ∃ c l, W = bandWord c l := by
  simp only [auxWords, mem_insert_iff, mem_singleton_iff] at hW
  rcases hW with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩

/-- The words before, after and surrounding a main birth or death are main words. -/
theorem mem_mainWords_of_mem_mainSteps {op : BandOperation ι} (hop : op ∈ mainSteps A B C) :
    op.before ∈ mainWords A B C ∧ op.after ∈ mainWords A B C ∧
      op.surrounding ∈ mainWords A B C := by
  simp only [mainSteps, List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl <;>
    simp [mainWords, mainDeathC, mainDeathA, mainBirthC, mainDeathB]

/-- The words before, after and surrounding an auxiliary birth are auxiliary words. -/
theorem mem_auxWords_of_mem_auxSteps {op : BandOperation ι} (hop : op ∈ auxSteps A B C) :
    op.before ∈ auxWords A B C ∧ op.after ∈ auxWords A B C ∧
      op.surrounding ∈ auxWords A B C := by
  simp only [auxSteps, List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl <;> simp [auxWords, auxBirthB, auxBirthA, auxBirthC]

end Words

namespace RepaintingBaseline

variable {ι : Type*} (R : RepaintingBaseline ι)

/-- **Two labels near a point after the central birth.** At a point other than the four corners
where the starting guide has at most two labels, so does the guide after the central birth.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:155–160, 321–326`. -/
theorem hasTwoLabelsNear_centralGuide {p : ℝ × ℝ} (hp : ¬ IsSquareCorner R.n p)
    (hg : HasTwoLabelsNear R.guide p) : HasTwoLabelsNear R.centralGuide p := by
  by_cases hc : p ∈ closure (centralRegion R.n)
  · have hS := mem_openSquare_of_mem_closure_centralRegion hc hp
    refine ⟨R.finalLabel, R.oldLabel, ?_⟩
    filter_upwards [(isOpen_openSquare R.n).mem_nhds hS] with q hq
    by_cases hqc : q ∈ centralRegion R.n
    · simp [R.centralGuide_of_mem hqc]
    · simp [R.centralGuide_of_notMem hqc, R.guide_openSquare q hq]
  · refine hg.congr ?_
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hc] with q hq
    rw [R.centralGuide_of_notMem fun h => hq (subset_closure h)]

/-- Near a point of the curve `x = -8` of the band of `e`, every completed guide is `C_e`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:166–168, 234–241`. -/
theorem eventually_completedGuide_nbrLabel (E : List SquareEdge) {e : SquareEdge} {p : ℝ × ℝ}
    (h1 : 0 < e.par p) (h2 : e.par p < R.n) (hd : e.nor R.n p = -8 * bandWidth R.n (e.par p)) :
    R.completedGuide E =ᶠ[𝓝 p] fun _ => R.nbrLabel e := by
  have hw := bandWidth_pos h1 h2
  have := bandWidth_le_left R.n (e.par p)
  have hN : p ∈ edgeNeighbor R.n e := ⟨h1, h2, by linarith, by linarith⟩
  filter_upwards [(isOpen_edgeNeighbor R.n e).mem_nhds hN] with q hq
  rw [R.completedGuide_of_notMem_closedSquare E (notMem_closedSquare_of_mem_edgeNeighbor hq),
    R.guide_edgeNeighbor e q hq]

/-- Near a point of the curve `x = 2` of the band of `e`, every completed guide is the final
label `B`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:155–161, 227–241`. -/
theorem eventually_completedGuide_finalLabel (E : List SquareEdge) {e : SquareEdge}
    {p : ℝ × ℝ} (h1 : 0 < e.par p) (h2 : e.par p < R.n)
    (hd : e.nor R.n p = 2 * bandWidth R.n (e.par p)) :
    R.completedGuide E =ᶠ[𝓝 p] fun _ => R.finalLabel := by
  have hc := mem_centralRegion_of_nor_eq_two_mul h1 h2 hd
  have hV : ∀ᶠ q in 𝓝 p, ∀ e' : SquareEdge, e' ≠ e → q ∉ closedEdgeBand R.n e' (-8) 2 := by
    rw [eventually_all]
    intro e'
    by_cases he : e' = e
    · exact Eventually.of_forall fun _ h => absurd he h
    · filter_upwards [(isClosed_closedEdgeBand _ _ _ _).isOpen_compl.mem_nhds
        (notMem_closedEdgeBand_of_nor_eq_two_mul he h1 h2 hd)] with q hq _
      exact hq
  filter_upwards [(isOpen_centralRegion _).mem_nhds hc, hV] with q hqc hqV
  have hcq := R.centralGuide_of_mem hqc
  by_cases hqb : q ∈ edgeBand R.n e (-8) 2
  · rw [R.completedGuide_of_mem_edgeBand hqb]
    split_ifs
    · obtain ⟨s1, s2, -, -⟩ := hqb
      have hw := bandWidth_pos s1 s2
      have hx : 0 < bandCoord R.n e q := div_pos (hw.trans (hqc.2.2.2.2 e)) hw
      simp [mainWordFive, bandWord, not_lt.2 hx.le]
    · exact hcq
  · rw [R.completedGuide_of_forall_notMem fun e' _ => ?_, hcq]
    by_cases he : e' = e
    · exact he ▸ hqb
    · exact fun h => hqV e' he (edgeBand_subset_closedEdgeBand _ _ _ _ h)

/-- **Two labels near a point after completed edges.** At a point other than the four corners
where the starting guide has at most two labels, so does every completed guide.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:227–241, 321–326`. -/
theorem hasTwoLabelsNear_completedGuide (E : List SquareEdge) {p : ℝ × ℝ}
    (hp : ¬ IsSquareCorner R.n p) (hg : HasTwoLabelsNear R.guide p) :
    HasTwoLabelsNear (R.completedGuide E) p := by
  induction E with
  | nil => exact R.hasTwoLabelsNear_centralGuide hp hg
  | cons e E ih =>
    have hW := mainWords_props (A := R.oldLabel) (B := R.finalLabel) (C := R.nbrLabel e)
      (W := mainWordFive R.finalLabel (R.nbrLabel e)) (by simp [mainWords])
    exact hasTwoLabelsNear_bandUpdate R.n_pos hW.1 hW.2.1 hW.2.2
      (fun h => hp (h ▸ isSquareCorner_point_zero _ e))
      (fun h => hp (h ▸ isSquareCorner_point_end _ e)) ih
      (fun h1 h2 hd => R.eventually_completedGuide_nbrLabel E h1 h2 hd)
      (fun h1 h2 hd => R.eventually_completedGuide_finalLabel E h1 h2 hd)

/-- **Two labels near a point on the main sheet.** At a point other than the four corners where
the starting guide has at most two labels, so does every main guide along an edge whose band
carries a main word.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:160–165, 207–241, 321–326`. -/
theorem hasTwoLabelsNear_mainGuide (E : List SquareEdge) (e : SquareEdge) {W : ℝ → ι}
    (hW : W ∈ mainWords R.oldLabel R.finalLabel (R.nbrLabel e)) {p : ℝ × ℝ}
    (hp : ¬ IsSquareCorner R.n p) (hg : HasTwoLabelsNear R.guide p) :
    HasTwoLabelsNear (R.mainGuide E e W) p := by
  have hW := mainWords_props hW
  exact hasTwoLabelsNear_bandUpdate R.n_pos hW.1 hW.2.1 hW.2.2
    (fun h => hp (h ▸ isSquareCorner_point_zero _ e))
    (fun h => hp (h ▸ isSquareCorner_point_end _ e)) (R.hasTwoLabelsNear_completedGuide E hp hg)
    (fun h1 h2 hd => R.eventually_completedGuide_nbrLabel E h1 h2 hd)
    (fun h1 h2 hd => R.eventually_completedGuide_finalLabel E h1 h2 hd)

/-- **Two labels near a point on the auxiliary sheet.** Every auxiliary guide along `e` whose band
carries an auxiliary word has at most two labels near every point other than the two endpoints
of `e`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:187–197, 321–326`. -/
theorem hasTwoLabelsNear_auxGuide (e : SquareEdge) {W : ℝ → ι}
    (hW : W ∈ auxWords R.oldLabel R.finalLabel (R.nbrLabel e)) {p : ℝ × ℝ}
    (h0 : p ≠ e.point R.n 0 0) (h1 : p ≠ e.point R.n R.n 0) :
    HasTwoLabelsNear (R.auxGuide e W) p := by
  have hW := auxWords_props hW
  exact hasTwoLabelsNear_bandUpdate R.n_pos hW.1 hW.2.1 hW.2.2 h0 h1
    (hasTwoLabelsNear_of_eventuallyEq_const (Eventually.of_forall fun _ => rfl))
    (fun _ _ _ => Eventually.of_forall fun _ => rfl)
    (fun _ _ _ => Eventually.of_forall fun _ => rfl)

/-- The unmodified guides of a large-scale repainting: the starting guide, the guide after the
central birth, the guides after completed edges, and the main and auxiliary guides along an edge
whose band carries a main or an auxiliary word.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:155–241, 321–326`. -/
def IsUnmodifiedGuide (g : ℝ × ℝ → ι) : Prop :=
  g = R.guide ∨ g = R.centralGuide ∨ (∃ E, g = R.completedGuide E) ∨
    (∃ E e W, W ∈ mainWords R.oldLabel R.finalLabel (R.nbrLabel e) ∧ g = R.mainGuide E e W) ∨
    ∃ e W, W ∈ auxWords R.oldLabel R.finalLabel (R.nbrLabel e) ∧ g = R.auxGuide e W

/-- Every unmodified guide has at most two labels near every point other than the four corners
at which the starting guide has at most two. -/
theorem IsUnmodifiedGuide.hasTwoLabelsNear {g : ℝ × ℝ → ι} (h : R.IsUnmodifiedGuide g) {p : ℝ × ℝ}
    (hp : ¬ IsSquareCorner R.n p) (hg : HasTwoLabelsNear R.guide p) : HasTwoLabelsNear g p := by
  rcases h with rfl | rfl | ⟨E, rfl⟩ | ⟨E, e, W, hW, rfl⟩ | ⟨e, W, hW, rfl⟩
  · exact hg
  · exact R.hasTwoLabelsNear_centralGuide hp hg
  · exact R.hasTwoLabelsNear_completedGuide E hp hg
  · exact R.hasTwoLabelsNear_mainGuide E e hW hp hg
  · exact R.hasTwoLabelsNear_auxGuide e hW (fun h => hp (h ▸ isSquareCorner_point_zero _ e))
      (fun h => hp (h ▸ isSquareCorner_point_end _ e))

end RepaintingBaseline

/-! ### True vertices on the blocks of the hierarchy -/

/-- Two labels near a point pull back along a map continuous there. -/
theorem HasTwoLabelsNear.comp {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : Y → ι}
    {φ : X → Y} {c : X} (h : HasTwoLabelsNear f (φ c)) (hφ : ContinuousAt φ c) :
    HasTwoLabelsNear (f ∘ φ) c := by
  obtain ⟨P, Q, h⟩ := h
  exact ⟨P, Q, hφ.eventually h⟩

/-- **True vertices of the unmodified guides are grid corners.** In the repainting of the block
`S` of side `n` from a block guide, every true vertex of every unmodified guide, placed on the
block, is a grid corner `(n a, n b)`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:321–326`. -/
theorem IsTrueVertex.eq_blockCorner_of_isUnmodifiedGuide {ι : Type*} {n : ℝ} (hn : 0 < n)
    {lab : ℤ × ℤ → ι} {S : ℤ × ℤ} {B : ι} {g : ℝ × ℝ → ι}
    (hg : (blockBaseline hn lab S B).IsUnmodifiedGuide g) {c : ℝ × ℝ}
    (h : IsTrueVertex (shiftGuide (blockCorner n S) g) c) :
    ∃ Q : ℤ × ℤ, c = blockCorner n Q := by
  by_contra hQ
  push Not at hQ
  set o := blockCorner n S
  have hp : ¬ IsSquareCorner n (c - o) := by
    intro hc
    rcases hc with hc | hc | hc | hc
    · exact hQ S (by rw [← sub_eq_zero, hc]; rfl)
    · refine hQ (S.1 + 1, S.2) ?_
      rw [sub_eq_iff_eq_add] at hc
      rw [hc]; simp [o, blockCorner, mul_add, add_comm]
    · refine hQ (S.1, S.2 + 1) ?_
      rw [sub_eq_iff_eq_add] at hc
      rw [hc]; simp [o, blockCorner, mul_add, add_comm]
    · refine hQ (S.1 + 1, S.2 + 1) ?_
      rw [sub_eq_iff_eq_add] at hc
      rw [hc]; simp [o, blockCorner, mul_add, add_comm]
  have hb : HasTwoLabelsNear (blockBaseline hn lab S B).guide (c - o) := by
    have := (hasTwoLabelsNear_blockGuide hn lab (c := c - o + o) (by rwa [sub_add_cancel])).comp
      (φ := fun q => q + o) (continuous_id.add continuous_const).continuousAt
    exact this
  have := (RepaintingBaseline.IsUnmodifiedGuide.hasTwoLabelsNear _ hg hp hb).comp
    (φ := fun q => q - o) (continuous_id.sub continuous_const).continuousAt
  exact this.not_isTrueVertex h

/-- **No other unmodified true vertex in the tenfold enlargements.** For `n > 20 t`, the closed
square of radius `10 t` about a grid corner contains no true vertex of an unmodified guide of the
repainting of a block other than that corner.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:321–326, 341–343`. -/
theorem eq_blockCorner_of_isTrueVertex_of_mem_closedBall {ι : Type*} {n t : ℝ} (hn : 0 < n)
    (ht : 20 * t < n) {lab : ℤ × ℤ → ι} {S : ℤ × ℤ} {B : ι} {g : ℝ × ℝ → ι}
    (hg : (blockBaseline hn lab S B).IsUnmodifiedGuide g) {Q : ℤ × ℤ} {c : ℝ × ℝ}
    (hc : c ∈ closedBall (blockCorner n Q) (10 * t))
    (h : IsTrueVertex (shiftGuide (blockCorner n S) g) c) : c = blockCorner n Q := by
  obtain ⟨Q', rfl⟩ := h.eq_blockCorner_of_isUnmodifiedGuide hn hg
  by_contra hne
  have := le_dist_blockCorner_of_ne hn fun h : Q' = Q => hne (by rw [h])
  rw [mem_closedBall] at hc
  linarith

end TNLean.PEPS.Approximation
