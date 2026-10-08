/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Edge bands of a repainted dyadic square

Let `S = [0, n] ^ 2` be an `n`-square of the padded dyadic hierarchy that is being repainted
from its old label `A` to its final label `B`. For each of its four edges let `s` be the
coordinate parallel to the edge, measured from one endpoint, and `d` the normal coordinate,
positive into `S`. With the width `w(s) = 10 ^ (-3) min(s, n - s)` and the normal ratio
`x = d / w(s)`, an interval `α < x < β` with `0 < s < n` is a polygonal band along the edge.
This file formalizes:

* the edge coordinates, the bands and the lens `Y = {-7 < x < -7/2}`;
* the disjointness of the bands `-8 < x < 2` along distinct edges, and the containment of
  the exterior part of a band in the exterior neighboring square;
* the mark distances and the core conical estimate: with `a₀ = 1/5000`, a point within
  `a₀ min(n, d_V(y))` of a point `y` of a closed band lies in a slightly larger open band.

The clearance estimates of Lemma 7.2 built on these bands are in
`TNLean.PEPS.Approximation.DyadicRepaintingClearance`.

Distances are ambient sup distances: `ℝ × ℝ` carries the maximum metric.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), §7, `06-geometry.tex`: equation
  `eq:geometry-band` (lines 146–150), the edge construction (lines 155–241), and
  Lemma 7.2 `lem:geometry-angular` (lines 254–319).
-/

namespace TNLean.PEPS.Approximation

open Set Metric

/-! ### Edge coordinates -/

/-- The four edges of the square `[0, n] ^ 2`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:142–145`. -/
inductive SquareEdge
  | bottom
  | right
  | top
  | left
  deriving DecidableEq

/-- There are four edges. -/
instance : Fintype SquareEdge where
  elems := {.bottom, .right, .top, .left}
  complete e := by cases e <;> simp

namespace SquareEdge

/-- The coordinate `s` parallel to an edge, measured from one endpoint.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:143–145`. -/
def par : SquareEdge → ℝ × ℝ → ℝ
  | bottom, p => p.1
  | top, p => p.1
  | left, p => p.2
  | right, p => p.2

/-- The normal coordinate `d` of an edge of `[0, n] ^ 2`, positive into the square.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:143–145`. -/
def nor (n : ℝ) : SquareEdge → ℝ × ℝ → ℝ
  | bottom, p => p.2
  | top, p => n - p.2
  | left, p => p.1
  | right, p => n - p.1

/-- The point with edge coordinates `(s, d)`. -/
def point (n : ℝ) : SquareEdge → ℝ → ℝ → ℝ × ℝ
  | bottom, s, d => (s, d)
  | top, s, d => (s, n - d)
  | left, s, d => (d, s)
  | right, s, d => (n - d, s)

@[simp] theorem par_point (n : ℝ) (e : SquareEdge) (s d : ℝ) : e.par (e.point n s d) = s := by
  cases e <;> rfl

@[simp] theorem nor_point (n : ℝ) (e : SquareEdge) (s d : ℝ) :
    e.nor n (e.point n s d) = d := by
  cases e <;> simp [nor, point]

theorem point_par_nor (n : ℝ) (e : SquareEdge) (p : ℝ × ℝ) :
    e.point n (e.par p) (e.nor n p) = p := by
  cases e <;> simp [point, par, nor]

/-- Sup distance in edge coordinates. -/
theorem dist_eq (n : ℝ) (e : SquareEdge) (y z : ℝ × ℝ) :
    dist y z = max |e.par y - e.par z| |e.nor n y - e.nor n z| := by
  cases e <;> simp only [Prod.dist_eq, Real.dist_eq, par, nor]
  · rw [show n - y.1 - (n - z.1) = -(y.1 - z.1) by ring, abs_neg, max_comm]
  · rw [show n - y.2 - (n - z.2) = -(y.2 - z.2) by ring, abs_neg]
  · rw [max_comm]

theorem abs_par_sub_le (n : ℝ) (e : SquareEdge) (y z : ℝ × ℝ) :
    |e.par y - e.par z| ≤ dist y z :=
  (dist_eq n e y z).symm ▸ le_max_left _ _

theorem abs_nor_sub_le (n : ℝ) (e : SquareEdge) (y z : ℝ × ℝ) :
    |e.nor n y - e.nor n z| ≤ dist y z :=
  (dist_eq n e y z).symm ▸ le_max_right _ _

theorem continuous_par (e : SquareEdge) : Continuous e.par := by
  cases e <;> [exact continuous_fst; exact continuous_snd; exact continuous_fst;
    exact continuous_snd]

theorem continuous_nor (n : ℝ) (e : SquareEdge) : Continuous (e.nor n) := by
  cases e <;> [exact continuous_snd; exact continuous_const.sub continuous_fst;
    exact continuous_const.sub continuous_snd; exact continuous_fst]

end SquareEdge

open SquareEdge

/-! ### Band widths, bands and the lens -/

/-- The band width `w(s) = 10 ^ (-3) min(s, n - s)`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), equation `eq:geometry-band`,
`06-geometry.tex:146–150`. -/
noncomputable def bandWidth (n s : ℝ) : ℝ := min s (n - s) / 1000

theorem bandWidth_le_left (n s : ℝ) : bandWidth n s ≤ s / 1000 :=
  div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)

theorem bandWidth_le_right (n s : ℝ) : bandWidth n s ≤ (n - s) / 1000 :=
  div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)

theorem bandWidth_nonneg {n s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ n) : 0 ≤ bandWidth n s :=
  div_nonneg (le_min h0 (by linarith)) (by norm_num)

theorem bandWidth_pos {n s : ℝ} (h0 : 0 < s) (h1 : s < n) : 0 < bandWidth n s :=
  div_pos (lt_min h0 (by linarith)) (by norm_num)

theorem abs_bandWidth_sub_le (n s s' : ℝ) :
    |bandWidth n s - bandWidth n s'| ≤ |s - s'| / 1000 := by
  have h := abs_min_sub_min_le_max s (n - s) s' (n - s')
  rw [show n - s - (n - s') = -(s - s') by ring, abs_neg, max_self] at h
  rw [bandWidth, bandWidth, ← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 1000)]
  exact div_le_div_of_nonneg_right h (by norm_num)

theorem continuous_bandWidth (n : ℝ) : Continuous (bandWidth n) := by
  unfold bandWidth
  fun_prop

/-- The open band `{0 < s < n, α < x < β}` along an edge, with `x = d / w(s)`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:146–153`. -/
def edgeBand (n : ℝ) (e : SquareEdge) (α β : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 < e.par p ∧ e.par p < n ∧ α * bandWidth n (e.par p) < e.nor n p ∧
    e.nor n p < β * bandWidth n (e.par p)}

/-- The closed band `{0 ≤ s ≤ n, α w(s) ≤ d ≤ β w(s)}`; it contains the closure of the open
band. Since `w(0) = w(n) = 0`, it pinches to the edge line at the two endpoints; when
`α ≤ 0 ≤ β` it also contains the whole edge segment `{0 ≤ s ≤ n, d = 0}`. -/
def closedEdgeBand (n : ℝ) (e : SquareEdge) (α β : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ e.par p ∧ e.par p ≤ n ∧ α * bandWidth n (e.par p) ≤ e.nor n p ∧
    e.nor n p ≤ β * bandWidth n (e.par p)}

/-- The normal ratio `x = d / w(s)`. -/
noncomputable def bandCoord (n : ℝ) (e : SquareEdge) (p : ℝ × ℝ) : ℝ :=
  e.nor n p / bandWidth n (e.par p)

/-- The lens `Y = {0 < s < n, -7 < x < -7/2}` of the edge exchange.

Source: Polynomial-PEPS manuscript (Sept 24 2026), equation `eq:geometry-lens`,
`06-geometry.tex:199–202`. -/
def edgeLens (n : ℝ) (e : SquareEdge) : Set (ℝ × ℝ) := edgeBand n e (-7) (-7 / 2)

/-- The open exterior neighboring `n`-square across an edge, `{0 < s < n, -n < d < 0}`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:166–168`. -/
def edgeNeighbor (n : ℝ) (e : SquareEdge) : Set (ℝ × ℝ) :=
  {p | 0 < e.par p ∧ e.par p < n ∧ -n < e.nor n p ∧ e.nor n p < 0}

theorem isOpen_edgeBand (n : ℝ) (e : SquareEdge) (α β : ℝ) : IsOpen (edgeBand n e α β) := by
  have hp := e.continuous_par
  have hd := e.continuous_nor n
  have hw : Continuous fun p => bandWidth n (e.par p) := (continuous_bandWidth n).comp hp
  exact (isOpen_lt continuous_const hp).inter ((isOpen_lt hp continuous_const).inter
    ((isOpen_lt (continuous_const.mul hw) hd).inter (isOpen_lt hd (continuous_const.mul hw))))

theorem isClosed_closedEdgeBand (n : ℝ) (e : SquareEdge) (α β : ℝ) :
    IsClosed (closedEdgeBand n e α β) := by
  have hp := e.continuous_par
  have hd := e.continuous_nor n
  have hw : Continuous fun p => bandWidth n (e.par p) := (continuous_bandWidth n).comp hp
  exact (isClosed_le continuous_const hp).inter ((isClosed_le hp continuous_const).inter
    ((isClosed_le (continuous_const.mul hw) hd).inter (isClosed_le hd (continuous_const.mul hw))))

theorem isOpen_edgeNeighbor (n : ℝ) (e : SquareEdge) : IsOpen (edgeNeighbor n e) := by
  have hp := e.continuous_par
  have hd := e.continuous_nor n
  exact (isOpen_lt continuous_const hp).inter ((isOpen_lt hp continuous_const).inter
    ((isOpen_lt continuous_const hd).inter (isOpen_lt hd continuous_const)))

theorem edgeBand_subset_closedEdgeBand (n : ℝ) (e : SquareEdge) (α β : ℝ) :
    edgeBand n e α β ⊆ closedEdgeBand n e α β :=
  fun _ ⟨h1, h2, h3, h4⟩ => ⟨h1.le, h2.le, h3.le, h4.le⟩

theorem closure_edgeBand_subset (n : ℝ) (e : SquareEdge) (α β : ℝ) :
    closure (edgeBand n e α β) ⊆ closedEdgeBand n e α β :=
  closure_minimal (edgeBand_subset_closedEdgeBand n e α β) (isClosed_closedEdgeBand n e α β)

/-- On the open band, the interval condition on `x = d / w(s)` is the band condition. -/
theorem mem_edgeBand_iff_bandCoord {n : ℝ} {e : SquareEdge} {α β : ℝ} {p : ℝ × ℝ} :
    p ∈ edgeBand n e α β ↔
      0 < e.par p ∧ e.par p < n ∧ α < bandCoord n e p ∧ bandCoord n e p < β := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    have hw := bandWidth_pos h1 h2
    exact ⟨h1, h2, (lt_div_iff₀ hw).2 h3, (div_lt_iff₀ hw).2 h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    have hw := bandWidth_pos h1 h2
    exact ⟨h1, h2, (lt_div_iff₀ hw).1 h3, (div_lt_iff₀ hw).1 h4⟩

/-! ### Disjointness of the edge bands -/

private theorem bandWidth_facts {n : ℝ} {e : SquareEdge} {α β : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ edgeBand n e α β) :
    0 < e.par p ∧ e.par p < n ∧ α * bandWidth n (e.par p) < e.nor n p ∧
      e.nor n p < β * bandWidth n (e.par p) ∧ 0 ≤ bandWidth n (e.par p) ∧
      bandWidth n (e.par p) ≤ e.par p / 1000 ∧ bandWidth n (e.par p) ≤ (n - e.par p) / 1000 :=
  ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2, bandWidth_nonneg hp.1.le hp.2.1.le,
    bandWidth_le_left _ _, bandWidth_le_right _ _⟩

/-- **Band disjointness.** The bands `-8 < x < 2` along distinct edges of `S` are disjoint.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:227–236`: opposite edges
are separated by `n`, while for adjacent edges a common point would have `r₁ < 0.008 r₂` and
`r₂ < 0.008 r₁`. -/
theorem disjoint_edgeBand {n : ℝ} {e e' : SquareEdge} (h : e ≠ e') :
    Disjoint (edgeBand n e (-8) 2) (edgeBand n e' (-8) 2) := by
  rw [Set.disjoint_left]
  intro p hp hp'
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := bandWidth_facts hp
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := bandWidth_facts hp'
  cases e <;> cases e' <;> simp only [par, nor, ne_eq, not_true_eq_false] at * <;> linarith

/-- The exterior part `-8 < x < 0` of an edge band lies in the exterior neighboring square.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:234–236`. -/
theorem edgeBand_neg_subset_edgeNeighbor {n : ℝ} (e : SquareEdge) :
    edgeBand n e (-8) 0 ⊆ edgeNeighbor n e := by
  intro p hp
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := bandWidth_facts hp
  exact ⟨a1, a2, by linarith, by linarith⟩

/-- **Diameter.** Two points of a closed band with `-8 ≤ α` and `β ≤ 8` are at sup distance at
most `n`; see `BandOperation.dist_le_of_mem_closure_changed` for the changed regions.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Lemma 7.2 `lem:geometry-angular`,
`06-geometry.tex:257`. -/
theorem dist_le_of_mem_closedEdgeBand {n : ℝ} {e : SquareEdge} {α β : ℝ} (hα : -8 ≤ α)
    (hβ : β ≤ 8) {y z : ℝ × ℝ} (hy : y ∈ closedEdgeBand n e α β)
    (hz : z ∈ closedEdgeBand n e α β) : dist y z ≤ n := by
  obtain ⟨y1, y2, y3, y4⟩ := hy
  obtain ⟨z1, z2, z3, z4⟩ := hz
  have wy0 := bandWidth_nonneg y1 y2
  have wz0 := bandWidth_nonneg z1 z2
  have wy1 := bandWidth_le_left n (e.par y)
  have wy2 := bandWidth_le_right n (e.par y)
  have wz1 := bandWidth_le_left n (e.par z)
  have wz2 := bandWidth_le_right n (e.par z)
  have ha1 : -8 * bandWidth n (e.par y) ≤ α * bandWidth n (e.par y) :=
    mul_le_mul_of_nonneg_right hα wy0
  have ha2 : β * bandWidth n (e.par y) ≤ 8 * bandWidth n (e.par y) :=
    mul_le_mul_of_nonneg_right hβ wy0
  have hb1 : -8 * bandWidth n (e.par z) ≤ α * bandWidth n (e.par z) :=
    mul_le_mul_of_nonneg_right hα wz0
  have hb2 : β * bandWidth n (e.par z) ≤ 8 * bandWidth n (e.par z) :=
    mul_le_mul_of_nonneg_right hβ wz0
  rw [dist_eq n e]
  refine max_le (abs_le.2 ⟨by linarith, by linarith⟩) (abs_le.2 ⟨by linarith, by linarith⟩)

/-! ### Mark distances -/

/-- The sup distance `d_V(y)` from the two endpoints of an edge, the marked points of an edge
operation.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:170, 246–248`. -/
noncomputable def edgeMarkDist (n : ℝ) (e : SquareEdge) (y : ℝ × ℝ) : ℝ :=
  min (dist y (e.point n 0 0)) (dist y (e.point n n 0))

/-- The sup distance `d_V(y)` from the four corners of `[0, n] ^ 2`, the marked points of the
central birth.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:157–160, 246–248`. -/
noncomputable def cornerMarkDist (n : ℝ) (y : ℝ × ℝ) : ℝ :=
  min (min (dist y (0, 0)) (dist y (n, 0))) (min (dist y (0, n)) (dist y (n, n)))

theorem edgeMarkDist_le_add (n : ℝ) (e : SquareEdge) (y z : ℝ × ℝ) :
    edgeMarkDist n e y ≤ edgeMarkDist n e z + dist y z := by
  unfold edgeMarkDist
  rw [← min_add_add_right]
  exact min_le_min (by linarith [dist_triangle y z (e.point n 0 0), dist_comm y z])
    (by linarith [dist_triangle y z (e.point n n 0), dist_comm y z])

theorem dist_point_zero (n : ℝ) (e : SquareEdge) (y : ℝ × ℝ) :
    dist y (e.point n 0 0) = max |e.par y| |e.nor n y| := by
  rw [dist_eq n e]; simp

theorem dist_point_end (n : ℝ) (e : SquareEdge) (y : ℝ × ℝ) :
    dist y (e.point n n 0) = max |e.par y - n| |e.nor n y| := by
  rw [dist_eq n e]; simp

/-- On a closed band with `|α|, |β| ≤ 8`, the endpoint distance is at most the parallel distance
`min(s, n - s)` to the nearer endpoint. -/
theorem edgeMarkDist_le_of_mem_closedEdgeBand {n : ℝ} {e : SquareEdge} {α β : ℝ}
    (hα : -8 ≤ α) (hβ : β ≤ 8) {y : ℝ × ℝ} (hy : y ∈ closedEdgeBand n e α β) :
    edgeMarkDist n e y ≤ min (e.par y) (n - e.par y) := by
  obtain ⟨y1, y2, y3, y4⟩ := hy
  have w0 := bandWidth_nonneg y1 y2
  have ha1 : -8 * bandWidth n (e.par y) ≤ α * bandWidth n (e.par y) :=
    mul_le_mul_of_nonneg_right hα w0
  have ha2 : β * bandWidth n (e.par y) ≤ 8 * bandWidth n (e.par y) :=
    mul_le_mul_of_nonneg_right hβ w0
  have hd : |e.nor n y| ≤ min (e.par y) (n - e.par y) := by
    have : bandWidth n (e.par y) = min (e.par y) (n - e.par y) / 1000 := rfl
    have hm : 0 ≤ min (e.par y) (n - e.par y) := le_min y1 (by linarith)
    rw [abs_le]; constructor <;> nlinarith
  unfold edgeMarkDist
  rw [dist_point_zero, dist_point_end]
  rcases min_choice (e.par y) (n - e.par y) with hm | hm <;> rw [hm] at hd ⊢
  · exact min_le_of_left_le (max_le (by rw [abs_of_nonneg y1]) hd)
  · exact min_le_of_right_le (max_le (by rw [abs_sub_comm, abs_of_nonneg (by linarith)]) hd)

/-! ### The core conical estimate -/

/-- The fixed angular constant `a₀` of Lemma 7.2. -/
noncomputable def angularConstant : ℝ := 1 / 5000

theorem angularConstant_pos : 0 < angularConstant := by norm_num [angularConstant]

/-- **Conical band estimate.** If a closed band `[α, β]` lies inside an open band `(α', β')`
with margins at least `1/2` in the normal ratio, all inside `[-8, 8]`, then the open sup ball of
radius `a₀ min(s, n - s)` about a point of the closed band lies in the open band.

Source: Polynomial-PEPS manuscript (Sept 24 2026), proof of Lemma 7.2 `lem:geometry-angular`,
`06-geometry.tex:283–310`: strict interval margins and homogeneity near the marked points. -/
theorem mem_edgeBand_of_dist_lt {n : ℝ} {e : SquareEdge} {α β α' β' : ℝ}
    (hαβ : α ≤ β) (hα : α' + 1 / 2 ≤ α) (hβ : β + 1 / 2 ≤ β') (hα' : -8 ≤ α') (hβ' : β' ≤ 8)
    {y z : ℝ × ℝ} (hy : y ∈ closedEdgeBand n e α β)
    (hz : dist y z < angularConstant * min (e.par y) (n - e.par y)) :
    z ∈ edgeBand n e α' β' := by
  obtain ⟨y1, y2, y3, y4⟩ := hy
  have hss := e.abs_par_sub_le n y z
  have hdd := e.abs_nor_sub_le n y z
  have hws := abs_bandWidth_sub_le n (e.par y) (e.par z)
  set s := e.par y
  set m := min s (n - s) with hm
  have hw : bandWidth n s = m / 1000 := rfl
  have hm0 : 0 ≤ m := le_min y1 (by linarith)
  have hms : m ≤ s := min_le_left _ _
  have hmn : m ≤ n - s := min_le_right _ _
  unfold angularConstant at hz
  have hr : dist y z < m / 5000 := by linarith
  have hd0 : 0 ≤ dist y z := dist_nonneg
  have hmpos : 0 < m := by linarith
  rw [abs_le] at hss hdd
  obtain ⟨hss1, hss2⟩ := hss
  obtain ⟨hdd1, hdd2⟩ := hdd
  have hws' : |bandWidth n s - bandWidth n (e.par z)| ≤ m / 5000 / 1000 := by
    refine hws.trans (div_le_div_of_nonneg_right ?_ (by norm_num))
    rw [abs_le]; constructor <;> linarith
  have hB : |β' * bandWidth n s - β' * bandWidth n (e.par z)| ≤ 8 * (m / 5000 / 1000) := by
    rw [← mul_sub, abs_mul]
    exact mul_le_mul (abs_le.2 ⟨by linarith, hβ'⟩) hws' (abs_nonneg _) (by norm_num)
  have hA : |α' * bandWidth n s - α' * bandWidth n (e.par z)| ≤ 8 * (m / 5000 / 1000) := by
    rw [← mul_sub, abs_mul]
    exact mul_le_mul (abs_le.2 ⟨hα', by linarith⟩) hws' (abs_nonneg _) (by norm_num)
  rw [abs_le] at hA hB
  have h1 : β * bandWidth n s ≤ β' * bandWidth n s - 1 / 2 * bandWidth n s := by
    have := mul_le_mul_of_nonneg_right hβ (show 0 ≤ bandWidth n s by rw [hw]; positivity)
    linarith
  have h2 : α' * bandWidth n s + 1 / 2 * bandWidth n s ≤ α * bandWidth n s := by
    have := mul_le_mul_of_nonneg_right hα (show 0 ≤ bandWidth n s by rw [hw]; positivity)
    linarith
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · linarith [hA.1, hA.2]
  · linarith [hB.1, hB.2]

/-- The clearance at a point of a closed band, in terms of the mark distance. -/
theorem mem_edgeBand_of_dist_lt_markDist {n : ℝ} {e : SquareEdge} {α β α' β' : ℝ}
    (hαβ : α ≤ β) (hα : α' + 1 / 2 ≤ α) (hβ : β + 1 / 2 ≤ β') (hα' : -8 ≤ α') (hβ' : β' ≤ 8)
    {y z : ℝ × ℝ} (hy : y ∈ closedEdgeBand n e α β)
    (hz : dist y z < angularConstant * min n (edgeMarkDist n e y)) :
    z ∈ edgeBand n e α' β' := by
  refine mem_edgeBand_of_dist_lt hαβ hα hβ hα' hβ' hy (hz.trans_le ?_)
  refine mul_le_mul_of_nonneg_left ((min_le_right _ _).trans ?_) angularConstant_pos.le
  exact edgeMarkDist_le_of_mem_closedEdgeBand (by linarith) (by linarith) hy

end TNLean.PEPS.Approximation
