/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Edge bands of a repainted dyadic square and their angular separation

Let `S = [0, n] ^ 2` be an `n`-square of the padded dyadic hierarchy that is being repainted
from its old label `A` to its final label `B`. For each of its four edges let `s` be the
coordinate parallel to the edge, measured from one endpoint, and `d` the normal coordinate,
positive into `S`. With the width `w(s) = 10 ^ (-3) min(s, n - s)` and the normal ratio
`x = d / w(s)`, an interval `α < x < β` with `0 < s < n` is a polygonal band along the edge.

The large-scale repainting first births `B` in the central part of `S` (the points beyond
`x = 1` for every edge), and then for each edge runs a fixed sequence of births, deaths and
one lens exchange with an auxiliary sheet, recorded by the normal words of the main and
auxiliary sheets. This file formalizes:

* the edge coordinates, the bands and the lens `Y = {-7 < x < -7/2}`;
* the normal words of the edge construction and the identities between them (the changed
  interval of every elementary birth or death, the surrounding sector, and the main word
  produced by the lens exchange);
* the disjointness of the bands `-8 < x < 2` along distinct edges, and the containment of
  the exterior part of a band in the exterior neighboring square;
* the clearance estimates of the proof of Lemma 7.2 (`lem:geometry-angular`) for guides with
  the stated properties: one fixed constant `a₀ = 1/5000` gives the conical clearance
  `dist(y, {f ≠ P∘}) ≥ a₀ min(n, d_V(y))` for every point `y` of the closed changed region of
  the central birth and of each elementary edge birth or death, and the clearance
  `dist(y, ∂Y) ≥ a₀ min(n, d_V(y))` for every point `y` of the closed noncommon-`C` set of the
  lens exchange; the changed regions have diameter at most `n`;
* the Lipschitz step of the outer-hole enlargement used in the point treatment.

Distances are ambient sup distances: `ℝ × ℝ` carries the maximum metric.

Labels are elements of an arbitrary type `ι`, and nothing assumes `A`, `B`, `C` distinct: the
source's nominal labels may coincide (`06-geometry.tex:168–169`), and identifying labels only
shrinks the obstructing sets (`06-geometry.tex:315–318`).

**Scope restriction (guide properties assumed; `S` at the origin):** the source states
Lemma 7.2 for the guides of its schedule. The clearance theorems `BandOperation.clearance`,
`centralBirth_clearance` and `lensExchange_clearance` are instead stated for every guide with
the properties the source's proof uses (`06-geometry.tex:276–299`): the source's normal word
on the band `-8 < x < 2` and no change off it (edge operations), the label `A` on the open
square (central birth), and the label `C` on the exterior band `-8 < x < 0` (main sheet of the
exchange). The source derives these properties from the disjointness of the bands
(`06-geometry.tex:227–241`), proved here as `disjoint_edgeBand`; the schedule itself, and so
this derivation, is not formalized. The square is `S = [0, n] ^ 2`; an aligned square
`(n r, n s) + [0, n] ^ 2` is its translate, and sup distances are translation invariant.
Documented in `docs/paper-gaps/openai26_dyadic_geometry_guide_properties.tex`.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), §7, `06-geometry.tex`: equation
  `eq:geometry-band` (lines 146–150), the edge construction (lines 155–241), Lemma 7.2
  `lem:geometry-angular` (lines 254–319), and the point-treatment estimates (lines 357–415).
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
band and meets the edge line only at the two endpoints. -/
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

/-! ### Normal words of the edge construction -/

/-- A normal word: label `c` below the first interface, then at each interface `t` the label
switches to the paired label. On an interface itself the label to its right is taken. The
source instead samples labels after one generic displacement (`06-geometry.tex:72–77`); the
two conventions differ only on the interface curves, and no clearance below depends on the
values there.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:161–170, 193–197`. -/
noncomputable def bandWord {ι : Type*} (c : ι) : List (ℝ × ι) → ℝ → ι
  | [], _ => c
  | (t, l) :: rest, x => if x < t then c else bandWord l rest x

section Words

variable {ι : Type*} (A B C : ι)

/-- The normal word `C | A | B` at interfaces `0, 1` at the start of an edge operation.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:160–165`. -/
noncomputable def edgeStartWord : ℝ → ι := bandWord C [(0, A), (1, B)]

/-- The auxiliary word after the birth of `B` in `-6 < x < -1`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:188–190`. -/
noncomputable def auxWordOne : ℝ → ι := bandWord C [(-6, B), (-1, C)]

/-- The auxiliary word after the birth of `A` in `-5 < x < -2`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:188–190`. -/
noncomputable def auxWordTwo : ℝ → ι := bandWord C [(-6, B), (-5, A), (-2, B), (-1, C)]

/-- The auxiliary word `C | B | A | C | A | B | C` at interfaces `-6, …, -1`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), equation `eq:geometry-aux-word`,
`06-geometry.tex:190–197`. -/
noncomputable def auxWord : ℝ → ι :=
  bandWord C [(-6, B), (-5, A), (-4, C), (-3, A), (-2, B), (-1, C)]

/-- The main word `C | B | A | C | A | B` at interfaces `-6, -5, -4, 0, 1` after the exchange.

Source: Polynomial-PEPS manuscript (Sept 24 2026), equation `eq:geometry-main-word`,
`06-geometry.tex:207–212`. -/
noncomputable def mainWordOne : ℝ → ι := bandWord C [(-6, B), (-5, A), (-4, C), (0, A), (1, B)]

/-- The main word `C | B | A | B` at `-6, -5, 1`, after the `C` band `(-4, 0)` dies into `A`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:216–217`. -/
noncomputable def mainWordTwo : ℝ → ι := bandWord C [(-6, B), (-5, A), (1, B)]

/-- The main word `C | B` at `-6`, after the `A` band `(-5, 1)` dies into `B`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:217–218`. -/
noncomputable def mainWordThree : ℝ → ι := bandWord C [(-6, B)]

/-- The main word `C | B | C | B` at `-6, -3, 0`, after the birth of `C` in `(-3, 0)`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:218–219`. -/
noncomputable def mainWordFour : ℝ → ι := bandWord C [(-6, B), (-3, C), (0, B)]

/-- The final main word `C | B` at `0`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:219–220`. -/
noncomputable def mainWordFive : ℝ → ι := bandWord C [(0, B)]

/-- **The exchange produces the main word.** Replacing the starting main word by the auxiliary
word on the lens `-7 < x < -7/2` gives `eq:geometry-main-word`, at every value of `x`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:199–212`. -/
theorem lens_exchange_word (x : ℝ) :
    (if -7 < x ∧ x < -7 / 2 then auxWord A B C x else edgeStartWord A B C x) =
      mainWordOne A B C x := by
  by_cases h : -7 < x ∧ x < -7 / 2
  · simp only [h, and_self, ↓reduceIte]
    obtain ⟨h1, h2⟩ := h
    simp only [auxWord, mainWordOne, bandWord]
    split_ifs <;> first | rfl | (exfalso; linarith)
  · simp only [h, ↓reduceIte]
    have h' : x ≤ -7 ∨ -7 / 2 ≤ x := by
      rcases le_or_gt x (-7) with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (le_of_not_gt fun h2 => h ⟨h1, h2⟩)
    simp only [edgeStartWord, mainWordOne, bandWord]
    rcases h' with h' | h' <;> split_ifs <;> first | rfl | (exfalso; linarith)

end Words

/-! ### Lemma 7.2 -/

/-- One elementary birth or death of the edge construction: a before word and an after word that
differ only in the closed changed interval `[lo, hi]`, a surrounding word (the before word for a
birth, the after word for a death) equal to the label `P∘` on the open sector `(lo', hi')`, with
margins at least `1/2` and the sector inside `(-8, 2)`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:246–252, 283–293`. -/
structure BandOperation (ι : Type*) where
  /-- The normal word before the operation. -/
  before : ℝ → ι
  /-- The normal word after the operation. -/
  after : ℝ → ι
  /-- The surrounding word: `before` for a birth, `after` for a death. -/
  surrounding : ℝ → ι
  /-- The surrounding label `P∘`. -/
  label : ι
  /-- The changed interval. -/
  lo : ℝ
  hi : ℝ
  /-- The surrounding sector. -/
  lo' : ℝ
  hi' : ℝ
  changed : ∀ x, before x ≠ after x → lo ≤ x ∧ x ≤ hi
  sector : ∀ x, lo' < x → x < hi' → surrounding x = label
  lo_le_hi : lo ≤ hi
  margin_lo : lo' + 1 / 2 ≤ lo
  margin_hi : hi + 1 / 2 ≤ hi'
  lo'_ge : -8 ≤ lo'
  hi'_le : hi' ≤ 2

/-- The changed set of an elementary edge operation lies in the closed band of its changed
interval, when the guides have the operation's words on the band `-8 < x < 2` and agree off it.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:246–252`. -/
theorem BandOperation.changed_subset_closedEdgeBand {ι : Type*} (op : BandOperation ι) {n : ℝ}
    (e : SquareEdge) {fb fa : ℝ × ℝ → ι}
    (hfb : ∀ p ∈ edgeBand n e (-8) 2, fb p = op.before (bandCoord n e p))
    (hfa : ∀ p ∈ edgeBand n e (-8) 2, fa p = op.after (bandCoord n e p))
    (hoff : ∀ p ∉ edgeBand n e (-8) 2, fb p = fa p) :
    {p | fb p ≠ fa p} ⊆ closedEdgeBand n e op.lo op.hi := by
  intro p hp
  by_cases hb : p ∈ edgeBand n e (-8) 2
  · have hx := op.changed _ (by rwa [← hfb p hb, ← hfa p hb])
    obtain ⟨h1, h2, -, -⟩ := mem_edgeBand_iff_bandCoord.1 hb
    have hw := bandWidth_pos h1 h2
    exact ⟨h1.le, h2.le, (le_div_iff₀ hw).1 hx.1, (div_le_iff₀ hw).1 hx.2⟩
  · exact absurd (hoff p hb) hp

/-- **Diameter of a changed region.** Two points of the closure of the changed set of an
elementary edge operation are at sup distance at most `n`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Lemma 7.2 `lem:geometry-angular`,
`06-geometry.tex:257`. -/
theorem BandOperation.dist_le_of_mem_closure_changed {ι : Type*} (op : BandOperation ι) {n : ℝ}
    (e : SquareEdge) {fb fa : ℝ × ℝ → ι}
    (hfb : ∀ p ∈ edgeBand n e (-8) 2, fb p = op.before (bandCoord n e p))
    (hfa : ∀ p ∈ edgeBand n e (-8) 2, fa p = op.after (bandCoord n e p))
    (hoff : ∀ p ∉ edgeBand n e (-8) 2, fb p = fa p) {y z : ℝ × ℝ}
    (hy : y ∈ closure {p | fb p ≠ fa p}) (hz : z ∈ closure {p | fb p ≠ fa p}) :
    dist y z ≤ n := by
  have hsub := closure_minimal (op.changed_subset_closedEdgeBand e hfb hfa hoff)
    (isClosed_closedEdgeBand n e op.lo op.hi)
  have := op.margin_lo
  have := op.margin_hi
  have := op.lo'_ge
  have := op.hi'_le
  exact dist_le_of_mem_closedEdgeBand (by linarith) (by linarith) (hsub hy) (hsub hz)

/-- **Clearance of the edge births and deaths in the proof of Lemma 7.2.** For an elementary
birth or death of the edge construction, every point `y` of the closure of the changed region lies at ambient sup distance
at least `a₀ min(n, d_V(y))` from every position of a label other than `P∘` in the surrounding
guide. Here the guides `fb` (before) and `fa` (after) have the operation's normal words on the
band `-8 < x < 2` and agree off it, and the surrounding guide `fs` has the surrounding word on
that band. These guide properties are assumed rather than derived from the schedule (see the
module's scope restriction).

Source: Polynomial-PEPS manuscript (Sept 24 2026), Lemma 7.2 `lem:geometry-angular`,
equation `eq:geometry-birth-clearance`, `06-geometry.tex:254–264, 283–293`. -/
theorem BandOperation.clearance {ι : Type*} (op : BandOperation ι) {n : ℝ} (e : SquareEdge)
    {fb fa fs : ℝ × ℝ → ι}
    (hfb : ∀ p ∈ edgeBand n e (-8) 2, fb p = op.before (bandCoord n e p))
    (hfa : ∀ p ∈ edgeBand n e (-8) 2, fa p = op.after (bandCoord n e p))
    (hoff : ∀ p ∉ edgeBand n e (-8) 2, fb p = fa p)
    (hfs : ∀ p ∈ edgeBand n e (-8) 2, fs p = op.surrounding (bandCoord n e p))
    {y : ℝ × ℝ} (hy : y ∈ closure {p | fb p ≠ fa p}) {z : ℝ × ℝ} (hz : fs z ≠ op.label) :
    angularConstant * min n (edgeMarkDist n e y) ≤ dist y z := by
  have hyc := closure_minimal (op.changed_subset_closedEdgeBand e hfb hfa hoff)
    (isClosed_closedEdgeBand n e op.lo op.hi) hy
  refine le_of_not_gt fun hlt => ?_
  have hlo := op.margin_lo
  have hhi := op.margin_hi
  have hlo' := op.lo'_ge
  have hhi' := op.hi'_le
  have hzY := mem_edgeBand_of_dist_lt_markDist op.lo_le_hi hlo hhi hlo' (by linarith) hyc hlt
  have hzB : z ∈ edgeBand n e (-8) 2 := by
    obtain ⟨h1, h2, h3, h4⟩ := mem_edgeBand_iff_bandCoord.1 hzY
    exact mem_edgeBand_iff_bandCoord.2 ⟨h1, h2, by linarith, by linarith⟩
  obtain ⟨-, -, h3, h4⟩ := mem_edgeBand_iff_bandCoord.1 hzY
  exact hz ((hfs z hzB).trans (op.sector _ h3 h4))

section Operations

variable {ι : Type*} (A B C : ι)

/-- Birth of `B` in `-6 < x < -1` on the uniform auxiliary sheet `C`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:188–189, 283`. -/
noncomputable def auxBirthB : BandOperation ι where
  before := bandWord C []
  after := auxWordOne B C
  surrounding := bandWord C []
  label := C
  lo := -6
  hi := -1
  lo' := -7
  hi' := 0
  changed x h := by
    simp only [auxWordOne, bandWord] at h
    split_ifs at h <;> first | exact absurd rfl h | constructor <;> linarith
  sector _ _ _ := rfl
  lo_le_hi := by norm_num
  margin_lo := by norm_num
  margin_hi := by norm_num
  lo'_ge := by norm_num
  hi'_le := by norm_num

/-- Birth of `A` in `-5 < x < -2` inside the auxiliary `B` band `(-6, -1)`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:189, 284–286`. -/
noncomputable def auxBirthA : BandOperation ι where
  before := auxWordOne B C
  after := auxWordTwo A B C
  surrounding := auxWordOne B C
  label := B
  lo := -5
  hi := -2
  lo' := -6
  hi' := -1
  changed x h := by
    simp only [auxWordOne, auxWordTwo, bandWord] at h
    split_ifs at h <;> first | exact absurd rfl h | constructor <;> linarith
  sector x h1 h2 := by
    simp only [auxWordOne, bandWord]
    split_ifs <;> first | rfl | (exfalso; linarith)
  lo_le_hi := by norm_num
  margin_lo := by norm_num
  margin_hi := by norm_num
  lo'_ge := by norm_num
  hi'_le := by norm_num

/-- Birth of `C` in `-4 < x < -3` inside the auxiliary `A` band `(-5, -2)`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:189–190, 284–286`. -/
noncomputable def auxBirthC : BandOperation ι where
  before := auxWordTwo A B C
  after := auxWord A B C
  surrounding := auxWordTwo A B C
  label := A
  lo := -4
  hi := -3
  lo' := -5
  hi' := -2
  changed x h := by
    simp only [auxWordTwo, auxWord, bandWord] at h
    split_ifs at h <;> first | exact absurd rfl h | constructor <;> linarith
  sector x h1 h2 := by
    simp only [auxWordTwo, bandWord]
    split_ifs <;> first | rfl | (exfalso; linarith)
  lo_le_hi := by norm_num
  margin_lo := by norm_num
  margin_hi := by norm_num
  lo'_ge := by norm_num
  hi'_le := by norm_num

/-- Death of the main `C` band `(-4, 0)` into `A`; the surrounding `A` interval is `(-5, 1)`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:216, 286–287`. -/
noncomputable def mainDeathC : BandOperation ι where
  before := mainWordOne A B C
  after := mainWordTwo A B C
  surrounding := mainWordTwo A B C
  label := A
  lo := -4
  hi := 0
  lo' := -5
  hi' := 1
  changed x h := by
    simp only [mainWordOne, mainWordTwo, bandWord] at h
    split_ifs at h <;> first | exact absurd rfl h | constructor <;> linarith
  sector x h1 h2 := by
    simp only [mainWordTwo, bandWord]
    split_ifs <;> first | rfl | (exfalso; linarith)
  lo_le_hi := by norm_num
  margin_lo := by norm_num
  margin_hi := by norm_num
  lo'_ge := by norm_num
  hi'_le := by norm_num

/-- Death of the main `A` band `(-5, 1)` into `B`; the surrounding `B` sector includes `(-6, 2)`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:216–218, 287–288`. -/
noncomputable def mainDeathA : BandOperation ι where
  before := mainWordTwo A B C
  after := mainWordThree B C
  surrounding := mainWordThree B C
  label := B
  lo := -5
  hi := 1
  lo' := -6
  hi' := 2
  changed x h := by
    simp only [mainWordTwo, mainWordThree, bandWord] at h
    split_ifs at h <;> first | exact absurd rfl h | constructor <;> linarith
  sector x h1 h2 := by
    simp only [mainWordThree, bandWord]
    split_ifs <;> first | rfl | (exfalso; linarith)
  lo_le_hi := by norm_num
  margin_lo := by norm_num
  margin_hi := by norm_num
  lo'_ge := by norm_num
  hi'_le := by norm_num

/-- Birth of `C` in `(-3, 0)` inside the main `B` sector, which includes `(-6, 2)`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:218–219, 289–290`. -/
noncomputable def mainBirthC : BandOperation ι where
  before := mainWordThree B C
  after := mainWordFour B C
  surrounding := mainWordThree B C
  label := B
  lo := -3
  hi := 0
  lo' := -6
  hi' := 2
  changed x h := by
    simp only [mainWordThree, mainWordFour, bandWord] at h
    split_ifs at h <;> first | exact absurd rfl h | constructor <;> linarith
  sector x h1 h2 := by
    simp only [mainWordThree, bandWord]
    split_ifs <;> first | rfl | (exfalso; linarith)
  lo_le_hi := by norm_num
  margin_lo := by norm_num
  margin_hi := by norm_num
  lo'_ge := by norm_num
  hi'_le := by norm_num

/-- Death of the remaining main `B` band `(-6, -3)` into `C`; the surrounding `C` sector
includes `(-8, 0)`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:219–220, 290–292`. -/
noncomputable def mainDeathB : BandOperation ι where
  before := mainWordFour B C
  after := mainWordFive B C
  surrounding := mainWordFive B C
  label := C
  lo := -6
  hi := -3
  lo' := -8
  hi' := 0
  changed x h := by
    simp only [mainWordFour, mainWordFive, bandWord] at h
    split_ifs at h <;> first | exact absurd rfl h | constructor <;> linarith
  sector x h1 h2 := by
    simp only [mainWordFive, bandWord, h2, ↓reduceIte]
  lo_le_hi := by norm_num
  margin_lo := by norm_num
  margin_hi := by norm_num
  lo'_ge := by norm_num
  hi'_le := by norm_num

/-- The seven elementary births and deaths of one edge construction, in order.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:185–221`. -/
noncomputable def edgeOperations : List (BandOperation ι) :=
  [auxBirthB B C, auxBirthA A B C, auxBirthC A B C, mainDeathC A B C, mainDeathA A B C,
    mainBirthC B C, mainDeathB B C]

end Operations

/-! ### The central birth -/

/-- The changed region of the central birth: the points of the open square `(0, n) ^ 2` beyond
the `x = 1` boundary for every edge, i.e. with `d > w(s)` for all four edges.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:155–160`. -/
def centralRegion (n : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ p.1 < n ∧ 0 < p.2 ∧ p.2 < n ∧ ∀ e : SquareEdge, bandWidth n (e.par p) < e.nor n p}

private def closedCentralRegion (n : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ p.1 ≤ n ∧ 0 ≤ p.2 ∧ p.2 ≤ n ∧
    bandWidth n p.1 ≤ p.2 ∧ bandWidth n p.1 ≤ n - p.2 ∧
    bandWidth n p.2 ≤ p.1 ∧ bandWidth n p.2 ≤ n - p.1}

private theorem isClosed_closedCentralRegion (n : ℝ) : IsClosed (closedCentralRegion n) := by
  have h1 : Continuous (Prod.fst : ℝ × ℝ → ℝ) := continuous_fst
  have h2 : Continuous (Prod.snd : ℝ × ℝ → ℝ) := continuous_snd
  have w1 : Continuous fun p : ℝ × ℝ => bandWidth n p.1 := (continuous_bandWidth n).comp h1
  have w2 : Continuous fun p : ℝ × ℝ => bandWidth n p.2 := (continuous_bandWidth n).comp h2
  exact (isClosed_le continuous_const h1).inter ((isClosed_le h1 continuous_const).inter
    ((isClosed_le continuous_const h2).inter ((isClosed_le h2 continuous_const).inter
    ((isClosed_le w1 h2).inter ((isClosed_le w1 (continuous_const.sub h2)).inter
    ((isClosed_le w2 h1).inter (isClosed_le w2 (continuous_const.sub h1))))))))

private theorem closure_centralRegion_subset (n : ℝ) :
    closure (centralRegion n) ⊆ closedCentralRegion n := by
  refine closure_minimal ?_ (isClosed_closedCentralRegion n)
  rintro p ⟨h1, h2, h3, h4, h5⟩
  have b := h5 .bottom
  have t := h5 .top
  have l := h5 .left
  have r := h5 .right
  simp only [par, nor] at b t l r
  exact ⟨h1.le, h2.le, h3.le, h4.le, b.le, t.le, l.le, r.le⟩

/-- **Clearance of the central birth in the proof of Lemma 7.2.** Every point `y` of the closed central region lies at ambient
sup distance at least `a₀ min(n, d_V(y))` from every position of a label other than `A` in any
guide which is `A` on the open square `(0, n) ^ 2`; here `V` is the set of four corners.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Lemma 7.2 `lem:geometry-angular`,
equation `eq:geometry-birth-clearance`, `06-geometry.tex:254–264, 276–281`. -/
theorem centralBirth_clearance {ι : Type*} {n : ℝ} {f : ℝ × ℝ → ι} {A : ι}
    (hf : ∀ p : ℝ × ℝ, 0 < p.1 → p.1 < n → 0 < p.2 → p.2 < n → f p = A)
    {y : ℝ × ℝ} (hy : y ∈ closure (centralRegion n)) {z : ℝ × ℝ} (hz : f z ≠ A) :
    angularConstant * min n (cornerMarkDist n y) ≤ dist y z := by
  obtain ⟨y1, y2, y3, y4, b, t, l, r⟩ := closure_centralRegion_subset n hy
  set u := min y.1 (n - y.1) with hu
  set v := min y.2 (n - y.2) with hv
  have hwu : bandWidth n y.1 = u / 1000 := rfl
  have hwv : bandWidth n y.2 = v / 1000 := rfl
  have hvu : u / 1000 ≤ v := le_min (by linarith) (by linarith)
  have huv : v / 1000 ≤ u := le_min (by linarith) (by linarith)
  have hu0 : 0 ≤ u := le_min y1 (by linarith)
  have hv0 : 0 ≤ v := le_min y3 (by linarith)
  -- the mark distance is at most the distance to the nearest corner, `max u v`
  have hmark : cornerMarkDist n y ≤ max u v := by
    unfold cornerMarkDist
    simp only [Prod.dist_eq, Real.dist_eq, sub_zero]
    rcases min_choice y.1 (n - y.1) with h1 | h1 <;>
      rcases min_choice y.2 (n - y.2) with h2 | h2
    · refine min_le_of_left_le (min_le_of_left_le ?_)
      rw [abs_of_nonneg y1, abs_of_nonneg y3, hu, hv, h1, h2]
    · refine min_le_of_right_le (min_le_of_left_le ?_)
      rw [abs_of_nonneg y1, abs_sub_comm, abs_of_nonneg (by linarith), hu, hv, h1, h2]
    · refine min_le_of_left_le (min_le_of_right_le ?_)
      rw [abs_sub_comm, abs_of_nonneg (by linarith), abs_of_nonneg y3, hu, hv, h1, h2]
    · refine min_le_of_right_le (min_le_of_right_le ?_)
      rw [abs_sub_comm, abs_of_nonneg (by linarith), abs_sub_comm y.2,
        abs_of_nonneg (by linarith), hu, hv, h1, h2]
  refine le_of_not_gt fun hlt => ?_
  have hmin : min n (cornerMarkDist n y) ≤ max u v := (min_le_right _ _).trans hmark
  have hr : dist y z < max u v / 5000 := by
    unfold angularConstant at hlt; nlinarith
  have hd := Prod.dist_eq (x := y) (y := z)
  have hzd1 : |y.1 - z.1| < min u v := by
    have : |y.1 - z.1| ≤ dist y z := by rw [hd, Real.dist_eq]; exact le_max_left _ _
    rcases le_total u v with h | h
    · rw [max_eq_right h] at hr; rw [min_eq_left h]; linarith
    · rw [max_eq_left h] at hr; rw [min_eq_right h]; linarith
  have hzd2 : |y.2 - z.2| < min u v := by
    have : |y.2 - z.2| ≤ dist y z := by rw [hd, Real.dist_eq]; exact le_max_right _ _
    rcases le_total u v with h | h
    · rw [max_eq_right h] at hr; rw [min_eq_left h]; linarith
    · rw [max_eq_left h] at hr; rw [min_eq_right h]; linarith
  rw [abs_lt] at hzd1 hzd2
  have := min_le_left u v
  have := min_le_right u v
  have := min_le_left y.1 (n - y.1)
  have := min_le_right y.1 (n - y.1)
  have := min_le_left y.2 (n - y.2)
  have := min_le_right y.2 (n - y.2)
  exact hz (hf z (by linarith) (by linarith) (by linarith) (by linarith))

/-- **Diameter of the central changed region.** Two points of the closure of the central region
are at sup distance at most `n`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Lemma 7.2 `lem:geometry-angular`,
`06-geometry.tex:257`. -/
theorem dist_le_of_mem_closure_centralRegion {n : ℝ} {y z : ℝ × ℝ}
    (hy : y ∈ closure (centralRegion n)) (hz : z ∈ closure (centralRegion n)) :
    dist y z ≤ n := by
  obtain ⟨y1, y2, y3, y4, -⟩ := closure_centralRegion_subset n hy
  obtain ⟨z1, z2, z3, z4, -⟩ := closure_centralRegion_subset n hz
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  exact max_le (abs_le.2 ⟨by linarith, by linarith⟩) (abs_le.2 ⟨by linarith, by linarith⟩)

/-! ### The lens exchange -/

private theorem frontier_edgeLens_subset {n : ℝ} {e : SquareEdge} {z : ℝ × ℝ}
    (hz : z ∈ frontier (edgeLens n e)) :
    z = e.point n 0 0 ∨ z = e.point n n 0 ∨
      (0 < e.par z ∧ e.par z < n ∧
        (e.nor n z = -7 * bandWidth n (e.par z) ∨
          e.nor n z = -7 / 2 * bandWidth n (e.par z))) := by
  rw [edgeLens, frontier, (isOpen_edgeBand n e _ _).interior_eq] at hz
  obtain ⟨hzc, hzo⟩ := hz
  obtain ⟨z1, z2, z3, z4⟩ := closure_edgeBand_subset n e _ _ hzc
  rcases z1.lt_or_eq with z1 | z1
  · rcases z2.lt_or_eq with z2 | z2
    · right; right
      refine ⟨z1, z2, ?_⟩
      by_contra h
      exact hzo ⟨z1, z2, lt_of_le_of_ne z3 fun h' => h (Or.inl h'.symm),
        lt_of_le_of_ne z4 fun h' => h (Or.inr h')⟩
    · right; left
      have hw : bandWidth n (e.par z) = 0 := by
        simp [bandWidth, z2, show (0 : ℝ) ≤ n by linarith]
      rw [hw] at z3 z4
      rw [← point_par_nor n e z, z2, show e.nor n z = 0 by linarith]
  · left
    have hw : bandWidth n (e.par z) = 0 := by
      simp [bandWidth, ← z1, show (0 : ℝ) ≤ n by linarith]
    rw [hw] at z3 z4
    rw [← point_par_nor n e z, ← z1, show e.nor n z = 0 by linarith]

/-- **Clearance of the lens exchange in the proof of Lemma 7.2.** Before the exchange the main
guide `fm` is `C` on the exterior band `-8 < x < 0`, and the auxiliary guide `fx` has the word
`eq:geometry-aux-word` on the band `-8 < x < 2` and is `C` off it. Then every point `y` of the
closure of the positions that are not common `C` on the two guides lies at ambient sup distance
at least `a₀ min(n, d_V(y))` from the boundary of the lens `Y`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Lemma 7.2 `lem:geometry-angular`,
equation `eq:geometry-exchange-clearance`, `06-geometry.tex:265–272, 295–299`. -/
theorem lensExchange_clearance {ι : Type*} {n : ℝ} (e : SquareEdge) {A B C : ι}
    {fm fx : ℝ × ℝ → ι} (hfm : ∀ p ∈ edgeBand n e (-8) 0, fm p = C)
    (hfx : ∀ p ∈ edgeBand n e (-8) 2, fx p = auxWord A B C (bandCoord n e p))
    (hfx' : ∀ p ∉ edgeBand n e (-8) 2, fx p = C)
    {y : ℝ × ℝ} (hy : y ∈ closure {p | fm p ≠ C ∨ fx p ≠ C})
    {z : ℝ × ℝ} (hz : z ∈ frontier (edgeLens n e)) :
    angularConstant * min n (edgeMarkDist n e y) ≤ dist y z := by
  have ha0 := angularConstant_pos
  have hsub : {p | fm p ≠ C ∨ fx p ≠ C} ⊆
      (edgeBand n e (-8) 0)ᶜ ∪ (closedEdgeBand n e (-6) (-4) ∪ closedEdgeBand n e (-3) (-1)) := by
    rintro p (hp | hp)
    · exact Or.inl fun h => hp (hfm p h)
    · right
      by_cases hb : p ∈ edgeBand n e (-8) 2
      · rw [hfx p hb] at hp
        obtain ⟨h1, h2, -, -⟩ := mem_edgeBand_iff_bandCoord.1 hb
        have hw := bandWidth_pos h1 h2
        have key : (-6 ≤ bandCoord n e p ∧ bandCoord n e p ≤ -4) ∨
            (-3 ≤ bandCoord n e p ∧ bandCoord n e p ≤ -1) := by
          simp only [auxWord, bandWord] at hp
          split_ifs at hp <;> first | exact absurd rfl hp |
            (left; constructor <;> linarith) | (right; constructor <;> linarith)
        rcases key with ⟨k1, k2⟩ | ⟨k1, k2⟩
        · exact Or.inl ⟨h1.le, h2.le, (le_div_iff₀ hw).1 k1, (div_le_iff₀ hw).1 k2⟩
        · exact Or.inr ⟨h1.le, h2.le, (le_div_iff₀ hw).1 k1, (div_le_iff₀ hw).1 k2⟩
      · exact absurd (hfx' p hb) hp
  have hcl : IsClosed ((edgeBand n e (-8) 0)ᶜ ∪
      (closedEdgeBand n e (-6) (-4) ∪ closedEdgeBand n e (-3) (-1))) :=
    (isOpen_edgeBand n e _ _).isClosed_compl.union
      ((isClosed_closedEdgeBand n e _ _).union (isClosed_closedEdgeBand n e _ _))
  have hyc := closure_minimal hsub hcl hy
  have hmarkle : angularConstant * min n (edgeMarkDist n e y) ≤ edgeMarkDist n e y := by
    have : min n (edgeMarkDist n e y) ≤ edgeMarkDist n e y := min_le_right _ _
    have h0 : 0 ≤ edgeMarkDist n e y := le_min dist_nonneg dist_nonneg
    unfold angularConstant at *; nlinarith [min_le_right n (edgeMarkDist n e y)]
  rcases frontier_edgeLens_subset hz with rfl | rfl | ⟨z1, z2, hzγ⟩
  · exact hmarkle.trans (min_le_left _ _)
  · exact hmarkle.trans (min_le_right _ _)
  have wz := bandWidth_pos z1 z2
  rcases hyc with hyN | hyb
  · -- `y` lies outside the open exterior band `-8 < x < 0`
    refine le_of_not_gt fun hlt => ?_
    set mz := min (e.par z) (n - e.par z)
    have hwz : bandWidth n (e.par z) = mz / 1000 := rfl
    have hmz : 0 < mz := lt_min z1 (by linarith)
    have hmarkz : edgeMarkDist n e z ≤ mz := by
      refine edgeMarkDist_le_of_mem_closedEdgeBand (α := -7) (β := -7 / 2) (by norm_num)
        (by norm_num) ⟨z1.le, z2.le, ?_, ?_⟩ <;> rcases hzγ with h | h <;> rw [h] <;> nlinarith
    have htri := edgeMarkDist_le_add n e y z
    have hdist : dist y z < mz / 2000 := by
      have h1 : dist y z < angularConstant * edgeMarkDist n e y :=
        hlt.trans_le (mul_le_mul_of_nonneg_left (min_le_right _ _) ha0.le)
      unfold angularConstant at h1; nlinarith [dist_nonneg (x := y) (y := z)]
    have hss := e.abs_par_sub_le n y z
    have hdd := e.abs_nor_sub_le n y z
    have hws := (abs_bandWidth_sub_le n (e.par y) (e.par z)).trans
      (div_le_div_of_nonneg_right hss (by norm_num))
    rw [abs_le] at hss hdd hws
    have := min_le_left (e.par z) (n - e.par z)
    have := min_le_right (e.par z) (n - e.par z)
    apply hyN
    refine ⟨by linarith, by linarith, ?_, ?_⟩ <;> rcases hzγ with h | h <;> rw [hwz] at h <;>
      rw [hwz] at hws <;> nlinarith
  · -- `y` lies in one of the two closed auxiliary bands
    have hzC : z ∈ closedEdgeBand n e (-7) (-7) ∨ z ∈ closedEdgeBand n e (-7 / 2) (-7 / 2) := by
      rcases hzγ with h | h
      · exact Or.inl ⟨z1.le, z2.le, h.ge, h.le⟩
      · exact Or.inr ⟨z1.le, z2.le, h.ge, h.le⟩
    refine le_of_not_gt fun hlt => ?_
    rcases hyb with hy | hy
    · have hzY := mem_edgeBand_of_dist_lt_markDist (α' := -13 / 2) (β' := -7 / 2)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hy hlt
      rcases hzC with ⟨-, -, h1, h2⟩ | ⟨-, -, h1, h2⟩ <;> obtain ⟨-, -, h3, h4⟩ := hzY <;>
        nlinarith
    · have hzY := mem_edgeBand_of_dist_lt_markDist (α' := -7 / 2) (β' := -1 / 2)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hy hlt
      rcases hzC with ⟨-, -, h1, h2⟩ | ⟨-, -, h1, h2⟩ <;> obtain ⟨-, -, h3, h4⟩ := hzY <;>
        nlinarith

/-! ### Point treatment: the outer-hole enlargement -/

/-- **Lipschitz step of the outer-hole enlargement.** Let `g` (the distance from the lens boundary) and `h` (the mark
distance) be `1`-Lipschitz, let `t > 0`, and suppose `2 ε₀ (a + 1) ≤ a / 2`. If a hole center
`c` has the tapered clearance `g c ≥ a max(t, min(n, h c))`, then every point `x` with
`|x - c| ≤ 2 ε₀ t` has `g x ≥ (a / 2) max(t, min(n, h x))`. This is the arithmetic step used
in the point treatment; the instantiation with the lens-boundary distance and the mark
distance, and the birth-side enlargement of `06-geometry.tex:368–373`, are not formalized here.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:405–415`. -/
theorem tapered_clearance_of_center {X : Type*} [PseudoMetricSpace X] {g h : X → ℝ}
    (hg : ∀ x c, g c ≤ g x + dist x c) (hh : ∀ x c, h x ≤ h c + dist x c)
    {a ε t n : ℝ} (ha : 0 < a) (ht : 0 < t) (haε : 2 * ε * (a + 1) ≤ a / 2)
    {x c : X} (hc : a * max t (min n (h c)) ≤ g c) (hx : dist x c ≤ 2 * ε * t) :
    a / 2 * max t (min n (h x)) ≤ g x := by
  set δ := dist x c
  have hδ : 0 ≤ δ := dist_nonneg
  have hQ : max t (min n (h x)) ≤ max t (min n (h c)) + δ := by
    refine max_le (by linarith [le_max_left t (min n (h c))]) ?_
    have := hh x c
    rcases le_total n (h c) with h1 | h1
    · have : min n (h x) ≤ n := min_le_left _ _
      have : n = min n (h c) := (min_eq_left h1).symm
      linarith [le_max_right t (min n (h c))]
    · have : min n (h x) ≤ h x := min_le_right _ _
      have : h c = min n (h c) := (min_eq_right h1).symm
      linarith [le_max_right t (min n (h c))]
  have htQ : t ≤ max t (min n (h x)) := le_max_left _ _
  have h1 := hg x c
  have h2 : a * max t (min n (h x)) ≤ a * max t (min n (h c)) + a * δ := by nlinarith
  have h3 : (a + 1) * δ ≤ (a + 1) * (2 * ε * t) := mul_le_mul_of_nonneg_left hx (by linarith)
  have h4 : (a + 1) * (2 * ε * t) ≤ a / 2 * t := by nlinarith
  have h5 : a / 2 * t ≤ a / 2 * max t (min n (h x)) := mul_le_mul_of_nonneg_left htQ (by linarith)
  nlinarith

end TNLean.PEPS.Approximation
