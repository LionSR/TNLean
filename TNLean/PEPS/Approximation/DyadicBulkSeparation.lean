/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.AngularSeparationBridges

/-!
# The angular premise of the bulk changes from the logarithmic floors

The bulk births, deaths and lens exchanges of the dyadic repainting schedule are bounded changes
once their raw target is separated from their exterior in the sense of `AngularSeparation`
(`TNLean.PEPS.Approximation.DyadicBulkSteps`). After the point treatment, the source proves this
separation in the plane, in the coordinates of the repainted block moved to the origin: the
logarithmic floor `eq:geometry-floor` against the positions of other labels, and its enlargement
by the outer holes at the true vertices (`06-geometry.tex`, lines 357–373 and 389–415). This
file restates these floors as the angular premise, with the marked points of the change, and
moves them back to the block by a translation.

* For an edge birth or death (`BandOperation.angularSeparation_bandUpdate`) and for the central
  birth (`RepaintingBaseline.angularSeparation_central`), the closure of the remaining changed
  region is separated, with constant `a₀ / 2`, from the positions of other labels in the
  surrounding guide and from every point within `2 ε₀ t` of one of its true vertices. Every outer
  hole of the surrounding frame lies in this zone, so the exterior of the birth lies there too.
* For the lens exchange (`RepaintingBaseline.floor_exchange_frontier`), every point of the
  closure of the positions that are not common `C_e`, and every point within `2 ε₀ t` of a true
  vertex of either sheet, satisfies the floor `(a₀ / 2) max(t, min(n, d_V))` against the boundary
  of the lens. This is the premise of `lensExchange_step_of_frontier`.

Here `a₀ = angularConstant`, `t` is the radius of the treated squares and `V` the endpoints of
the edge or the four corners of the block. Passing from these plane sets to the site sets of the
encoded frames is left to the assembly.

## Main definitions

* `TNLean.PEPS.Approximation.vertexZone`: the points within a given distance of a true vertex.

## Main results

* `TNLean.PEPS.Approximation.BandOperation.angularSeparation_bandUpdate`.
* `TNLean.PEPS.Approximation.RepaintingBaseline.angularSeparation_central`.
* `TNLean.PEPS.Approximation.RepaintingBaseline.floor_exchange_frontier`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), proof of Proposition 7.1 `prop:protocol`,
  `06-geometry.tex`, lines 357–430 (`eq:geometry-floor`, the outer-hole enlargement, and the
  exchange); Proposition 3.4 `prop:angular`, `02-information.tex`, lines 635–658.
-/

namespace TNLean.PEPS.Approximation

open Set Metric SquareEdge

/-- The points within distance `r` of a true vertex of a guide. With `r = 2 ε₀ t` it contains
the outer hole squares of the true vertices after the point treatment.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:368–373`. -/
def vertexZone {ι : Type*} (g : ℝ × ℝ → ι) (r : ℝ) : Set (ℝ × ℝ) :=
  {x | ∃ c, IsTrueVertex g c ∧ dist x c ≤ r}

theorem half_angularConstant_le : angularConstant / 2 ≤ angularConstant := by
  linarith [angularConstant_pos]

/-- **The angular premise of an edge birth or death.** After homogenizing the before, after and
surrounding guides of an elementary operation on the treated squares of radius `t ≤ n`, the
closure of the remaining changed region is separated from the positions of other labels in the
surrounding guide and from every point within `2 ε₀ t` of one of its true vertices, with
constant `a₀ / 2`, floor `t`, and the two endpoints of the edge as marked points; the same holds
after a common translation by `d`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), equation `eq:geometry-floor` and the
outer-hole enlargement, `06-geometry.tex:357–373`. -/
theorem BandOperation.angularSeparation_bandUpdate {ι : Type*} (op : BandOperation ι)
    {n t ε₀ : ℝ} (ht : 0 ≤ t) (htn : t ≤ n) (hε : 2 * ε₀ ≤ angularConstant / 2)
    (e : SquareEdge) (g : ℝ × ℝ → ι) (d : ℝ × ℝ) :
    AngularSeparation
      ((· + d) '' closure {p |
        homogenize (edgeTreated n e t) op.label (bandUpdate n e op.before g) p ≠
          homogenize (edgeTreated n e t) op.label (bandUpdate n e op.after g) p})
      ((· + d) '' ({z | homogenize (edgeTreated n e t) op.label
          (bandUpdate n e op.surrounding g) z ≠ op.label} ∪
        vertexZone (homogenize (edgeTreated n e t) op.label (bandUpdate n e op.surrounding g))
          (2 * (ε₀ * t))))
      n t (angularConstant / 2)
      (({e.point n 0 0, e.point n n 0} : Finset (ℝ × ℝ)).image (· + d)) := by
  refine AngularSeparation.translate (AngularSeparation.union_right ?_ ?_) d
  · refine AngularSeparation.mono_const (a := angularConstant) (fun y hy z hz => ?_) ht
      half_angularConstant_le
    rw [← min_edgeMarkDist_eq]
    exact op.floor_bandUpdate htn e g hy hz
  · rintro y hy x ⟨c, hc, hx⟩
    rw [← min_edgeMarkDist_eq]
    exact op.floor_outerHole ht htn hε e g hy hc hx

/-- **The angular premise of the central birth.** After homogenizing the starting and central
guides on the treated squares of radius `t ≤ n` about the four corners, the closure of the
remaining changed region is separated from the positions of other labels in the starting guide
and from every point within `2 ε₀ t` of one of its true vertices, with constant `a₀ / 2`, floor
`t`, and the four corners as marked points; the same holds after a common translation by `d`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), equation `eq:geometry-floor` and the
outer-hole enlargement, `06-geometry.tex:357–373`. -/
theorem RepaintingBaseline.angularSeparation_central {ι : Type*} (R : RepaintingBaseline ι)
    {t ε₀ : ℝ} (ht : 0 ≤ t) (htn : t ≤ R.n) (hε : 2 * ε₀ ≤ angularConstant / 2)
    (d : ℝ × ℝ) :
    AngularSeparation
      ((· + d) '' closure {p | homogenize (cornerTreated R.n t) R.oldLabel R.guide p ≠
        homogenize (cornerTreated R.n t) R.oldLabel R.centralGuide p})
      ((· + d) '' ({z | homogenize (cornerTreated R.n t) R.oldLabel R.guide z ≠ R.oldLabel} ∪
        vertexZone (homogenize (cornerTreated R.n t) R.oldLabel R.guide) (2 * (ε₀ * t))))
      R.n t (angularConstant / 2)
      (({(0, 0), (R.n, 0), (0, R.n), (R.n, R.n)} : Finset (ℝ × ℝ)).image (· + d)) := by
  refine AngularSeparation.translate (AngularSeparation.union_right ?_ ?_) d
  · refine AngularSeparation.mono_const (a := angularConstant) (fun y hy z hz => ?_) ht
      half_angularConstant_le
    rw [← min_cornerMarkDist_eq]
    exact R.floor_central htn hy hz
  · rintro y hy x ⟨c, hc, hx⟩
    rw [← min_cornerMarkDist_eq]
    exact R.floor_central_outerHole ht htn hε hy hc hx

/-- **The floor of the lens exchange against the lens boundary.** After homogenizing both
sheets to `C_e` on the treated squares of radius `0 < t ≤ n`, every point of the closure of the
positions that are not common `C_e`, and every point within `2 ε₀ t` of a true vertex of either
sheet, satisfies the floor `(a₀ / 2) max(t, min(n, d_V))` against every point of the boundary of
the lens, with the two endpoints of the edge as marked points; the same holds after a common
translation by `d`. This is the premise of `lensExchange_step_of_frontier` with the lens as the
plane set.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:389–426`. -/
theorem RepaintingBaseline.floor_exchange_frontier {ι : Type*} (R : RepaintingBaseline ι)
    {t ε₀ : ℝ} (ht : 0 < t) (htn : t ≤ R.n)
    (hε : 2 * ε₀ * (angularConstant + 1) ≤ angularConstant / 2) (E : List SquareEdge)
    (e : SquareEdge) (d : ℝ × ℝ) :
    ∀ x ∈ (· + d) '' (closure {p |
        homogenize (edgeTreated R.n e t) (R.nbrLabel e)
            (R.mainGuide E e (edgeStartWord R.oldLabel R.finalLabel (R.nbrLabel e))) p ≠
          R.nbrLabel e ∨
        homogenize (edgeTreated R.n e t) (R.nbrLabel e)
            (R.auxGuide e (auxWord R.oldLabel R.finalLabel (R.nbrLabel e))) p ≠ R.nbrLabel e} ∪
      vertexZone (homogenize (edgeTreated R.n e t) (R.nbrLabel e)
          (R.mainGuide E e (edgeStartWord R.oldLabel R.finalLabel (R.nbrLabel e))))
        (2 * ε₀ * t) ∪
      vertexZone (homogenize (edgeTreated R.n e t) (R.nbrLabel e)
          (R.auxGuide e (auxWord R.oldLabel R.finalLabel (R.nbrLabel e)))) (2 * ε₀ * t)),
      ∀ z ∈ frontier ((· + d) '' edgeLens R.n e),
        angularConstant / 2 * max t (cappedMarkDistance R.n
          (({e.point R.n 0 0, e.point R.n R.n 0} : Finset (ℝ × ℝ)).image (· + d)) x) ≤
          dist x z := by
  rintro _ ⟨y, hy, rfl⟩ z hz
  change z ∈ frontier ((Homeomorph.addRight d) '' edgeLens R.n e) at hz
  rw [← Homeomorph.image_frontier] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  change _ ≤ dist (y + d) (w + d)
  rw [dist_add_right, cappedMarkDistance_translate, ← min_edgeMarkDist_eq]
  rcases hy with (hy | ⟨c, hc, hy⟩) | ⟨c, hc, hy⟩
  · exact (mul_le_mul_of_nonneg_right half_angularConstant_le
      (ht.le.trans (le_max_left _ _))).trans (R.floor_exchange htn E e hy hw)
  · exact R.floor_exchange_outerHole ht htn hε E e (Or.inl hc) hy w hw
  · exact R.floor_exchange_outerHole ht htn hε E e (Or.inr hc) hy w hw

end TNLean.PEPS.Approximation
