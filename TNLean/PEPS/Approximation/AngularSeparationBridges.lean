/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.AngularAnnularLayers
import TNLean.PEPS.Approximation.DyadicPointTreatment

/-!
# Checking the angular separation premise

Proposition 3.4 (`prop:angular`) of the polynomial-PEPS manuscript asks for the angular
separation `eq:info-angular-separation` between a target `X` and an exterior `E`, in the pairwise
form `AngularSeparation`. The geometry of Section 7 supplies plane floors of a different shape:
a floor against the labels other than the bulk owner and the outer hole sites for a birth or a
death, and a floor against the lens boundary `∂Y` for an exchange. This file turns those floors
into the premise.

## Main results

* `AngularSeparation.translate`: the premise is invariant under a common translation of the
  sites and the marked points.
* `AngularSeparation.union_right`, `AngularSeparation.mono_right`, `AngularSeparation.mono_left`,
  `AngularSeparation.mono_const`: the premise for unions and subsets of the exterior and the
  target, and for a smaller constant.
* `angularSeparation_of_frontier`: a floor against the boundary of a plane set `K` gives the
  premise for a target inside `K` and an exterior outside it. Any segment from a point of `T` to a
  point of `E` crosses `∂Y`, `06-geometry.tex`, lines 418–426.
* `min_edgeMarkDist_eq`, `min_cornerMarkDist_eq`: the mark distances of the edge operations and
  of the central birth are the capped mark distances to two and four marked points.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Proposition 3.4 `prop:angular`,
  `02-information.tex`, lines 635–658; `06-geometry.tex`, lines 357–430.
-/

noncomputable section

namespace TNLean.PEPS.Approximation

open Set

/-- Translating a point and the marks together preserves the capped mark distance. -/
theorem cappedMarkDistance_translate (n : ℝ) (V : Finset (ℝ × ℝ)) (x d : ℝ × ℝ) :
    cappedMarkDistance n (V.image (· + d)) (x + d) = cappedMarkDistance n V x := by
  classical
  have key : ∀ r, r ≤ cappedMarkDistance n (V.image (· + d)) (x + d) ↔
      r ≤ cappedMarkDistance n V x := by
    intro r
    simp only [le_cappedMarkDistance_iff, Finset.forall_mem_image, dist_add_right]
  exact le_antisymm ((key _).1 le_rfl) ((key _).2 le_rfl)

/-- **Translation invariance of the angular premise.** -/
theorem AngularSeparation.translate {X E : Set (ℝ × ℝ)} {n t a : ℝ} {V : Finset (ℝ × ℝ)}
    (h : AngularSeparation X E n t a V) (d : ℝ × ℝ) :
    AngularSeparation ((· + d) '' X) ((· + d) '' E) n t a (V.image (· + d)) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  simpa only [cappedMarkDistance_translate, dist_add_right] using h x hx y hy

/-- The premise against two exteriors gives it against their union. -/
theorem AngularSeparation.union_right {X E₁ E₂ : Set (ℝ × ℝ)} {n t a : ℝ}
    {V : Finset (ℝ × ℝ)} (h₁ : AngularSeparation X E₁ n t a V)
    (h₂ : AngularSeparation X E₂ n t a V) : AngularSeparation X (E₁ ∪ E₂) n t a V := by
  rintro x hx y (hy | hy)
  exacts [h₁ x hx y hy, h₂ x hx y hy]

/-- The premise passes to a smaller exterior. -/
theorem AngularSeparation.mono_right {X E E' : Set (ℝ × ℝ)} {n t a : ℝ} {V : Finset (ℝ × ℝ)}
    (h : AngularSeparation X E n t a V) (hE : E' ⊆ E) : AngularSeparation X E' n t a V :=
  fun x hx y hy => h x hx y (hE hy)

/-- The premise passes to a smaller target. -/
theorem AngularSeparation.mono_left {X X' E : Set (ℝ × ℝ)} {n t a : ℝ} {V : Finset (ℝ × ℝ)}
    (h : AngularSeparation X E n t a V) (hX : X' ⊆ X) : AngularSeparation X' E n t a V :=
  fun x hx y hy => h x (hX hx) y hy

/-- The premise passes to a smaller constant, for a nonnegative logarithmic floor. -/
theorem AngularSeparation.mono_const {X E : Set (ℝ × ℝ)} {n t a a' : ℝ} {V : Finset (ℝ × ℝ)}
    (h : AngularSeparation X E n t a V) (ht : 0 ≤ t) (ha : a' ≤ a) :
    AngularSeparation X E n t a' V := fun x hx y hy =>
  (mul_le_mul_of_nonneg_right ha (ht.trans (le_max_left _ _))).trans (h x hx y hy)

/-- **Separation across a boundary.** Let `K` be a plane set and `X`, `E` two sets of points lying
on opposite sides of it. If every point of `X` satisfies the floor `a max(t, min(n, d_V))` against
every point of the boundary of `K`, the angular premise holds for `X` and `E`: any segment from a
point of `X` to a point of `E` crosses the boundary.

Source: `06-geometry.tex`, lines 418–426. -/
theorem angularSeparation_of_frontier {K X E : Set (ℝ × ℝ)} {n t a : ℝ} {V : Finset (ℝ × ℝ)}
    (hside : (X ⊆ K ∧ E ⊆ Kᶜ) ∨ (X ⊆ Kᶜ ∧ E ⊆ K))
    (hfloor : ∀ x ∈ X, ∀ z ∈ frontier K, a * max t (cappedMarkDistance n V x) ≤ dist x z) :
    AngularSeparation X E n t a V := by
  intro x hx y hy
  refine le_dist_of_frontier (hfloor x hx) ?_
  rcases hside with ⟨hX, hE⟩ | ⟨hX, hE⟩
  · exact Or.inl ⟨hX hx, hE hy⟩
  · exact Or.inr ⟨hX hx, hE hy⟩

/-- The mark distance of an edge operation, capped at `n`, is the capped mark distance to the two
endpoints of the edge. Source: `06-geometry.tex`, lines 243–252. -/
theorem min_edgeMarkDist_eq (n : ℝ) (e : SquareEdge) (y : ℝ × ℝ) :
    min n (edgeMarkDist n e y) =
      cappedMarkDistance n {e.point n 0 0, e.point n n 0} y := by
  classical
  refine le_antisymm ((le_cappedMarkDistance_iff _ _ _ _).2 ⟨min_le_left _ _, ?_⟩) ?_
  · simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
      edgeMarkDist]
    exact ⟨(min_le_right _ _).trans (min_le_left _ _),
      (min_le_right _ _).trans (min_le_right _ _)⟩
  · exact le_min (cappedMarkDistance_le_cap _ _ _)
      (le_min (cappedMarkDistance_le_dist _ _ (by simp))
        (cappedMarkDistance_le_dist _ _ (by simp)))

/-- The mark distance of the central birth, capped at `n`, is the capped mark distance to the
four corners of `[0, n] ^ 2`. Source: `06-geometry.tex`, lines 157–160 and 246–248. -/
theorem min_cornerMarkDist_eq (n : ℝ) (y : ℝ × ℝ) :
    min n (cornerMarkDist n y) =
      cappedMarkDistance n {(0, 0), (n, 0), (0, n), (n, n)} y := by
  classical
  refine le_antisymm ((le_cappedMarkDistance_iff _ _ _ _).2 ⟨min_le_left _ _, ?_⟩) ?_
  · simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
      cornerMarkDist]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      exact (min_le_right _ _).trans (by
        simp only [min_le_iff, le_refl, true_or, or_true])
  · exact le_min (cappedMarkDistance_le_cap _ _ _)
      (le_min (le_min (cappedMarkDistance_le_dist _ _ (by simp))
          (cappedMarkDistance_le_dist _ _ (by simp)))
        (le_min (cappedMarkDistance_le_dist _ _ (by simp))
          (cappedMarkDistance_le_dist _ _ (by simp))))

end TNLean.PEPS.Approximation
