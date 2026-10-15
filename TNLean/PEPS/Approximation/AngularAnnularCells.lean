/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.AngularAnnularLayers
import TNLean.PEPS.Approximation.AngularCellGeometry

/-!
# Uniform cell bounds for the literal annular layers

The finite square cover is derived from the target's diameter in the first
or sole layer, and from actual marked-point witnesses in every later layer.
Consequently the selected and newly added cells have one bound independent
of the scale, marked-point positions, grid translation and physical domain.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground
states*, September 24, 2026, Proposition 3.4, `02-information.tex`, lines
681–717, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
All Lean proofs are original; no upstream Lean proof text was reused.
The conditional-information estimate and information reset remain separate.
-/

namespace TNLean.PEPS.Approximation

open AngularGrid

/-- Every literal new layer has a bounded finite square cover, including
the initial and sole layers. Only the source diameter and mark-count bounds
are assumed; a cover is constructed rather than supplied. -/
theorem exists_annularLayer_cover {X : Set (ℝ × ℝ)} {n A₀ : ℝ}
    {V : Finset (ℝ × ℝ)} {m₀ : ℕ} (hn : 0 < n)
    (hdiam : ∀ x ∈ X, ∀ y ∈ X, dist x y ≤ A₀ * n)
    (hV : V.card ≤ m₀) (m j : ℕ) :
    ∃ F : Finset (ℝ × ℝ), F.card ≤ m₀ + 1 ∧
      ∀ x ∈ annularLayer X n V m j,
        ∃ c ∈ F, dist x c ≤ max A₀ 2 * dyadicScale n j := by
  classical
  by_cases hj : j = 0
  · subst j
    by_cases hX : X.Nonempty
    · obtain ⟨c, hc⟩ := hX
      refine ⟨{c}, by simp, fun x hx ↦ ⟨c, by simp, ?_⟩⟩
      rw [dyadicScale_zero]
      exact (hdiam x (annularLayer_subset X n V m 0 hx) c hc).trans
        (mul_le_mul_of_nonneg_right (le_max_left A₀ 2) hn.le)
    · refine ⟨∅, by simp, fun x hx ↦ ?_⟩
      exact (hX ⟨x, annularLayer_subset X n V m 0 hx⟩).elim
  · refine ⟨V, hV.trans (Nat.le_succ m₀), fun x hx ↦ ?_⟩
    obtain ⟨c, hc, hxc⟩ := exists_mark_near_of_mem_annularLayer hn.le
      (Nat.pos_of_ne_zero hj) hx
    refine ⟨c, hc, hxc.le.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (le_max_right A₀ 2)
      (dyadicScale_pos hn j).le

/-- The actual cells touching an enlarged new layer have a uniform bound.
The bound depends only on the fixed geometry, not on any marked-point
locations, physical sets, grid origin, or scale. -/
theorem exists_annularLayer_selectedIndices {X : Set (ℝ × ℝ)} {n A₀ d r : ℝ}
    {V : Finset (ℝ × ℝ)} {m₀ : ℕ} (hn : 0 < n) (hd : 0 < d)
    (hdiam : ∀ x ∈ X, ∀ y ∈ X, dist x y ≤ A₀ * n)
    (hV : V.card ≤ m₀) (o : ℝ × ℝ) (m j : ℕ) :
    ∃ S : Finset (ℤ × ℤ),
      (∀ i, i ∈ S ↔ touches o (d * dyadicScale n j) (r * dyadicScale n j)
        (annularLayer X n V m j) i) ∧
      S.card ≤ (m₀ + 1) * (2 * ⌈(max A₀ 2 + r) / d⌉₊ + 3) ^ 2 := by
  obtain ⟨F, hF, hcover⟩ := exists_annularLayer_cover hn hdiam hV m j
  obtain ⟨S, hS, hcard⟩ := exists_selectedIndices_scaled
    (o := o) (d := d) (r := r) hd (dyadicScale_pos hn j) hcover
  exact ⟨S, hS, hcard.trans (Nat.mul_le_mul_right _ hF)⟩

/-- The bounded ambient squares of side `s_j` asserted before the cell
construction are themselves a literal grid cover. -/
theorem exists_annularLayer_square_cover {X : Set (ℝ × ℝ)} {n A₀ : ℝ}
    {V : Finset (ℝ × ℝ)} {m₀ : ℕ} (hn : 0 < n)
    (hdiam : ∀ x ∈ X, ∀ y ∈ X, dist x y ≤ A₀ * n)
    (hV : V.card ≤ m₀) (o : ℝ × ℝ) (m j : ℕ) :
    ∃ S : Finset (ℤ × ℤ),
      S.card ≤ (m₀ + 1) * (2 * ⌈max A₀ 2⌉₊ + 3) ^ 2 ∧
      ∀ x ∈ annularLayer X n V m j,
        ∃ i ∈ S, x ∈ cell o (dyadicScale n j) i := by
  obtain ⟨S, hS, hcard⟩ := exists_annularLayer_selectedIndices
    (d := 1) (r := 0) hn (by norm_num) hdiam hV o m j
  refine ⟨S, by simpa using hcard, fun x hx ↦ ?_⟩
  refine ⟨owner o (dyadicScale n j) x, ?_, mem_cell_owner (dyadicScale_pos hn j)⟩
  apply (hS _).2
  refine ⟨x, ?_, x, hx, ?_⟩
  · simpa only [one_mul] using (mem_cell_owner (o := o) (x := x) (dyadicScale_pos hn j))
  · simp

/-- The cells newly selected at a later annular step have the same uniform
bound even when the preceding processed group is arbitrarily large. -/
theorem exists_annular_newIndices {X : Set (ℝ × ℝ)} {n A₀ d r : ℝ}
    {V : Finset (ℝ × ℝ)} {m₀ : ℕ} (hn : 0 < n) (hd : 0 < d)
    (hdiam : ∀ x ∈ X, ∀ y ∈ X, dist x y ≤ A₀ * n)
    (hV : V.card ≤ m₀) (o : ℝ × ℝ) (m j : ℕ) :
    ∃ S : Finset (ℤ × ℤ),
      (∀ i, i ∈ S ↔
        touches o (d * dyadicScale n (j + 1)) (r * dyadicScale n (j + 1))
          (cumulativeLayer X n V m (j + 1)) i ∧
        ¬ touches o (d * dyadicScale n (j + 1)) (r * dyadicScale n (j + 1))
          (cumulativeLayer X n V m j) i) ∧
      S.card ≤ (m₀ + 1) * (2 * ⌈(max A₀ 2 + r) / d⌉₊ + 3) ^ 2 := by
  obtain ⟨F, hF, hcover⟩ := exists_annularLayer_cover hn hdiam hV m (j + 1)
  obtain ⟨S, hS, hcard⟩ := exists_newIndices_scaled
    (o := o) (d := d) (r := r) (cumulativeLayer X n V m j)
    hd (dyadicScale_pos hn (j + 1)) hcover
  refine ⟨S, ?_, hcard.trans (Nat.mul_le_mul_right _ hF)⟩
  intro i
  simpa only [cumulativeLayer_succ] using hS i

/-- Applying the cumulative separation theorem to the literal selected cells
gives the printed clearance at every scale, including the last and sole ones. -/
theorem annular_selectedRegion_clearance {X E : Set (ℝ × ℝ)}
    {n t a a' d : ℝ} {V : Finset (ℝ × ℝ)}
    (c : DyadicCutoff n t) (hn : 0 < n) (ha : 0 ≤ a) (hd : 0 < d)
    (hsep : AngularSeparation X E n t a V) {j : ℕ} (hj : j ≤ c.last)
    {o x y : ℝ × ℝ}
    (hx : x ∈ selectedRegion o (d * dyadicScale n j)
      ((3 / 2) * a' * dyadicScale n j) (cumulativeLayer X n V c.last j))
    (hy : y ∈ near ((3 / 2) * a' * dyadicScale n j) E) :
    (a / 2 - 3 * a' - d) * dyadicScale n j ≤ dist x y := by
  apply angular_selectedRegion_clearance hd (dyadicScale_pos hn j) ?_ hx hy
  intro u hu v hv
  have h := cumulativeLayer_separation c hn.le ha hsep hj hu hv
  nlinarith

end TNLean.PEPS.Approximation
