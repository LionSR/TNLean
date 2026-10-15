/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.AngularAnnularCells

/-! # Boundary cases and consumers of the annular geometry -/

open TNLean.PEPS.Approximation
open TNLean.PEPS.Approximation.AngularGrid

example : dyadicScale 8 3 = 1 := by
  norm_num [dyadicScale]

example {n t : ℝ} (ht : 0 < t) (htn : t ≤ n) :
    Nonempty (DyadicCutoff n t) := exists_dyadicCutoff ht htn

example (X : Set (ℝ × ℝ)) (n : ℝ) (V : Finset (ℝ × ℝ)) :
    annularLayer X n V 0 0 = X := annularLayer_sole X n V

example (X : Set (ℝ × ℝ)) (n : ℝ) (m : ℕ) :
    annularLayer X n ∅ m 0 = X := annularLayer_empty_marks_zero X n m

example {n : ℝ} (hn : 0 ≤ n) (X : Set (ℝ × ℝ)) (m : ℕ) :
    annularLayer X n ∅ m 1 = ∅ := annularLayer_empty_marks_of_pos hn X m (by decide)

example (o : ℝ × ℝ) (q r : ℝ) : selectedRegion o q r ∅ = ∅ := by
  ext x
  simp [selectedRegion, touches, near]

example {X : Set (ℝ × ℝ)} {n A₀ d r : ℝ} {V : Finset (ℝ × ℝ)} {m₀ : ℕ}
    (hn : 0 < n) (hd : 0 < d)
    (hdiam : ∀ x ∈ X, ∀ y ∈ X, dist x y ≤ A₀ * n)
    (hV : V.card ≤ m₀) (o : ℝ × ℝ) (m j : ℕ) :
    ∃ S : Finset (ℤ × ℤ),
      (∀ i, i ∈ S ↔ touches o (d * dyadicScale n j) (r * dyadicScale n j)
        (annularLayer X n V m j) i) ∧
      S.card ≤ (m₀ + 1) * (2 * ⌈(max A₀ 2 + r) / d⌉₊ + 3) ^ 2 :=
  exists_annularLayer_selectedIndices hn hd hdiam hV o m j

example {o : ℝ × ℝ} {a' d s : ℝ} {Λ A : Set (ℝ × ℝ)}
    (hd : 0 < d) (hs : 0 < s) {x y : ℝ × ℝ}
    (hx : x ∈ Λ ∩ near (a' * s) A)
    (hy : y ∈ Λ \ selectedRegion o (d * s) ((3 / 2) * a' * s) A) :
    a' * s / 2 < dist x y := angular_target_core_clearance hd hs hx hy
