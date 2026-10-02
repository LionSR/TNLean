/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.IntegerCellNoHoles
import TNLean.PEPS.IntegerContourRayPotential
import TNLean.PEPS.IntegerCellExteriorCollar
import TNLean.PEPS.IntegerExteriorConnectivity
import TNLean.PEPS.IntegerCellContactConnectivity
import Mathlib.GroupTheory.Perm.Cycle.Basic

/-!
# Connectivity of the exposed integer-cell contour

Let a finite set of occupied integer centers have a simply connected union of
closed unit squares. The missing centers near the occupied cells form a connected
four-neighbor graph when each edge is required to have one common nearby occupied
cell. This is the safe graph whose straight edges lie in the exterior collar.

The proof follows the exposed edges with the occupied cell on their left.
At a diagonal occupied contact the successor takes the right turn, retaining
connectivity through shared corners. A finite signed contour has a horizontal-ray
winding potential. Connectivity of the occupied contact graph and of the entire
missing-cell graph forces every exposed edge into a single successor orbit.
Local successor steps and nearby missing centers then give safe graph walks.

**Scope restriction (auxiliary cell geometry):** This proves exterior-collar
connectivity for the actual simply connected finite closed-cell union. It neither
defines a disk by connectivity nor asserts the physical entropy theorem of SCP10,
arXiv:1001.3807, Theorem 6.9, lines 1935–2076. See
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

open scoped BigOperators
noncomputable section
namespace TNLean.PEPS

-- Outward directions are east, north, west, and south.
private def normal (j : Fin 4) : ℤ × ℤ := ![(1, 0), (0, 1), (-1, 0), (0, -1)] j

private theorem normal_twice (j : Fin 4) : normal (j + 1 + 1) = -normal j := by
  fin_cases j <;> decide

private theorem normal_prev (j : Fin 4) : normal (j + -1) = -normal (j + 1) := by
  fin_cases j <;> decide

private theorem direction_next_prev (j : Fin 4) : j + 1 + -1 = j := by
  fin_cases j <;> decide

private theorem direction_prev_next (j : Fin 4) : j + -1 + 1 = j := by
  fin_cases j <;> decide

private def boundaryDarts (A : Finset (ℤ × ℤ)) : Finset ((ℤ × ℤ) × Fin 4) :=
  (A.product Finset.univ).filter (fun d => d.1 + normal d.2 ∉ A)

private theorem mem_boundaryDarts {A : Finset (ℤ × ℤ)} {d : (ℤ × ℤ) × Fin 4} :
    d ∈ boundaryDarts A ↔ d.1 ∈ A ∧ d.1 + normal d.2 ∉ A := by
  obtain ⟨a, j⟩ := d
  simp [boundaryDarts]

private abbrev BoundaryDart (A : Finset (ℤ × ℤ)) := {d // d ∈ boundaryDarts A}

private theorem dart_occupied {A : Finset (ℤ × ℤ)} (d : BoundaryDart A) : d.1.1 ∈ A :=
  ((mem_boundaryDarts).mp d.2).1

private theorem dart_missing {A : Finset (ℤ × ℤ)} (d : BoundaryDart A) :
    d.1.1 + normal d.1.2 ∉ A := ((mem_boundaryDarts).mp d.2).2

-- At a shared corner, take the right turn if the diagonal cell is occupied.
private def nextDart {A : Finset (ℤ × ℤ)} (d : BoundaryDart A) : BoundaryDart A :=
  if hc : d.1.1 + normal d.1.2 + normal (d.1.2 + 1) ∈ A then
    ⟨(d.1.1 + normal d.1.2 + normal (d.1.2 + 1), d.1.2 + -1), by
      apply mem_boundaryDarts.mpr
      refine ⟨hc, ?_⟩
      simp only [normal_prev, add_neg_cancel_right]
      exact dart_missing d⟩
  else if hb : d.1.1 + normal (d.1.2 + 1) ∈ A then
    ⟨(d.1.1 + normal (d.1.2 + 1), d.1.2), by
      apply mem_boundaryDarts.mpr
      refine ⟨hb, ?_⟩
      simpa only [add_right_comm] using hc⟩
  else
    ⟨(d.1.1, d.1.2 + 1), by
      exact mem_boundaryDarts.mpr ⟨dart_occupied d, hb⟩⟩

private def prevDart {A : Finset (ℤ × ℤ)} (d : BoundaryDart A) : BoundaryDart A :=
  if hc : d.1.1 + normal d.1.2 - normal (d.1.2 + 1) ∈ A then
    ⟨(d.1.1 + normal d.1.2 - normal (d.1.2 + 1), d.1.2 + 1), by
      apply mem_boundaryDarts.mpr
      refine ⟨hc, ?_⟩
      simpa only [sub_add_cancel] using dart_missing d⟩
  else if hb : d.1.1 - normal (d.1.2 + 1) ∈ A then
    ⟨(d.1.1 - normal (d.1.2 + 1), d.1.2), by
      apply mem_boundaryDarts.mpr
      refine ⟨hb, ?_⟩
      simpa only [sub_add_eq_add_sub] using hc⟩
  else
    ⟨(d.1.1, d.1.2 + -1), by
      apply mem_boundaryDarts.mpr
      refine ⟨dart_occupied d, ?_⟩
      simpa only [normal_prev, sub_eq_add_neg] using hb⟩

private theorem prevDart_nextDart {A : Finset (ℤ × ℤ)} (d : BoundaryDart A) :
    prevDart (nextDart d) = d := by
  apply Subtype.ext
  by_cases hc : d.1.1 + normal d.1.2 + normal (d.1.2 + 1) ∈ A
  · have hdiag : (d.1.1 + normal d.1.2 + normal (d.1.2 + 1)) +
        normal (d.1.2 + -1) - normal d.1.2 = d.1.1 := by
      rw [normal_prev]
      abel
    simp only [nextDart, dite_eq_left hc, prevDart,
      hdiag, direction_prev_next, dite_eq_left (dart_occupied d)]
  · by_cases hb : d.1.1 + normal (d.1.2 + 1) ∈ A
    · have hdiag : d.1.1 + normal (d.1.2 + 1) + normal d.1.2 -
          normal (d.1.2 + 1) = d.1.1 + normal d.1.2 := by abel
      have hbase : d.1.1 + normal (d.1.2 + 1) - normal (d.1.2 + 1) = d.1.1 :=
        add_sub_cancel_right _ _
      have hp0 := hdiag ▸ dart_missing d
      simp only [nextDart, dite_eq_right hc, dite_eq_left hb, prevDart,
        dite_eq_right hp0, hbase, dite_eq_left (dart_occupied d)]
    · have hdiag : d.1.1 + normal (d.1.2 + 1) - normal (d.1.2 + 1 + 1) =
          d.1.1 + normal d.1.2 + normal (d.1.2 + 1) := by rw [normal_twice]; abel
      have hbase : d.1.1 - normal (d.1.2 + 1 + 1) = d.1.1 + normal d.1.2 := by
        rw [normal_twice, sub_neg_eq_add]
      have hp0 := hdiag ▸ hc
      have hp1 := hbase ▸ dart_missing d
      simp only [nextDart, dite_eq_right hc, dite_eq_right hb, prevDart,
        dite_eq_right hp0, dite_eq_right hp1, direction_next_prev]

private def boundaryPermutation (A : Finset (ℤ × ℤ)) : Equiv.Perm (BoundaryDart A) :=
  Equiv.ofBijective nextDart ⟨(Function.LeftInverse.injective prevDart_nextDart),
    Finite.surjective_of_injective (Function.LeftInverse.injective prevDart_nextDart)⟩

-- Corner k denotes the real point k - (1/2, 1/2).
private def corner (j : Fin 4) : ℤ × ℤ := ![(1, 0), (1, 1), (0, 1), (0, 0)] j

private theorem corner_next (j : Fin 4) : corner (j + 1) = corner j + normal (j + 1) := by
  fin_cases j <;> decide

private theorem corner_prev (j : Fin 4) : corner (j + -1) + normal j = corner j := by
  fin_cases j <;> decide

private def tailCorner {A : Finset (ℤ × ℤ)} (d : BoundaryDart A) := d.1.1 + corner d.1.2
private def headCorner {A : Finset (ℤ × ℤ)} (d : BoundaryDart A) :=
  tailCorner d + normal (d.1.2 + 1)

private theorem tailCorner_nextDart {A : Finset (ℤ × ℤ)} (d : BoundaryDart A) :
    tailCorner (nextDart d) = headCorner d := by
  simp only [nextDart, tailCorner, headCorner]
  split_ifs with hc hb
  · change d.1.1 + normal d.1.2 + normal (d.1.2 + 1) + corner (d.1.2 + -1) = _
    rw [show d.1.1 + normal d.1.2 + normal (d.1.2 + 1) + corner (d.1.2 + -1) =
      d.1.1 + (corner (d.1.2 + -1) + normal d.1.2) + normal (d.1.2 + 1) by abel,
      corner_prev]
  · change d.1.1 + normal (d.1.2 + 1) + corner d.1.2 = _
    abel
  · change d.1.1 + corner (d.1.2 + 1) = _
    rw [corner_next, add_assoc]

private theorem sum_boundary_divergence {A : Finset (ℤ × ℤ)}
    (I : BoundaryDart A → ℤ) (hI : ∀ d, I (nextDart d) = I d)
    (f : ℤ × ℤ → ℤ) :
    ∑ d, I d * (f (headCorner d) - f (tailCorner d)) = 0 := by
  have hsum := Equiv.sum_comp (boundaryPermutation A) (fun d => I d * f (tailCorner d))
  change (∑ d, I (nextDart d) * f (tailCorner (nextDart d))) =
    ∑ d, I d * f (tailCorner d) at hsum
  simp only [hI, tailCorner_nextDart] at hsum
  simp only [mul_sub, Finset.sum_sub_distrib, hsum, sub_self]

private def rayContribution {A : Finset (ℤ × ℤ)} (d : BoundaryDart A) (a : ℤ × ℤ) : ℤ :=
  if d.1.2 = 0 then
    if d.1.1.2 = a.2 ∧ a.1 < d.1.1.1 + 1 then 1 else 0
  else if d.1.2 = 2 then
    if d.1.1.2 = a.2 ∧ a.1 < d.1.1.1 then -1 else 0
  else 0

private def dartWeight {A : Finset (ℤ × ℤ)} (I : BoundaryDart A → ℤ)
    (a : ℤ × ℤ) (j : Fin 4) : ℤ :=
  if h : (a, j) ∈ boundaryDarts A then I ⟨(a, j), h⟩ else 0

private theorem sum_dart_indicator {A : Finset (ℤ × ℤ)} (I : BoundaryDart A → ℤ)
    (a : ℤ × ℤ) (j : Fin 4) :
    (∑ d, if d.1 = (a, j) then I d else 0) = dartWeight I a j := by
  classical
  by_cases h : (a, j) ∈ boundaryDarts A
  · rw [dartWeight, dite_eq_left h]
    have he := Fintype.sum_eq_single (f := fun d : BoundaryDart A =>
      if d.1 = (a, j) then I d else 0) (⟨(a, j), h⟩ : BoundaryDart A)
      (by
        intro d hd
        have hne : d.1 ≠ (a, j) := fun he => hd (Subtype.ext he)
        simp only [hne, ite_false])
    simpa using he
  · rw [dartWeight, dite_eq_right h]
    apply Finset.sum_eq_zero
    intro d _
    have hd : d.1 ≠ (a, j) := by intro he; exact h (he ▸ d.2)
    simp only [hd, ite_false]

private def dartHorizontal {A : Finset (ℤ × ℤ)} (I : BoundaryDart A → ℤ)
    (d : BoundaryDart A) : (ℤ × ℤ) →₀ ℤ :=
  if d.1.2 = 3 then Finsupp.single d.1.1 (I d)
  else if d.1.2 = 1 then Finsupp.single (d.1.1 + (0, 1)) (-I d) else 0

private def dartVertical {A : Finset (ℤ × ℤ)} (I : BoundaryDart A → ℤ)
    (d : BoundaryDart A) : (ℤ × ℤ) →₀ ℤ :=
  if d.1.2 = 0 then Finsupp.single (d.1.1 + (1, 0)) (I d)
  else if d.1.2 = 2 then Finsupp.single d.1.1 (-I d) else 0

private def contourHorizontal {A : Finset (ℤ × ℤ)} (I : BoundaryDart A → ℤ) :
    (ℤ × ℤ) →₀ ℤ := ∑ d, dartHorizontal I d

private def contourVertical {A : Finset (ℤ × ℤ)} (I : BoundaryDart A → ℤ) :
    (ℤ × ℤ) →₀ ℤ := ∑ d, dartVertical I d

private theorem contourVertical_apply {A : Finset (ℤ × ℤ)}
    (I : BoundaryDart A → ℤ) (k : ℤ × ℤ) :
    contourVertical I k = dartWeight I (k - (1, 0)) 0 - dartWeight I k 2 := by
  have he (d : BoundaryDart A) : dartVertical I d k =
      (if d.1 = (k - (1, 0), 0) then I d else 0) -
      (if d.1 = (k, 2) then I d else 0) := by
    obtain ⟨⟨b, j⟩, hd⟩ := d
    have hbk : k = b + (1, 0) ↔ b = k - (1, 0) := by
      constructor <;> intro h <;> rw [h] <;> simp
    fin_cases j <;> simp [dartVertical, Finsupp.single_apply, hbk, eq_comm]
  simp only [contourVertical, Finsupp.finsetSum_apply, he, Finset.sum_sub_distrib,
    sum_dart_indicator]

private theorem contourHorizontal_apply {A : Finset (ℤ × ℤ)}
    (I : BoundaryDart A → ℤ) (k : ℤ × ℤ) :
    contourHorizontal I k = dartWeight I k 3 - dartWeight I (k - (0, 1)) 1 := by
  have he (d : BoundaryDart A) : dartHorizontal I d k =
      (if d.1 = (k, 3) then I d else 0) -
      (if d.1 = (k - (0, 1), 1) then I d else 0) := by
    obtain ⟨⟨b, j⟩, hd⟩ := d
    have hbk : k = b + (0, 1) ↔ b = k - (0, 1) := by
      constructor <;> intro h <;> rw [h] <;> simp
    fin_cases j <;> simp [dartHorizontal, Finsupp.single_apply, hbk, eq_comm]
  simp only [contourHorizontal, Finsupp.finsetSum_apply, he, Finset.sum_sub_distrib,
    sum_dart_indicator]

private theorem contourFlow {A : Finset (ℤ × ℤ)}
    (I : BoundaryDart A → ℤ) (hI : ∀ d, I (nextDart d) = I d) (k : ℤ × ℤ) :
    contourHorizontal I k + contourVertical I k - contourHorizontal I (k - (1, 0)) -
      contourVertical I (k - (0, 1)) = 0 := by
  have he (d : BoundaryDart A) :
      dartHorizontal I d k + dartVertical I d k - dartHorizontal I d (k - (1, 0)) -
        dartVertical I d (k - (0, 1)) =
      -(I d * ((if headCorner d = k then 1 else 0) -
        (if tailCorner d = k then 1 else 0))) := by
    obtain ⟨⟨b, j⟩, hd⟩ := d
    fin_cases j <;>
      simp [dartHorizontal, dartVertical, Finsupp.single_apply, headCorner,
        tailCorner, corner, normal, Prod.ext_iff] <;>
      split_ifs <;> simp_all <;> omega
  simp only [contourHorizontal, contourVertical, Finsupp.finsetSum_apply,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, he, Finset.sum_neg_distrib]
  rw [sum_boundary_divergence I hI (fun a => if a = k then 1 else 0), neg_zero]

private def windingPotential {A : Finset (ℤ × ℤ)} (I : BoundaryDart A → ℤ)
    (a : ℤ × ℤ) : ℤ := ∑ d, I d * rayContribution d a

private theorem windingPotential_eq_ray {A : Finset (ℤ × ℤ)}
    (I : BoundaryDart A → ℤ) (a : ℤ × ℤ) :
    windingPotential I a = integerContourRayPotential (contourVertical I) a := by
  have he (d : BoundaryDart A) : integerContourRayPotential (dartVertical I d) a =
      I d * rayContribution d a := by
    by_cases hj : d.1.2 = 0
    · simp [dartVertical, hj, integerContourRayPotential, Finsupp.sum_single_index,
        rayContribution, mul_ite]
    · by_cases hj' : d.1.2 = 2
      · rw [dartVertical, ite_eq_right hj, ite_eq_left hj', integerContourRayPotential,
          Finsupp.sum_single_index (by simp)]
        simp only [rayContribution, ite_eq_right hj, ite_eq_left hj', mul_ite,
          mul_neg, mul_one, mul_zero]
      · simp [dartVertical, hj, hj', integerContourRayPotential, rayContribution]
  unfold contourVertical integerContourRayPotential
  rw [← Finsupp.sum_finsetSum_index (by intro k; simp)
    (by intro k m n; split_ifs <;> rfl)]
  exact (Finset.sum_congr rfl (fun d _ => he d)).symm

private theorem windingPotential_horizontal {A : Finset (ℤ × ℤ)}
    (I : BoundaryDart A → ℤ) (a : ℤ × ℤ) :
    windingPotential I a - windingPotential I (a + (1, 0)) =
      dartWeight I a 0 - dartWeight I (a + (1, 0)) 2 := by
  have he := integerContourRayPotential_east (contourVertical I) a
  rw [← windingPotential_eq_ray, ← windingPotential_eq_ray, contourVertical_apply,
    add_sub_cancel_right] at he
  omega

private theorem windingPotential_vertical {A : Finset (ℤ × ℤ)}
    (I : BoundaryDart A → ℤ) (hI : ∀ d, I (nextDart d) = I d) (a : ℤ × ℤ) :
    windingPotential I a - windingPotential I (a + (0, 1)) =
      dartWeight I a 1 - dartWeight I (a + (0, 1)) 3 := by
  have he := integerContourRayPotential_north (contourHorizontal I) (contourVertical I)
    (contourFlow I hI) a
  rw [← windingPotential_eq_ray, ← windingPotential_eq_ray, contourHorizontal_apply,
    add_sub_cancel_right] at he
  omega

private theorem windingPotential_normal {A : Finset (ℤ × ℤ)}
    (I : BoundaryDart A → ℤ) (hI : ∀ d, I (nextDart d) = I d)
    (a : ℤ × ℤ) (j : Fin 4) :
    windingPotential I a - windingPotential I (a + normal j) =
      dartWeight I a j - dartWeight I (a + normal j) (j + 1 + 1) := by
  fin_cases j
  · simpa [normal] using windingPotential_horizontal I a
  · simpa [normal] using windingPotential_vertical I hI a
  · have he := windingPotential_horizontal I (a + (-1, 0))
    simp only [show a + (-1, 0) + (1, 0) = a by ext <;> simp] at he
    simpa [normal] using (show windingPotential I a - windingPotential I (a + (-1, 0)) =
      dartWeight I a 2 - dartWeight I (a + (-1, 0)) 0 by omega)
  · have he := windingPotential_vertical I hI (a + (0, -1))
    simp only [show a + (0, -1) + (0, 1) = a by ext <;> simp] at he
    simpa [normal] using (show windingPotential I a - windingPotential I (a + (0, -1)) =
      dartWeight I a 3 - dartWeight I (a + (0, -1)) 1 by omega)

private theorem dartWeight_missing {A : Finset (ℤ × ℤ)} (I : BoundaryDart A → ℤ)
    {a : ℤ × ℤ} (ha : a ∉ A) (j : Fin 4) : dartWeight I a j = 0 := by
  simp [dartWeight, mem_boundaryDarts, ha]

private theorem windingPotential_normal_eq_of_same_membership {A : Finset (ℤ × ℤ)}
    (I : BoundaryDart A → ℤ) (hI : ∀ d, I (nextDart d) = I d)
    (a : ℤ × ℤ) (j : Fin 4) (ha : a ∈ A ↔ a + normal j ∈ A) :
    windingPotential I a = windingPotential I (a + normal j) := by
  have he := windingPotential_normal I hI a j
  have hzero : dartWeight I a j = 0 := by
    simp only [dartWeight, mem_boundaryDarts]
    split_ifs with hd
    · exact False.elim (hd.2 (ha.mp hd.1))
    · rfl
  have hzero' : dartWeight I (a + normal j) (j + 1 + 1) = 0 := by
    simp only [dartWeight, mem_boundaryDarts, normal_twice, add_neg_cancel_right]
    split_ifs with hd
    · exact False.elim (hd.2 (ha.mpr hd.1))
    · rfl
  rw [hzero, hzero', sub_self] at he
  omega

private theorem windingPotential_diagonal_eq_of_mem {A : Finset (ℤ × ℤ)}
    (I : BoundaryDart A → ℤ) (hI : ∀ d, I (nextDart d) = I d)
    (a : ℤ × ℤ) (j : Fin 4) (ha : a ∈ A)
    (hc : a + normal j + normal (j + 1) ∈ A) :
    windingPotential I a = windingPotential I (a + normal j + normal (j + 1)) := by
  by_cases hq : a + normal j ∈ A
  · exact (windingPotential_normal_eq_of_same_membership I hI a j
      (by simp only [ha, hq])).trans
      (windingPotential_normal_eq_of_same_membership I hI (a + normal j) (j + 1)
        (by simp only [hq, hc]))
  · let d : BoundaryDart A := ⟨(a, j), mem_boundaryDarts.mpr ⟨ha, hq⟩⟩
    have hi := hI d
    change I (nextDart d) = I d at hi
    have hw : dartWeight I (a + normal j + normal (j + 1)) (j + 1 + 1 + 1) =
        dartWeight I a j := by
      have hj : j + 1 + 1 + 1 = j + -1 := by fin_cases j <;> decide
      have he : nextDart d = ⟨(a + normal j + normal (j + 1), j + -1),
          mem_boundaryDarts.mpr ⟨hc, by simpa [normal_prev] using hq⟩⟩ := by
        simp only [nextDart, d, hc, dite_eq_left]
      simp only [dartWeight, mem_boundaryDarts, ha, hq, not_false_eq_true, and_self,
        dite_eq_left, hj]
      rw [← hi, he]
      simp only [hc, normal_prev, add_neg_cancel_right, hq, not_false_eq_true, and_self,
        dite_eq_left]
    have he := windingPotential_normal I hI a j
    have he' := windingPotential_normal I hI (a + normal j) (j + 1)
    rw [dartWeight_missing I hq, hw] at he'
    rw [dartWeight_missing I hq] at he
    omega

private theorem near_cases (a b : ℤ × ℤ) (hab : IsIntegerCellNear a b) :
    b = a ∨ ∃ j : Fin 4, b = a + normal j ∨ b = a + normal j + normal (j + 1) := by
  have hx := abs_le.mp hab.1
  have hy := abs_le.mp hab.2
  have hc : b = a ∨ b = a + (1, 0) ∨ b = a + (0, 1) ∨ b = a + (-1, 0) ∨
      b = a + (0, -1) ∨ b = a + (1, 1) ∨ b = a + (-1, 1) ∨
      b = a + (-1, -1) ∨ b = a + (1, -1) := by
    simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add]
    omega
  rcases hc with he | he | he | he | he | he | he | he | he
  · exact Or.inl he
  · exact Or.inr ⟨0, Or.inl (by simpa [normal] using he)⟩
  · exact Or.inr ⟨1, Or.inl (by simpa [normal] using he)⟩
  · exact Or.inr ⟨2, Or.inl (by simpa [normal] using he)⟩
  · exact Or.inr ⟨3, Or.inl (by simpa [normal] using he)⟩
  · exact Or.inr ⟨0, Or.inr (by simpa [normal, add_assoc] using he)⟩
  · exact Or.inr ⟨1, Or.inr (by simpa [normal, add_assoc] using he)⟩
  · exact Or.inr ⟨2, Or.inr (by simpa [normal, add_assoc] using he)⟩
  · exact Or.inr ⟨3, Or.inr (by simpa [normal, add_assoc] using he)⟩

private theorem windingPotential_eq_of_occupied_near {A : Finset (ℤ × ℤ)}
    (I : BoundaryDart A → ℤ) (hI : ∀ d, I (nextDart d) = I d)
    (a b : ℤ × ℤ) (ha : a ∈ A) (hb : b ∈ A) (hab : IsIntegerCellNear a b) :
    windingPotential I a = windingPotential I b := by
  rcases near_cases a b hab with rfl | ⟨j, he | he⟩
  · rfl
  · rw [he]
    exact windingPotential_normal_eq_of_same_membership I hI a j
      (by rw [← he]; simp only [ha, hb])
  · rw [he]
    exact windingPotential_diagonal_eq_of_mem I hI a j ha (he ▸ hb)

private theorem windingPotential_eq_of_missing_adj {A : Finset (ℤ × ℤ)}
    (I : BoundaryDart A → ℤ) (hI : ∀ d, I (nextDart d) = I d)
    (a b : ℤ × ℤ) (ha : a ∉ A) (hb : b ∉ A)
    (hab : (SimpleGraph.addCayley {(1, 0), (0, 1)}).Adj a b) :
    windingPotential I a = windingPotential I b := by
  obtain ⟨_, c, hc, he⟩ := (SimpleGraph.addCayley_adj' _ a b).mp hab
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
  rcases hc with rfl | rfl
  · rcases he with he | he
    · simpa [normal, he] using windingPotential_normal_eq_of_same_membership I hI a 0
        (by simp [normal, ha, he, hb])
    · simpa [normal, ← he] using
        (windingPotential_normal_eq_of_same_membership I hI b 0
          (by simp [normal, ← he, ha, hb])).symm
  · rcases he with he | he
    · simpa [normal, he] using windingPotential_normal_eq_of_same_membership I hI a 1
        (by simp [normal, ha, he, hb])
    · simpa [normal, ← he] using
        (windingPotential_normal_eq_of_same_membership I hI b 1
          (by simp [normal, ← he, ha, hb])).symm

private theorem exists_windingPotential_zero {A : Finset (ℤ × ℤ)}
    (I : BoundaryDart A → ℤ) : ∃ a : ℤ × ℤ, a ∉ A ∧ windingPotential I a = 0 := by
  let n : ℕ := A.sup (fun b => b.1.natAbs)
  let N : ℤ := (n : ℤ) + 2
  have hbound (b : ℤ × ℤ) (hb : b ∈ A) : b.1 + 1 < N := by
    have hle := Finset.le_sup (f := fun b : ℤ × ℤ => b.1.natAbs) hb
    have hi : b.1 ≤ (b.1.natAbs : ℤ) := by rw [Int.natCast_natAbs]; exact le_abs_self _
    have hi' : (b.1.natAbs : ℤ) ≤ (n : ℤ) := by
      exact_mod_cast hle
    dsimp [N]
    omega
  refine ⟨(N, 0), ?_, ?_⟩
  · intro ha
    have := hbound (N, 0) ha
    simp at this
  · unfold windingPotential
    apply Finset.sum_eq_zero
    intro d _
    have hd := hbound d.1.1 (dart_occupied d)
    unfold rayContribution
    split_ifs <;> omega

private theorem eq_of_reachable {V W : Type*} {Γ : SimpleGraph V}
    (f : V → W) (hf : ∀ ⦃v w⦄, Γ.Adj v w → f v = f w) {v w : V}
    (h : Γ.Reachable v w) : f v = f w :=
  Relation.reflTransGen_le_of_equivalence_of_le (Setoid.ker f).iseqv
    (fun _ _ h => hf h) v w ((SimpleGraph.reachable_iff_reflTransGen v w).mp h)

private theorem windingPotential_eq_of_missing_reachable {A : Finset (ℤ × ℤ)}
    (I : BoundaryDart A → ℤ) (hI : ∀ d, I (nextDart d) = I d)
    {a b : {a : ℤ × ℤ // a ∉ A}}
    (hab : SimpleGraph.Reachable
      ((SimpleGraph.addCayley {(1, 0), (0, 1)}).induce {a : ℤ × ℤ | a ∉ A}) a b) :
    windingPotential I a.1 = windingPotential I b.1 := by
  exact eq_of_reachable
    (Γ := (SimpleGraph.addCayley {(1, 0), (0, 1)}).induce {a : ℤ × ℤ | a ∉ A})
    (fun a => windingPotential I a.1)
    (fun {a b} h => windingPotential_eq_of_missing_adj I hI _ _ a.2 b.2 h) hab

private theorem windingPotential_eq_of_occupied_reachable {A : Finset (ℤ × ℤ)}
    (I : BoundaryDart A → ℤ) (hI : ∀ d, I (nextDart d) = I d)
    {a b : {a : ℤ × ℤ // a ∈ A}}
    (hab : (integerCellContactGraph A).Reachable a b) :
    windingPotential I a.1 = windingPotential I b.1 := by
  exact eq_of_reachable (Γ := integerCellContactGraph A) (fun a => windingPotential I a.1)
    (fun {a b} h => windingPotential_eq_of_occupied_near I hI _ _ a.2 b.2 h.2) hab

private theorem windingPotential_missing_zero {A : Finset (ℤ × ℤ)}
    (hSC : IsSimplyConnected (integerClosedCellUnion A))
    (I : BoundaryDart A → ℤ) (hI : ∀ d, I (nextDart d) = I d)
    {a : ℤ × ℤ} (ha : a ∉ A) : windingPotential I a = 0 := by
  obtain ⟨b, hb, he⟩ := exists_windingPotential_zero I
  exact (windingPotential_eq_of_missing_reachable I hI
    ((integerCellComplement_connected_of_isSimplyConnected A hSC).preconnected
      ⟨a, ha⟩ ⟨b, hb⟩)).trans he

private theorem dartWeight_self {A : Finset (ℤ × ℤ)} (I : BoundaryDart A → ℤ)
    (d : BoundaryDart A) : dartWeight I d.1.1 d.1.2 = I d := by
  obtain ⟨⟨a, j⟩, hd⟩ := d
  simp only [dartWeight, hd, dite_eq_left]

private theorem dart_value_eq_windingPotential {A : Finset (ℤ × ℤ)}
    (hSC : IsSimplyConnected (integerClosedCellUnion A))
    (I : BoundaryDart A → ℤ) (hI : ∀ d, I (nextDart d) = I d)
    (d : BoundaryDart A) : I d = windingPotential I d.1.1 := by
  have he := windingPotential_normal I hI d.1.1 d.1.2
  rw [windingPotential_missing_zero hSC I hI (dart_missing d), sub_zero,
    dartWeight_self, dartWeight_missing I (dart_missing d), sub_zero] at he
  exact he.symm

-- The orbit indicator has one constant winding value on all occupied cells.
private theorem boundaryPermutation_sameCycle {A : Finset (ℤ × ℤ)}
    (hSC : IsSimplyConnected (integerClosedCellUnion A)) (d e : BoundaryDart A) :
    (boundaryPermutation A).SameCycle d e := by
  classical
  let I : BoundaryDart A → ℤ := fun f =>
    if (boundaryPermutation A).SameCycle d f then 1 else 0
  have hI : ∀ f, I (nextDart f) = I f := by
    intro f
    change (if (boundaryPermutation A).SameCycle d (boundaryPermutation A f) then 1 else 0) = _
    simp only [Equiv.Perm.sameCycle_apply_right, I]
  have hde := windingPotential_eq_of_occupied_reachable I hI
    ((integerCellContactGraph_connected_of_isSimplyConnected A hSC).preconnected
      ⟨d.1.1, dart_occupied d⟩ ⟨e.1.1, dart_occupied e⟩)
  rw [← dart_value_eq_windingPotential hSC I hI d,
    ← dart_value_eq_windingPotential hSC I hI e] at hde
  have hd : I d = 1 := by simp [I, Equiv.Perm.SameCycle.refl]
  by_contra he
  have he' : I e = 0 := by simp [I, he]
  omega

private theorem near_normal (a : ℤ × ℤ) (j : Fin 4) :
    IsIntegerCellNear (a + normal j) a := by
  fin_cases j <;> simp [IsIntegerCellNear, normal]

private theorem near_diagonal (a : ℤ × ℤ) (j : Fin 4) :
    IsIntegerCellNear (a + normal j + normal (j + 1)) a := by
  fin_cases j <;> simp [IsIntegerCellNear, normal, add_assoc]

private theorem grid_adj_normal (a : ℤ × ℤ) (j : Fin 4) :
    (SimpleGraph.addCayley {(1, 0), (0, 1)}).Adj a (a + normal j) := by
  rw [SimpleGraph.addCayley_adj']
  refine ⟨?_, ?_⟩
  · fin_cases j <;> simp [normal, Prod.ext_iff]
  · fin_cases j
    · exact ⟨(1, 0), by simp, Or.inl rfl⟩
    · exact ⟨(0, 1), by simp, Or.inl rfl⟩
    · refine ⟨(1, 0), by simp, Or.inr ?_⟩
      change a = a + (-1, 0) + (1, 0)
      ext <;> simp
    · refine ⟨(0, 1), by simp, Or.inr ?_⟩
      change a = a + (0, -1) + (0, 1)
      ext <;> simp

private def dartExterior {A : Finset (ℤ × ℤ)} (d : BoundaryDart A) :
    integerExteriorBand A :=
  ⟨d.1.1 + normal d.1.2, dart_missing d, d.1.1, dart_occupied d,
    near_normal d.1.1 d.1.2⟩

private theorem collar_adj_of_normal {A : Finset (ℤ × ℤ)}
    (q r : integerExteriorBand A) (a : ℤ × ℤ) (ha : a ∈ A)
    (hq : IsIntegerCellNear q.1 a) (hr : IsIntegerCellNear r.1 a)
    (j : Fin 4) (he : r.1 = q.1 + normal j) :
    (integerExteriorCollarGraph A).Adj q r := by
  exact ⟨he ▸ grid_adj_normal q.1 j, a, ha, hq, hr⟩

private theorem dartExterior_next_reachable {A : Finset (ℤ × ℤ)} (d : BoundaryDart A) :
    (integerExteriorCollarGraph A).Reachable (dartExterior d) (dartExterior (nextDart d)) := by
  by_cases hc : d.1.1 + normal d.1.2 + normal (d.1.2 + 1) ∈ A
  · have he : dartExterior (nextDart d) = dartExterior d := by
      apply Subtype.ext
      change (nextDart d).1.1 + normal (nextDart d).1.2 = d.1.1 + normal d.1.2
      simp only [nextDart, dite_eq_left hc, normal_prev]
      abel
    rw [he]
  · by_cases hb : d.1.1 + normal (d.1.2 + 1) ∈ A
    · have he : (dartExterior (nextDart d)).1 =
          d.1.1 + normal d.1.2 + normal (d.1.2 + 1) := by
        change (nextDart d).1.1 + normal (nextDart d).1.2 = _
        simp only [nextDart, dite_eq_right hc, dite_eq_left hb]
        abel
      have hnear : IsIntegerCellNear (dartExterior (nextDart d)).1 d.1.1 := by
        rw [he]
        exact near_diagonal d.1.1 d.1.2
      exact (collar_adj_of_normal (dartExterior d) (dartExterior (nextDart d))
        d.1.1 (dart_occupied d) (near_normal d.1.1 d.1.2) hnear (d.1.2 + 1) he).reachable
    · let c : integerExteriorBand A :=
        ⟨d.1.1 + normal d.1.2 + normal (d.1.2 + 1), hc, d.1.1,
          dart_occupied d, near_diagonal _ _⟩
      have he : (dartExterior (nextDart d)).1 = d.1.1 + normal (d.1.2 + 1) := by
        change (nextDart d).1.1 + normal (nextDart d).1.2 = _
        simp only [nextDart, dite_eq_right hc, dite_eq_right hb]
      have h₁ : (integerExteriorCollarGraph A).Adj (dartExterior d) c :=
        collar_adj_of_normal (dartExterior d) c d.1.1 (dart_occupied d)
          (near_normal d.1.1 d.1.2) (near_diagonal d.1.1 d.1.2) (d.1.2 + 1) rfl
      have hnear : IsIntegerCellNear (dartExterior (nextDart d)).1 d.1.1 := by
        rw [he]
        exact near_normal d.1.1 (d.1.2 + 1)
      have he' : c.1 = (dartExterior (nextDart d)).1 + normal d.1.2 := by
        change d.1.1 + normal d.1.2 + normal (d.1.2 + 1) =
          (dartExterior (nextDart d)).1 + normal d.1.2
        rw [he]
        abel
      have h₂ : (integerExteriorCollarGraph A).Adj (dartExterior (nextDart d)) c :=
        collar_adj_of_normal (dartExterior (nextDart d)) c d.1.1 (dart_occupied d)
          hnear (near_diagonal d.1.1 d.1.2) d.1.2 he' 
      exact h₁.reachable.trans h₂.symm.reachable

private theorem dartExterior_reachable {A : Finset (ℤ × ℤ)}
    (hSC : IsSimplyConnected (integerClosedCellUnion A)) (d e : BoundaryDart A) :
    (integerExteriorCollarGraph A).Reachable (dartExterior d) (dartExterior e) := by
  obtain ⟨n, rfl⟩ := (boundaryPermutation_sameCycle hSC d e).exists_nat_pow_eq
  induction n with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ n ih =>
    have he : (boundaryPermutation A ^ (n + 1)) d =
        nextDart ((boundaryPermutation A ^ n) d) := by
      rw [pow_succ', Equiv.Perm.mul_apply]
      rfl
    rw [he]
    exact ih.trans (dartExterior_next_reachable _)

private theorem band_normal_reachable_dart {A : Finset (ℤ × ℤ)}
    (q : integerExteriorBand A) (a : ℤ × ℤ) (ha : a ∈ A) (j : Fin 4)
    (he : q.1 = a + normal j) :
    ∃ d : BoundaryDart A, (integerExteriorCollarGraph A).Reachable q (dartExterior d) := by
  have hq : a + normal j ∉ A := he ▸ q.2.1
  let d : BoundaryDart A := ⟨(a, j), mem_boundaryDarts.mpr ⟨ha, hq⟩⟩
  refine ⟨d, ?_⟩
  have hd : q = dartExterior d := Subtype.ext he
  rw [hd]

private theorem band_diagonal_reachable_dart {A : Finset (ℤ × ℤ)}
    (q : integerExteriorBand A) (a : ℤ × ℤ) (ha : a ∈ A) (j : Fin 4)
    (he : q.1 = a + normal j + normal (j + 1)) :
    ∃ d : BoundaryDart A, (integerExteriorCollarGraph A).Reachable q (dartExterior d) := by
  by_cases hb : a + normal j ∈ A
  · exact band_normal_reachable_dart q (a + normal j) hb (j + 1) he
  · let d : BoundaryDart A := ⟨(a, j), mem_boundaryDarts.mpr ⟨ha, hb⟩⟩
    have hnear : IsIntegerCellNear q.1 a := he ▸ near_diagonal a j
    refine ⟨d, ?_⟩
    exact (collar_adj_of_normal (dartExterior d) q a ha (near_normal a j) hnear
      (j + 1) he).symm.reachable

private theorem band_reachable_dart {A : Finset (ℤ × ℤ)} (q : integerExteriorBand A) :
    ∃ d : BoundaryDart A, (integerExteriorCollarGraph A).Reachable q (dartExterior d) := by
  obtain ⟨a, ha, hnear⟩ := q.2.2
  have hnear' : IsIntegerCellNear a q.1 := by
    simpa only [IsIntegerCellNear, abs_sub_comm] using hnear
  rcases near_cases a q.1 hnear' with he | ⟨j, he | he⟩
  · exact False.elim (q.2.1 (he ▸ ha))
  · exact band_normal_reachable_dart q a ha j he
  · exact band_diagonal_reachable_dart q a ha j he

private theorem exteriorCollarGraph_preconnected {A : Finset (ℤ × ℤ)}
    (hSC : IsSimplyConnected (integerClosedCellUnion A)) :
    (integerExteriorCollarGraph A).Preconnected := by
  intro q r
  obtain ⟨d, hd⟩ := band_reachable_dart q
  obtain ⟨e, he⟩ := band_reachable_dart r
  exact hd.trans ((dartExterior_reachable hSC d e).trans he.symm)

private theorem boundaryDart_nonempty {A : Finset (ℤ × ℤ)} (hA : A.Nonempty) :
    Nonempty (BoundaryDart A) := by
  obtain ⟨a, ha, hmax⟩ := A.exists_max_image (fun a => a.1) hA
  have hq : a + normal 0 ∉ A := by
    intro h
    have hm := hmax (a + normal 0) h
    simp [normal] at hm
  exact ⟨⟨(a, 0), mem_boundaryDarts.mpr ⟨ha, hq⟩⟩⟩

/-- The graph of missing cell centers near a simply connected finite closed-cell
union is connected through four-neighbor edges having a common occupied-cell
support. This is auxiliary exterior-collar geometry for SCP10, Theorem 6.9. -/
theorem integerExteriorCollarGraph_connected_of_isSimplyConnected
    (A : Finset (ℤ × ℤ)) (hSC : IsSimplyConnected (integerClosedCellUnion A)) :
    (integerExteriorCollarGraph A).Connected := by
  obtain ⟨a⟩ := (integerCellContactGraph_connected_of_isSimplyConnected A hSC).nonempty
  obtain ⟨d⟩ := boundaryDart_nonempty ⟨a.1, a.2⟩
  exact { preconnected := exteriorCollarGraph_preconnected hSC, nonempty := ⟨dartExterior d⟩ }

end TNLean.PEPS
