/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.IsolatedStars

/-!
# The eight closed cones of the normalized fan

The eight elementary triangles of the normalized square `[-1, 1]²`, divided
at its corners and side midpoints, span eight closed cones with apex at the
origin. With the cross product `a × b = a₁ b₂ - a₂ b₁`, the cone of a slot with
initial direction `a` and final direction `b` is `{y | 0 ≤ a × y, 0 ≤ y × b}`;
here `a × b = 1`, and `b` is the initial direction of the next slot.

We record that every vector lies in some cone, that two cones which are not
consecutive meet only at the origin, that two consecutive cones meet exactly
in the ray of their common direction, and that on a cone the sup norm is the
linear functional `y × b + a × y`. Consequently the closed triangle of
half-side `r` about `c` is the set of points `x` with `x - c` in the cone and
`‖x - c‖ ≤ r`, its interior is given by the strict inequalities, and every
point of a closed cone is a limit of points of the open cone.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:initial-stars`, lines 340–348, and
`geometry:repair-induction`, lines 506–514.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Written from the manuscript; no upstream Lean text is reused.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The cross product `a × b = a₁ b₂ - a₂ b₁` of two plane vectors.
Auxiliary to area-law Section 11, lines 340–348. -/
def repairCross (a b : ℝ × ℝ) : ℝ :=
  a.1 * b.2 - a.2 * b.1

/-- The initial direction of an elementary wedge of the normalized fan.
Auxiliary to area-law Section 11, lines 340–348. -/
def repairFanStart (s : RepairFanSlot) : ℝ × ℝ :=
  cellFanStart (-1, -1) 1 (0, 0) repairFanSplit s

theorem repairFanStart_eq (s : RepairFanSlot) :
    repairFanStart s = cellFanSideVector s.1 ((s.2.val : ℝ) - 1) := by
  rcases s with ⟨i, j⟩
  rw [repairFanStart, cellFanStart_eq]
  simp [cellFanCenter, repairFanSplit]

theorem repairFanDirection_eq (s : RepairFanSlot) :
    repairFanDirection s = cellFanSideVector s.1 (s.2.val : ℝ) := by
  rcases s with ⟨i, j⟩
  rw [repairFanDirection, cellFanEnd_eq]
  simp [cellFanCenter, repairFanSplit]

/-- The final direction of a wedge is the initial direction of the next one.
Auxiliary to area-law Section 11, lines 340–348. -/
theorem repairFanStart_next (s : RepairFanSlot) :
    repairFanStart (cellFanNext s) = repairFanDirection s :=
  (cellFanEnd_eq_cellFanStart_next (-1, -1) 1 (0, 0) s).symm

theorem repairCross_start_direction (s : RepairFanSlot) :
    repairCross (repairFanStart s) (repairFanDirection s) = 1 := by
  rw [repairFanStart_eq, repairFanDirection_eq]
  rcases s with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> norm_num [cellFanSideVector, repairCross]

theorem repairFanDirection_ne_zero (s : RepairFanSlot) : repairFanDirection s ≠ 0 :=
  (repairFanDirection_mem s).1

/-- The perimeter position of a slot, from `0` to `7`.
Auxiliary to area-law Section 11, lines 340–348. -/
def repairSlotCode (s : RepairFanSlot) : ℕ :=
  2 * s.1.val + s.2.val

theorem repairSlotCode_lt (s : RepairFanSlot) : repairSlotCode s < 8 := by
  rcases s with ⟨i, j⟩
  have hi := i.isLt
  have hj := j.isLt
  simp only [repairFanSplit, ite_true] at hj
  simp only [repairSlotCode]
  omega

theorem repairSlotCode_next (s : RepairFanSlot) :
    repairSlotCode (cellFanNext s) = (repairSlotCode s + 1) % 8 := by
  rcases s with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> rfl

theorem repairSlotCode_injective : Function.Injective repairSlotCode := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  have hj := j.isLt
  have hj' := j'.isLt
  simp only [repairFanSplit, ite_true] at hj hj'
  simp only [repairSlotCode] at h
  have h₁ : i = i' := Fin.ext (by omega)
  subst h₁
  have h₂ : j = j' := Fin.ext (by omega)
  subst h₂
  rfl

/-- No slot is its own perimeter successor.
Auxiliary to area-law Section 11, lines 340–348. -/
theorem cellFanNext_ne_self (s : RepairFanSlot) : cellFanNext s ≠ s := by
  intro h
  have := congrArg repairSlotCode h
  rw [repairSlotCode_next] at this
  have := repairSlotCode_lt s
  omega

/-- The closed cone of an elementary wedge, with apex at the origin.
Auxiliary to area-law Section 11, lines 340–348. -/
def repairFanCone (s : RepairFanSlot) : Set (ℝ × ℝ) :=
  {y | 0 ≤ repairCross (repairFanStart s) y ∧ 0 ≤ repairCross y (repairFanDirection s)}

/-- The open cone of an elementary wedge.
Auxiliary to area-law Section 11, lines 340–348. -/
def repairFanOpenCone (s : RepairFanSlot) : Set (ℝ × ℝ) :=
  {y | 0 < repairCross (repairFanStart s) y ∧ 0 < repairCross y (repairFanDirection s)}

theorem repairFanOpenCone_subset (s : RepairFanSlot) :
    repairFanOpenCone s ⊆ repairFanCone s :=
  fun _ h ↦ ⟨h.1.le, h.2.le⟩

theorem smul_mem_repairFanCone {s : RepairFanSlot} {y : ℝ × ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hy : y ∈ repairFanCone s) : t • y ∈ repairFanCone s := by
  simp only [repairFanCone, repairCross, Set.mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] at hy ⊢
  constructor <;> nlinarith [mul_nonneg ht hy.1, mul_nonneg ht hy.2]

/-- A vector with vanishing cross product against `d` is a multiple of `d`,
with coefficient read by any `a` with `a × d = 1`.
Auxiliary to area-law Section 11, lines 340–348. -/
theorem eq_repairCross_smul_of_repairCross_eq_zero {a d y : ℝ × ℝ}
    (had : repairCross a d = 1) (hy : repairCross y d = 0) :
    y = repairCross a y • d := by
  simp only [repairCross] at had hy ⊢
  ext
  · simp only [Prod.smul_fst, smul_eq_mul]
    linear_combination (-y.1) * had + a.1 * hy
  · simp only [Prod.smul_snd, smul_eq_mul]
    linear_combination (-y.2) * had + a.2 * hy

/-- Membership in the ray of `d`, for `a × d = 1`.
Auxiliary to area-law Section 11, lines 340–348. -/
theorem sameRay_iff_repairCross {a d y : ℝ × ℝ} (had : repairCross a d = 1) :
    SameRay ℝ y d ↔ repairCross y d = 0 ∧ 0 ≤ repairCross a y := by
  have hd : d ≠ 0 := by
    rintro rfl
    simp [repairCross] at had
  constructor
  · intro h
    obtain ⟨r, hr, rfl⟩ := h.symm.exists_nonneg_left hd
    refine ⟨?_, ?_⟩
    · simp only [repairCross, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    · have : repairCross a (r • d) = r * repairCross a d := by
        simp only [repairCross, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        ring
      rw [this, had, mul_one]
      exact hr
  · rintro ⟨h0, hpos⟩
    rw [eq_repairCross_smul_of_repairCross_eq_zero had h0]
    exact SameRay.sameRay_nonneg_smul_left d hpos

/-- Two consecutive cones meet exactly in the ray of their common direction.
Auxiliary to area-law Section 11, lines 340–348 and 497–504. -/
theorem mem_repairFanCone_inter_next_iff (s : RepairFanSlot) (y : ℝ × ℝ) :
    (y ∈ repairFanCone s ∧ y ∈ repairFanCone (cellFanNext s)) ↔
      SameRay ℝ y (repairFanDirection s) := by
  have h1 := repairCross_start_direction s
  have h2 := repairCross_start_direction (cellFanNext s)
  rw [repairFanStart_next] at h2
  rw [sameRay_iff_repairCross h1]
  simp only [repairFanCone, Set.mem_ofPred_eq, repairFanStart_next]
  constructor
  · rintro ⟨⟨ha, hb⟩, hc, -⟩
    refine ⟨le_antisymm ?_ hb, ha⟩
    simp only [repairCross] at hc ⊢
    linarith
  · rintro ⟨h0, hpos⟩
    have hy := eq_repairCross_smul_of_repairCross_eq_zero h1 h0
    set r := repairCross (repairFanStart s) y
    refine ⟨⟨hpos, h0.ge⟩, ?_, ?_⟩
    · rw [hy]
      simp only [repairCross, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring_nf
      rfl
    · rw [hy]
      have : repairCross (r • repairFanDirection s) (repairFanDirection (cellFanNext s)) =
          r * repairCross (repairFanDirection s) (repairFanDirection (cellFanNext s)) := by
        simp only [repairCross, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        ring
      rw [this, h2, mul_one]
      exact hpos

/-- Cones that are neither equal nor consecutive meet only at the origin.
Auxiliary to area-law Section 11, lines 340–348 and 497–504. -/
theorem eq_zero_of_mem_repairFanCone {s u : RepairFanSlot} {y : ℝ × ℝ} (hsu : s ≠ u)
    (h₁ : u ≠ cellFanNext s) (h₂ : s ≠ cellFanNext u)
    (hs : y ∈ repairFanCone s) (hu : y ∈ repairFanCone u) : y = 0 := by
  simp only [repairFanCone, Set.mem_ofPred_eq, repairFanStart_eq, repairFanDirection_eq]
    at hs hu
  rcases s with ⟨i, j⟩
  rcases u with ⟨i', j'⟩
  fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j' <;>
    first
    | exact absurd rfl hsu
    | exact absurd rfl h₁
    | exact absurd rfl h₂
    | (simp only [cellFanSideVector, repairCross] at hs hu
       norm_num at hs hu
       ext <;> simp <;> linarith [hs.1, hs.2, hu.1, hu.2])

/-- Every plane vector lies in one of the eight closed cones.
Auxiliary to area-law Section 11, lines 340–348. -/
theorem exists_mem_repairFanCone (y : ℝ × ℝ) : ∃ s, y ∈ repairFanCone s := by
  simp only [repairFanCone, Set.mem_ofPred_eq, repairFanStart_eq, repairFanDirection_eq]
  rcases le_total 0 y.2 with h2 | h2 <;> rcases le_total 0 y.1 with h1 | h1
  · rcases le_total y.2 y.1 with h | h
    · exact ⟨⟨0, 1⟩, by
        norm_num [cellFanSideVector, repairCross, repairFanSplit]
        constructor <;> linarith⟩
    · exact ⟨⟨1, 0⟩, by
        norm_num [cellFanSideVector, repairCross, repairFanSplit]
        constructor <;> linarith⟩
  · rcases le_total y.2 (-y.1) with h | h
    · exact ⟨⟨2, 0⟩, by
        norm_num [cellFanSideVector, repairCross, repairFanSplit]
        constructor <;> linarith⟩
    · exact ⟨⟨1, 1⟩, by
        norm_num [cellFanSideVector, repairCross, repairFanSplit]
        constructor <;> linarith⟩
  · rcases le_total (-y.1) y.2 with h | h
    · exact ⟨⟨0, 0⟩, by
        norm_num [cellFanSideVector, repairCross, repairFanSplit]
        constructor <;> linarith⟩
    · exact ⟨⟨3, 1⟩, by
        norm_num [cellFanSideVector, repairCross, repairFanSplit]
        constructor <;> linarith⟩
  · rcases le_total y.1 y.2 with h | h
    · exact ⟨⟨2, 1⟩, by
        norm_num [cellFanSideVector, repairCross, repairFanSplit]
        constructor <;> linarith⟩
    · exact ⟨⟨3, 0⟩, by
        norm_num [cellFanSideVector, repairCross, repairFanSplit]
        constructor <;> linarith⟩

/-- On a closed cone the sup norm is the linear functional `y × b + a × y`.
Auxiliary to area-law Section 11, lines 340–348. -/
theorem norm_eq_of_mem_repairFanCone {s : RepairFanSlot} {y : ℝ × ℝ}
    (hy : y ∈ repairFanCone s) :
    ‖y‖ = repairCross y (repairFanDirection s) + repairCross (repairFanStart s) y := by
  simp only [repairFanCone, Set.mem_ofPred_eq, repairFanStart_eq, repairFanDirection_eq] at hy
  rw [repairFanStart_eq, repairFanDirection_eq, Prod.norm_def, Real.norm_eq_abs,
    Real.norm_eq_abs]
  rcases s with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp only [cellFanSideVector, repairCross] at hy ⊢ <;> norm_num at hy ⊢ <;>
    refine le_antisymm (max_le (abs_le.mpr ⟨by linarith, by linarith⟩)
      (abs_le.mpr ⟨by linarith, by linarith⟩)) ?_ <;>
    first
    | exact le_max_of_le_left (le_trans (by linarith) (le_abs_self _))
    | exact le_max_of_le_left (le_trans (by linarith) (neg_le_abs _))
    | exact le_max_of_le_right (le_trans (by linarith) (le_abs_self _))
    | exact le_max_of_le_right (le_trans (by linarith) (neg_le_abs _))

/-- The normalized closed triangle is the closed cone clipped by the unit
square. Auxiliary to area-law Section 11, lines 340–348. -/
theorem mem_normalizedTriangle_iff (s : RepairFanSlot) (y : ℝ × ℝ) :
    y ∈ (cellFanPolygon (-1, -1) 1 (0, 0) repairFanSplit s).region ↔
      y ∈ repairFanCone s ∧ ‖y‖ ≤ 1 := by
  have hreg : (cellFanPolygon (-1, -1) 1 (0, 0) repairFanSplit s).region =
      convexHull ℝ {cellFanCenter (-1, -1) 1 (0, 0), repairFanStart s,
        repairFanDirection s} := rfl
  have hc : cellFanCenter (-1, -1) 1 (0, 0) = 0 := by
    ext <;> simp [cellFanCenter]
  rw [hreg, hc]
  set a := repairFanStart s
  set b := repairFanDirection s
  have hab : repairCross a b = 1 := repairCross_start_direction s
  let K : Set (ℝ × ℝ) := {y | 0 ≤ repairCross y b} ∩ {y | 0 ≤ repairCross a y} ∩
    {y | repairCross y b + repairCross a y ≤ 1}
  have hK : convexHull ℝ {0, a, b} = K := by
    apply le_antisymm
    · apply convexHull_min
      · intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl | rfl <;>
          simp only [K, Set.mem_inter_iff, Set.mem_ofPred_eq] <;>
          simp only [repairCross] at hab ⊢ <;> norm_num <;>
          refine ⟨⟨?_, ?_⟩, ?_⟩ <;> linarith
      · have hl₁ : IsLinearMap ℝ fun y : ℝ × ℝ ↦ repairCross y b := by
          constructor <;> intros <;> simp [repairCross] <;> ring
        have hl₂ : IsLinearMap ℝ fun y : ℝ × ℝ ↦ repairCross a y := by
          constructor <;> intros <;> simp [repairCross] <;> ring
        have hl₃ : IsLinearMap ℝ fun y : ℝ × ℝ ↦ repairCross y b + repairCross a y := by
          constructor <;> intros <;> simp [repairCross] <;> ring
        exact ((convex_halfSpace_ge hl₁ 0).inter (convex_halfSpace_ge hl₂ 0)).inter
          (convex_halfSpace_le hl₃ 1)
    · rintro y ⟨⟨h₁, h₂⟩, h₃⟩
      simp only [Set.mem_ofPred_eq] at h₁ h₂ h₃
      have hsum := (convex_convexHull ℝ ({0, a, b} : Set (ℝ × ℝ))).sum_mem
        (t := Finset.univ)
        (w := ![1 - repairCross y b - repairCross a y, repairCross y b, repairCross a y])
        (z := ![0, a, b]) (fun i _ ↦ by fin_cases i <;> simp <;> linarith)
        (by simp [Fin.sum_univ_succ])
        (fun i _ ↦ by
          fin_cases i <;> apply subset_convexHull <;> simp)
      convert hsum using 1
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, smul_zero, zero_add, add_zero]
      simp only [repairCross] at hab ⊢
      ext
      · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        linear_combination (-y.1) * hab
      · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        linear_combination (-y.2) * hab
  rw [hK]
  simp only [K, Set.mem_inter_iff, Set.mem_ofPred_eq, repairFanCone]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, h₃⟩
    refine ⟨⟨h₂, h₁⟩, ?_⟩
    rw [norm_eq_of_mem_repairFanCone ⟨h₂, h₁⟩]
    exact h₃
  · rintro ⟨⟨h₁, h₂⟩, h₃⟩
    rw [norm_eq_of_mem_repairFanCone ⟨h₁, h₂⟩] at h₃
    exact ⟨⟨h₂, h₁⟩, h₃⟩

/-- The closed triangle of half-side `r > 0` about `c` consists of the points
`x` with `x - c` in the closed cone and `‖x - c‖ ≤ r`.
Auxiliary to area-law Section 11, lines 340–348. -/
theorem mem_repairCurrentFanTriangle_iff {c : ℝ × ℝ} {r : ℝ} (hr : 0 < r)
    (s : RepairFanSlot) (x : ℝ × ℝ) :
    x ∈ repairCurrentFanTriangle c r s ↔ x - c ∈ repairFanCone s ∧ ‖x - c‖ ≤ r := by
  simp only [repairCurrentFanTriangle, Set.mem_image, mem_normalizedTriangle_iff]
  constructor
  · rintro ⟨y, ⟨hy, hn⟩, rfl⟩
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le]
    exact ⟨smul_mem_repairFanCone hr.le hy, mul_le_of_le_one_right hr.le hn⟩
  · rintro ⟨hy, hn⟩
    refine ⟨r⁻¹ • (x - c), ⟨smul_mem_repairFanCone (inv_pos.mpr hr).le hy, ?_⟩, ?_⟩
    · rw [norm_smul, Real.norm_of_nonneg (inv_pos.mpr hr).le]
      exact inv_mul_le_one_of_le₀ hn hr.le
    · rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, add_sub_cancel]

/-- A point of the interior of `{x | 0 ≤ a × (x - c)}` with `a ≠ 0` has
`0 < a × (x - c)`. Auxiliary to area-law Section 11, lines 340–348. -/
theorem pos_of_mem_interior_repairCross {a c x : ℝ × ℝ} (ha : a ≠ 0)
    (hx : x ∈ interior {x | 0 ≤ repairCross a (x - c)}) : 0 < repairCross a (x - c) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  set w : ℝ × ℝ := (-a.2, a.1)
  have hw : 0 < repairCross a w := by
    have : a.1 ≠ 0 ∨ a.2 ≠ 0 := by
      by_contra h
      push Not at h
      exact ha (Prod.ext h.1 h.2)
    have hw' : repairCross a w = a.1 ^ 2 + a.2 ^ 2 := by
      simp only [repairCross, w]
      ring
    rw [hw']
    rcases this with h | h
    · nlinarith [sq_pos_of_ne_zero h, sq_nonneg a.2]
    · nlinarith [sq_pos_of_ne_zero h, sq_nonneg a.1]
  set t := ε / (2 * (‖w‖ + 1))
  have ht : 0 < t := by positivity
  have hmem : x - t • w ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
      Real.norm_of_nonneg ht.le]
    calc t * ‖w‖ ≤ t * (‖w‖ + 1) := by nlinarith [norm_nonneg w]
      _ = ε / 2 := by simp only [t]; field_simp
      _ < ε := by linarith
  have h := interior_subset (hball hmem)
  simp only [Set.mem_ofPred_eq] at h
  have hlin : repairCross a (x - t • w - c) = repairCross a (x - c) - t * repairCross a w := by
    simp only [repairCross, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]
    ring
  rw [hlin] at h
  nlinarith

/-- The interior of a closed triangle of half-side `r > 0` is the set of
points `x` with `x - c` in the open cone and `‖x - c‖ < r`.
Auxiliary to area-law Section 11, lines 340–348. -/
theorem interior_repairCurrentFanTriangle {c : ℝ × ℝ} {r : ℝ} (hr : 0 < r)
    (s : RepairFanSlot) :
    interior (repairCurrentFanTriangle c r s) =
      {x | x - c ∈ repairFanOpenCone s ∧ ‖x - c‖ < r} := by
  have hW : repairCurrentFanTriangle c r s =
      {x | 0 ≤ repairCross (repairFanStart s) (x - c)} ∩
        {x | 0 ≤ repairCross (-repairFanDirection s) (x - c)} ∩ Metric.closedBall c r := by
    ext x
    rw [mem_repairCurrentFanTriangle_iff hr]
    simp only [repairFanCone, Set.mem_inter_iff, Set.mem_ofPred_eq, Metric.mem_closedBall,
      dist_eq_norm, repairCross, Prod.fst_neg, Prod.snd_neg]
    constructor
    · rintro ⟨⟨h₁, h₂⟩, h₃⟩
      exact ⟨⟨h₁, by linarith⟩, h₃⟩
    · rintro ⟨⟨h₁, h₂⟩, h₃⟩
      exact ⟨⟨h₁, by linarith⟩, h₃⟩
  apply le_antisymm
  · intro x hx
    rw [hW, interior_inter, interior_inter, interior_closedBall c hr.ne'] at hx
    obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hx
    have hs := repairFanDirection_ne_zero s
    have ha : repairFanStart s ≠ 0 := by
      rw [repairFanStart_eq]
      rcases s with ⟨i, j⟩
      fin_cases i <;> fin_cases j <;> simp [cellFanSideVector, Prod.ext_iff]
    have p₁ := pos_of_mem_interior_repairCross ha h₁
    have p₂ := pos_of_mem_interior_repairCross (neg_ne_zero.mpr hs) h₂
    refine ⟨⟨p₁, ?_⟩, by simpa [dist_eq_norm] using h₃⟩
    simp only [repairCross, Prod.fst_neg, Prod.snd_neg] at p₂ ⊢
    linarith
  · apply interior_maximal
    · intro x ⟨hx, hn⟩
      rw [mem_repairCurrentFanTriangle_iff hr]
      exact ⟨repairFanOpenCone_subset s hx, hn.le⟩
    · have hc₁ : Continuous fun x : ℝ × ℝ ↦ repairCross (repairFanStart s) (x - c) := by
        unfold repairCross; fun_prop
      have hc₂ : Continuous fun x : ℝ × ℝ ↦ repairCross (x - c) (repairFanDirection s) := by
        unfold repairCross; fun_prop
      exact ((isOpen_lt continuous_const hc₁).inter (isOpen_lt continuous_const hc₂)).inter
        (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const)

/-- Every point of a translated closed cone in an open set is a limit of
points of the translated open cone in that set.
Auxiliary to area-law Section 11, lines 340–348. -/
theorem mem_closure_openCone_inter {c x : ℝ × ℝ} {s : RepairFanSlot} {N : Set (ℝ × ℝ)}
    (hN : IsOpen N) (hxN : x ∈ N) (hx : x - c ∈ repairFanCone s) :
    x ∈ closure ({z | z - c ∈ repairFanOpenCone s} ∩ N) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hN x hxN
  set m := repairFanStart s + repairFanDirection s
  set t := min ε δ / (2 * (‖m‖ + 1))
  have ht : 0 < t := by positivity
  have hdist : dist x (x + t • m) < min ε δ := by
    rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg ht.le]
    have hpos : 0 < min ε δ := lt_min hε hδ
    calc t * ‖m‖ ≤ t * (‖m‖ + 1) := by nlinarith [norm_nonneg m]
      _ = min ε δ / 2 := by simp only [t]; field_simp
      _ < min ε δ := by linarith
  refine ⟨x + t • m, ⟨?_, hball ?_⟩, hdist.trans_le (min_le_left _ _)⟩
  · have h1 := repairCross_start_direction s
    obtain ⟨hx₁, hx₂⟩ := hx
    simp only [repairFanOpenCone, Set.mem_ofPred_eq, m]
    simp only [repairCross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 hx₁ hx₂ ⊢
    constructor <;> nlinarith
  · rw [Metric.mem_ball, dist_comm]
    exact hdist.trans_le (min_le_right _ _)

/-- A ray from `c` is closed.
Auxiliary to area-law Section 11, lines 340–348. -/
theorem isClosed_setOf_sameRay_direction (c : ℝ × ℝ) (s : RepairFanSlot) :
    IsClosed {x : ℝ × ℝ | SameRay ℝ (x - c) (repairFanDirection s)} := by
  have h := repairCross_start_direction s
  simp_rw [sameRay_iff_repairCross h]
  have hc₁ : Continuous fun x : ℝ × ℝ ↦ repairCross (x - c) (repairFanDirection s) := by
    unfold repairCross; fun_prop
  have hc₂ : Continuous fun x : ℝ × ℝ ↦ repairCross (repairFanStart s) (x - c) := by
    unfold repairCross; fun_prop
  exact (isClosed_eq hc₁ continuous_const).inter (isClosed_le continuous_const hc₂)

/-- A point of an open cone lies in no other closed cone.
Auxiliary to area-law Section 11, lines 340–348 and 497–504. -/
theorem eq_of_mem_repairFanOpenCone_of_mem_repairFanCone {s u : RepairFanSlot}
    {y : ℝ × ℝ} (hs : y ∈ repairFanOpenCone s) (hu : y ∈ repairFanCone u) : s = u := by
  by_contra hsu
  by_cases h₁ : u = cellFanNext s
  · subst h₁
    have := hu.1
    rw [repairFanStart_next] at this
    have h2 := hs.2
    simp only [repairCross] at this h2
    linarith
  by_cases h₂ : s = cellFanNext u
  · subst h₂
    have := hs.1
    rw [repairFanStart_next] at this
    have h2 := hu.2
    simp only [repairCross] at this h2
    linarith
  have := eq_zero_of_mem_repairFanCone hsu h₁ h₂ (repairFanOpenCone_subset s hs) hu
  subst this
  have := hs.1
  simp [repairCross] at this

/-- A point of an open cone lies on no ray of the fan.
Auxiliary to area-law Section 11, lines 340–348. -/
theorem not_sameRay_of_mem_repairFanOpenCone {s t : RepairFanSlot} {y : ℝ × ℝ}
    (hs : y ∈ repairFanOpenCone s) : ¬SameRay ℝ y (repairFanDirection t) := by
  intro h
  rw [← mem_repairFanCone_inter_next_iff] at h
  have e₁ := eq_of_mem_repairFanOpenCone_of_mem_repairFanCone hs h.1
  have e₂ := eq_of_mem_repairFanOpenCone_of_mem_repairFanCone hs h.2
  subst e₁
  exact cellFanNext_ne_self s e₂.symm

end TNLean.PEPS.AreaLaw.Geometry
