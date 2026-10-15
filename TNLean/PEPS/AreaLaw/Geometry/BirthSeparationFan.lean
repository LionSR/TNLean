/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.BirthSeparationAngular
import TNLean.PEPS.AreaLaw.Geometry.RepairReplacementRegions

/-!
# The normalized replacement fan and its exterior bound

Normalize a removal square to `Q = [-1, 1]²`. Its eight elementary triangles
`T_s` are cut out by one outer facet `o_s · x ≤ 1` and two homogeneous radial
facets. Doubling the outer level gives the triangle `2 T_s` of `[-2, 2]²`, and
adding `o_s · x ≥ 1` gives its part outside the open square `int Q`. This
*exterior trapezoid* is the local upper bound for the old regions occupying the
wedge `s` after the removal of `Q`.

All facets have integer levels and coefficients with `|a| + |b| ≤ 2`, so these
sets are quarter-sectorial at every integer point. Two triangles of distinct
slots meet at most in the center unless they are consecutive, and a triangle
meets the exterior trapezoid of a different slot at most in a perimeter mark.
Every actual fan triangle of the normalized replacement fan lies in the
corresponding half-plane triangle.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, replacement instructions, lines 393–417;
`geometry:repair-induction`, lines 497–514; and `geometry:birth-separation`,
lines 573–659.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The outer normal and the two homogeneous radial facet normals of the
elementary triangle of slot `s` in `[-1, 1]²`. The sides are listed
counterclockwise from the right side, and each side is divided at its midpoint.
Source: area-law Section 11, lines 404–417 and 506–514. -/
def repairSlotFacets (s : RepairFanSlot) : (ℤ × ℤ) × (ℤ × ℤ) × (ℤ × ℤ) :=
  match s.1.val, s.2.val with
  | 0, 0 => ((1, 0), (0, 1), (-1, -1))
  | 0, _ => ((1, 0), (0, -1), (-1, 1))
  | 1, 0 => ((0, 1), (-1, 0), (1, -1))
  | 1, _ => ((0, 1), (1, 0), (-1, -1))
  | 2, 0 => ((-1, 0), (0, -1), (1, 1))
  | 2, _ => ((-1, 0), (0, 1), (1, -1))
  | 3, 0 => ((0, -1), (1, 0), (-1, 1))
  | _, _ => ((0, -1), (-1, 0), (1, 1))

/-- The closed triangle of slot `s` with outer level `L`: for `L = 1` the
elementary triangle `T_s` of `[-1, 1]²`, for `L = 2` its double `2 T_s`.
Source: area-law Section 11, lines 404–417 and 573–659. -/
def repairNormTriangle (L : ℤ) (s : RepairFanSlot) : Set (ℝ × ℝ) :=
  intHalfPlane (repairSlotFacets s).1.1 (repairSlotFacets s).1.2 L ∩
    intHalfPlane (repairSlotFacets s).2.1.1 (repairSlotFacets s).2.1.2 0 ∩
    intHalfPlane (repairSlotFacets s).2.2.1 (repairSlotFacets s).2.2.2 0

/-- The part of `2 T_s` outside the open square `int Q`: the exterior bound of
the old regions in the wedge `s` after removal of `Q`.
Source: area-law Section 11, lines 398–399 and 573–659. -/
def repairExteriorTrapezoid (s : RepairFanSlot) : Set (ℝ × ℝ) :=
  repairNormTriangle 2 s ∩
    intHalfPlane (-(repairSlotFacets s).1.1) (-(repairSlotFacets s).1.2) (-1)

private theorem repairSlotFacets_abs (s : RepairFanSlot) :
    |(repairSlotFacets s).1.1| + |(repairSlotFacets s).1.2| ≤ 2 ∧
    |(repairSlotFacets s).2.1.1| + |(repairSlotFacets s).2.1.2| ≤ 2 ∧
    |(repairSlotFacets s).2.2.1| + |(repairSlotFacets s).2.2.2| ≤ 2 := by
  rcases s with ⟨k, j⟩
  fin_cases k <;> fin_cases j <;> decide

theorem isQuarterSectorial_repairNormTriangle (L : ℤ) (s : RepairFanSlot) (i j : ℤ) :
    IsQuarterSectorial ((i : ℝ), (j : ℝ)) (repairNormTriangle L s) := by
  obtain ⟨h₁, h₂, h₃⟩ := repairSlotFacets_abs s
  exact ((isQuarterSectorial_intHalfPlane h₁ i j).inter
    (isQuarterSectorial_intHalfPlane h₂ i j)).inter (isQuarterSectorial_intHalfPlane h₃ i j)

theorem isQuarterSectorial_repairExteriorTrapezoid (s : RepairFanSlot) (i j : ℤ) :
    IsQuarterSectorial ((i : ℝ), (j : ℝ)) (repairExteriorTrapezoid s) := by
  obtain ⟨h₁, -, -⟩ := repairSlotFacets_abs s
  exact (isQuarterSectorial_repairNormTriangle 2 s i j).inter
    (isQuarterSectorial_intHalfPlane (by rwa [abs_neg, abs_neg]) i j)

theorem isClosed_intHalfPlane (a b n : ℤ) : IsClosed (intHalfPlane a b n) :=
  isClosed_le (by fun_prop) continuous_const

theorem isClosed_repairNormTriangle (L : ℤ) (s : RepairFanSlot) :
    IsClosed (repairNormTriangle L s) :=
  ((isClosed_intHalfPlane _ _ _).inter (isClosed_intHalfPlane _ _ _)).inter
    (isClosed_intHalfPlane _ _ _)

theorem isClosed_repairExteriorTrapezoid (s : RepairFanSlot) :
    IsClosed (repairExteriorTrapezoid s) :=
  (isClosed_repairNormTriangle 2 s).inter (isClosed_intHalfPlane _ _ _)

/-- The triangle with outer level `L ≥ 0` lies in the closed square of
half-side `L`. -/
theorem norm_le_of_mem_repairNormTriangle {L : ℤ} {s : RepairFanSlot} {x : ℝ × ℝ}
    (hx : x ∈ repairNormTriangle L s) : ‖x‖ ≤ L := by
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hx
  rcases s with ⟨k, j⟩
  simp only [intHalfPlane, Set.mem_ofPred_eq] at h₁ h₂ h₃
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, max_le_iff, abs_le, abs_le]
  fin_cases k <;> fin_cases j <;> simp [repairSlotFacets] at h₁ h₂ h₃ <;>
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith

theorem isCompact_repairNormTriangle (L : ℤ) (s : RepairFanSlot) :
    IsCompact (repairNormTriangle L s) :=
  (isCompact_closedBall (0 : ℝ × ℝ) L).of_isClosed_subset
    (isClosed_repairNormTriangle L s) fun _ hx ↦ by
      simpa using norm_le_of_mem_repairNormTriangle hx

theorem isCompact_repairExteriorTrapezoid (s : RepairFanSlot) :
    IsCompact (repairExteriorTrapezoid s) :=
  (isCompact_repairNormTriangle 2 s).of_isClosed_subset
    (isClosed_repairExteriorTrapezoid s) Set.inter_subset_left

private theorem intPoint_of {x₁ x₂ : ℝ} (i j : ℤ) (h₁ : x₁ = i) (h₂ : x₂ = j) :
    ∃ i j : ℤ, (x₁, x₂) = ((i : ℝ), (j : ℝ)) :=
  ⟨i, j, by rw [h₁, h₂]⟩

/-- **Contact with an exterior trapezoid.** A triangle of `[-1, 1]²` meets the
exterior trapezoid of a different slot only in an integer point: the common
perimeter endpoint of two consecutive wedges.
Source: area-law Section 11, `geometry:repair-induction`, lines 497–504, and
`geometry:birth-separation`, lines 616–625. -/
theorem repairNormTriangle_inter_exteriorTrapezoid {s t : RepairFanSlot} (hst : s ≠ t)
    {x : ℝ × ℝ} (hx : x ∈ repairNormTriangle 1 s) (hy : x ∈ repairExteriorTrapezoid t) :
    ∃ i j : ℤ, x = ((i : ℝ), (j : ℝ)) := by
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hx
  obtain ⟨⟨⟨g₁, g₂⟩, g₃⟩, g₄⟩ := hy
  rcases s with ⟨k, a⟩
  rcases t with ⟨l, b⟩
  simp only [intHalfPlane, Set.mem_ofPred_eq] at h₁ h₂ h₃ g₁ g₂ g₃ g₄
  obtain ⟨x₁, x₂⟩ := x
  fin_cases k <;> fin_cases a <;> fin_cases l <;> fin_cases b <;>
    simp [repairSlotFacets] at hst h₁ h₂ h₃ g₁ g₂ g₃ g₄ <;>
    first
    | (exfalso; linarith)
    | exact intPoint_of 1 0 (by norm_num; linarith) (by norm_num; linarith)
    | exact intPoint_of 1 1 (by norm_num; linarith) (by norm_num; linarith)
    | exact intPoint_of 0 1 (by norm_num; linarith) (by norm_num; linarith)
    | exact intPoint_of (-1) 1 (by norm_num; linarith) (by norm_num; linarith)
    | exact intPoint_of (-1) 0 (by norm_num; linarith) (by norm_num; linarith)
    | exact intPoint_of (-1) (-1) (by norm_num; linarith) (by norm_num; linarith)
    | exact intPoint_of 0 (-1) (by norm_num; linarith) (by norm_num; linarith)
    | exact intPoint_of 1 (-1) (by norm_num; linarith) (by norm_num; linarith)

/-- Two elementary fan triangles of the normalized replacement fan are
*consecutive* when an endpoint of one outer segment is the opposite endpoint
of the other. This is the adjacency of the run graph.
Source: area-law Section 11, lines 313–318 and 404–417. -/
def RepairSlotConsecutive (s t : RepairFanSlot) : Prop :=
  cellFanEnd (-1, -1) 1 (0, 0) repairFanSplit s = cellFanStart (-1, -1) 1 (0, 0) repairFanSplit t ∨
    cellFanEnd (-1, -1) 1 (0, 0) repairFanSplit t = cellFanStart (-1, -1) 1 (0, 0) repairFanSplit s

/-- **Contact of nonconsecutive triangles.** Two distinct triangles of
`[-1, 1]²` that are not consecutive meet only at the center.
Source: area-law Section 11, lines 404–417 and 616–625. -/
theorem repairNormTriangle_inter_eq_zero {s t : RepairFanSlot} (hst : s ≠ t)
    (hcons : ¬ RepairSlotConsecutive s t) {x : ℝ × ℝ} (hx : x ∈ repairNormTriangle 1 s)
    (hy : x ∈ repairNormTriangle 1 t) : x = 0 := by
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hx
  obtain ⟨⟨g₁, g₂⟩, g₃⟩ := hy
  rcases s with ⟨k, a⟩
  rcases t with ⟨l, b⟩
  simp only [intHalfPlane, Set.mem_ofPred_eq] at h₁ h₂ h₃ g₁ g₂ g₃
  obtain ⟨x₁, x₂⟩ := x
  unfold RepairSlotConsecutive at hcons
  fin_cases k <;> fin_cases a <;> fin_cases l <;> fin_cases b <;>
    simp [repairSlotFacets] at hst h₁ h₂ h₃ g₁ g₂ g₃ <;>
    first
    | exact Prod.ext (by simp; linarith) (by simp; linarith)
    | (exfalso; apply hcons; norm_num [cellFanStart_eq, cellFanEnd_eq, cellFanCenter,
        cellFanSideVector, repairFanSplit])

theorem convex_intHalfPlane (a b n : ℤ) : Convex ℝ (intHalfPlane a b n) := by
  intro x hx y hy p q hp hq hpq
  simp only [intHalfPlane, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul] at hx hy ⊢
  have : (a : ℝ) * (p * x.1 + q * y.1) + b * (p * x.2 + q * y.2) =
      p * (a * x.1 + b * x.2) + q * (a * y.1 + b * y.2) := by ring
  have hn : (n : ℝ) = p * n + q * n := by rw [← add_mul, hpq, one_mul]
  rw [this]
  linarith [mul_le_mul_of_nonneg_left hx hp, mul_le_mul_of_nonneg_left hy hq]

theorem convex_repairNormTriangle (L : ℤ) (s : RepairFanSlot) :
    Convex ℝ (repairNormTriangle L s) :=
  ((convex_intHalfPlane _ _ _).inter (convex_intHalfPlane _ _ _)).inter
    (convex_intHalfPlane _ _ _)

/-- Every actual triangle of the normalized replacement fan lies in its
half-plane triangle.
Source: area-law Section 11, lines 404–417. -/
theorem cellFanPolygon_region_subset_repairNormTriangle (s : RepairFanSlot) :
    (cellFanPolygon (-1, -1) 1 (0, 0) repairFanSplit s).region ⊆ repairNormTriangle 1 s := by
  change convexHull ℝ {cellFanCenter (-1, -1) 1 (0, 0),
    cellFanStart (-1, -1) 1 (0, 0) repairFanSplit s,
    cellFanEnd (-1, -1) 1 (0, 0) repairFanSplit s} ⊆ _
  refine convexHull_min ?_ (convex_repairNormTriangle 1 s)
  rcases s with ⟨k, a⟩
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl <;>
    fin_cases k <;> fin_cases a <;>
    norm_num [repairNormTriangle, intHalfPlane, repairSlotFacets, cellFanStart_eq,
      cellFanEnd_eq, cellFanCenter, cellFanSideVector, repairFanSplit]

end TNLean.PEPS.AreaLaw.Geometry
