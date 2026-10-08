/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.BeltMarks
import TNLean.PEPS.AreaLaw.Geometry.Templates
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

/-!
# Separation on the quarter mesh

The nine marks of every cell at scale `j` lie on the mesh of spacing
`2 ^ ℓ / 4` whenever `ℓ ≤ j + 1`. Distinct mesh points are separated by
one mesh spacing. A mesh point outside a line of horizontal, vertical or
diagonal slope through mesh points is separated from that line by at
least half a mesh spacing, in the maximum metric on the plane.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:initial-stars`, lines 352–359.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The translated square mesh with spacing `q`.
Source: area-law Section 11, `geometry:initial-stars`, lines 352–359. -/
def affineMesh (o : ℝ × ℝ) (q : ℝ) : Set (ℝ × ℝ) :=
  Set.range (fun z : ℤ × ℤ ↦ o + q • integerPoint z)

/-- The cell marks lie on the quarter mesh whenever their scale is at least `ℓ - 1`.
Source: area-law Section 11, `geometry:initial-stars`, lines 352–359. -/
theorem beltMarks_subset_affineMesh (o : ℝ × ℝ) (ℓ j : ℕ)
    (F : Finset (ℤ × ℤ)) (hℓj : ℓ ≤ j + 1) :
    (beltMarks o j F : Set (ℝ × ℝ)) ⊆ affineMesh o ((2 : ℝ) ^ ℓ / 4) := by
  classical
  intro x hx
  obtain ⟨z, _, hz⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
  have hp : ((2 : ℝ) ^ ℓ / 4) * (2 : ℝ) ^ (j + 1 - ℓ) = (2 : ℝ) ^ j / 2 := by
    rw [div_mul_eq_mul_div, ← pow_add, Nat.add_sub_of_le hℓj, pow_succ]
    ring
  refine ⟨((2 : ℤ) ^ (j + 1 - ℓ) * (2 * z.1 + i.1.val),
    (2 : ℤ) ^ (j + 1 - ℓ) * (2 * z.2 + i.2.val)), ?_⟩
  apply Prod.ext <;> dsimp [integerPoint] <;> push_cast <;>
    rw [← mul_assoc, hp] <;> ring

private theorem abs_mul_int_ge {q : ℝ} (hq : 0 < q) (n : ℤ) (hn : n ≠ 0) :
    q ≤ |q * (n : ℝ)| := by
  have hn' : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
  simpa [abs_mul, abs_of_pos hq] using mul_le_mul_of_nonneg_left hn' hq.le

/-- Distinct points of a positive-spacing mesh are separated by at least its spacing.
Source: area-law Section 11, `geometry:initial-stars`, lines 352–359. -/
theorem affineMesh_dist_ge {o : ℝ × ℝ} {q : ℝ} (hq : 0 < q)
    {x y : ℝ × ℝ} (hx : x ∈ affineMesh o q) (hy : y ∈ affineMesh o q)
    (hxy : x ≠ y) : q ≤ dist x y := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  have hab : a ≠ b := by rintro rfl; exact hxy rfl
  have hab' : a.1 ≠ b.1 ∨ a.2 ≠ b.2 := by
    by_contra h
    push Not at h
    exact hab (Prod.ext h.1 h.2)
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  rcases hab' with h | h
  · have hg := abs_mul_int_ge hq (a.1 - b.1) (sub_ne_zero.mpr h)
    have he : (o + q • integerPoint a).1 - (o + q • integerPoint b).1 =
        q * ((a.1 - b.1 : ℤ) : ℝ) := by dsimp [integerPoint]; push_cast; ring
    exact (he ▸ hg).trans (le_max_left _ _)
  · have hg := abs_mul_int_ge hq (a.2 - b.2) (sub_ne_zero.mpr h)
    have he : (o + q • integerPoint a).2 - (o + q • integerPoint b).2 =
        q * ((a.2 - b.2 : ℤ) : ℝ) := by dsimp [integerPoint]; push_cast; ring
    exact (he ▸ hg).trans (le_max_right _ _)

private theorem mem_nonvertical_line_iff {u v x : ℝ × ℝ} {m : ℝ}
    (huv : u.1 ≠ v.1) (hs : v.2 - u.2 = m * (v.1 - u.1)) :
    x ∈ affineSpan ℝ {u, v} ↔ x.2 - m * x.1 = u.2 - m * u.1 := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  constructor
  · rintro ⟨r, rfl⟩
    rw [AffineMap.lineMap_apply_module']
    dsimp
    linear_combination r * hs
  · intro hx
    refine ⟨(x.1 - u.1) / (v.1 - u.1), ?_⟩
    have hd := div_mul_cancel₀ (x.1 - u.1) (sub_ne_zero.mpr huv.symm)
    rw [AffineMap.lineMap_apply_module']
    apply Prod.ext <;> dsimp
    · linarith
    · linear_combination ((x.1 - u.1) / (v.1 - u.1)) * hs + m * hd - hx

private theorem mem_vertical_line_iff {u v x : ℝ × ℝ}
    (huv : u.2 ≠ v.2) (hs : u.1 = v.1) :
    x ∈ affineSpan ℝ {u, v} ↔ x.1 = u.1 := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  constructor
  · rintro ⟨r, rfl⟩
    rw [AffineMap.lineMap_apply_module']
    dsimp
    rw [← hs]
    ring
  · intro hx
    refine ⟨(x.2 - u.2) / (v.2 - u.2), ?_⟩
    have hd := div_mul_cancel₀ (x.2 - u.2) (sub_ne_zero.mpr huv.symm)
    rw [AffineMap.lineMap_apply_module']
    apply Prod.ext <;> dsimp
    · rw [← hs, hx]; ring
    · linarith

private theorem mesh_linear_gap {o : ℝ × ℝ} {q : ℝ} (hq : 0 < q)
    (a b : ℤ) {x u : ℝ × ℝ} (hx : x ∈ affineMesh o q) (hu : u ∈ affineMesh o q)
    (hne : (a : ℝ) * x.1 + b * x.2 ≠ (a : ℝ) * u.1 + b * u.2) :
    q ≤ |((a : ℝ) * x.1 + b * x.2) - ((a : ℝ) * u.1 + b * u.2)| := by
  obtain ⟨c, rfl⟩ := hx
  obtain ⟨d, rfl⟩ := hu
  have he : ((a : ℝ) * (o + q • integerPoint c).1 +
      b * (o + q • integerPoint c).2) -
      ((a : ℝ) * (o + q • integerPoint d).1 + b * (o + q • integerPoint d).2) =
      q * ((a * (c.1 - d.1) + b * (c.2 - d.2) : ℤ) : ℝ) := by
    dsimp [integerPoint]
    push_cast
    ring
  have hn : a * (c.1 - d.1) + b * (c.2 - d.2) ≠ 0 := by
    intro hn
    apply hne
    apply sub_eq_zero.mp
    rw [he, hn]
    simp
  rw [he]
  exact abs_mul_int_ge hq _ hn

private theorem linear_form_dist_le (x y : ℝ × ℝ) {m : ℝ} (hm : |m| ≤ 1) :
    |(x.2 - m * x.1) - (y.2 - m * y.1)| ≤ 2 * dist x y := by
  have hfst : |x.1 - y.1| ≤ dist x y := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact le_max_left _ _
  have hsnd : |x.2 - y.2| ≤ dist x y := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact le_max_right _ _
  calc
    _ = |(x.2 - y.2) - m * (x.1 - y.1)| := by congr 1; ring
    _ ≤ |x.2 - y.2| + |m * (x.1 - y.1)| := abs_sub _ _
    _ = |x.2 - y.2| + |m| * |x.1 - y.1| := by rw [abs_mul]
    _ ≤ dist x y + |x.1 - y.1| := by
      exact add_le_add hsnd (by simpa using mul_le_mul_of_nonneg_right hm (abs_nonneg _))
    _ ≤ dist x y + dist x y := add_le_add le_rfl hfst
    _ = 2 * dist x y := by ring

private theorem nonvertical_mesh_line_dist_ge {o : ℝ × ℝ} {q : ℝ}
    (hq : 0 < q) {u v x y : ℝ × ℝ} (hu : u ∈ affineMesh o q)
    (hx : x ∈ affineMesh o q) (m : ℤ) (hm : |(m : ℝ)| ≤ 1)
    (huv : u.1 ≠ v.1) (hs : v.2 - u.2 = (m : ℝ) * (v.1 - u.1))
    (hout : x ∉ affineSpan ℝ {u, v}) (hy : y ∈ affineSpan ℝ {u, v}) :
    q / 2 ≤ dist x y := by
  have hne : x.2 - (m : ℝ) * x.1 ≠ u.2 - (m : ℝ) * u.1 := by
    intro he
    exact hout ((mem_nonvertical_line_iff huv hs).mpr he)
  have hne' : ((-m : ℤ) : ℝ) * x.1 + (1 : ℤ) * x.2 ≠
      ((-m : ℤ) : ℝ) * u.1 + (1 : ℤ) * u.2 := by
    simpa [sub_eq_add_neg, add_comm] using hne
  have hg := mesh_linear_gap hq (-m) 1 hx hu hne'
  have hg' : q ≤ |(x.2 - (m : ℝ) * x.1) - (u.2 - (m : ℝ) * u.1)| := by
    simpa [sub_eq_add_neg, add_comm] using hg
  have hy' := (mem_nonvertical_line_iff huv hs).mp hy
  rw [← hy'] at hg'
  have hb := linear_form_dist_le x y hm
  linarith

/-- A mesh point outside a line of an allowed slope through mesh points is at least
half a mesh spacing from every point of the line.
Source: area-law Section 11, `geometry:initial-stars`, lines 352–359. -/
theorem affineMesh_line_dist_ge {o : ℝ × ℝ} {q : ℝ} (hq : 0 < q)
    {u v x y : ℝ × ℝ} (hu : u ∈ affineMesh o q) (hv : v ∈ affineMesh o q)
    (hx : x ∈ affineMesh o q) (hs : IsAllowedSlope (v - u))
    (hout : x ∉ affineSpan ℝ {u, v}) (hy : y ∈ affineSpan ℝ {u, v}) :
    q / 2 ≤ dist x y := by
  by_cases huv : u = v
  · subst v
    have hy' : y = u := by simpa using hy
    subst y
    have hxu : x ≠ u := by
      intro h
      subst x
      exact hout (left_mem_affineSpan_pair ℝ u u)
    have hg := affineMesh_dist_ge hq hx hv hxu
    linarith
  by_cases hf : u.1 = v.1
  · have hsnd : u.2 ≠ v.2 := by
      intro h
      exact huv (Prod.ext hf h)
    have hne : x.1 ≠ u.1 := by
      intro h
      exact hout ((mem_vertical_line_iff hsnd hf).mpr h)
    have hg := mesh_linear_gap hq 1 0 hx hu (by simpa using hne)
    have hg' : q ≤ |x.1 - u.1| := by simpa using hg
    have hy' := (mem_vertical_line_iff hsnd hf).mp hy
    rw [← hy'] at hg'
    have hb : |x.1 - y.1| ≤ dist x y := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      exact le_max_left _ _
    linarith
  rcases hs with hs | hs | hs | hs
  · exact False.elim (hf (by dsimp at hs; linarith))
  · apply nonvertical_mesh_line_dist_ge hq hu hx 0 (by norm_num) hf _ hout hy
    dsimp at hs
    norm_num
    linarith
  · apply nonvertical_mesh_line_dist_ge hq hu hx 1 (by norm_num) hf _ hout hy
    dsimp at hs
    norm_num
    linarith
  · apply nonvertical_mesh_line_dist_ge hq hu hx (-1) (by norm_num) hf _ hout hy
    dsimp at hs
    norm_num
    linarith

end TNLean.PEPS.AreaLaw.Geometry
