/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.Templates
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Integer rows of sampled template polygons

The row interval property is derived from the convex hull in `TemplatePolygon.region`
and the exact sampling equation in `Template.mem_sample`. Integer dilation is treated
as a union of translated integer squares, including for empty pieces and overlapping unions.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
Lemma 9.4 (`scanner:templates`), `08-scanner.tex`, lines 571–629, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Original formalization from the mathematical manuscript. No upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw

/-- Membership in an ambient integer dilation, in coordinate inequalities. -/
theorem mem_ambientDilation_iff {S : Finset (ℤ × ℤ)} {r : ℕ} {x : ℤ × ℤ} :
    x ∈ ambientDilation S r ↔ ∃ p ∈ S,
      p.1 - r ≤ x.1 ∧ x.1 ≤ p.1 + r ∧ p.2 - r ≤ x.2 ∧ x.2 ≤ p.2 + r := by
  simp only [ambientDilation, Finset.mem_biUnion, Finset.mem_product, Finset.mem_Icc]
  tauto

/-- Dilation preserves inclusion without any connectedness assumption. -/
theorem ambientDilation_mono {S U : Finset (ℤ × ℤ)} (h : S ⊆ U) (r : ℕ) :
    ambientDilation S r ⊆ ambientDilation U r := by
  intro x hx
  obtain ⟨p, hp, hx⟩ := mem_ambientDilation_iff.mp hx
  exact mem_ambientDilation_iff.mpr ⟨p, h hp, hx⟩

/-- Increasing the radius preserves inclusion. -/
theorem ambientDilation_mono_radius (S : Finset (ℤ × ℤ)) {r t : ℕ} (h : r ≤ t) :
    ambientDilation S r ⊆ ambientDilation S t := by
  intro x hx
  obtain ⟨p, hp, hx⟩ := mem_ambientDilation_iff.mp hx
  exact mem_ambientDilation_iff.mpr ⟨p, hp, by omega⟩

/-- A point in a new layer of a union belongs to a new layer of a constituent.
No disjointness or nonemptiness of the constituents is needed. -/
theorem ambientDilation_biUnion_sdiff_subset {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (S : ι → Finset (ℤ × ℤ)) (r t : ℕ) :
    ambientDilation (I.biUnion S) r \ ambientDilation (I.biUnion S) t ⊆
      I.biUnion (fun i ↦ ambientDilation (S i) r \ ambientDilation (S i) t) := by
  intro x hx
  obtain ⟨hx, hn⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨p, hp, hpx⟩ := mem_ambientDilation_iff.mp hx
  obtain ⟨i, hi, hp⟩ := Finset.mem_biUnion.mp hp
  refine Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_sdiff.mpr ⟨?_, ?_⟩⟩
  · exact mem_ambientDilation_iff.mpr ⟨p, hp, hpx⟩
  · intro h
    exact hn (ambientDilation_mono (Finset.subset_biUnion_of_mem S hi) t h)

/-- Layer cardinalities are subadditive over arbitrary finite unions. -/
theorem card_ambientDilation_biUnion_sdiff_le {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (S : ι → Finset (ℤ × ℤ)) (r t : ℕ) :
    (ambientDilation (I.biUnion S) r \ ambientDilation (I.biUnion S) t).card ≤
      ∑ i ∈ I, (ambientDilation (S i) r \ ambientDilation (S i) t).card :=
  (Finset.card_le_card (ambientDilation_biUnion_sdiff_subset I S r t)).trans
    Finset.card_biUnion_le

namespace Geometry

/-- Horizontal integer coordinates on a fixed row of a finite lattice set. -/
def latticeRow (S : Finset (ℤ × ℤ)) (y : ℤ) : Finset ℤ :=
  (S.filter fun p ↦ p.2 = y).image Prod.fst

@[simp] theorem mem_latticeRow {S : Finset (ℤ × ℤ)} {x y : ℤ} :
    x ∈ latticeRow S y ↔ (x, y) ∈ S := by
  simp only [latticeRow, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨h, rfl⟩, rfl⟩
    exact h
  · intro h
    exact ⟨(x, y), ⟨h, rfl⟩, rfl⟩

/-- Every permitted polygon is convex by its actual convex-hull definition. -/
theorem TemplatePolygon.convex_region (P : TemplatePolygon) : Convex ℝ P.region := by
  cases P <;> exact convex_convexHull ℝ _

/-- Horizontal sections of a convex planar set contain the interval between any
two of their points. This statement has no slope or sign restriction. -/
theorem horizontal_mem_of_mem_of_le {K : Set (ℝ × ℝ)} (hK : Convex ℝ K)
    {a b x y : ℝ} (ha : (a, y) ∈ K) (hb : (b, y) ∈ K)
    (hax : a ≤ x) (hxb : x ≤ b) : (x, y) ∈ K := by
  let f : ℝ →ᵃ[ℝ] ℝ × ℝ :=
    { toFun := fun t ↦ (t, y)
      linear := LinearMap.inl ℝ ℝ ℝ
      map_vadd' := by intro p v; ext <;> simp }
  exact (hK.affine_preimage f).ordConnected.out ha hb ⟨hax, hxb⟩

/-- Exact sampling and convexity imply that every sampled horizontal row is
an integer interval. This is a consequence of the model, not a template field. -/
theorem Template.mem_sample_of_row_between {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (i : Fin T.pieceCount) {a b x y : ℤ}
    (ha : (a, y) ∈ T.sample i) (hb : (b, y) ∈ T.sample i)
    (hax : a ≤ x) (hxb : x ≤ b) : (x, y) ∈ T.sample i := by
  apply (T.mem_sample i _).mpr
  exact horizontal_mem_of_mem_of_le (T.polygon i).convex_region
    ((T.mem_sample i _).mp ha) ((T.mem_sample i _).mp hb)
    (by exact_mod_cast hax) (by exact_mod_cast hxb)

/-- The endpoints of a nonempty sampled row are its attained integer extrema. -/
theorem Template.latticeRow_eq_Icc {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (i : Fin T.pieceCount) (y : ℤ)
    (h : (latticeRow (T.sample i) y).Nonempty) :
    latticeRow (T.sample i) y =
      Finset.Icc ((latticeRow (T.sample i) y).min' h)
        ((latticeRow (T.sample i) y).max' h) := by
  ext x
  constructor
  · intro hx
    exact Finset.mem_Icc.mpr ⟨Finset.min'_le _ _ hx, Finset.le_max' _ _ hx⟩
  · intro hx
    obtain ⟨hax, hxb⟩ := Finset.mem_Icc.mp hx
    exact mem_latticeRow.mpr (T.mem_sample_of_row_between i
      (mem_latticeRow.mp (Finset.min'_mem _ h))
      (mem_latticeRow.mp (Finset.max'_mem _ h)) hax hxb)

/-- Every nonempty sampled piece lies in the integer square of radius `s₀`
about any one of its sampled sites. -/
theorem Template.sample_subset_box {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (i : Fin T.pieceCount) {p : ℤ × ℤ}
    (hp : p ∈ T.sample i) :
    T.sample i ⊆ (Finset.Icc (p.1 - (s₀ : ℤ)) (p.1 + s₀)).product
      (Finset.Icc (p.2 - (s₀ : ℤ)) (p.2 + s₀)) := by
  intro x hx
  have h := T.piece_diameter i (integerPoint x) ((T.mem_sample i x).mp hx)
    (integerPoint p) ((T.mem_sample i p).mp hp)
  change max |(x.1 : ℝ) - p.1| |(x.2 : ℝ) - p.2| ≤ (s₀ : ℝ) at h
  obtain ⟨h₁, h₂⟩ := max_le_iff.mp h
  have h₁' : |x.1 - p.1| ≤ (s₀ : ℤ) := by exact_mod_cast h₁
  have h₂' : |x.2 - p.2| ≤ (s₀ : ℤ) := by exact_mod_cast h₂
  rw [abs_le] at h₁' h₂'
  simp only [Finset.mem_product, Finset.mem_Icc]
  omega

/-- A uniform area bound for each sample, including empty sampled polygons. -/
theorem Template.card_sample_le {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (i : Fin T.pieceCount) :
    (T.sample i).card ≤ (2 * s₀ + 1) ^ 2 := by
  obtain h | ⟨p, hp⟩ := (T.sample i).eq_empty_or_nonempty
  · simp [h]
  · calc
      (T.sample i).card ≤
          ((Finset.Icc (p.1 - (s₀ : ℤ)) (p.1 + s₀)).product
            (Finset.Icc (p.2 - (s₀ : ℤ)) (p.2 + s₀))).card :=
        Finset.card_le_card (T.sample_subset_box i hp)
      _ = (2 * s₀ + 1) ^ 2 := by
        simp only [Finset.card_product, Int.card_Icc]
        have h (a : ℤ) : a + (s₀ : ℤ) + 1 - (a - s₀) = (2 * s₀ + 1 : ℕ) := by
          omega
        simp only [h, Int.toNat_natCast, pow_two]

/-- The area estimate in Lemma 9.4, with the explicit universal constant `9`.
It follows from the actual piece diameters and scale, with no row assumption. -/
theorem template_card_le {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (hC : 1 ≤ Ctpl) : T.points.card ≤ 9 * n * s₀ := by
  have hcard : T.points.card ≤ T.pieceCount * (2 * s₀ + 1) ^ 2 := by
    rw [T.cover]
    simpa using Finset.card_biUnion_le_card_mul Finset.univ T.sample
      ((2 * s₀ + 1) ^ 2) (fun i _ ↦ T.card_sample_le i)
  have hscale : (T.pieceCount : ℝ) * (s₀ + 1) ≤ n := by
    calc
      (T.pieceCount : ℝ) * (s₀ + 1) ≤ Ctpl * T.pieceCount * (s₀ + 1) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hC)
          (show 0 ≤ (T.pieceCount : ℝ) * (s₀ + 1) by positivity)]
      _ ≤ n := T.scale
  have hn : T.pieceCount * (s₀ + 1) ≤ n := by exact_mod_cast hscale
  have hs := T.s₀_pos
  calc
    T.points.card ≤ T.pieceCount * (2 * s₀ + 1) ^ 2 := hcard
    _ ≤ T.pieceCount * (9 * (s₀ + 1) * s₀) := by
      gcongr
      nlinarith
    _ ≤ 9 * n * s₀ := by nlinarith [Nat.mul_le_mul_right (9 * s₀) hn]

/-- Rounding an affine lower endpoint commutes with every integer row shift,
including negative coordinates. -/
theorem ceil_affine_row (c : ℝ) (m y : ℤ) :
    ⌈c + (m : ℝ) * y⌉ = ⌈c⌉ + m * y := by
  rw [← Int.cast_mul, Int.ceil_add_intCast]

/-- Rounding an affine upper endpoint commutes with every integer row shift. -/
theorem floor_affine_row (c : ℝ) (m y : ℤ) :
    ⌊c + (m : ℝ) * y⌋ = ⌊c⌋ + m * y := by
  rw [← Int.cast_mul, Int.floor_add_intCast]

/-- A row of an integer dilation is exactly the union of the original rows in
the radius window, with each original site extended horizontally by the radius.
This description also applies to empty samples. -/
theorem mem_latticeRow_ambientDilation {S : Finset (ℤ × ℤ)} {r : ℕ} {x y : ℤ} :
    x ∈ latticeRow (ambientDilation S r) y ↔
      ∃ z ∈ Finset.Icc (y - r) (y + r), ∃ a ∈ latticeRow S z,
        x ∈ Finset.Icc (a - r) (a + r) := by
  simp only [mem_latticeRow, mem_ambientDilation_iff, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨a, z⟩, hp, h⟩
    exact ⟨z, by omega, a, hp, by omega⟩
  · rintro ⟨z, hz, a, ha, hx⟩
    exact ⟨(a, z), ha, by omega⟩

end Geometry
end TNLean.PEPS.AreaLaw
