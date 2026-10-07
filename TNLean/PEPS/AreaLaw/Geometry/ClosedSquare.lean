/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.FiniteDomain
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-!
# Closed-square samples and their crossing edges

We intersect an arbitrary finite induced integer-lattice domain with a closed
square of real center and radius. Counting its four sides bounds its unordered
crossing edges by `8 * r + 4`, without connectedness or unclipped-square assumptions.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, `03-patches.tex`, lines 14–22, 53–66, 215–228, 323–336.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

/-!
## Original proof provenance

Source: September 24, 2026,
preprints/
Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/
build/sections/03-patches.tex,
sec:patches and prop:patch; independently formalized;
no upstream Lean proof text reused.

Provenance-ID: 8767-tnlean.peps.arealaw.geometry.closedsquaresample
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.closedSquareSample

Provenance-ID: 8767-tnlean.peps.arealaw.geometry.mem_closedsquaresample
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.mem_closedSquareSample

Provenance-ID: 8767-tnlean.peps.arealaw.geometry.closedsquaresample_mono
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.closedSquareSample_mono

Provenance-ID: 8767-tnlean.peps.arealaw.geometry.mem_closedsquaresample_iff_int
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.mem_closedSquareSample_iff_int

Provenance-ID: 8767-tnlean.peps.arealaw.geometry.card_edgeboundary_closedsquaresample_le
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.card_edgeBoundary_closedSquareSample_le

Provenance-ID: 8767-tnlean.peps.arealaw.geometry.squareradius
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.squareRadius

Provenance-ID: 8767-tnlean.peps.arealaw.geometry.mem_closedsquaresample_iff_radius
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.mem_closedSquareSample_iff_radius

Provenance-ID: 8767-tnlean.peps.arealaw.geometry.abs_coordinate_sub_le_one_of_adj
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.abs_coordinate_sub_le_one_of_adj

Provenance-ID: 8767-tnlean.peps.arealaw.geometry.mem_closedsquaresample_of_adj
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.mem_closedSquareSample_of_adj

Provenance-ID: 8767-tnlean.peps.arealaw.geometry.abs_squareradius_sub_le_one_of_adj
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.abs_squareRadius_sub_le_one_of_adj

Provenance-ID: 8767-tnlean.peps.arealaw.geometry.mem_edgeboundary_pair_iff
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.mem_edgeBoundary_pair_iff

Provenance-ID: 8767-tnlean.peps.arealaw.geometry.mem_edgeboundary_closedsquaresample_iff
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.mem_edgeBoundary_closedSquareSample_iff

Provenance-ID: 8767-tnlean.peps.arealaw.geometry.card_closedsquaresample_le
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.card_closedSquareSample_le

Provenance-ID: 8767-tnlean.peps.arealaw.geometry.card_closedsquaresample_le_eightyone
Downstream declaration: TNLean.PEPS.AreaLaw.Geometry.card_closedSquareSample_le_eightyOne
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The domain sites in the closed real square of center `c` and radius `r`.
Source: polynomial-PEPS `03-patches.tex`, lines 14–22. -/
noncomputable def closedSquareSample (Λ : Finset (ℤ × ℤ)) (c : ℝ × ℝ) (r : ℝ) :
    Finset (Site Λ) := by
  classical
  exact Finset.univ.filter fun x ↦
    |(x.1.1 : ℝ) - c.1| ≤ r ∧ |(x.1.2 : ℝ) - c.2| ≤ r

/-- Both coordinate inequalities include equality on the square boundary. -/
@[simp] theorem mem_closedSquareSample {Λ : Finset (ℤ × ℤ)} {c : ℝ × ℝ} {r : ℝ}
    {x : Site Λ} :
    x ∈ closedSquareSample Λ c r ↔
      |(x.1.1 : ℝ) - c.1| ≤ r ∧ |(x.1.2 : ℝ) - c.2| ≤ r := by
  classical
  simp [closedSquareSample]

/-- Increasing the radius enlarges the sampled square, including clipped samples. -/
theorem closedSquareSample_mono (Λ : Finset (ℤ × ℤ)) (c : ℝ × ℝ)
    {r s : ℝ} (hrs : r ≤ s) : closedSquareSample Λ c r ⊆ closedSquareSample Λ c s := by
  intro x hx
  rw [mem_closedSquareSample] at hx ⊢
  exact ⟨hx.1.trans hrs, hx.2.trans hrs⟩

/-- The closed-square condition expressed by integer coordinate intervals. -/
theorem mem_closedSquareSample_iff_int {Λ : Finset (ℤ × ℤ)} {c : ℝ × ℝ} {r : ℝ}
    {x : Site Λ} :
    x ∈ closedSquareSample Λ c r ↔
      x.1.1 ∈ Finset.Icc ⌈c.1 - r⌉ ⌊c.1 + r⌋ ∧
        x.1.2 ∈ Finset.Icc ⌈c.2 - r⌉ ⌊c.2 + r⌋ := by
  simp only [mem_closedSquareSample, abs_le, Finset.mem_Icc, Int.ceil_le, Int.le_floor]
  constructor <;> rintro ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩ <;> constructor <;> constructor <;> linarith

private def rectangleBoundaryEdges (a b : ℤ × ℤ) : Finset (Sym2 (ℤ × ℤ)) :=
  ((Finset.Icc a.2 b.2).image fun z ↦ s((a.1, z), (a.1 - 1, z))) ∪
    ((Finset.Icc a.2 b.2).image fun z ↦ s((b.1, z), (b.1 + 1, z))) ∪
    ((Finset.Icc a.1 b.1).image fun z ↦ s((z, a.2), (z, a.2 - 1))) ∪
    ((Finset.Icc a.1 b.1).image fun z ↦ s((z, b.2), (z, b.2 + 1)))

private theorem mem_rectangleBoundaryEdges {Λ : Finset (ℤ × ℤ)}
    {a b : ℤ × ℤ} {x y : Site Λ} (hxy : (domainGraph Λ).Adj x y)
    (hx : x.1.1 ∈ Finset.Icc a.1 b.1 ∧ x.1.2 ∈ Finset.Icc a.2 b.2)
    (hy : ¬(y.1.1 ∈ Finset.Icc a.1 b.1 ∧ y.1.2 ∈ Finset.Icc a.2 b.2)) :
    s(x.1, y.1) ∈ rectangleBoundaryEdges a b := by
  simp only [Finset.mem_Icc] at hx hy
  simp only [rectangleBoundaryEdges, Finset.mem_union, Finset.mem_image]
  rcases hxy with ⟨h₂, h₁ | h₁⟩ | ⟨h₁, h₂ | h₂⟩
  · refine Or.inl (Or.inl (Or.inr ⟨x.1.2, Finset.mem_Icc.mpr hx.2, ?_⟩))
    have hb : x.1.1 = b.1 := by omega
    apply Sym2.eq_iff.mpr
    left
    constructor <;> apply Prod.ext <;> dsimp <;> omega
  · refine Or.inl (Or.inl (Or.inl ⟨x.1.2, Finset.mem_Icc.mpr hx.2, ?_⟩))
    have ha : x.1.1 = a.1 := by omega
    apply Sym2.eq_iff.mpr
    left
    constructor <;> apply Prod.ext <;> dsimp <;> omega
  · refine Or.inr ⟨x.1.1, Finset.mem_Icc.mpr hx.1, ?_⟩
    have hb : x.1.2 = b.2 := by omega
    apply Sym2.eq_iff.mpr
    left
    constructor <;> apply Prod.ext <;> dsimp <;> omega
  · refine Or.inl (Or.inr ⟨x.1.1, Finset.mem_Icc.mpr hx.1, ?_⟩)
    have ha : x.1.2 = a.2 := by omega
    apply Sym2.eq_iff.mpr
    left
    constructor <;> apply Prod.ext <;> dsimp <;> omega

private theorem card_rectangleBoundaryEdges_le (a b : ℤ × ℤ) :
    (rectangleBoundaryEdges a b).card ≤
      2 * (Finset.Icc a.1 b.1).card + 2 * (Finset.Icc a.2 b.2).card := by
  unfold rectangleBoundaryEdges
  calc
    _ ≤ ((Finset.Icc a.2 b.2).image fun z ↦ s((a.1, z), (a.1 - 1, z))).card +
        ((Finset.Icc a.2 b.2).image fun z ↦ s((b.1, z), (b.1 + 1, z))).card +
        ((Finset.Icc a.1 b.1).image fun z ↦ s((z, a.2), (z, a.2 - 1))).card +
        ((Finset.Icc a.1 b.1).image fun z ↦ s((z, b.2), (z, b.2 + 1))).card := by
      repeat first | apply (Finset.card_union_le _ _).trans | gcongr
    _ ≤ _ := by
      have h₁ := Finset.card_image_le (s := Finset.Icc a.2 b.2)
        (f := fun z ↦ s((a.1, z), (a.1 - 1, z)))
      have h₂ := Finset.card_image_le (s := Finset.Icc a.2 b.2)
        (f := fun z ↦ s((b.1, z), (b.1 + 1, z)))
      have h₃ := Finset.card_image_le (s := Finset.Icc a.1 b.1)
        (f := fun z ↦ s((z, a.2), (z, a.2 - 1)))
      have h₄ := Finset.card_image_le (s := Finset.Icc a.1 b.1)
        (f := fun z ↦ s((z, b.2), (z, b.2 + 1)))
      omega

private theorem card_integerInterval_le (c r : ℝ) (hr : 0 ≤ r) :
    ((Finset.Icc ⌈c - r⌉ ⌊c + r⌋).card : ℝ) ≤ 2 * r + 1 := by
  by_cases h : ⌈c - r⌉ ≤ ⌊c + r⌋ + 1
  · have hc := Int.card_Icc_of_le _ _ h
    have hc' : ((Finset.Icc ⌈c - r⌉ ⌊c + r⌋).card : ℝ) =
        (⌊c + r⌋ : ℝ) + 1 - ⌈c - r⌉ := by exact_mod_cast hc
    rw [hc']
    linarith [Int.floor_le (c + r), Int.le_ceil (c - r)]
  · have he : Finset.Icc ⌈c - r⌉ ⌊c + r⌋ = ∅ :=
      Finset.Icc_eq_empty_of_lt (by omega)
    rw [he, Finset.card_empty, Nat.cast_zero]
    linarith

/-- A sampled closed square has at most `8 * r + 4` unordered crossing edges.
Source: polynomial-PEPS `03-patches.tex`, lines 323–326. The statement
holds for every finite induced domain, including holes and disconnected domains. -/
theorem card_edgeBoundary_closedSquareSample_le (Λ : Finset (ℤ × ℤ)) (c : ℝ × ℝ)
    {r : ℝ} (hr : 0 ≤ r) :
    ((edgeBoundary Λ (closedSquareSample Λ c r)).card : ℝ) ≤ 8 * r + 4 := by
  classical
  let a : ℤ × ℤ := (⌈c.1 - r⌉, ⌈c.2 - r⌉)
  let b : ℤ × ℤ := (⌊c.1 + r⌋, ⌊c.2 + r⌋)
  have hcard : (edgeBoundary Λ (closedSquareSample Λ c r)).card ≤
      (rectangleBoundaryEdges a b).card := by
    apply Finset.card_le_card_of_injOn (Sym2.map Subtype.val)
    · intro e he
      obtain ⟨he, x, hx, y, hy, rfl⟩ := Finset.mem_filter.mp he
      have hxy : (domainGraph Λ).Adj x y := by simpa using he
      exact mem_rectangleBoundaryEdges hxy
        (mem_closedSquareSample_iff_int.mp hx)
        (fun h ↦ hy (mem_closedSquareSample_iff_int.mpr h))
    · exact (Sym2.map.injective Subtype.val_injective).injOn
  have hbound := hcard.trans (card_rectangleBoundaryEdges_le a b)
  have hreal : ((edgeBoundary Λ (closedSquareSample Λ c r)).card : ℝ) ≤
      2 * ((Finset.Icc ⌈c.1 - r⌉ ⌊c.1 + r⌋).card : ℝ) +
        2 * ((Finset.Icc ⌈c.2 - r⌉ ⌊c.2 + r⌋).card : ℝ) := by
    exact_mod_cast hbound
  linarith [card_integerInterval_le c.1 r hr, card_integerInterval_le c.2 r hr]

/-- The sup-norm distance of a lattice point from a real center.
Source: polynomial-PEPS `03-patches.tex`, lines 215–217. -/
noncomputable def squareRadius (c : ℝ × ℝ) (x : ℤ × ℤ) : ℝ :=
  max |(x.1 : ℝ) - c.1| |(x.2 : ℝ) - c.2|

/-- A closed square includes precisely the sites at radial distance at most its radius. -/
theorem mem_closedSquareSample_iff_radius {Λ : Finset (ℤ × ℤ)} {c : ℝ × ℝ}
    {r : ℝ} {x : Site Λ} :
    x ∈ closedSquareSample Λ c r ↔ squareRadius c x.1 ≤ r := by
  simp [squareRadius]

/-- The two coordinate displacements of nearest neighbors are at most one. -/
theorem abs_coordinate_sub_le_one_of_adj {Λ : Finset (ℤ × ℤ)} {x y : Site Λ}
    (hxy : (domainGraph Λ).Adj x y) :
    |(x.1.1 : ℝ) - y.1.1| ≤ 1 ∧ |(x.1.2 : ℝ) - y.1.2| ≤ 1 := by
  have hi : |x.1.1 - y.1.1| ≤ (1 : ℤ) ∧ |x.1.2 - y.1.2| ≤ (1 : ℤ) := by
    simp only [abs_le]
    rcases hxy with ⟨h₂, h₁ | h₁⟩ | ⟨h₁, h₂ | h₂⟩ <;> omega
  exact_mod_cast hi

/-- A nearest neighbor of a sampled site lies in the square enlarged by one. -/
theorem mem_closedSquareSample_of_adj {Λ : Finset (ℤ × ℤ)} {c : ℝ × ℝ}
    {r : ℝ} {x y : Site Λ} (hxy : (domainGraph Λ).Adj x y)
    (hx : x ∈ closedSquareSample Λ c r) : y ∈ closedSquareSample Λ c (r + 1) := by
  have hd := abs_coordinate_sub_le_one_of_adj hxy.symm
  rw [mem_closedSquareSample] at hx ⊢
  constructor
  · linarith [abs_sub_le (y.1.1 : ℝ) x.1.1 c.1]
  · linarith [abs_sub_le (y.1.2 : ℝ) x.1.2 c.2]

/-- Radial distances of nearest neighbors differ by at most one.
Source: polynomial-PEPS `03-patches.tex`, lines 215–217. -/
theorem abs_squareRadius_sub_le_one_of_adj {Λ : Finset (ℤ × ℤ)} {c : ℝ × ℝ}
    {x y : Site Λ} (hxy : (domainGraph Λ).Adj x y) :
    |squareRadius c x.1 - squareRadius c y.1| ≤ 1 := by
  have hx : x ∈ closedSquareSample Λ c (squareRadius c x.1) :=
    mem_closedSquareSample_iff_radius.mpr le_rfl
  have hy : y ∈ closedSquareSample Λ c (squareRadius c y.1) :=
    mem_closedSquareSample_iff_radius.mpr le_rfl
  have h₁ := mem_closedSquareSample_iff_radius.mp (mem_closedSquareSample_of_adj hxy hx)
  have h₂ := mem_closedSquareSample_iff_radius.mp (mem_closedSquareSample_of_adj hxy.symm hy)
  rw [abs_le]
  constructor <;> linarith

/-- An unordered pair crosses a cut exactly when its adjacent endpoints are on opposite sides. -/
theorem mem_edgeBoundary_pair_iff {Λ : Finset (ℤ × ℤ)} {A : Finset (Site Λ)}
    {x y : Site Λ} :
    s(x, y) ∈ edgeBoundary Λ A ↔ (domainGraph Λ).Adj x y ∧
      ((x ∈ A ∧ y ∉ A) ∨ (y ∈ A ∧ x ∉ A)) := by
  classical
  simp only [edgeBoundary, Finset.mem_filter, SimpleGraph.mem_edgeFinset,
    SimpleGraph.mem_edgeSet, Sym2.eq_iff]
  constructor
  · rintro ⟨hxy, a, ha, b, hb, hab⟩
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hxy, Or.inl ⟨ha, hb⟩⟩
    · exact ⟨hxy, Or.inr ⟨ha, hb⟩⟩
  · rintro ⟨hxy, h | h⟩
    · exact ⟨hxy, x, h.1, y, h.2, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨hxy, y, h.1, x, h.2, Or.inr ⟨rfl, rfl⟩⟩

/-- The exact crossing interval is left-closed and right-open.
Source: polynomial-PEPS `03-patches.tex`, lines 218–223. -/
theorem mem_edgeBoundary_closedSquareSample_iff {Λ : Finset (ℤ × ℤ)} {c : ℝ × ℝ}
    {r : ℝ} {x y : Site Λ} (hxy : (domainGraph Λ).Adj x y) :
    s(x, y) ∈ edgeBoundary Λ (closedSquareSample Λ c r) ↔
      min (squareRadius c x.1) (squareRadius c y.1) ≤ r ∧
        r < max (squareRadius c x.1) (squareRadius c y.1) := by
  rw [mem_edgeBoundary_pair_iff, and_iff_right hxy]
  simp only [mem_closedSquareSample_iff_radius, not_le, min_le_iff, lt_max_iff]
  grind

/-- A closed square has at most `(2 * r + 1)²` sampled lattice sites.
Source: polynomial-PEPS `03-patches.tex`, lines 53–54. -/
theorem card_closedSquareSample_le (Λ : Finset (ℤ × ℤ)) (c : ℝ × ℝ)
    {r : ℝ} (hr : 0 ≤ r) :
    ((closedSquareSample Λ c r).card : ℝ) ≤ (2 * r + 1) ^ 2 := by
  classical
  have hcard : (closedSquareSample Λ c r).card ≤
      ((Finset.Icc ⌈c.1 - r⌉ ⌊c.1 + r⌋).product
        (Finset.Icc ⌈c.2 - r⌉ ⌊c.2 + r⌋)).card := by
    apply Finset.card_le_card_of_injOn Subtype.val
    · intro x hx
      exact Finset.mem_product.mpr (mem_closedSquareSample_iff_int.mp hx)
    · exact Subtype.val_injective.injOn
  have hp := Finset.card_product
    (Finset.Icc ⌈c.1 - r⌉ ⌊c.1 + r⌋) (Finset.Icc ⌈c.2 - r⌉ ⌊c.2 + r⌋)
  have hcard' := hcard.trans_eq hp
  have hreal : ((closedSquareSample Λ c r).card : ℝ) ≤
      ((Finset.Icc ⌈c.1 - r⌉ ⌊c.1 + r⌋).card : ℝ) *
        ((Finset.Icc ⌈c.2 - r⌉ ⌊c.2 + r⌋).card : ℝ) := by exact_mod_cast hcard'
  refine hreal.trans ?_
  rw [pow_two]
  exact mul_le_mul (card_integerInterval_le c.1 r hr) (card_integerInterval_le c.2 r hr)
    (by positivity) (by positivity)

/-- Patches of radius at most four contain at most 81 sites.
Source: polynomial-PEPS `03-patches.tex`, lines 53–54. -/
theorem card_closedSquareSample_le_eightyOne (Λ : Finset (ℤ × ℤ)) (c : ℝ × ℝ)
    {r : ℝ} (hr : 0 ≤ r) (hr4 : r ≤ 4) : (closedSquareSample Λ c r).card ≤ 81 := by
  have h := card_closedSquareSample_le Λ c hr
  have hbound : (2 * r + 1) ^ 2 ≤ (81 : ℝ) := by nlinarith
  exact_mod_cast h.trans hbound

end TNLean.PEPS.AreaLaw.Geometry
