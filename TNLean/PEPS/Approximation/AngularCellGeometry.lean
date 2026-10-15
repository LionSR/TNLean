/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.AngularGridCells
import TNLean.PEPS.Approximation.AngularResetWidth

/-!
# Ambient cell enlargements and physical clearance

The cells are actual half-open squares in a translated grid in the ambient
sup metric. Selecting every cell meeting an enlargement covers that
enlargement and adds at most one cell side to its radius. The statements
below apply before intersecting with an arbitrary physical domain, so holes,
boundary clipping and empty regions cause no change in the constants.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground
states*, September 24, 2026, Proposition 3.4, `02-information.tex`, lines
692–744, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
These are original Lean proofs of the manuscript's geometry; no upstream
Lean proof text was reused. No conditional-information or reset theorem
is assumed or proved here.
-/

namespace TNLean.PEPS.Approximation.AngularGrid

/-- The union of all grid cells meeting the indicated ambient enlargement.
Source: Proposition 3.4, definition of the region before physical sampling. -/
def selectedRegion (o : ℝ × ℝ) (q r : ℝ) (A : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {x | ∃ i, touches o q r A i ∧ x ∈ cell o q i}

/-- Ambient enlargement commutes with a union, including empty sets. -/
theorem near_union (r : ℝ) (A B : Set (ℝ × ℝ)) :
    near r (A ∪ B) = near r A ∪ near r B := by
  ext x
  constructor
  · rintro ⟨y, hy | hy, hxy⟩
    · exact Or.inl ⟨y, hy, hxy⟩
    · exact Or.inr ⟨y, hy, hxy⟩
  · rintro (⟨y, hy, hxy⟩ | ⟨y, hy, hxy⟩)
    · exact ⟨y, Or.inl hy, hxy⟩
    · exact ⟨y, Or.inr hy, hxy⟩

/-- Enlargements increase with both the set and the radius. -/
theorem near_mono {A B : Set (ℝ × ℝ)} {r t : ℝ}
    (hAB : A ⊆ B) (hrt : r ≤ t) : near r A ⊆ near t B := by
  rintro x ⟨y, hy, hxy⟩
  exact ⟨y, hAB hy, hxy.trans hrt⟩

/-- Every point of the enlargement belongs to a selected cell. -/
theorem near_subset_selectedRegion {o : ℝ × ℝ} {q r : ℝ}
    (A : Set (ℝ × ℝ)) (hq : 0 < q) :
    near r A ⊆ selectedRegion o q r A := by
  intro x hx
  exact ⟨owner o q x, ⟨x, mem_cell_owner hq, hx⟩, mem_cell_owner hq⟩

/-- A whole selected cell lies within one cell side of the enlargement.
Source: Proposition 3.4, the radius `1.5 a' s + d s`. -/
theorem selectedRegion_subset_near {o : ℝ × ℝ} {q r : ℝ}
    (A : Set (ℝ × ℝ)) (hq : 0 < q) :
    selectedRegion o q r A ⊆ near (r + q) A := by
  rintro x ⟨i, ⟨y, hy, z, hz, hyz⟩, hx⟩
  refine ⟨z, hz, ?_⟩
  have hxy := dist_le_of_mem_cell hq hx hy
  have htri := dist_triangle x y z
  linarith

/-- The selected old group is part of the current selected region whenever
the previously processed points are included in the current points. -/
theorem selectedRegion_mono {o : ℝ × ℝ} {q r : ℝ}
    {A B : Set (ℝ × ℝ)} (hAB : A ⊆ B) :
    selectedRegion o q r A ⊆ selectedRegion o q r B := by
  rintro x ⟨i, ⟨y, hy, z, hz, hyz⟩, hx⟩
  exact ⟨i, ⟨y, hy, z, hAB hz, hyz⟩, hx⟩

/-- A selected cell that does not meet the old enlargement meets the new one.
Source: Proposition 3.4, the group of newly added cells. -/
theorem touches_new_of_not_old {o : ℝ × ℝ} {q r : ℝ}
    {A B : Set (ℝ × ℝ)} {i : ℤ × ℤ}
    (hi : touches o q r (A ∪ B) i) (hold : ¬ touches o q r A i) :
    touches o q r B i := by
  rcases hi with ⟨x, hx, y, hy | hy, hxy⟩
  · exact (hold ⟨x, hx, y, hy, hxy⟩).elim
  · exact ⟨x, hx, y, hy, hxy⟩

/-- The cells newly selected after adjoining a finitely covered layer form an
actual finite set. The old group need not satisfy a cardinality bound. -/
theorem exists_newIndices_scaled {o : ℝ × ℝ} {d s R r : ℝ}
    (A : Set (ℝ × ℝ)) {B : Set (ℝ × ℝ)} {F : Finset (ℝ × ℝ)}
    (hd : 0 < d) (hs : 0 < s)
    (hcover : ∀ x ∈ B, ∃ c ∈ F, dist x c ≤ R * s) :
    ∃ S : Finset (ℤ × ℤ),
      (∀ i, i ∈ S ↔ touches o (d * s) (r * s) (A ∪ B) i ∧
        ¬ touches o (d * s) (r * s) A i) ∧
      S.card ≤ F.card * (2 * ⌈(R + r) / d⌉₊ + 3) ^ 2 := by
  classical
  obtain ⟨T, hT, hcard⟩ := exists_selectedIndices_scaled (o := o) (r := r) hd hs hcover
  refine ⟨T.filter (fun i ↦ ¬ touches o (d * s) (r * s) A i), ?_,
    (Finset.card_filter_le _ _).trans hcard⟩
  intro i
  rw [Finset.mem_filter, hT]
  constructor
  · rintro ⟨⟨x, hx, y, hy, hxy⟩, hi⟩
    exact ⟨⟨x, hx, y, Or.inr hy, hxy⟩, hi⟩
  · rintro ⟨hi, hold⟩
    exact ⟨touches_new_of_not_old hi hold, hold⟩

/-- A selected region inherits the separation after paying its enlargement,
one cell side and the enlargement on the other region. -/
theorem selectedRegion_clearance {o : ℝ × ℝ} {q r t b : ℝ}
    {A E : Set (ℝ × ℝ)} (hq : 0 < q)
    (hsep : ∀ x ∈ A, ∀ y ∈ E, b ≤ dist x y)
    {x y : ℝ × ℝ} (hx : x ∈ selectedRegion o q r A) (hy : y ∈ near t E) :
    b - r - t - q ≤ dist x y := by
  obtain ⟨u, hu, hxu⟩ := selectedRegion_subset_near A hq hx
  obtain ⟨v, hv, hyv⟩ := hy
  have hsep' := hsep u hu v hv
  have htri₁ := dist_triangle u x v
  have htri₂ := dist_triangle x y v
  rw [dist_comm u x] at htri₁
  linarith

/-- A core point and a point outside a larger closed enlargement are separated
by strictly more than the difference of the radii. -/
theorem near_core_clearance {A : Set (ℝ × ℝ)} {r t : ℝ}
    {x y : ℝ × ℝ} (hx : x ∈ near r A) (hy : y ∉ near t A) :
    t - r < dist x y := by
  obtain ⟨z, hz, hxz⟩ := hx
  by_contra h
  have hxy : dist x y ≤ t - r := le_of_not_gt h
  apply hy
  refine ⟨z, hz, ?_⟩
  have htri := dist_triangle y x z
  rw [dist_comm y x] at htri
  linarith

/-- The entire old cell group fits inside its preceding-scale enlargement.
The constants are fixed independently of the sets and the physical domain.
Source: Proposition 3.4, lines 701–705. -/
theorem old_selectedRegion_subset {o : ℝ × ℝ} {a' d s : ℝ}
    (A : Set (ℝ × ℝ)) (ha' : 0 < a') (hd : 0 < d)
    (hda' : d < a' / 4) (hs : 0 < s) :
    selectedRegion o (d * s) ((3 / 2) * a' * s) A ⊆ near (2 * a' * s) A := by
  apply (selectedRegion_subset_near A (mul_pos hd hs)).trans
  apply near_mono (Set.Subset.refl A)
  nlinarith [mul_pos ha' hs, mul_lt_mul_of_pos_right hda' hs]

/-- The enlarged exterior fits inside its preceding-scale enlargement. -/
theorem exterior_near_subset {a' s : ℝ} (E : Set (ℝ × ℝ))
    (ha' : 0 ≤ a') (hs : 0 ≤ s) :
    near ((3 / 2) * a' * s) E ⊆ near (2 * a' * s) E := by
  apply near_mono (Set.Subset.refl E)
  nlinarith [mul_nonneg ha' hs]

/-- Both physically sampled cores are contained in their enlarged regions. -/
theorem angular_core_subsets {o : ℝ × ℝ} {a' d s : ℝ}
    (Λ A E : Set (ℝ × ℝ)) (ha' : 0 ≤ a') (hd : 0 < d) (hs : 0 < s) :
    (Λ ∩ near (a' * s) A ⊆
      Λ ∩ selectedRegion o (d * s) ((3 / 2) * a' * s) A) ∧
    (Λ ∩ near (a' * s) E ⊆ Λ ∩ near ((3 / 2) * a' * s) E) := by
  have hr : a' * s ≤ (3 / 2) * a' * s := by
    nlinarith [mul_nonneg ha' hs.le]
  constructor
  · rintro x ⟨hxΛ, hx⟩
    exact ⟨hxΛ, near_subset_selectedRegion A (mul_pos hd hs)
      (near_mono (Set.Subset.refl A) hr hx)⟩
  · rintro x ⟨hxΛ, hx⟩
    exact ⟨hxΛ, near_mono (Set.Subset.refl E) hr hx⟩

/-- The printed cell-clearance coefficient is positive under the source's
fixed choice of geometric constants. -/
theorem angular_clearance_pos {a a' d : ℝ} (ha' : 0 < a')
    (ha'a : a' < a / 100) (hd : d < a' / 4) :
    0 < a / 2 - 3 * a' - d := by
  linarith

/-- Every selected cell point has the source's clearance from the enlarged
exterior, before any physical clipping. -/
theorem angular_selectedRegion_clearance {o : ℝ × ℝ} {a a' d s : ℝ}
    {A E : Set (ℝ × ℝ)} (hd : 0 < d) (hs : 0 < s)
    (hsep : ∀ x ∈ A, ∀ y ∈ E, (a / 2) * s ≤ dist x y)
    {x y : ℝ × ℝ}
    (hx : x ∈ selectedRegion o (d * s) ((3 / 2) * a' * s) A)
    (hy : y ∈ near ((3 / 2) * a' * s) E) :
    (a / 2 - 3 * a' - d) * s ≤ dist x y := by
  have h := selectedRegion_clearance (mul_pos hd hs) hsep hx hy
  nlinarith

/-- Arbitrary physical clipping preserves disjointness of the two regions.
Source: Proposition 3.4, the physical regions `R` and `C`. -/
theorem angular_physical_disjoint {o : ℝ × ℝ} {a a' d s : ℝ}
    (Λ : Set (ℝ × ℝ)) {A E : Set (ℝ × ℝ)}
    (ha' : 0 < a') (ha'a : a' < a / 100) (hd : 0 < d)
    (hda' : d < a' / 4) (hs : 0 < s)
    (hsep : ∀ x ∈ A, ∀ y ∈ E, (a / 2) * s ≤ dist x y) :
    Disjoint (Λ ∩ selectedRegion o (d * s) ((3 / 2) * a' * s) A)
      (Λ ∩ near ((3 / 2) * a' * s) E) := by
  rw [Set.disjoint_left]
  intro x hx hy
  have h := angular_selectedRegion_clearance hd hs hsep hx.2 hy.2
  have hp := mul_pos (angular_clearance_pos ha' ha'a hda') hs
  exact (lt_irrefl (0 : ℝ)) (by simpa only [dist_self] using hp.trans_le h)

/-- The target core has at least the printed half-radius buffer from the
physical complement of the selected cells; in fact the inequality is strict. -/
theorem angular_target_core_clearance {o : ℝ × ℝ} {a' d s : ℝ}
    {Λ A : Set (ℝ × ℝ)} (hd : 0 < d) (hs : 0 < s)
    {x y : ℝ × ℝ} (hx : x ∈ Λ ∩ near (a' * s) A)
    (hy : y ∈ Λ \ selectedRegion o (d * s) ((3 / 2) * a' * s) A) :
    a' * s / 2 < dist x y := by
  have hout : y ∉ near ((3 / 2) * a' * s) A :=
    fun h ↦ hy.2 (near_subset_selectedRegion A (mul_pos hd hs) h)
  have h := near_core_clearance hx.2 hout
  linarith

/-- The exterior core has the same half-radius buffer after physical clipping. -/
theorem angular_exterior_core_clearance {a' s : ℝ}
    {Λ E : Set (ℝ × ℝ)} {x y : ℝ × ℝ}
    (hx : x ∈ Λ ∩ near (a' * s) E)
    (hy : y ∈ Λ \ near ((3 / 2) * a' * s) E) :
    a' * s / 2 < dist x y := by
  have h := near_core_clearance hx.2 hy.2
  linarith

/-- The accepted uniform numerical estimate fits the geometric choice `a'/3`.
The slope and threshold are chosen before every system size and annular scale.
This does not assert the physical information-reset theorem. -/
theorem exists_angular_cell_reset_width (K C₃ C₄ a' : ℝ) (ha' : 0 < a') :
    ∃ D : ℝ, 1 ≤ D ∧ 4 * C₄ / (a' / 3) ≤ D ∧
      ∃ L₀ : ℝ, 2 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
        ∀ s : ℝ, D * Real.log L ≤ s →
          C₃ * (1 + Real.log s) ^ K + C₄ * Real.log L < (a' / 3) * s := by
  obtain ⟨D, hD, hCD, L₀, hL₀, hbound⟩ :=
    exists_angular_reset_width_bound K C₃ C₄ (a' / 3) (by positivity)
  refine ⟨D, hD, hCD, L₀, hL₀, fun L hL s hs ↦ ?_⟩
  exact ((hbound L hL).2 s hs).1.trans_lt ((hbound L hL).2 s hs).2

end TNLean.PEPS.Approximation.AngularGrid
