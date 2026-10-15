/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.BirthSeparationRepair
import TNLean.PEPS.AreaLaw.Geometry.BirthSeparationAtoms
import TNLean.PEPS.AreaLaw.Geometry.FanFrontiers
import TNLean.PEPS.AreaLaw.Geometry.TemplatePolygons
import TNLean.PEPS.AreaLaw.Geometry.AdjacentScales
import TNLean.PEPS.AreaLaw.Geometry.CellSides
import TNLean.PEPS.AreaLaw.Geometry.FanSideContacts
import TNLean.PEPS.AreaLaw.Geometry.InitialRegionInterfaces
import TNLean.PEPS.AreaLaw.Geometry.InitialRegionInteriors
import TNLean.PEPS.AreaLaw.Geometry.InitialRegionRegularity

/-!
# Birth separation of the initial belt tiles

Let `x` be an initial belt tile in a belt cell `Q` of side `u = t_k`. Its closed
birth is a union of fan triangles of `Q`. Every earlier or peer identifier `y`
of the same label, that is, every primary and every other initial belt tile,
has final actual region at distance at least `c₁ u^ρ₀` from the birth of `x`,
for one constant `c₁ > 0` chosen before all data.

Normalize `Q` to `[0, 4]²`. Near `Q` only the same and the adjacent layers
occur, so every fan triangle and every closed fine cell meeting the region
of interest is bounded by lines of the normalized belt arrangement. Each point
of the birth of `x` lies in an atom contained in that birth, and each point of
the open region of `y` near `Q` lies in an atom contained in the birth of `y`.

* *No common segments.* The two births of the same label share no
  nondegenerate segment, so the two atoms meet only in integer points.
* *Compactness.* The uniform atom dichotomy gives distance at least `η`, in
  normalized units, unless both points lie within `1/4` of a common integer
  point `q` of the two atoms, where the angular estimate holds.
* *Contacts are marks of `Q`.* A common point of the two births lies in the
  closed cell `Q`. If `y` is another run of `Q`, it is the center of `Q`. Otherwise
  it lies on the boundary of `Q`; a contact with a coordinate of odd normalized
  value would lie inside an elementary side of `Q`, and the atom of `y` would
  share a unit segment of that side with the fan triangle of `x`. Hence the
  contact is one of the nine marks of `Q`.
* *The following trim.* The first removal cuts from every old identifier the
  square of half-side `d(S) ≥ u^ρ₀ / 4` about each mark of `Q`, so the final
  region of `y` stays at distance more than `u^ρ₀ / 4` from the contact.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:birth-separation`, lines 573–659,
with the belt case of the finite local patterns in lines 597–604; the belt
construction and its interfaces, lines 299–330; the trim, lines 380–399;
open actual regions and closed births, lines 545–561; and the order of
identifiers, lines 563–571.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-! ### Normalization at a fine cell -/

section Normalize

variable (o : ℝ × ℝ) (ℓ : ℕ) (z : ℤ × ℤ)

/-- The lower left corner of the fine cell of scale `ℓ` and index `z`. -/
def beltCellOrigin : ℝ × ℝ := (o.1 + (2 : ℝ) ^ ℓ * z.1, o.2 + (2 : ℝ) ^ ℓ * z.2)

/-- The normalization sending the fine cell of scale `ℓ` and index `z` to
`[0, 4]²`, so that lengths are measured in units of a quarter of its side.
Source: area-law Section 11, `geometry:birth-separation`, lines 592–604. -/
def beltNormalize : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
  (Homeomorph.addRight (-beltCellOrigin o ℓ z)).trans
    (Homeomorph.smulOfNeZero (4 / (2 : ℝ) ^ ℓ) (by positivity))

variable {o ℓ z}

theorem beltNormalize_apply (p : ℝ × ℝ) :
    beltNormalize o ℓ z p = (4 / (2 : ℝ) ^ ℓ) • (p - beltCellOrigin o ℓ z) := by
  simp [beltNormalize, sub_eq_add_neg]

theorem beltNormalize_fst (p : ℝ × ℝ) :
    (beltNormalize o ℓ z p).1 = 4 / (2 : ℝ) ^ ℓ * (p.1 - (o.1 + (2 : ℝ) ^ ℓ * z.1)) := by
  simp [beltNormalize_apply, beltCellOrigin]

theorem beltNormalize_snd (p : ℝ × ℝ) :
    (beltNormalize o ℓ z p).2 = 4 / (2 : ℝ) ^ ℓ * (p.2 - (o.2 + (2 : ℝ) ^ ℓ * z.2)) := by
  simp [beltNormalize_apply, beltCellOrigin]

theorem norm_beltNormalize_sub (p q : ℝ × ℝ) :
    ‖beltNormalize o ℓ z p - beltNormalize o ℓ z q‖ = 4 / (2 : ℝ) ^ ℓ * ‖p - q‖ := by
  rw [beltNormalize_apply, beltNormalize_apply, ← smul_sub, sub_sub_sub_cancel_right,
    norm_smul, Real.norm_of_nonneg (by positivity)]

theorem beltNormalize_combo {a b : ℝ × ℝ} {θ₁ θ₂ : ℝ} (h : θ₁ + θ₂ = 1) :
    beltNormalize o ℓ z (θ₁ • a + θ₂ • b) =
      θ₁ • beltNormalize o ℓ z a + θ₂ • beltNormalize o ℓ z b := by
  ext
  · simp only [beltNormalize_fst, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    linear_combination (4 / (2 : ℝ) ^ ℓ * (o.1 + (2 : ℝ) ^ ℓ * z.1)) * h
  · simp only [beltNormalize_snd, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    linear_combination (4 / (2 : ℝ) ^ ℓ * (o.2 + (2 : ℝ) ^ ℓ * z.2)) * h

theorem convex_beltNormalize_image {P : Set (ℝ × ℝ)} (hP : Convex ℝ P) :
    Convex ℝ (beltNormalize o ℓ z '' P) := by
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ a b ha hb hab
  exact ⟨a • p + b • q, hP hp hq ha hb hab, beltNormalize_combo hab⟩

/-- A segment in the image of a set pulls back to a segment of the set. -/
theorem segment_symm_subset_of_subset_image {X : Set (ℝ × ℝ)} {a b : ℝ × ℝ}
    (h : segment ℝ a b ⊆ beltNormalize o ℓ z '' X) :
    segment ℝ ((beltNormalize o ℓ z).symm a) ((beltNormalize o ℓ z).symm b) ⊆ X := by
  rintro w ⟨θ₁, θ₂, h₁, h₂, h₁₂, rfl⟩
  have hw := h ⟨θ₁, θ₂, h₁, h₂, h₁₂, rfl⟩
  have he : θ₁ • a + θ₂ • b = beltNormalize o ℓ z
      (θ₁ • (beltNormalize o ℓ z).symm a + θ₂ • (beltNormalize o ℓ z).symm b) := by
    rw [beltNormalize_combo h₁₂]; simp
  rw [he] at hw
  obtain ⟨x, hx, hxe⟩ := hw
  rw [← (beltNormalize o ℓ z).injective hxe]
  exact hx

end Normalize

/-! ### Fan triangles and cells bounded by the arrangement -/

section Pieces

variable {o : ℝ × ℝ} {ℓ ℓ' : ℕ} {z w : ℤ × ℤ}

private theorem scale_ratio (hℓ : ℓ ≤ ℓ' + 1) :
    4 / (2 : ℝ) ^ ℓ * (2 : ℝ) ^ ℓ' = 2 * (2 : ℝ) ^ (ℓ' + 1 - ℓ) := by
  have h : ℓ' + 2 = (ℓ' + 1 - ℓ) + 1 + ℓ := by omega
  have h₂ : (2 : ℝ) ^ ℓ' * 4 = (2 : ℝ) ^ (ℓ' + 2) := by rw [pow_add]; norm_num
  rw [h, pow_add, pow_add] at h₂
  field_simp
  linarith

private theorem scale_self : 4 / (2 : ℝ) ^ ℓ * (2 : ℝ) ^ ℓ = 4 := by
  field_simp

/-- Frontier points of a fine cell of an adjacent or coarser scale lie, after
normalization, on lines of the belt arrangement. -/
theorem isBeltArrangementPoint_of_mem_frontier_dyadicCell (hℓ : ℓ ≤ ℓ' + 1) {p : ℝ × ℝ}
    (hp : p ∈ frontier (dyadicCell o ℓ' w)) :
    IsBeltArrangementPoint (beltNormalize o ℓ z p) := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ ℓ' := by positivity
  have hlt (a : ℝ) (i : ℤ) : a + (2 : ℝ) ^ ℓ' * i < a + (2 : ℝ) ^ ℓ' * (i + 1) := by
    nlinarith
  rw [dyadicCell, frontier_prod_eq, frontier_Ico (hlt _ _), frontier_Ico (hlt _ _)] at hp
  have hH := scale_ratio (ℓ := ℓ) (ℓ' := ℓ') hℓ
  have hQ := scale_self (ℓ := ℓ)
  rcases hp with ⟨-, hp₂⟩ | ⟨hp₁, -⟩
  · right; left
    rcases hp₂ with hp₂ | hp₂ <;> (try simp only [Set.mem_singleton_iff] at hp₂)
    · refine ⟨2 * (2 : ℤ) ^ (ℓ' + 1 - ℓ) * w.2 - 4 * z.2, ?_⟩
      rw [beltNormalize_snd, hp₂]; push_cast
      linear_combination (w.2 : ℝ) * hH - (z.2 : ℝ) * hQ
    · refine ⟨2 * (2 : ℤ) ^ (ℓ' + 1 - ℓ) * (w.2 + 1) - 4 * z.2, ?_⟩
      rw [beltNormalize_snd, hp₂]; push_cast
      linear_combination ((w.2 : ℝ) + 1) * hH - (z.2 : ℝ) * hQ
  · left
    rcases hp₁ with hp₁ | hp₁ <;> (try simp only [Set.mem_singleton_iff] at hp₁)
    · refine ⟨2 * (2 : ℤ) ^ (ℓ' + 1 - ℓ) * w.1 - 4 * z.1, ?_⟩
      rw [beltNormalize_fst, hp₁]; push_cast
      linear_combination (w.1 : ℝ) * hH - (z.1 : ℝ) * hQ
    · refine ⟨2 * (2 : ℤ) ^ (ℓ' + 1 - ℓ) * (w.1 + 1) - 4 * z.1, ?_⟩
      rw [beltNormalize_fst, hp₁]; push_cast
      linear_combination ((w.1 : ℝ) + 1) * hH - (z.1 : ℝ) * hQ

private theorem exists_cellFanEnd_eq (split : Fin 4 → Bool) (j : CellFanSlot split) :
    ∃ τ : ℝ, (τ = 0 ∨ τ = 1) ∧ cellFanEnd o ℓ' w split j =
      cellFanCenter o ℓ' w + ((2 : ℝ) ^ ℓ' / 2) • cellFanSideVector j.1 τ := by
  refine ⟨_, ?_, cellFanEnd_eq o ℓ' w split j⟩
  obtain ⟨side, i⟩ := j
  by_cases hs : split side
  · have hi : i.val < 2 := by simpa [hs] using i.isLt
    simp only [hs, if_true]
    rcases (show i.val = 0 ∨ i.val = 1 by omega) with h | h <;> simp [h]
  · simp [hs]

/-- Points of the radial segments of a fan of an adjacent or coarser scale lie,
after normalization, on lines of the belt arrangement. -/
theorem isBeltArrangementPoint_of_mem_radial (hℓ : ℓ ≤ ℓ' + 1) (split : Fin 4 → Bool)
    (j : CellFanSlot split) {p : ℝ × ℝ}
    (hp : p ∈ segment ℝ (cellFanCenter o ℓ' w) (cellFanEnd o ℓ' w split j)) :
    IsBeltArrangementPoint (beltNormalize o ℓ z p) := by
  have hH := scale_ratio (ℓ := ℓ) (ℓ' := ℓ') hℓ
  have hQ := scale_self (ℓ := ℓ)
  obtain ⟨τ, hτ, hend⟩ := exists_cellFanEnd_eq (o := o) (ℓ' := ℓ') (w := w) split j
  rw [hend, segment_eq_image'] at hp
  obtain ⟨θ, -, rfl⟩ := hp
  set v := cellFanSideVector j.1 τ with hv
  show IsBeltArrangementPoint (beltNormalize o ℓ z
    (cellFanCenter o ℓ' w + θ • (cellFanCenter o ℓ' w + ((2 : ℝ) ^ ℓ' / 2) • v -
      cellFanCenter o ℓ' w)))
  rw [add_sub_cancel_left]
  have e₁ : (beltNormalize o ℓ z (cellFanCenter o ℓ' w + θ • (((2 : ℝ) ^ ℓ' / 2) • v))).1 =
      2 * (2 : ℝ) ^ (ℓ' + 1 - ℓ) * w.1 + (2 : ℝ) ^ (ℓ' + 1 - ℓ) +
        θ * (2 : ℝ) ^ (ℓ' + 1 - ℓ) * v.1 - 4 * z.1 := by
    rw [beltNormalize_fst]
    simp only [cellFanCenter, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    linear_combination ((w.1 : ℝ) + 1 / 2 + θ * v.1 / 2) * hH - (z.1 : ℝ) * hQ
  have e₂ : (beltNormalize o ℓ z (cellFanCenter o ℓ' w + θ • (((2 : ℝ) ^ ℓ' / 2) • v))).2 =
      2 * (2 : ℝ) ^ (ℓ' + 1 - ℓ) * w.2 + (2 : ℝ) ^ (ℓ' + 1 - ℓ) +
        θ * (2 : ℝ) ^ (ℓ' + 1 - ℓ) * v.2 - 4 * z.2 := by
    rw [beltNormalize_snd]
    simp only [cellFanCenter, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    linear_combination ((w.2 : ℝ) + 1 / 2 + θ * v.2 / 2) * hH - (z.2 : ℝ) * hQ
  generalize beltNormalize o ℓ z (cellFanCenter o ℓ' w + θ • (((2 : ℝ) ^ ℓ' / 2) • v)) = P
    at e₁ e₂ ⊢
  obtain ⟨side, i⟩ := j
  simp only at hv
  rcases hτ with rfl | rfl <;> fin_cases side <;>
    simp [hv, cellFanSideVector] at e₁ e₂ <;>
    first
    | exact Or.inl ⟨2 * 2 ^ (ℓ' + 1 - ℓ) * w.1 + 2 ^ (ℓ' + 1 - ℓ) - 4 * z.1, by
        rw [e₁]; push_cast; linear_combination⟩
    | exact Or.inr (Or.inl ⟨2 * 2 ^ (ℓ' + 1 - ℓ) * w.2 + 2 ^ (ℓ' + 1 - ℓ) - 4 * z.2, by
        rw [e₂]; push_cast; linear_combination⟩)
    | exact Or.inr (Or.inr (Or.inl
        ⟨2 ^ (ℓ' + 1 - ℓ) * (w.1 + w.2 + 1) - 2 * (z.1 + z.2), by
          rw [e₁, e₂]; push_cast; linear_combination⟩))
    | exact Or.inr (Or.inr (Or.inr
        ⟨2 ^ (ℓ' + 1 - ℓ) * (w.1 - w.2) - 2 * (z.1 - z.2), by
          rw [e₁, e₂]; push_cast; linear_combination⟩))

private theorem isClosed_cellFanPolygon_region (split : Fin 4 → Bool)
    (i : CellFanSlot split) : IsClosed (cellFanPolygon o ℓ' w split i).region := by
  change IsClosed (convexHull ℝ {cellFanCenter o ℓ' w, cellFanStart o ℓ' w split i,
    cellFanEnd o ℓ' w split i})
  exact (((Set.finite_singleton (cellFanEnd o ℓ' w split i)).insert
    (cellFanStart o ℓ' w split i)).insert (cellFanCenter o ℓ' w)).isClosed_convexHull ℝ

/-- **Atoms in a fan triangle.** After normalization at a fine cell of scale
`ℓ`, every point of a fan triangle of a cell of scale `ℓ' ≥ ℓ - 1` lies in an
atom contained in the normalized triangle.
Source: area-law Section 11, `geometry:birth-separation`, lines 597–604. -/
theorem exists_beltAtom_subset_cellFanPolygon (hℓ : ℓ ≤ ℓ' + 1) (split : Fin 4 → Bool)
    (i : CellFanSlot split) {p : ℝ × ℝ} (hp : p ∈ (cellFanPolygon o ℓ' w split i).region) :
    ∃ c s, beltNormalize o ℓ z p ∈ beltAtom c s ∧
      beltAtom c s ⊆ beltNormalize o ℓ z '' (cellFanPolygon o ℓ' w split i).region := by
  refine exists_beltAtom_subset ((beltNormalize o ℓ z).isClosed_image.mpr
    (isClosed_cellFanPolygon_region split i)) (convex_beltNormalize_image ?_) ?_ ?_
    (Set.mem_image_of_mem _ hp)
  · rw [TemplatePolygon.region_eq_convexHull_vertices]; exact convex_convexHull ℝ _
  · rw [← Homeomorph.image_interior]
    exact (cellFanPolygon_interior_nonempty_and_closure_eq o ℓ' w split i).1.image _
  · rw [← Homeomorph.image_frontier]
    rintro _ ⟨q, hq, rfl⟩
    rcases cellFanPolygon_frontier_subset_outer_and_radials o ℓ' w split i hq with h | h
    · exact isBeltArrangementPoint_of_mem_frontier_dyadicCell hℓ h
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp h
      exact isBeltArrangementPoint_of_mem_radial hℓ split j hj

/-- **Atoms in a closed fine cell.** After normalization at a fine cell of
scale `ℓ`, every point of a closed fine cell of scale `ℓ' ≥ ℓ - 1` lies in an
atom contained in the normalized closed cell.
Source: area-law Section 11, `geometry:birth-separation`, lines 597–604. -/
theorem exists_beltAtom_subset_closure_dyadicCell (hℓ : ℓ ≤ ℓ' + 1) {p : ℝ × ℝ}
    (hp : p ∈ closure (dyadicCell o ℓ' w)) :
    ∃ c s, beltNormalize o ℓ z p ∈ beltAtom c s ∧
      beltAtom c s ⊆ beltNormalize o ℓ z '' closure (dyadicCell o ℓ' w) := by
  refine exists_beltAtom_subset ((beltNormalize o ℓ z).isClosed_image.mpr isClosed_closure)
    (convex_beltNormalize_image (convex_closure_dyadicCell o ℓ' w)) ?_ ?_
    (Set.mem_image_of_mem _ hp)
  · rw [← Homeomorph.image_interior]
    refine Set.Nonempty.image _ ?_
    refine (Set.Nonempty.mono (interior_mono subset_closure) ?_)
    rw [interior_dyadicCell_eq_corners]
    obtain ⟨h₁, h₂⟩ := dyadicCellCorner_lt o ℓ' w
    exact (Set.nonempty_Ioo.mpr h₁).prod (Set.nonempty_Ioo.mpr h₂)
  · rw [← Homeomorph.image_frontier]
    rintro _ ⟨q, hq, rfl⟩
    exact isBeltArrangementPoint_of_mem_frontier_dyadicCell hℓ (frontier_closure_subset hq)

end Pieces

/-! ### The normalized reference cell -/

section Reference

variable {o : ℝ × ℝ} {ℓ : ℕ} {z : ℤ × ℤ}

theorem beltNormalize_image_segment (a b : ℝ × ℝ) :
    beltNormalize o ℓ z '' segment ℝ a b =
      segment ℝ (beltNormalize o ℓ z a) (beltNormalize o ℓ z b) := by
  ext q
  constructor
  · rintro ⟨_, ⟨θ₁, θ₂, h₁, h₂, h₁₂, rfl⟩, rfl⟩
    exact ⟨θ₁, θ₂, h₁, h₂, h₁₂, (beltNormalize_combo h₁₂).symm⟩
  · rintro ⟨θ₁, θ₂, h₁, h₂, h₁₂, rfl⟩
    exact ⟨θ₁ • a + θ₂ • b, ⟨θ₁, θ₂, h₁, h₂, h₁₂, rfl⟩, beltNormalize_combo h₁₂⟩

/-- The fan points of the reference cell in normalized coordinates. -/
theorem beltNormalize_cellFanCenter_add (u : ℝ × ℝ) :
    beltNormalize o ℓ z (cellFanCenter o ℓ z + ((2 : ℝ) ^ ℓ / 2) • u) =
      (2 + 2 * u.1, 2 + 2 * u.2) := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ ℓ := by positivity
  ext
  · rw [beltNormalize_fst]
    simp only [cellFanCenter, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    field_simp
    ring
  · rw [beltNormalize_snd]
    simp only [cellFanCenter, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    field_simp
    ring

private theorem cellFanSideVector_int (side : Fin 4) (k : ℤ) :
    ∃ m n : ℤ, cellFanSideVector side k = ((m : ℝ), (n : ℝ)) := by
  fin_cases side
  · exact ⟨1, k, by simp [cellFanSideVector]⟩
  · exact ⟨-k, 1, by simp [cellFanSideVector]⟩
  · exact ⟨-1, -k, by simp [cellFanSideVector]⟩
  · exact ⟨k, -1, by simp [cellFanSideVector]⟩

/-- The endpoints of the elementary sides of the reference cell are, after
normalization, points with even integer coordinates. -/
theorem exists_beltNormalize_cellFanStart_eq (split : Fin 4 → Bool) (i : CellFanSlot split) :
    ∃ m n : ℤ, beltNormalize o ℓ z (cellFanStart o ℓ z split i) =
      (((2 * m : ℤ) : ℝ), ((2 * n : ℤ) : ℝ)) := by
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (if split i.1 then (i.2.val : ℝ) - 1 else -1) = k := by
    split_ifs
    · exact ⟨i.2.val - 1, by push_cast; ring⟩
    · exact ⟨-1, by norm_num⟩
  obtain ⟨m, n, hmn⟩ := cellFanSideVector_int i.1 k
  refine ⟨1 + m, 1 + n, ?_⟩
  rw [cellFanStart_eq, hk, beltNormalize_cellFanCenter_add, hmn]
  push_cast; ext <;> simp <;> ring

theorem exists_beltNormalize_cellFanEnd_eq (split : Fin 4 → Bool) (i : CellFanSlot split) :
    ∃ m n : ℤ, beltNormalize o ℓ z (cellFanEnd o ℓ z split i) =
      (((2 * m : ℤ) : ℝ), ((2 * n : ℤ) : ℝ)) := by
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (if split i.1 then (i.2.val : ℝ) else 1) = k := by
    split_ifs
    · exact ⟨i.2.val, by push_cast; ring⟩
    · exact ⟨1, by norm_num⟩
  obtain ⟨m, n, hmn⟩ := cellFanSideVector_int i.1 k
  refine ⟨1 + m, 1 + n, ?_⟩
  rw [cellFanEnd_eq, hk, beltNormalize_cellFanCenter_add, hmn]
  push_cast; ext <;> simp <;> ring

/-- A point whose normalized coordinates are even and lie in `[0, 4]` is one of
the nine marks of the reference cell.
Source: area-law Section 11, `geometry:initial-stars`, lines 325–330. -/
theorem mem_beltCellMarks_of_beltNormalize_eq {v : ℝ × ℝ} {m n : ℤ} (hm : 0 ≤ m ∧ m ≤ 2)
    (hn : 0 ≤ n ∧ n ≤ 2)
    (h : beltNormalize o ℓ z v = (((2 * m : ℤ) : ℝ), ((2 * n : ℤ) : ℝ))) :
    v ∈ beltCellMarks o ℓ z := by
  classical
  have hpos : (0 : ℝ) < (2 : ℝ) ^ ℓ := by positivity
  let i : Fin 3 × Fin 3 := (⟨m.toNat, by omega⟩, ⟨n.toNat, by omega⟩)
  have hmark : beltNormalize o ℓ z
      (o.1 + (2 : ℝ) ^ ℓ * z.1 + (2 : ℝ) ^ ℓ * (i.1.val : ℝ) / 2,
        o.2 + (2 : ℝ) ^ ℓ * z.2 + (2 : ℝ) ^ ℓ * (i.2.val : ℝ) / 2) =
      (((2 * m : ℤ) : ℝ), ((2 * n : ℤ) : ℝ)) := by
    have e₁ : ((i.1.val : ℕ) : ℝ) = m := by
      simp only [i]; exact_mod_cast Int.toNat_of_nonneg hm.1
    have e₂ : ((i.2.val : ℕ) : ℝ) = n := by
      simp only [i]; exact_mod_cast Int.toNat_of_nonneg hn.1
    ext
    · rw [beltNormalize_fst, e₁]; push_cast; field_simp; ring
    · rw [beltNormalize_snd, e₂]; push_cast; field_simp; ring
  rw [← hmark] at h
  rw [(beltNormalize o ℓ z).injective h]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

/-- The normalized reference cell is `[0, 4]²`. -/
theorem beltNormalize_mem_Icc {v : ℝ × ℝ} (hv : v ∈ closure (dyadicCell o ℓ z)) :
    (beltNormalize o ℓ z v).1 ∈ Set.Icc (0 : ℝ) 4 ∧ (beltNormalize o ℓ z v).2 ∈ Set.Icc (0 : ℝ) 4 := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ ℓ := by positivity
  rw [closure_dyadicCell] at hv
  obtain ⟨⟨h₁, h₂⟩, h₃, h₄⟩ := hv
  rw [beltNormalize_fst, beltNormalize_snd]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · apply mul_nonneg (by positivity); linarith
  · rw [div_mul_eq_mul_div, div_le_iff₀ hpos]; nlinarith
  · apply mul_nonneg (by positivity); linarith
  · rw [div_mul_eq_mul_div, div_le_iff₀ hpos]; nlinarith

private theorem add_mem_uIcc_of_odd {a b j : ℤ} (hj : Odd j) (ha : Even a) (hb : Even b)
    (h : (j : ℝ) ∈ Set.uIcc (a : ℝ) (b : ℝ)) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    (j : ℝ) + σ ∈ Set.uIcc (a : ℝ) (b : ℝ) := by
  rw [Set.mem_uIcc] at h ⊢
  obtain ⟨r, hr⟩ := hj
  obtain ⟨p, hp⟩ := ha
  obtain ⟨q, hq⟩ := hb
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · have a₁ : a ≤ j := by exact_mod_cast h₁
    have a₂ : j ≤ b := by exact_mod_cast h₂
    have b₁ : ((a : ℤ) : ℝ) ≤ ((j - 1 : ℤ) : ℝ) := by exact_mod_cast (by omega : a ≤ j - 1)
    have b₂ : ((j + 1 : ℤ) : ℝ) ≤ ((b : ℤ) : ℝ) := by exact_mod_cast (by omega : j + 1 ≤ b)
    push_cast at b₁ b₂
    left
    rcases hσ with rfl | rfl <;> constructor <;> linarith
  · have a₁ : b ≤ j := by exact_mod_cast h₁
    have a₂ : j ≤ a := by exact_mod_cast h₂
    have b₁ : ((b : ℤ) : ℝ) ≤ ((j - 1 : ℤ) : ℝ) := by exact_mod_cast (by omega : b ≤ j - 1)
    have b₂ : ((j + 1 : ℤ) : ℝ) ≤ ((a : ℤ) : ℝ) := by exact_mod_cast (by omega : j + 1 ≤ a)
    push_cast at b₁ b₂
    right
    rcases hσ with rfl | rfl <;> constructor <;> linarith

/-- On an axis-parallel segment between points with even integer coordinates,
an integer point with an odd coordinate is the midpoint of a unit subsegment
along the segment.
Source: area-law Section 11, lines 299–310. -/
theorem add_mem_segment_of_odd {m₁ n₁ m₂ n₂ i j : ℤ}
    (hax : m₁ = m₂ ∨ n₁ = n₂)
    (hq : ((i : ℝ), (j : ℝ)) ∈ segment ℝ (((2 * m₁ : ℤ) : ℝ), ((2 * n₁ : ℤ) : ℝ))
      (((2 * m₂ : ℤ) : ℝ), ((2 * n₂ : ℤ) : ℝ)))
    (hodd : ¬ (Even i ∧ Even j)) :
    (Odd (i + j) ∧ ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ((i : ℝ) + σ, (j : ℝ)) ∈
      segment ℝ (((2 * m₁ : ℤ) : ℝ), ((2 * n₁ : ℤ) : ℝ))
        (((2 * m₂ : ℤ) : ℝ), ((2 * n₂ : ℤ) : ℝ))) ∨
    (Odd (i + j) ∧ ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ((i : ℝ), (j : ℝ) + σ) ∈
      segment ℝ (((2 * m₁ : ℤ) : ℝ), ((2 * n₁ : ℤ) : ℝ))
        (((2 * m₂ : ℤ) : ℝ), ((2 * n₂ : ℤ) : ℝ))) := by
  rcases hax with rfl | rfl
  · -- a vertical segment
    rw [← Prod.image_mk_segment_right, segment_eq_uIcc] at hq ⊢
    obtain ⟨y, hy, hyq⟩ := hq
    simp only [Prod.mk.injEq] at hyq
    obtain ⟨hi, rfl⟩ := hyq
    have hi' : i = 2 * m₁ := by exact_mod_cast hi.symm
    have hie : Even i := ⟨m₁, by omega⟩
    have hjo : Odd j := by
      rcases Int.even_or_odd j with h | h
      · exact absurd ⟨hie, h⟩ hodd
      · exact h
    right
    refine ⟨hie.add_odd hjo, fun σ hσ ↦ ⟨(j : ℝ) + σ, ?_, by simp [hi]⟩⟩
    exact add_mem_uIcc_of_odd hjo ⟨n₁, by ring⟩ ⟨n₂, by ring⟩ hy hσ
  · -- a horizontal segment
    rw [← Prod.image_mk_segment_left, segment_eq_uIcc] at hq ⊢
    obtain ⟨x, hx, hxq⟩ := hq
    simp only [Prod.mk.injEq] at hxq
    obtain ⟨rfl, hj⟩ := hxq
    have hj' : j = 2 * n₁ := by exact_mod_cast hj.symm
    have hje : Even j := ⟨n₁, by omega⟩
    have hio : Odd i := by
      rcases Int.even_or_odd i with h | h
      · exact absurd ⟨h, hje⟩ hodd
      · exact h
    left
    refine ⟨hio.add_even hje, fun σ hσ ↦ ⟨(i : ℝ) + σ, ?_, by simp [hj]⟩⟩
    exact add_mem_uIcc_of_odd hio ⟨m₁, by ring⟩ ⟨m₂, by ring⟩ hx hσ

end Reference

/-! ### Initial regions near a belt cell -/

section Core

variable {o : ℝ × ℝ} {k₀ : ℕ} {Z : Finset (ℤ × ℤ)} {C : ℕ}
  {a b : (k : ℕ) → Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k))}
  {hC : 2 ≤ C} {h₀ : 50000000 ≤ k₀}

/-- The initial identifier of a run of a selected belt cell: an initial belt
tile.
Source: area-law Section 11, `prop:two-families`, lines 299–323. -/
abbrev initialBeltRun (k : ℕ) (hk : k₀ ≤ k) (z : ℤ × ℤ)
    (hz : z ∈ beltCellIndices (fineLayerIndices o k (fineScaleIndex k) Z C)
      (2 ^ (pitchScaleIndex k - fineScaleIndex k)) (a k) (b k))
    (R : CellFanRun o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z)
      (beltCellFanColor o k₀ Z C a b k z hC h₀ hk hz)) :
    InitialRegionIndex o k₀ Z C a b hC h₀ :=
  .inr (.inr ⟨⟨k, hk⟩, ⟨z, hz⟩, R⟩)

variable {k : ℕ} {hk : k₀ ≤ k} {z : ℤ × ℤ}
  {hz : z ∈ beltCellIndices (fineLayerIndices o k (fineScaleIndex k) Z C)
    (2 ^ (pitchScaleIndex k - fineScaleIndex k)) (a k) (b k)}

theorem initialBeltRun_birth_subset_closure
    (R : CellFanRun o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z)
      (beltCellFanColor o k₀ Z C a b k z hC h₀ hk hz)) :
    initialBirthRegion o k₀ Z C a b hC h₀ (initialBeltRun k hk z hz R) ⊆
      closure (dyadicCell o (fineScaleIndex k) z) := by
  change cellFanRunRegion _ _ _ _ _ R ⊆ _
  rw [← cellFanRunRegions_cover]
  exact Set.subset_iUnion (fun R ↦ cellFanRunRegion _ _ _ _ _ R) R

theorem cellFanPolygon_subset_initialBeltRun_birth
    {R : CellFanRun o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z)
      (beltCellFanColor o k₀ Z C a b k z hC h₀ hk hz)}
    {t : CellFanSlot (fineLayerSplitMask o k₀ k Z C z)} (ht : t ∈ R.supp) :
    (cellFanPolygon o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) t).region ⊆
      initialBirthRegion o k₀ Z C a b hC h₀ (initialBeltRun k hk z hz R) :=
  Set.subset_biUnion_of_mem (u := fun t ↦
    (cellFanPolygon o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) t).region) ht

/-- An initial identifier whose open region meets the interior of a belt cell
is a run of that cell.
Source: area-law Section 11, `prop:two-families`, lines 299–323. -/
theorem exists_eq_initialBeltRun_of_inter_interior (y : InitialRegionIndex o k₀ Z C a b hC h₀)
    (h : (initialOpenRegion o k₀ Z C a b hC h₀ y ∩
      interior (closure (dyadicCell o (fineScaleIndex k) z))).Nonempty) :
    ∃ R, y = initialBeltRun k hk z hz R := by
  obtain ⟨w, hwy, hwQ⟩ := h
  have hwc := interior_subset hwQ
  rw [← cellFanPolygons_cover o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z)] at hwc
  obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hwc
  have hU : IsOpen (initialOpenRegion o k₀ Z C a b hC h₀ y ∩
      interior (closure (dyadicCell o (fineScaleIndex k) z))) :=
    isOpen_interior.inter isOpen_interior
  have hne : (interior (cellFanPolygon o (fineScaleIndex k) z
      (fineLayerSplitMask o k₀ k Z C z) t).region ∩ (initialOpenRegion o k₀ Z C a b hC h₀ y ∩
      interior (closure (dyadicCell o (fineScaleIndex k) z)))).Nonempty := by
    rw [← closure_inter_open_nonempty_iff hU, (cellFanPolygon_interior_nonempty_and_closure_eq
      o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) t).2]
    exact ⟨w, ht, hwy, hwQ⟩
  obtain ⟨w', hw'T, hw'y, -⟩ := hne
  let R := (cellFanRunGraph o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z)
    (beltCellFanColor o k₀ Z C a b k z hC h₀ hk hz)).connectedComponentMk t
  have hw'x : w' ∈ initialOpenRegion o k₀ Z C a b hC h₀ (initialBeltRun k hk z hz R) :=
    interior_mono (cellFanPolygon_subset_initialBeltRun_birth
      ((SimpleGraph.ConnectedComponent.mem_supp_iff R t).mpr rfl)) hw'T
  refine ⟨R, ?_⟩
  by_contra hne
  exact Set.disjoint_left.mp (initialOpenRegion_pairwise_disjoint o k₀ Z C a b hC h₀ hne)
    hw'y hw'x

/-- Two distinct initial identifiers of the same label share no nondegenerate
segment.
Source: area-law Section 11, `prop:two-families`, lines 299–323. -/
theorem not_segment_subset_initialBirthRegion_inter {x y : InitialRegionIndex o k₀ Z C a b hC h₀}
    (hyx : y ≠ x) (hcol : initialRegionColor o k₀ Z C a b hC h₀ y =
      initialRegionColor o k₀ Z C a b hC h₀ x) {p q : ℝ × ℝ} (hpq : p ≠ q)
    (hx : segment ℝ p q ⊆ initialBirthRegion o k₀ Z C a b hC h₀ x)
    (hy : segment ℝ p q ⊆ initialBirthRegion o k₀ Z C a b hC h₀ y) : False :=
  initialRegionColor_ne_of_segment_subset_inter o k₀ Z C a b hC h₀ y x hyx p q hpq
    (fun _ hw ↦ ⟨hy hw, hx hw⟩) hcol

/-- **Contacts are marks of the belt cell.** Let `x` be an initial belt tile of
a cell `Q`, let `y` be a distinct initial identifier of the same label, and let
`q` be an integer point, in the coordinates normalized at `Q`, lying in the
birth of `x` and in an atom contained in the normalized birth of `y`. Then `q`
is the normalized position of one of the nine marks of `Q`.
Source: area-law Section 11, `geometry:birth-separation`, lines 606–615, with
the belt construction, lines 299–330. -/
theorem beltNormalize_symm_mem_beltCellMarks
    {R : CellFanRun o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z)
      (beltCellFanColor o k₀ Z C a b k z hC h₀ hk hz)}
    {y : InitialRegionIndex o k₀ Z C a b hC h₀} (hyx : y ≠ initialBeltRun k hk z hz R)
    (hcol : initialRegionColor o k₀ Z C a b hC h₀ y =
      initialRegionColor o k₀ Z C a b hC h₀ (initialBeltRun k hk z hz R))
    {c : ℤ × ℤ} {s : RepairFanSlot}
    (hB : beltAtom c s ⊆ beltNormalize o (fineScaleIndex k) z ''
      initialBirthRegion o k₀ Z C a b hC h₀ y)
    {i j : ℤ} (hqB : ((i : ℝ), (j : ℝ)) ∈ beltAtom c s)
    (hvx : (beltNormalize o (fineScaleIndex k) z).symm ((i : ℝ), (j : ℝ)) ∈
      initialBirthRegion o k₀ Z C a b hC h₀ (initialBeltRun k hk z hz R)) :
    (beltNormalize o (fineScaleIndex k) z).symm ((i : ℝ), (j : ℝ)) ∈
      beltCellMarks o (fineScaleIndex k) z := by
  set N := beltNormalize o (fineScaleIndex k) z
  set v := N.symm ((i : ℝ), (j : ℝ)) with hv
  have hNv : N v = ((i : ℝ), (j : ℝ)) := N.apply_symm_apply _
  have hvy : v ∈ initialBirthRegion o k₀ Z C a b hC h₀ y := by
    obtain ⟨v', hv', he⟩ := hB hqB
    rw [hv, ← he, N.symm_apply_apply]
    exact hv'
  have hvQ := initialBeltRun_birth_subset_closure R hvx
  by_cases hint : v ∈ interior (closure (dyadicCell o (fineScaleIndex k) z))
  · -- `y` is another run of the cell
    have hmeet : (initialOpenRegion o k₀ Z C a b hC h₀ y ∩
        interior (closure (dyadicCell o (fineScaleIndex k) z))).Nonempty := by
      rw [initialBirthRegion_eq_closure_initialOpenRegion] at hvy
      obtain ⟨w, hw₁, hw₂⟩ := mem_closure_iff.mp hvy _ isOpen_interior hint
      exact ⟨w, hw₂, hw₁⟩
    obtain ⟨R', rfl⟩ := exists_eq_initialBeltRun_of_inter_interior (hk := hk) (hz := hz) y hmeet
    have hRR' : R' ≠ R := fun h ↦ hyx (h ▸ rfl)
    by_cases hc : v = cellFanCenter o (fineScaleIndex k) z
    · rw [hc]
      refine mem_beltCellMarks_of_beltNormalize_eq (m := 1) (n := 1) (by norm_num) (by norm_num) ?_
      have := beltNormalize_cellFanCenter_add (o := o) (ℓ := fineScaleIndex k) (z := z) 0
      simp only [smul_zero, add_zero] at this
      rw [this]; norm_num
    · exfalso
      have hcenter (S : CellFanRun o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z)
          (beltCellFanColor o k₀ Z C a b k z hC h₀ hk hz)) :
          cellFanCenter o (fineScaleIndex k) z ∈
            initialBirthRegion o k₀ Z C a b hC h₀ (initialBeltRun k hk z hz S) := by
        obtain ⟨t, ht⟩ := S.nonempty_supp
        exact cellFanPolygon_subset_initialBeltRun_birth ht
          (subset_convexHull ℝ _ (Set.mem_insert _ _))
      have hnt : (cellFanRunRegion o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z)
          (beltCellFanColor o k₀ Z C a b k z hC h₀ hk hz) R' ∩
          cellFanRunRegion o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z)
          (beltCellFanColor o k₀ Z C a b k z hC h₀ hk hz) R).Nontrivial :=
        ⟨v, ⟨hvy, hvx⟩, _, ⟨hcenter R', hcenter R⟩, hc⟩
      have hne := cellFanRunRegions_contact_colors_ne o (fineScaleIndex k) z
        (fineLayerSplitMask o k₀ k Z C z) (beltCellFanColor o k₀ Z C a b k z hC h₀ hk hz)
        R' R hRR' hnt
      obtain ⟨t', ht'⟩ := R'.nonempty_supp
      obtain ⟨t, ht⟩ := R.nonempty_supp
      apply hne t' ht' t ht
      rw [← initialRegionColor_beltRun_eq o k₀ Z C a b hC h₀ k z hk hz R' t' ht',
        ← initialRegionColor_beltRun_eq o k₀ Z C a b hC h₀ k z hk hz R t ht]
      exact hcol
  · -- the contact lies on the boundary of the cell
    have hfr : v ∈ frontier (dyadicCell o (fineScaleIndex k) z) :=
      ⟨hvQ, fun h ↦ hint (interior_mono subset_closure h)⟩
    obtain ⟨side, hside⟩ := exists_dyadicCellSide_of_mem_frontier o (fineScaleIndex k) z v hfr
    obtain ⟨t, ht, hvt⟩ := Set.mem_iUnion₂.mp hvx
    have hseg : v ∈ segment ℝ
        (cellFanStart o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) t)
        (cellFanEnd o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) t) := by
      have h := cellFanPolygon_inter_dyadicCellSide o (fineScaleIndex k) z
        (fineLayerSplitMask o k₀ k Z C z) t side
      exact (h.subset ⟨hvt, hside⟩).1
    obtain ⟨m₁, n₁, hS⟩ := exists_beltNormalize_cellFanStart_eq (o := o)
      (ℓ := fineScaleIndex k) (z := z) (fineLayerSplitMask o k₀ k Z C z) t
    obtain ⟨m₂, n₂, hE⟩ := exists_beltNormalize_cellFanEnd_eq (o := o)
      (ℓ := fineScaleIndex k) (z := z) (fineLayerSplitMask o k₀ k Z C z) t
    have hTseg : segment ℝ
        (N (cellFanStart o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) t))
        (N (cellFanEnd o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) t)) ⊆
        N '' initialBirthRegion o k₀ Z C a b hC h₀ (initialBeltRun k hk z hz R) := by
      rw [← beltNormalize_image_segment]
      refine Set.image_mono (Set.Subset.trans ?_ (cellFanPolygon_subset_initialBeltRun_birth ht))
      apply (convex_convexHull ℝ _).segment_subset
      · exact subset_convexHull ℝ _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      · exact subset_convexHull ℝ _ (Set.mem_insert_of_mem _
          (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    have hqseg : ((i : ℝ), (j : ℝ)) ∈ segment ℝ
        (N (cellFanStart o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) t))
        (N (cellFanEnd o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z) t)) := by
      rw [← beltNormalize_image_segment, ← hNv]
      exact Set.mem_image_of_mem _ hseg
    rw [hS, hE] at hTseg hqseg
    have hax : m₁ = m₂ ∨ n₁ = n₂ := by
      rcases (cellFan_elementary_geometry o (fineScaleIndex k) z
        (fineLayerSplitMask o k₀ k Z C z) t).2 with ⟨h, -⟩ | ⟨h, -⟩
      · left
        have h' := congrArg Prod.fst hS
        have h'' := congrArg Prod.fst hE
        rw [beltNormalize_fst] at h' h''
        rw [h] at h'
        have : ((2 * m₁ : ℤ) : ℝ) = ((2 * m₂ : ℤ) : ℝ) := h'.symm.trans h''
        have := Int.cast_injective this
        omega
      · right
        have h' := congrArg Prod.snd hS
        have h'' := congrArg Prod.snd hE
        rw [beltNormalize_snd] at h' h''
        rw [h] at h'
        have : ((2 * n₁ : ℤ) : ℝ) = ((2 * n₂ : ℤ) : ℝ) := h'.symm.trans h''
        have := Int.cast_injective this
        omega
    by_cases heven : Even i ∧ Even j
    · obtain ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ := heven
      obtain ⟨⟨h₁, h₂⟩, h₃, h₄⟩ := beltNormalize_mem_Icc hvQ
      rw [hNv] at h₁ h₂ h₃ h₄
      simp only at h₁ h₂ h₃ h₄
      rw [hm] at h₁ h₂
      rw [hn] at h₃ h₄
      push_cast at h₁ h₂ h₃ h₄
      have a₁ : (0 : ℝ) ≤ m := by linarith
      have a₂ : (m : ℝ) ≤ 2 := by linarith
      have a₃ : (0 : ℝ) ≤ n := by linarith
      have a₄ : (n : ℝ) ≤ 2 := by linarith
      refine mem_beltCellMarks_of_beltNormalize_eq (m := m) (n := n)
        ⟨by exact_mod_cast a₁, by exact_mod_cast a₂⟩ ⟨by exact_mod_cast a₃, by exact_mod_cast a₄⟩
        ?_
      rw [hNv, hm, hn]; push_cast; ring_nf
    · exfalso
      rcases add_mem_segment_of_odd hax hqseg heven with ⟨hodd, hσ⟩ | ⟨hodd, hσ⟩
      · obtain ⟨⟨σ, hσ₁, hBseg⟩, -⟩ := beltAtom_axis_segments hodd hqB
        have h₁ : segment ℝ ((i : ℝ), (j : ℝ)) ((i : ℝ) + σ, (j : ℝ)) ⊆
            N '' initialBirthRegion o k₀ Z C a b hC h₀ (initialBeltRun k hk z hz R) :=
          ((convex_segment _ _).segment_subset hqseg (hσ σ hσ₁)).trans hTseg
        have hne : N.symm ((i : ℝ), (j : ℝ)) ≠ N.symm ((i : ℝ) + σ, (j : ℝ)) := by
          intro h
          have h' := congrArg Prod.fst (N.symm.injective h)
          simp only at h'
          rcases hσ₁ with rfl | rfl <;> linarith
        exact not_segment_subset_initialBirthRegion_inter hyx hcol hne
          (segment_symm_subset_of_subset_image h₁)
          (segment_symm_subset_of_subset_image (hBseg.trans hB))
      · obtain ⟨-, ⟨σ, hσ₁, hBseg⟩⟩ := beltAtom_axis_segments hodd hqB
        have h₁ : segment ℝ ((i : ℝ), (j : ℝ)) ((i : ℝ), (j : ℝ) + σ) ⊆
            N '' initialBirthRegion o k₀ Z C a b hC h₀ (initialBeltRun k hk z hz R) :=
          ((convex_segment _ _).segment_subset hqseg (hσ σ hσ₁)).trans hTseg
        have hne : N.symm ((i : ℝ), (j : ℝ)) ≠ N.symm ((i : ℝ), (j : ℝ) + σ) := by
          intro h
          have h' := congrArg Prod.snd (N.symm.injective h)
          simp only at h'
          rcases hσ₁ with rfl | rfl <;> linarith
        exact not_segment_subset_initialBirthRegion_inter hyx hcol hne
          (segment_symm_subset_of_subset_image h₁)
          (segment_symm_subset_of_subset_image (hBseg.trans hB))

/-- Every point of the birth of an initial identifier other than the dummy that
lies within one fine side of a point of a belt cell lies in an atom, in the
coordinates normalized at that cell, contained in the normalized birth.
Source: area-law Section 11, `geometry:birth-separation`, lines 592–604, with
`geometry:nonadjacent` and the scale comparison, lines 193–207. -/
theorem exists_beltAtom_subset_initialBirthRegion
    (hk' : k₀ ≤ k) (hzF : z ∈ fineLayerIndices o k (fineScaleIndex k) Z C)
    (y : InitialRegionIndex o k₀ Z C a b hC h₀) (hyd : y ≠ .inl ())
    {p w : ℝ × ℝ} (hp : p ∈ closure (dyadicCell o (fineScaleIndex k) z))
    (hw : w ∈ initialBirthRegion o k₀ Z C a b hC h₀ y)
    (hpw : dist p w < (2 : ℝ) ^ fineScaleIndex k) :
    ∃ c s, beltNormalize o (fineScaleIndex k) z w ∈ beltAtom c s ∧
      beltAtom c s ⊆ beltNormalize o (fineScaleIndex k) z ''
        initialBirthRegion o k₀ Z C a b hC h₀ y := by
  have hpL : p ∈ closure (dyadicLayer o k Z C) :=
    closure_mono (dyadicCell_subset_dyadicLayer_of_mem_fineLayerIndices o k (fineScaleIndex k)
      Z C z (fineScaleIndex_le k) hzF) hp
  have hscale : ∀ h, w ∈ closure (dyadicLayer o h Z C) →
      fineScaleIndex k ≤ fineScaleIndex h + 1 := by
    intro h hwL
    have hnear : dist p w < 10 * (2 : ℝ) ^ fineScaleIndex k := by
      have : (0 : ℝ) < (2 : ℝ) ^ fineScaleIndex k := by positivity
      linarith
    obtain ⟨h₁, h₂⟩ := dyadicLayer_nearby_indices o k h Z C p w hC (h₀.trans hk') hpL hwL hnear
    rcases (show h + 1 = k ∨ k ≤ h by omega) with rfl | hkh
    · rcases fineScaleIndex_succ h with e | e <;> omega
    · have := fineScaleIndex_mono hkh; omega
  rcases y with ⟨⟩ | (⟨h, J⟩ | ⟨h, w', R'⟩)
  · exact absurd rfl hyd
  · change w ∈ primaryBirthRegion o h.val (fineScaleIndex h.val) (pitchScaleIndex h.val) Z C
      (a h.val).val (b h.val).val J.val at hw
    have hrw := primaryBirthRegion_eq_iUnion_nonbeltCell_closure o h.val (fineScaleIndex h.val)
      (pitchScaleIndex h.val) Z C (a h.val) (b h.val) J.val (fineScaleIndex_le h.val)
      ((fineScaleIndex_le h.val).trans (le_pitchScaleIndex h.val))
    rw [hrw] at hw
    obtain ⟨w', hw'F, hw'⟩ := Set.mem_iUnion₂.mp hw
    have hw'L : w ∈ closure (dyadicLayer o h.val Z C) :=
      closure_mono (dyadicCell_subset_dyadicLayer_of_mem_fineLayerIndices o h.val
        (fineScaleIndex h.val) Z C w' (fineScaleIndex_le h.val)
        (Finset.mem_filter.mp hw'F).1) hw'
    obtain ⟨c, s, h₁, h₂⟩ := exists_beltAtom_subset_closure_dyadicCell (o := o) (z := z)
      (hscale h.val hw'L) hw'
    refine ⟨c, s, h₁, h₂.trans (Set.image_mono ?_)⟩
    change _ ⊆ primaryBirthRegion o h.val (fineScaleIndex h.val) (pitchScaleIndex h.val) Z C
      (a h.val).val (b h.val).val J.val
    rw [hrw]
    exact Set.subset_biUnion_of_mem (u := fun w' ↦ closure (dyadicCell o (fineScaleIndex h.val) w'))
      hw'F
  · change w ∈ cellFanRunRegion _ _ _ _ _ R' at hw
    obtain ⟨t, ht, hwt⟩ := Set.mem_iUnion₂.mp hw
    have hw'F : w'.val ∈ fineLayerIndices o h.val (fineScaleIndex h.val) Z C :=
      Finset.mem_of_mem_filter _ w'.property
    have hwc : w ∈ closure (dyadicCell o (fineScaleIndex h.val) w'.val) := by
      rw [← cellFanPolygons_cover o (fineScaleIndex h.val) w'.val
        (fineLayerSplitMask o k₀ h.val Z C w'.val)]
      exact Set.mem_iUnion.mpr ⟨t, hwt⟩
    have hw'L : w ∈ closure (dyadicLayer o h.val Z C) :=
      closure_mono (dyadicCell_subset_dyadicLayer_of_mem_fineLayerIndices o h.val
        (fineScaleIndex h.val) Z C w'.val (fineScaleIndex_le h.val) hw'F) hwc
    obtain ⟨c, s, h₁, h₂⟩ := exists_beltAtom_subset_cellFanPolygon (o := o) (z := z)
      (hscale h.val hw'L) _ t hwt
    refine ⟨c, s, h₁, h₂.trans (Set.image_mono ?_)⟩
    exact Set.subset_biUnion_of_mem (u := fun t ↦ (cellFanPolygon o (fineScaleIndex h.val) w'.val
      (fineLayerSplitMask o k₀ h.val Z C w'.val) t).region) ht

end Core

/-- **Birth separation of an initial belt tile from its comparison regions.**
There is one fixed `c₁ > 0` with the following property. Let `x` be an initial
belt tile in a belt cell of side `u = t_k`, and let `y` be another initial
identifier of the same label other than the dummy: a primary or another initial
belt tile. Let `Y` lie in the open region of `y` and avoid, at sup distance
`u^ρ₀ / 4`, the nine marks of the cell, as the first trim guarantees. Then every
point of the closed birth of `x` has distance at least `c₁ u^ρ₀` from `Y`.
Source: area-law Section 11, `geometry:birth-separation`, lines 573–659. -/
theorem exists_initialBeltRun_birth_separation :
    ∃ c₁ > 0, ∀ (o : ℝ × ℝ) (k₀ : ℕ) (Z : Finset (ℤ × ℤ)) (C : ℕ)
      (a b : (k : ℕ) → Fin (2 ^ (pitchScaleIndex k - fineScaleIndex k)))
      (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (k : ℕ) (hk : k₀ ≤ k) (z : ℤ × ℤ)
      (hz : z ∈ beltCellIndices (fineLayerIndices o k (fineScaleIndex k) Z C)
        (2 ^ (pitchScaleIndex k - fineScaleIndex k)) (a k) (b k))
      (R : CellFanRun o (fineScaleIndex k) z (fineLayerSplitMask o k₀ k Z C z)
        (beltCellFanColor o k₀ Z C a b k z hC h₀ hk hz))
      (y : InitialRegionIndex o k₀ Z C a b hC h₀),
      y ≠ initialBeltRun k hk z hz R → y ≠ .inl () →
      initialRegionColor o k₀ Z C a b hC h₀ y =
        initialRegionColor o k₀ Z C a b hC h₀ (initialBeltRun k hk z hz R) →
      ∀ Y ⊆ initialOpenRegion o k₀ Z C a b hC h₀ y,
      (∀ v ∈ beltCellMarks o (fineScaleIndex k) z, ∀ w ∈ Y,
        ((2 : ℝ) ^ fineScaleIndex k) ^ (Exponents.rho : ℝ) / 4 < dist w v) →
      ∀ p ∈ initialBirthRegion o k₀ Z C a b hC h₀ (initialBeltRun k hk z hz R), ∀ w ∈ Y,
        c₁ * ((2 : ℝ) ^ fineScaleIndex k) ^ (Exponents.rho : ℝ) ≤ dist p w := by
  obtain ⟨η, hη, hη1, hdich⟩ := exists_beltAtom_dichotomy
  refine ⟨min (η / 4) (1 / 8), lt_min (by positivity) (by norm_num), ?_⟩
  intro o k₀ Z C a b hC h₀ k hk z hz R y hyx hyd hcol Y hY htrim p hp w hw
  set u : ℝ := (2 : ℝ) ^ fineScaleIndex k with hu
  set N := beltNormalize o (fineScaleIndex k) z
  have hu1 : 1 ≤ u := one_le_pow₀ (by norm_num)
  have hu0 : 0 < u := by linarith
  have hρ : u ^ (Exponents.rho : ℝ) ≤ u := by
    calc u ^ (Exponents.rho : ℝ) ≤ u ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hu1 rho_pos_lt_one.2.le
      _ = u := Real.rpow_one u
  have hρ0 : 0 ≤ u ^ (Exponents.rho : ℝ) := Real.rpow_nonneg hu0.le _
  have hc₁ : min (η / 4) (1 / 8) * u ^ (Exponents.rho : ℝ) ≤ u ^ (Exponents.rho : ℝ) / 8 :=
    by nlinarith [min_le_right (η / 4) (1 / 8)]
  have hnorm (p q : ℝ × ℝ) : ‖N p - N q‖ = 4 / u * dist p q := by
    rw [norm_beltNormalize_sub, dist_eq_norm]
  by_cases hfar : u ≤ dist p w
  · nlinarith
  push Not at hfar
  -- the atom of the belt tile
  obtain ⟨t, ht, hpt⟩ := Set.mem_iUnion₂.mp hp
  obtain ⟨cA, sA, hpA, hA⟩ := exists_beltAtom_subset_cellFanPolygon (o := o) (z := z)
    (ℓ := fineScaleIndex k) (ℓ' := fineScaleIndex k) (by omega) _ t hpt
  have hAx : beltAtom cA sA ⊆ N '' initialBirthRegion o k₀ Z C a b hC h₀
      (initialBeltRun k hk z hz R) :=
    hA.trans (Set.image_mono (cellFanPolygon_subset_initialBeltRun_birth ht))
  -- the atom of the comparison region
  have hwy : w ∈ initialBirthRegion o k₀ Z C a b hC h₀ y := interior_subset (hY hw)
  obtain ⟨cB, sB, hwB, hBy⟩ := exists_beltAtom_subset_initialBirthRegion hk
    (Finset.mem_of_mem_filter z hz) y hyd (initialBeltRun_birth_subset_closure R hp) hwy hfar
  -- the two atoms meet only in integer points
  have hAB : ∀ q ∈ beltAtom cA sA, q ∈ beltAtom cB sB → ∃ i j : ℤ, q = ((i : ℝ), (j : ℝ)) := by
    intro q hqA hqB
    by_contra hne
    push Not at hne
    obtain ⟨a', b', hab, hseg⟩ := exists_segment_subset_beltAtom_inter hqA hqB hne
    exact not_segment_subset_initialBirthRegion_inter hyx hcol (N.symm.injective.ne hab)
      (segment_symm_subset_of_subset_image (hseg.trans (Set.inter_subset_left.trans hAx)))
      (segment_symm_subset_of_subset_image (hseg.trans (Set.inter_subset_right.trans hBy)))
  rcases hdich cA cB sA sB hAB (N p) hpA (N w) hwB with hd | ⟨q, ⟨hqA, hqB⟩, -, -, hang⟩
  · -- far from every contact
    rw [hnorm] at hd
    have : η * u ≤ 4 * dist p w := by
      have := mul_le_mul_of_nonneg_right hd hu0.le
      rwa [show 4 / u * dist p w * u = 4 * dist p w by field_simp] at this
    nlinarith [min_le_left (η / 4) (1 / 8)]
  · -- near a contact, which is a mark of the cell
    obtain ⟨i, j, rfl⟩ := hAB q hqA hqB
    have hvx : N.symm ((i : ℝ), (j : ℝ)) ∈
        initialBirthRegion o k₀ Z C a b hC h₀ (initialBeltRun k hk z hz R) := by
      obtain ⟨v', hv', he⟩ := hAx hqA
      rw [← he, N.symm_apply_apply]
      exact hv'
    have hmark := beltNormalize_symm_mem_beltCellMarks hyx hcol hBy hqB hvx
    have hgap := htrim _ hmark w hw
    have hq : ((i : ℝ), (j : ℝ)) = N (N.symm ((i : ℝ), (j : ℝ))) := (N.apply_symm_apply _).symm
    rw [hq, hnorm, hnorm] at hang
    have : dist w (N.symm ((i : ℝ), (j : ℝ))) / 2 ≤ dist p w := by
      have h4 : 0 < 4 / u := by positivity
      nlinarith
    linarith

end TNLean.PEPS.AreaLaw.Geometry
