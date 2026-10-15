/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.BirthSeparationRepair
import TNLean.PEPS.AreaLaw.Geometry.BirthSeparationAtoms
import TNLean.PEPS.AreaLaw.Geometry.FanFrontiers
import TNLean.PEPS.AreaLaw.Geometry.TemplatePolygons

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
  rw [TemplatePolygon.region_eq_convexHull_vertices]
  exact (Set.toFinite _).isClosed_convexHull (𝕜 := ℝ)

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

end TNLean.PEPS.AreaLaw.Geometry
