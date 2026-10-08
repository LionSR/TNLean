/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicFootprintScaling
import TNLean.PEPS.Approximation.DyadicRimPatterns

/-!
# Templates of the guides near a mark

The patch ratio `ν` of the point covers must not depend on the scale, the block, its labels, the
guide or the mark. The source argues that in units of `t` the old and new guides near a mark come
from a finite family of ray patterns, with or without the square clearing, so that the
compactness observation gives one ratio for all of them. This file proves this for the unmodified
guides of a large-scale repainting and their point treatments:

* scaling a repainting of a block of side `n` to the block `(0, 0)` of side one carries every
  unmodified guide to an unmodified guide composed with the scaling;
* relabelling the labels of a repainting carries every unmodified guide to the relabelling of an
  unmodified guide, at every point where the starting guides correspond;
* on the repainting of the unit square, every unmodified guide is conical about each corner: in
  the open sup square of radius `1/2` it is constant along each open ray from the corner, because
  the bands, the band coordinates, the central region and the block guide are;
* hence, for `8 t < n`, every unmodified guide of the repainting of a block, point-treated or not,
  is on the open square of radius `4 t` about a corner the relabelling of a template: one of the
  finitely many unmodified guides of a reference repainting labelled by the `3 × 3` window of
  blocks, about one of four corners, scaled from `t` to `1/32`, with one of finitely many
  homogenizing labels and label-equality types;
* with `exists_footprintRatio`, one ratio `ν > 0` gives the two-owner condition at footprint
  radius `ν t` near every mark of every large-scale repainting, at every scale.

The direct repaintings and the resizings, whose guides are block guides in units of `n`, are in
`TNLean.PEPS.Approximation.DyadicBlockFootprints`.

Distances are ambient sup distances: `ℝ × ℝ` carries the maximum metric.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), §7, `06-geometry.tex`: the straight-ray charts
  (lines 301–302), the point treatment (lines 330–338), the compactness observation and its
  uniformity (lines 447–479), and the point covers (lines 481–505).
-/

namespace TNLean.PEPS.Approximation

open Set Metric Filter Topology SquareEdge

/-! ### Scaling the square to side one -/

theorem SquareEdge.par_smul (e : SquareEdge) (a : ℝ) (p : ℝ × ℝ) :
    e.par (a • p) = a * e.par p := by
  cases e <;> simp [par]

theorem SquareEdge.nor_inv_smul {n : ℝ} (hn : n ≠ 0) (e : SquareEdge) (p : ℝ × ℝ) :
    e.nor 1 (n⁻¹ • p) = n⁻¹ * e.nor n p := by
  cases e <;> simp [nor] <;> field_simp

theorem bandWidth_inv_mul {n : ℝ} (hn : 0 < n) (s : ℝ) :
    bandWidth 1 (n⁻¹ * s) = n⁻¹ * bandWidth n s := by
  unfold bandWidth
  rw [show 1 - n⁻¹ * s = n⁻¹ * (n - s) by field_simp,
    ← mul_min_of_nonneg _ _ (inv_nonneg.2 hn.le)]
  ring

private theorem inv_mul_iffs {n : ℝ} (hn : 0 < n) :
    (∀ a : ℝ, 0 < n⁻¹ * a ↔ 0 < a) ∧ (∀ a : ℝ, n⁻¹ * a < 1 ↔ a < n) ∧
      ∀ a b : ℝ, n⁻¹ * a < n⁻¹ * b ↔ a < b := by
  have hi : 0 < n⁻¹ := inv_pos.2 hn
  refine ⟨fun a => mul_pos_iff_of_pos_left hi, fun a => ?_,
    fun a b => mul_lt_mul_iff_of_pos_left hi⟩
  rw [← mul_lt_mul_iff_of_pos_left hn, ← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul, mul_one]

/-- **Bands under scaling.** The scaling `p ↦ n⁻¹ p` carries the bands of the square of side `n`
to those of the unit square.

Source: Polynomial-PEPS manuscript (Sept 24 2026), equation `eq:geometry-band`,
`06-geometry.tex:146–153`. -/
theorem mem_edgeBand_inv_smul {n : ℝ} (hn : 0 < n) {e : SquareEdge} {α β : ℝ} {p : ℝ × ℝ} :
    n⁻¹ • p ∈ edgeBand 1 e α β ↔ p ∈ edgeBand n e α β := by
  obtain ⟨k1, k2, k3⟩ := inv_mul_iffs hn
  simp only [edgeBand, mem_ofPred_eq, e.par_smul, e.nor_inv_smul hn.ne', bandWidth_inv_mul hn]
  rw [show α * (n⁻¹ * bandWidth n (e.par p)) = n⁻¹ * (α * bandWidth n (e.par p)) by ring,
    show β * (n⁻¹ * bandWidth n (e.par p)) = n⁻¹ * (β * bandWidth n (e.par p)) by ring]
  simp only [k1, k2, k3]

/-- The normal ratio `x = d / w(s)` is invariant under the scaling `p ↦ n⁻¹ p`. -/
theorem bandCoord_inv_smul {n : ℝ} (hn : 0 < n) (e : SquareEdge) (p : ℝ × ℝ) :
    bandCoord 1 e (n⁻¹ • p) = bandCoord n e p := by
  simp only [bandCoord, e.par_smul, e.nor_inv_smul hn.ne', bandWidth_inv_mul hn]
  exact mul_div_mul_left _ _ (inv_ne_zero hn.ne')

/-- The scaling `p ↦ n⁻¹ p` carries the central region of the square of side `n` to that of the
unit square. -/
theorem mem_centralRegion_inv_smul {n : ℝ} (hn : 0 < n) {p : ℝ × ℝ} :
    n⁻¹ • p ∈ centralRegion 1 ↔ p ∈ centralRegion n := by
  obtain ⟨k1, k2, k3⟩ := inv_mul_iffs hn
  simp only [centralRegion, mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    SquareEdge.par_smul, SquareEdge.nor_inv_smul hn.ne', bandWidth_inv_mul hn, k1, k2, k3]

theorem bandUpdate_inv_smul {ι : Type*} {n : ℝ} (hn : 0 < n) (e : SquareEdge) (W : ℝ → ι)
    {g g' : ℝ × ℝ → ι} (hg : ∀ p, g p = g' (n⁻¹ • p)) (p : ℝ × ℝ) :
    bandUpdate n e W g p = bandUpdate 1 e W g' (n⁻¹ • p) := by
  by_cases hb : p ∈ edgeBand n e (-8) 2
  · rw [bandUpdate_of_mem hb, bandUpdate_of_mem ((mem_edgeBand_inv_smul hn).2 hb),
      bandCoord_inv_smul hn]
  · rw [bandUpdate_of_notMem hb,
      bandUpdate_of_notMem fun h => hb ((mem_edgeBand_inv_smul hn).1 h), hg]

/-- A normal word followed by a relabelling is the normal word of the relabelled labels. -/
theorem comp_bandWord {ι κ : Type*} (σ : ι → κ) (c : ι) (l : List (ℝ × ι)) :
    σ ∘ bandWord c l = bandWord (σ c) (l.map fun q => (q.1, σ q.2)) := by
  funext x
  induction l generalizing c with
  | nil => rfl
  | cons q rest ih =>
    obtain ⟨t, l'⟩ := q
    simp only [Function.comp_apply, bandWord, List.map_cons] at ih ⊢
    split_ifs
    · rfl
    · exact ih l'

theorem bandUpdate_comp {ι κ : Type*} (σ : ι → κ) (n : ℝ) (e : SquareEdge) (W : ℝ → ι)
    {g : ℝ × ℝ → ι} {g' : ℝ × ℝ → κ} {p : ℝ × ℝ} (hg : g' p = σ (g p)) :
    bandUpdate n e (σ ∘ W) g' p = σ (bandUpdate n e W g p) := by
  by_cases hb : p ∈ edgeBand n e (-8) 2
  · rw [bandUpdate_of_mem hb, bandUpdate_of_mem hb]; rfl
  · rw [bandUpdate_of_notMem hb, bandUpdate_of_notMem hb, hg]

section Words

variable {ι κ : Type*} (σ : ι → κ) (A B C : ι)

theorem comp_mainWords {W : ℝ → ι} (hW : W ∈ mainWords A B C) :
    σ ∘ W ∈ mainWords (σ A) (σ B) (σ C) := by
  simp only [mainWords, mem_insert_iff, mem_singleton_iff] at hW ⊢
  rcases hW with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [edgeStartWord, mainWordOne, mainWordTwo, mainWordThree, mainWordFour, mainWordFive,
      comp_bandWord]

theorem comp_auxWords {W : ℝ → ι} (hW : W ∈ auxWords A B C) :
    σ ∘ W ∈ auxWords (σ A) (σ B) (σ C) := by
  simp only [auxWords, mem_insert_iff, mem_singleton_iff] at hW ⊢
  rcases hW with rfl | rfl | rfl | rfl <;>
    simp [auxWordOne, auxWordTwo, auxWord, comp_bandWord]

/-- Every main word of relabelled labels is the relabelling of a main word. -/
theorem exists_mainWords_comp {W' : ℝ → κ} (hW : W' ∈ mainWords (σ A) (σ B) (σ C)) :
    ∃ W ∈ mainWords A B C, W' = σ ∘ W := by
  simp only [mainWords, mem_insert_iff, mem_singleton_iff] at hW
  rcases hW with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨edgeStartWord A B C, by simp [mainWords], by simp [edgeStartWord, comp_bandWord]⟩
  · exact ⟨mainWordOne A B C, by simp [mainWords], by simp [mainWordOne, comp_bandWord]⟩
  · exact ⟨mainWordTwo A B C, by simp [mainWords], by simp [mainWordTwo, comp_bandWord]⟩
  · exact ⟨mainWordThree B C, by simp [mainWords], by simp [mainWordThree, comp_bandWord]⟩
  · exact ⟨mainWordFour B C, by simp [mainWords], by simp [mainWordFour, comp_bandWord]⟩
  · exact ⟨mainWordFive B C, by simp [mainWords], by simp [mainWordFive, comp_bandWord]⟩

/-- Every auxiliary word of relabelled labels is the relabelling of an auxiliary word. -/
theorem exists_auxWords_comp {W' : ℝ → κ} (hW : W' ∈ auxWords (σ A) (σ B) (σ C)) :
    ∃ W ∈ auxWords A B C, W' = σ ∘ W := by
  simp only [auxWords, mem_insert_iff, mem_singleton_iff] at hW
  rcases hW with rfl | rfl | rfl | rfl
  · exact ⟨bandWord C [], by simp [auxWords], by simp [comp_bandWord]⟩
  · exact ⟨auxWordOne B C, by simp [auxWords], by simp [auxWordOne, comp_bandWord]⟩
  · exact ⟨auxWordTwo A B C, by simp [auxWords], by simp [auxWordTwo, comp_bandWord]⟩
  · exact ⟨auxWord A B C, by simp [auxWords], by simp [auxWord, comp_bandWord]⟩

end Words

namespace RepaintingBaseline

variable {ι κ : Type*}

/-! ### Rescaling a repainting to side one -/

/-- The repainting `R'` is the repainting `R` scaled by `p ↦ n⁻¹ p` to side one, with the same
labels. -/
structure IsRescale (R R' : RepaintingBaseline ι) : Prop where
  n_eq : R'.n = 1
  guide_eq : ∀ p, R.guide p = R'.guide (R.n⁻¹ • p)
  oldLabel_eq : R.oldLabel = R'.oldLabel
  finalLabel_eq : R.finalLabel = R'.finalLabel
  nbrLabel_eq : ∀ e, R.nbrLabel e = R'.nbrLabel e

section Rescale

variable {R R' : RepaintingBaseline ι} (h : R.IsRescale R')
include h

theorem IsRescale.centralGuide_eq (p : ℝ × ℝ) :
    R.centralGuide p = R'.centralGuide (R.n⁻¹ • p) := by
  by_cases hc : p ∈ centralRegion R.n
  · have hc' : R.n⁻¹ • p ∈ centralRegion R'.n := by
      rw [h.n_eq]; exact (mem_centralRegion_inv_smul R.n_pos).2 hc
    rw [R.centralGuide_of_mem hc, R'.centralGuide_of_mem hc', h.finalLabel_eq]
  · have hc' : R.n⁻¹ • p ∉ centralRegion R'.n := by
      rw [h.n_eq]; exact fun h' => hc ((mem_centralRegion_inv_smul R.n_pos).1 h')
    rw [R.centralGuide_of_notMem hc, R'.centralGuide_of_notMem hc', h.guide_eq]

theorem IsRescale.completedGuide_eq (E : List SquareEdge) (p : ℝ × ℝ) :
    R.completedGuide E p = R'.completedGuide E (R.n⁻¹ • p) := by
  induction E generalizing p with
  | nil => exact h.centralGuide_eq p
  | cons e E ih =>
    simp only [completedGuide]
    rw [bandUpdate_inv_smul R.n_pos e _ ih, h.n_eq, h.finalLabel_eq, h.nbrLabel_eq]

theorem IsRescale.mainGuide_eq (E : List SquareEdge) (e : SquareEdge) (W : ℝ → ι)
    (p : ℝ × ℝ) : R.mainGuide E e W p = R'.mainGuide E e W (R.n⁻¹ • p) := by
  simp only [mainGuide]
  rw [bandUpdate_inv_smul R.n_pos e W (h.completedGuide_eq E), h.n_eq]

theorem IsRescale.auxGuide_eq (e : SquareEdge) (W : ℝ → ι) (p : ℝ × ℝ) :
    R.auxGuide e W p = R'.auxGuide e W (R.n⁻¹ • p) := by
  simp only [auxGuide]
  rw [bandUpdate_inv_smul R.n_pos e W (g' := fun _ => R'.nbrLabel e)
    (fun _ => h.nbrLabel_eq e), h.n_eq]

/-- **Unmodified guides under rescaling.** Every unmodified guide of `R` is an unmodified guide of
the rescaled repainting composed with the scaling. -/
theorem IsRescale.isUnmodifiedGuide {g : ℝ × ℝ → ι} (hg : R.IsUnmodifiedGuide g) :
    ∃ g', R'.IsUnmodifiedGuide g' ∧ ∀ p, g p = g' (R.n⁻¹ • p) := by
  rcases hg with rfl | rfl | ⟨E, rfl⟩ | ⟨E, e, W, hW, rfl⟩ | ⟨e, W, hW, rfl⟩
  · exact ⟨_, Or.inl rfl, h.guide_eq⟩
  · exact ⟨_, Or.inr (Or.inl rfl), h.centralGuide_eq⟩
  · exact ⟨_, Or.inr (Or.inr (Or.inl ⟨E, rfl⟩)), h.completedGuide_eq E⟩
  · refine ⟨_, Or.inr (Or.inr (Or.inr (Or.inl ⟨E, e, W, ?_, rfl⟩))), h.mainGuide_eq E e W⟩
    rwa [← h.oldLabel_eq, ← h.finalLabel_eq, ← h.nbrLabel_eq]
  · refine ⟨_, Or.inr (Or.inr (Or.inr (Or.inr ⟨e, W, ?_, rfl⟩))), h.auxGuide_eq e W⟩
    rwa [← h.oldLabel_eq, ← h.finalLabel_eq, ← h.nbrLabel_eq]

end Rescale

/-! ### Relabelling a repainting -/

/-- The repainting `R'` is the repainting `R` with its labels relabelled by `σ`; the starting
guides need not be related. -/
structure IsRelabel (R : RepaintingBaseline ι) (R' : RepaintingBaseline κ) (σ : ι → κ) :
    Prop where
  n_eq : R'.n = R.n
  oldLabel_eq : R'.oldLabel = σ R.oldLabel
  finalLabel_eq : R'.finalLabel = σ R.finalLabel
  nbrLabel_eq : ∀ e, R'.nbrLabel e = σ (R.nbrLabel e)

section Relabel

variable {R : RepaintingBaseline ι} {R' : RepaintingBaseline κ} {σ : ι → κ} (h : R.IsRelabel R' σ)
include h

theorem IsRelabel.centralGuide_eq {p : ℝ × ℝ} (hp : R'.guide p = σ (R.guide p)) :
    R'.centralGuide p = σ (R.centralGuide p) := by
  by_cases hc : p ∈ centralRegion R.n
  · rw [R.centralGuide_of_mem hc, R'.centralGuide_of_mem (h.n_eq ▸ hc), h.finalLabel_eq]
  · rw [R.centralGuide_of_notMem hc, R'.centralGuide_of_notMem (h.n_eq ▸ hc), hp]

theorem IsRelabel.completedGuide_eq (E : List SquareEdge) {p : ℝ × ℝ}
    (hp : R'.guide p = σ (R.guide p)) : R'.completedGuide E p = σ (R.completedGuide E p) := by
  induction E with
  | nil => exact h.centralGuide_eq hp
  | cons e E ih =>
    simp only [completedGuide]
    rw [h.n_eq, h.finalLabel_eq, h.nbrLabel_eq, show mainWordFive (σ R.finalLabel)
      (σ (R.nbrLabel e)) = σ ∘ mainWordFive R.finalLabel (R.nbrLabel e) by
        simp [mainWordFive, comp_bandWord]]
    exact bandUpdate_comp σ R.n e _ ih

/-- **Unmodified guides under relabelling.** Every unmodified guide of the relabelled repainting
is the relabelling of an unmodified guide of `R` at every point where the starting guides are. -/
theorem IsRelabel.isUnmodifiedGuide {g' : ℝ × ℝ → κ} (hg : R'.IsUnmodifiedGuide g') :
    ∃ g, R.IsUnmodifiedGuide g ∧ ∀ p, R'.guide p = σ (R.guide p) → g' p = σ (g p) := by
  rcases hg with rfl | rfl | ⟨E, rfl⟩ | ⟨E, e, W', hW, rfl⟩ | ⟨e, W', hW, rfl⟩
  · exact ⟨_, Or.inl rfl, fun _ hp => hp⟩
  · exact ⟨_, Or.inr (Or.inl rfl), fun _ hp => h.centralGuide_eq hp⟩
  · exact ⟨_, Or.inr (Or.inr (Or.inl ⟨E, rfl⟩)), fun _ hp => h.completedGuide_eq E hp⟩
  · rw [h.oldLabel_eq, h.finalLabel_eq, h.nbrLabel_eq] at hW
    obtain ⟨W, hW₀, rfl⟩ := exists_mainWords_comp σ _ _ _ hW
    refine ⟨_, Or.inr (Or.inr (Or.inr (Or.inl ⟨E, e, W, hW₀, rfl⟩))), fun p hp => ?_⟩
    simp only [mainGuide]
    rw [h.n_eq]
    exact bandUpdate_comp σ R.n e W (h.completedGuide_eq E hp)
  · rw [h.oldLabel_eq, h.finalLabel_eq, h.nbrLabel_eq] at hW
    obtain ⟨W, hW₀, rfl⟩ := exists_auxWords_comp σ _ _ _ hW
    refine ⟨_, Or.inr (Or.inr (Or.inr (Or.inr ⟨e, W, hW₀, rfl⟩))), fun p _ => ?_⟩
    simp only [auxGuide]
    rw [h.n_eq, h.nbrLabel_eq]
    exact bandUpdate_comp σ R.n e W rfl

end Relabel

end RepaintingBaseline

/-! ### Conical guides about the corners of the unit square -/

/-- A labelling is conical about `c`: in the open sup square of radius `1/2` about `c` it is
constant along each open ray from `c`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:301–302, 486–488`. -/
def IsConicalAt {ι : Type*} (f : ℝ × ℝ → ι) (c : ℝ × ℝ) : Prop :=
  ∀ (w : ℝ × ℝ) (a b : ℝ), 0 < a → 0 < b → ‖a • w‖ < 1 / 2 → ‖b • w‖ < 1 / 2 →
    f (c + a • w) = f (c + b • w)

theorem corner_trichotomy {c : ℝ × ℝ} (hc : IsSquareCorner 1 c) (e : SquareEdge) :
    c = e.point 1 0 0 ∨ c = e.point 1 1 0 ∨ e.nor 1 c = 1 := by
  rcases hc with rfl | rfl | rfl | rfl <;> cases e <;> simp [point, nor]

theorem SquareEdge.par_add_smul (e : SquareEdge) (c w : ℝ × ℝ) (a : ℝ) :
    e.par (c + a • w) = e.par c + a * e.par w := by
  cases e <;> simp [par]

theorem SquareEdge.nor_add_smul (e : SquareEdge) (c w : ℝ × ℝ) (a : ℝ) :
    e.nor 1 (c + a • w) = e.nor 1 c + a * (e.nor 1 w - e.nor 1 0) := by
  cases e <;> simp [nor] <;> ring

private theorem abs_par_lt {e : SquareEdge} {a : ℝ} {w : ℝ × ℝ} (h : ‖a • w‖ < 1 / 2) :
    |a * e.par w| < 1 / 2 := by
  have := e.abs_par_sub_le 1 (a • w) 0
  rw [e.par_smul, show e.par (0 : ℝ × ℝ) = 0 by cases e <;> rfl, sub_zero, dist_zero_right] at this
  exact this.trans_lt h

private theorem abs_nor_lt {e : SquareEdge} {a : ℝ} {w : ℝ × ℝ} (h : ‖a • w‖ < 1 / 2) :
    |a * (e.nor 1 w - e.nor 1 0)| < 1 / 2 := by
  have := e.abs_nor_sub_le 1 (0 + a • w) 0
  rw [e.nor_add_smul, add_sub_cancel_left, zero_add, dist_zero_right] at this
  exact this.trans_lt h

private theorem cone_iff {a P N α β : ℝ} (ha : 0 < a) :
    (0 < a * P ∧ α * (a * P / 1000) < a * N ∧ a * N < β * (a * P / 1000)) ↔
      (0 < P ∧ α * (P / 1000) < N ∧ N < β * (P / 1000)) := by
  rw [show α * (a * P / 1000) = a * (α * (P / 1000)) by ring,
    show β * (a * P / 1000) = a * (β * (P / 1000)) by ring, mul_pos_iff_of_pos_left ha,
    mul_lt_mul_iff_of_pos_left ha, mul_lt_mul_iff_of_pos_left ha]

/-- Off the two endpoints of an edge, a point within `1/2` of a corner with normal coordinate `1`
lies in no band of normal ratio below `8`. -/
private theorem notMem_edgeBand_of_nor_eq_one {e : SquareEdge} {α β : ℝ} (hβ : β ≤ 8)
    {c w : ℝ × ℝ} {a : ℝ} (hc : e.nor 1 c = 1) (ha : ‖a • w‖ < 1 / 2) :
    c + a • w ∉ edgeBand 1 e α β := by
  rintro ⟨h1, h2, -, h4⟩
  have hw0 := bandWidth_nonneg h1.le h2.le
  have w1 := bandWidth_le_left 1 (e.par (c + a • w))
  have w2 := bandWidth_le_right 1 (e.par (c + a • w))
  have hd := abs_nor_lt (e := e) ha
  rw [e.nor_add_smul, hc] at h4
  rw [abs_lt] at hd
  nlinarith

/-- **Bands are conical about the corners.** -/
theorem mem_edgeBand_conical {c : ℝ × ℝ} (hc : IsSquareCorner 1 c) (e : SquareEdge) {α β : ℝ}
    (hβ : β ≤ 8) {w : ℝ × ℝ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (haw : ‖a • w‖ < 1 / 2)
    (hbw : ‖b • w‖ < 1 / 2) :
    c + a • w ∈ edgeBand 1 e α β ↔ c + b • w ∈ edgeBand 1 e α β := by
  have mem (x : ℝ) (hx : ‖x • w‖ < 1 / 2) : c + x • w ∈ ball c (1 / 2) := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]; exact hx
  rcases corner_trichotomy hc e with rfl | rfl | hn
  · rw [mem_edgeBand_iff_of_mem_ball (mem _ haw), mem_edgeBand_iff_of_mem_ball (mem _ hbw)]
    simp only [e.par_add_smul, e.nor_add_smul, par_point, nor_point, zero_add]
    rw [cone_iff ha, cone_iff hb]
  · rw [mem_edgeBand_iff_of_mem_ball_end (mem _ haw), mem_edgeBand_iff_of_mem_ball_end (mem _ hbw)]
    simp only [e.par_add_smul, e.nor_add_smul, par_point, nor_point, zero_add]
    have key (x : ℝ) (hx : 0 < x) : (1 + x * e.par w < 1 ∧
        α * ((1 - (1 + x * e.par w)) / 1000) < x * (e.nor 1 w - e.nor 1 0) ∧
        x * (e.nor 1 w - e.nor 1 0) < β * ((1 - (1 + x * e.par w)) / 1000)) ↔
        (0 < -e.par w ∧ α * (-e.par w / 1000) < e.nor 1 w - e.nor 1 0 ∧
          e.nor 1 w - e.nor 1 0 < β * (-e.par w / 1000)) := by
      rw [← cone_iff hx, show 1 - (1 + x * e.par w) = x * -e.par w by ring,
        show (1 + x * e.par w < 1) ↔ 0 < x * -e.par w by constructor <;> intro h <;> linarith]
    rw [key a ha, key b hb]
  · exact iff_of_false (notMem_edgeBand_of_nor_eq_one hβ hn haw)
      (notMem_edgeBand_of_nor_eq_one hβ hn hbw)

/-- **Band coordinates are conical about the corners.** -/
theorem bandCoord_conical {c : ℝ × ℝ} (hc : IsSquareCorner 1 c) (e : SquareEdge) {w : ℝ × ℝ}
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (haw : ‖a • w‖ < 1 / 2) (hbw : ‖b • w‖ < 1 / 2)
    (hx : c + a • w ∈ edgeBand 1 e (-8) 2) :
    bandCoord 1 e (c + a • w) = bandCoord 1 e (c + b • w) := by
  have hp := abs_par_lt (e := e) haw
  have hq := abs_par_lt (e := e) hbw
  rw [abs_lt] at hp hq
  rcases corner_trichotomy hc e with rfl | rfl | hn
  · simp only [bandCoord, e.par_add_smul, e.nor_add_smul, par_point, nor_point, zero_add]
    rw [bandWidth_of_le_half (by linarith), bandWidth_of_le_half (by linarith),
      mul_div_assoc a (e.par w), mul_div_assoc b (e.par w), mul_div_mul_left _ _ ha.ne',
      mul_div_mul_left _ _ hb.ne']
  · simp only [bandCoord, e.par_add_smul, e.nor_add_smul, par_point, nor_point, zero_add]
    rw [bandWidth_of_half_le (by linarith), bandWidth_of_half_le (by linarith),
      show (1 - (1 + a * e.par w)) / 1000 = a * (-e.par w / 1000) by ring,
      show (1 - (1 + b * e.par w)) / 1000 = b * (-e.par w / 1000) by ring,
      mul_div_mul_left _ _ ha.ne', mul_div_mul_left _ _ hb.ne']
  · exact absurd hx (notMem_edgeBand_of_nor_eq_one (by norm_num) hn haw)

private theorem box_conical {c₁ t a b : ℝ} (hc : c₁ = 0 ∨ c₁ = 1) (ha : 0 < a) (hb : 0 < b)
    (hat : |a * t| < 1 / 2) (hbt : |b * t| < 1 / 2) :
    (0 < c₁ + a * t ∧ c₁ + a * t < 1) ↔ (0 < c₁ + b * t ∧ c₁ + b * t < 1) := by
  rw [abs_lt] at hat hbt
  rcases hc with rfl | rfl
  · simp only [zero_add, mul_pos_iff_of_pos_left ha, mul_pos_iff_of_pos_left hb]
    constructor <;> rintro ⟨h, -⟩ <;> exact ⟨h, by linarith⟩
  · have e1 : 1 + a * t < 1 ↔ a * t < 0 := by constructor <;> intro h <;> linarith
    have e2 : 1 + b * t < 1 ↔ b * t < 0 := by constructor <;> intro h <;> linarith
    have n1 (x : ℝ) (hx : 0 < x) : x * t < 0 ↔ t < 0 :=
      ⟨fun h => neg_of_mul_neg_right h hx.le, fun h => mul_neg_of_pos_of_neg hx h⟩
    rw [e1, e2, n1 a ha, n1 b hb]
    constructor <;> rintro ⟨-, h⟩ <;> exact ⟨by linarith, h⟩

/-- **The central region is conical about the corners.** -/
theorem mem_centralRegion_conical {c : ℝ × ℝ} (hc : IsSquareCorner 1 c) {w : ℝ × ℝ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (haw : ‖a • w‖ < 1 / 2) (hbw : ‖b • w‖ < 1 / 2) :
    c + a • w ∈ centralRegion 1 ↔ c + b • w ∈ centralRegion 1 := by
  have hc' : (c.1 = 0 ∨ c.1 = 1) ∧ (c.2 = 0 ∨ c.2 = 1) := by
    rcases hc with rfl | rfl | rfl | rfl <;> simp
  have coord (x : ℝ) (hx : ‖x • w‖ < 1 / 2) : |x * w.1| < 1 / 2 ∧ |x * w.2| < 1 / 2 := by
    rw [Prod.norm_def, max_lt_iff] at hx
    simpa [Real.norm_eq_abs, abs_mul] using hx
  have edge (e : SquareEdge) :
      bandWidth 1 (e.par (c + a • w)) < e.nor 1 (c + a • w) ↔
        bandWidth 1 (e.par (c + b • w)) < e.nor 1 (c + b • w) := by
    have hp := abs_par_lt (e := e) haw
    have hq := abs_par_lt (e := e) hbw
    have np := abs_nor_lt (e := e) haw
    have nq := abs_nor_lt (e := e) hbw
    rw [abs_lt] at hp hq np nq
    simp only [e.par_add_smul, e.nor_add_smul]
    rcases corner_trichotomy hc e with rfl | rfl | hn
    · simp only [par_point, nor_point, zero_add]
      rw [bandWidth_of_le_half (by linarith), bandWidth_of_le_half (by linarith),
        mul_div_assoc, mul_div_assoc, mul_lt_mul_iff_of_pos_left ha,
        mul_lt_mul_iff_of_pos_left hb]
    · simp only [par_point, nor_point, zero_add]
      rw [bandWidth_of_half_le (by linarith), bandWidth_of_half_le (by linarith),
        show (1 - (1 + a * e.par w)) / 1000 = a * (-e.par w / 1000) by ring,
        show (1 - (1 + b * e.par w)) / 1000 = b * (-e.par w / 1000) by ring,
        mul_lt_mul_iff_of_pos_left ha, mul_lt_mul_iff_of_pos_left hb]
    · rw [hn]
      have w1 := bandWidth_le_left 1 (e.par c + a * e.par w)
      have w2 := bandWidth_le_right 1 (e.par c + a * e.par w)
      have w3 := bandWidth_le_left 1 (e.par c + b * e.par w)
      have w4 := bandWidth_le_right 1 (e.par c + b * e.par w)
      exact iff_of_true (by linarith) (by linarith)
  have hx := box_conical hc'.1 ha hb (coord a haw).1 (coord b hbw).1
  have hy := box_conical hc'.2 ha hb (coord a haw).2 (coord b hbw).2
  simp only [centralRegion, mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul] at hx hy ⊢
  rw [forall_congr' edge]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨(hx.1 ⟨h1, h2⟩).1, (hx.1 ⟨h1, h2⟩).2, (hy.1 ⟨h3, h4⟩).1, (hy.1 ⟨h3, h4⟩).2, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨(hx.2 ⟨h1, h2⟩).1, (hx.2 ⟨h1, h2⟩).2, (hy.2 ⟨h3, h4⟩).1, (hy.2 ⟨h3, h4⟩).2, h5⟩

private theorem floor_conical (k : ℤ) {t a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hat : |a * t| < 1 / 2) (hbt : |b * t| < 1 / 2) : ⌊(k : ℝ) + a * t⌋ = ⌊(k : ℝ) + b * t⌋ := by
  rw [abs_lt] at hat hbt
  rcases le_or_gt 0 t with ht | ht
  · have h1 : 0 ≤ a * t := mul_nonneg ha.le ht
    have h2 : 0 ≤ b * t := mul_nonneg hb.le ht
    rw [Int.floor_eq_iff.2 ⟨by linarith, by linarith⟩,
      Int.floor_eq_iff.2 ⟨by linarith, by linarith⟩]
  · have h1 : a * t < 0 := mul_neg_of_pos_of_neg ha ht
    have h2 : b * t < 0 := mul_neg_of_pos_of_neg hb ht
    have e1 : ⌊(k : ℝ) + a * t⌋ = k - 1 :=
      Int.floor_eq_iff.2 ⟨by push_cast; linarith, by push_cast; linarith⟩
    have e2 : ⌊(k : ℝ) + b * t⌋ = k - 1 :=
      Int.floor_eq_iff.2 ⟨by push_cast; linarith, by push_cast; linarith⟩
    rw [e1, e2]

/-- A guide uniform on the unit blocks is conical about every corner of the unit square. -/
theorem isConicalAt_blockGuide {ι : Type*} (lab : ℤ × ℤ → ι) {c : ℝ × ℝ}
    (hc : IsSquareCorner 1 c) : IsConicalAt (blockGuide 1 lab) c := by
  intro w a b ha hb haw hbw
  have coord (x : ℝ) (hx : ‖x • w‖ < 1 / 2) : |x * w.1| < 1 / 2 ∧ |x * w.2| < 1 / 2 := by
    rw [Prod.norm_def, max_lt_iff] at hx
    simpa [Real.norm_eq_abs, abs_mul] using hx
  obtain ⟨k₁, k₂, hk⟩ : ∃ k₁ k₂ : ℤ, c = ((k₁ : ℝ), (k₂ : ℝ)) := by
    rcases hc with rfl | rfl | rfl | rfl
    exacts [⟨0, 0, by simp⟩, ⟨1, 0, by simp⟩, ⟨0, 1, by simp⟩, ⟨1, 1, by simp⟩]
  subst hk
  simp only [blockGuide, blockIndex, div_one, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  rw [floor_conical k₁ ha hb (coord a haw).1 (coord b hbw).1,
    floor_conical k₂ ha hb (coord a haw).2 (coord b hbw).2]

/-- Replacing a band of a guide conical about a corner of the unit square by a word keeps it
conical. -/
theorem IsConicalAt.bandUpdate {ι : Type*} {g : ℝ × ℝ → ι} {c : ℝ × ℝ} (h : IsConicalAt g c)
    (hc : IsSquareCorner 1 c) (e : SquareEdge) (W : ℝ → ι) :
    IsConicalAt (bandUpdate 1 e W g) c := by
  intro w a b ha hb haw hbw
  by_cases hx : c + a • w ∈ edgeBand 1 e (-8) 2
  · have hy := (mem_edgeBand_conical hc e (by norm_num) ha hb haw hbw).1 hx
    rw [bandUpdate_of_mem hx, bandUpdate_of_mem hy, bandCoord_conical hc e ha hb haw hbw hx]
  · have hy := fun h' => hx ((mem_edgeBand_conical hc e (by norm_num) ha hb haw hbw).2 h')
    rw [bandUpdate_of_notMem hx, bandUpdate_of_notMem hy, h w a b ha hb haw hbw]

namespace RepaintingBaseline

variable {ι : Type*} (R : RepaintingBaseline ι)

/-- **Unmodified guides are conical about the corners.** For a repainting of a square of side one
whose starting guide is conical about a corner, every unmodified guide is conical about it: near
the corner, all its interfaces are rays.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:301–302, 486–488`. -/
theorem IsUnmodifiedGuide.isConicalAt (hn : R.n = 1) {c : ℝ × ℝ} (hc : IsSquareCorner 1 c)
    (hR : IsConicalAt R.guide c) {g : ℝ × ℝ → ι} (hg : R.IsUnmodifiedGuide g) :
    IsConicalAt g c := by
  have central : IsConicalAt R.centralGuide c := by
    intro w a b ha hb haw hbw
    have key := mem_centralRegion_conical hc ha hb haw hbw
    rw [← hn] at key
    by_cases hx : c + a • w ∈ centralRegion R.n
    · rw [R.centralGuide_of_mem hx, R.centralGuide_of_mem (key.1 hx)]
    · rw [R.centralGuide_of_notMem hx, R.centralGuide_of_notMem fun h => hx (key.2 h),
        hR w a b ha hb haw hbw]
  have completed (E : List SquareEdge) : IsConicalAt (R.completedGuide E) c := by
    induction E with
    | nil => exact central
    | cons e E ih =>
      simp only [completedGuide, hn]
      exact ih.bandUpdate hc e _
  rcases hg with rfl | rfl | ⟨E, rfl⟩ | ⟨E, e, W, -, rfl⟩ | ⟨e, W, -, rfl⟩
  · exact hR
  · exact central
  · exact completed E
  · simp only [mainGuide, hn]
    exact (completed E).bandUpdate hc e W
  · simp only [auxGuide, hn]
    exact IsConicalAt.bandUpdate (fun _ _ _ _ _ _ _ => rfl) hc e W

end RepaintingBaseline

/-! ### The reference repainting -/

/-- The `3 × 3` blocks about the block `(0, 0)`. -/
def windowBlocks : Finset (ℤ × ℤ) := Finset.Icc (-1) 1 ×ˢ Finset.Icc (-1) 1

/-- The labels of the reference repainting: one slot for each block of the window, and one slot
for the final label and for the blocks outside the window. -/
abbrev WindowSlot := Option windowBlocks

/-- The slot of a block. -/
def windowSlot (Q : ℤ × ℤ) : WindowSlot := if h : Q ∈ windowBlocks then some ⟨Q, h⟩ else none

/-- The labels that a repainting with block labels `lab` and final label `B` puts in the slots. -/
def windowLabel {ι : Type*} (lab : ℤ × ℤ → ι) (B : ι) : WindowSlot → ι
  | none => B
  | some Q => lab Q

/-- The reference repainting: the block `(0, 0)` of side one, labelled by the slots. -/
noncomputable def referenceRepainting : RepaintingBaseline WindowSlot :=
  blockBaseline one_pos windowSlot (0, 0) none

theorem nbrBlock_zero_mem_windowBlocks (e : SquareEdge) : e.nbrBlock (0, 0) ∈ windowBlocks := by
  cases e <;> decide

theorem windowLabel_windowSlot {ι : Type*} (lab : ℤ × ℤ → ι) (B : ι) {Q : ℤ × ℤ}
    (hQ : Q ∈ windowBlocks) : windowLabel lab B (windowSlot Q) = lab Q := by
  simp [windowSlot, hQ, windowLabel]

/-- The repainting of the block `(0, 0)` of side one with block labels `lab` and final label `B`
is the reference repainting relabelled by the window labels. -/
theorem isRelabel_referenceRepainting {ι : Type*} (lab : ℤ × ℤ → ι) (B : ι) :
    referenceRepainting.IsRelabel (blockBaseline one_pos lab (0, 0) B) (windowLabel lab B) where
  n_eq := rfl
  oldLabel_eq := (windowLabel_windowSlot lab B (by decide)).symm
  finalLabel_eq := rfl
  nbrLabel_eq e := (windowLabel_windowSlot lab B (nbrBlock_zero_mem_windowBlocks e)).symm

/-- The repainting of the block `S` of side `n` scales to the repainting of the block `(0, 0)` of
side one with the block labels translated by `S`. -/
theorem isRescale_blockBaseline {ι : Type*} {n : ℝ} (hn : 0 < n) (lab : ℤ × ℤ → ι)
    (S : ℤ × ℤ) (B : ι) :
    (blockBaseline hn lab S B).IsRescale (blockBaseline one_pos (fun Q => lab (Q + S)) (0, 0) B)
    where
  n_eq := rfl
  guide_eq p := by
    simp only [blockBaseline, blockGuide, blockIndex, blockCorner]
    congr 1
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      Int.cast_zero, mul_zero, add_zero, div_one]
    have h1 : (p.1 + n * S.1) / n = n⁻¹ * p.1 + S.1 := by field_simp
    have h2 : (p.2 + n * S.2) / n = n⁻¹ * p.2 + S.2 := by field_simp
    rw [h1, h2, Int.floor_add_intCast, Int.floor_add_intCast]
    rfl
  oldLabel_eq := by
    simp only [blockBaseline]
    congr 1
    exact Prod.ext (by simp) (by simp)
  finalLabel_eq := rfl
  nbrLabel_eq e := by
    cases e <;> simp only [blockBaseline, SquareEdge.nbrBlock] <;> congr 1 <;>
      refine Prod.ext ?_ ?_ <;> simp <;> ring

/-! ### Finitely many templates -/

namespace RepaintingBaseline

variable {ι : Type*} (R : RepaintingBaseline ι)

/-- A completed guide depends only on which edges are completed. -/
theorem completedGuide_congr {E E' : List SquareEdge} (h : ∀ e, e ∈ E ↔ e ∈ E') :
    R.completedGuide E = R.completedGuide E' := by
  funext p
  by_cases hb : ∃ e, p ∈ edgeBand R.n e (-8) 2
  · obtain ⟨e, he⟩ := hb
    rw [R.completedGuide_of_mem_edgeBand he, R.completedGuide_of_mem_edgeBand he]
    simp only [h e]
  · push Not at hb
    rw [R.completedGuide_of_forall_notMem fun e _ => hb e,
      R.completedGuide_of_forall_notMem fun e _ => hb e]

/-- **Finitely many unmodified guides.** A repainting has only finitely many unmodified guides. -/
theorem finite_isUnmodifiedGuide : {g | R.IsUnmodifiedGuide g}.Finite := by
  classical
  have hE (E : List SquareEdge) : R.completedGuide E = R.completedGuide E.toFinset.toList :=
    R.completedGuide_congr fun e => by simp
  have hM (e : SquareEdge) : (mainWords R.oldLabel R.finalLabel (R.nbrLabel e)).Finite := by
    unfold mainWords; exact Set.toFinite _
  have hA (e : SquareEdge) : (auxWords R.oldLabel R.finalLabel (R.nbrLabel e)).Finite := by
    unfold auxWords; exact Set.toFinite _
  refine ((((Set.finite_singleton R.guide).insert R.centralGuide).union
    (Set.finite_range fun s : Finset SquareEdge => R.completedGuide s.toList)).union
    ((Set.finite_iUnion fun s : Finset SquareEdge => Set.finite_iUnion fun e =>
      (hM e).image (R.mainGuide s.toList e)).union
    (Set.finite_iUnion fun e => (hA e).image (R.auxGuide e)))).subset ?_
  rintro g (rfl | rfl | ⟨E, rfl⟩ | ⟨E, e, W, hW, rfl⟩ | ⟨e, W, hW, rfl⟩)
  · exact Or.inl (Or.inl (Or.inr rfl))
  · exact Or.inl (Or.inl (Or.inl rfl))
  · exact Or.inl (Or.inr ⟨E.toFinset, (hE E).symm⟩)
  · refine Or.inr (Or.inl (mem_iUnion.2 ⟨E.toFinset, mem_iUnion.2 ⟨e, W, hW, ?_⟩⟩))
    simp only [mainGuide, ← hE]
  · exact Or.inr (Or.inr (mem_iUnion.2 ⟨e, W, hW, rfl⟩))

end RepaintingBaseline

/-- The point treatment at `v`: the guide homogenized to `P₀` on the open sup square of radius
`t` about `v` when `P = some P₀`, and the guide itself when `P = none`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:330–338`. -/
noncomputable def pointTreated {ι : Type*} (v : ℝ × ℝ) (t : ℝ) (P : Option ι)
    (f : ℝ × ℝ → ι) : ℝ × ℝ → ι :=
  Option.elim P f fun P₀ => homogenize (ball v t) P₀ f

/-- The index of the templates: an unmodified guide of the reference repainting, a corner of the
unit square, the homogenizing label if any, and a representative map of a label-equality type. -/
abbrev TemplateIndex : Type :=
  {g // referenceRepainting.IsUnmodifiedGuide g} × {c : ℝ × ℝ // IsSquareCorner 1 c} ×
    Option WindowSlot × (WindowSlot → WindowSlot)

instance : Finite TemplateIndex := by
  have h1 : Finite {g // referenceRepainting.IsUnmodifiedGuide g} :=
    referenceRepainting.finite_isUnmodifiedGuide.to_subtype
  have h2 : Finite {c : ℝ × ℝ // IsSquareCorner 1 c} :=
    (Set.toFinite ({(0, 0), (1, 0), (0, 1), (1, 1)} : Set (ℝ × ℝ))).subset
      (fun c hc => by rcases hc with rfl | rfl | rfl | rfl <;> simp) |>.to_subtype
  infer_instance

/-- The template guide of an index, in units of `t` about the mark: the reference guide about the
corner, scaled by `1/32`, point-treated on the unit square about the origin, and relabelled. -/
noncomputable def template (i : TemplateIndex) (u : ℝ × ℝ) : WindowSlot :=
  i.2.2.2 (pointTreated 0 1 i.2.2.1 (fun u => i.1.1 (i.2.1.1 + (1 / 32 : ℝ) • u)) u)

/-! ### The guides near a mark are relabelled templates -/

/-- The offset of the grid corner `Q` from the lower-left corner of the block `S`, in units of the
side. -/
def cornerOffset (S Q : ℤ × ℤ) : ℝ × ℝ := (((Q.1 - S.1 : ℤ) : ℝ), ((Q.2 - S.2 : ℤ) : ℝ))

theorem isSquareCorner_cornerOffset {S Q : ℤ × ℤ} (hQ : IsBlockCornerOf S Q) :
    IsSquareCorner 1 (cornerOffset S Q) := by
  obtain ⟨h1 | h1, h2 | h2⟩ := hQ <;> simp [IsSquareCorner, cornerOffset, h1, h2]

theorem blockCorner_sub_blockCorner (n : ℝ) (S Q : ℤ × ℤ) :
    blockCorner n Q - blockCorner n S = n • cornerOffset S Q := by
  refine Prod.ext ?_ ?_ <;> simp [blockCorner, cornerOffset] <;> ring

theorem blockIndex_mem_windowBlocks {c p : ℝ × ℝ} (hc : IsSquareCorner 1 c)
    (hp : dist p c < 1 / 8) : blockIndex 1 p ∈ windowBlocks := by
  have hc' : (c.1 = 0 ∨ c.1 = 1) ∧ (c.2 = 0 ∨ c.2 = 1) := by
    rcases hc with rfl | rfl | rfl | rfl <;> simp
  rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, abs_lt, abs_lt] at hp
  have k (x c₀ : ℝ) (hc₀ : c₀ = 0 ∨ c₀ = 1) (h1 : -(1 / 8) < x - c₀) (h2 : x - c₀ < 1 / 8) :
      ⌊x / 1⌋ ∈ Finset.Icc (-1 : ℤ) 1 := by
    rw [div_one, Finset.mem_Icc]
    have a : (-1 : ℝ) < x := by rcases hc₀ with rfl | rfl <;> linarith
    have b : x < 2 := by rcases hc₀ with rfl | rfl <;> linarith
    have a' : -1 ≤ ⌊x⌋ := Int.le_floor.2 (by push_cast; linarith)
    have b' : ⌊x⌋ < 2 := Int.floor_lt.2 (by push_cast; linarith)
    omega
  exact Finset.mem_product.2 ⟨k _ _ hc'.1 hp.1.1 hp.1.2, k _ _ hc'.2 hp.2.1 hp.2.2⟩

section Instantiation

variable {ι : Type*} {n t : ℝ} (hn : 0 < n) {lab : ℤ × ℤ → ι} {S : ℤ × ℤ} {B : ι}

/-- **The guides near a mark are relabelled templates.** For `8 t < n`, every unmodified guide of
the repainting of the block `S` is, on the open square of radius `4 t` about a corner `v` of the
block, the relabelling by the window labels of the reference guide about the corresponding corner
of the unit square, scaled from `t` to `1/32`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:301–302, 486–491`. -/
theorem exists_reference_eq {g : ℝ × ℝ → ι} (hg : (blockBaseline hn lab S B).IsUnmodifiedGuide g)
    {Q : ℤ × ℤ} (hQ : IsBlockCornerOf S Q) (ht : 0 < t) (htn : 8 * t < n) :
    ∃ g₀, referenceRepainting.IsUnmodifiedGuide g₀ ∧ ∀ u : ℝ × ℝ, ‖u‖ < 4 →
      shiftGuide (blockCorner n S) g (blockCorner n Q + t • u) =
        windowLabel (fun R => lab (R + S)) B (g₀ (cornerOffset S Q + (1 / 32 : ℝ) • u)) := by
  set c := cornerOffset S Q
  have hc := isSquareCorner_cornerOffset hQ
  obtain ⟨g₁, hg₁, hg₁eq⟩ := (isRescale_blockBaseline hn lab S B).isUnmodifiedGuide hg
  obtain ⟨g₀, hg₀, hg₀eq⟩ :=
    (isRelabel_referenceRepainting (fun R => lab (R + S)) B).isUnmodifiedGuide hg₁
  have hbase : IsConicalAt (blockBaseline one_pos (fun R => lab (R + S)) (0, 0) B).guide c := by
    intro w a b ha hb haw hbw
    have := isConicalAt_blockGuide (fun R => lab (R + S)) hc w a b ha hb haw hbw
    simpa only [blockBaseline, blockCorner, Int.cast_zero, mul_zero, Prod.mk_zero_zero,
      add_zero] using this
  have hcon := RepaintingBaseline.IsUnmodifiedGuide.isConicalAt _ rfl hc hbase hg₁
  refine ⟨g₀, hg₀, fun u hu => ?_⟩
  have hnt : 0 < n⁻¹ * t := mul_pos (inv_pos.2 hn) ht
  have hnt' : n⁻¹ * t < 1 / 8 := by
    rw [inv_mul_lt_iff₀ hn]; linarith
  have hsmall (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 8) : ‖x • u‖ < 1 / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hx0]
    nlinarith [norm_nonneg u]
  have hp : n⁻¹ • (blockCorner n Q + t • u - blockCorner n S) = c + (n⁻¹ * t) • u := by
    rw [add_sub_right_comm, blockCorner_sub_blockCorner, smul_add, smul_smul, smul_smul,
      inv_mul_cancel₀ hn.ne', one_smul]
  have hwin : dist (c + (1 / 32 : ℝ) • u) c < 1 / 8 := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 32)]
    linarith [norm_nonneg u]
  have hrel : (blockBaseline one_pos (fun R => lab (R + S)) (0, 0) B).guide
      (c + (1 / 32 : ℝ) • u) = windowLabel (fun R => lab (R + S)) B
        (referenceRepainting.guide (c + (1 / 32 : ℝ) • u)) := by
    have hm := blockIndex_mem_windowBlocks hc hwin
    simp only [referenceRepainting, blockBaseline, blockGuide, blockCorner, Int.cast_zero,
      mul_zero, Prod.mk_zero_zero, add_zero]
    rw [windowLabel_windowSlot _ _ hm]
  simp only [shiftGuide]
  rw [hg₁eq]
  change g₁ (n⁻¹ • (blockCorner n Q + t • u - blockCorner n S)) = _
  rw [hp, hcon u (n⁻¹ * t) (1 / 32) hnt (by norm_num) (hsmall _ hnt.le hnt'.le)
    (hsmall _ (by norm_num) (by norm_num)), hg₀eq _ hrel]

/-- **The point-treated guides near a mark are relabelled templates.** -/
theorem exists_template_eq {g : ℝ × ℝ → ι}
    (hg : (blockBaseline hn lab S B).IsUnmodifiedGuide g) {Q : ℤ × ℤ} (hQ : IsBlockCornerOf S Q)
    (ht : 0 < t) (htn : 8 * t < n) (Pκ : Option WindowSlot) :
    ∃ i : TemplateIndex, i.2.1.1 = cornerOffset S Q ∧ i.2.2.1 = Pκ ∧
      i.2.2.2 = classRep (windowLabel (fun R => lab (R + S)) B) ∧
      ∀ q ∈ ball (blockCorner n Q) (4 * t),
        pointTreated (blockCorner n Q) t (Pκ.map (windowLabel (fun R => lab (R + S)) B))
          (shiftGuide (blockCorner n S) g) q =
        windowLabel (fun R => lab (R + S)) B (template i (t⁻¹ • (q - blockCorner n Q))) := by
  set σ := windowLabel (fun R => lab (R + S)) B
  set v := blockCorner n Q
  obtain ⟨g₀, hg₀, heq⟩ := exists_reference_eq hn hg hQ ht htn
  refine ⟨(⟨g₀, hg₀⟩, ⟨_, isSquareCorner_cornerOffset hQ⟩, Pκ, classRep σ), rfl, rfl, rfl,
    fun q hq => ?_⟩
  set u := t⁻¹ • (q - v)
  have hqu : q = v + t • u := by
    simp only [u, smul_smul, mul_inv_cancel₀ ht.ne', one_smul, add_sub_cancel]
  have hu : ‖u‖ < 4 := by
    rw [mem_ball, dist_eq_norm] at hq
    simp only [u, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht]
    rw [inv_mul_lt_iff₀ ht]; linarith
  have hball : q ∈ ball v t ↔ u ∈ ball (0 : ℝ × ℝ) 1 := by
    rw [mem_ball, mem_ball, dist_eq_norm, dist_eq_norm, sub_zero]
    simp only [u, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht]
    rw [inv_mul_lt_iff₀ ht, mul_one]
  have hf := heq u hu
  rw [← hqu] at hf
  simp only [template, classRep_spec]
  cases Pκ with
  | none => simp only [Option.map_none, pointTreated, Option.elim]; exact hf
  | some k =>
    simp only [Option.map_some, pointTreated, Option.elim, homogenize]
    by_cases h : q ∈ ball v t
    · simp [h, hball.1 h]
    · simp only [h, hball.not.1 h, ite_false]
      exact hf

end Instantiation

/-! ### One footprint ratio for the point treatment -/

universe u

/-- **One footprint ratio for the point treatment at every scale.** Fix `ε₀ > 0`. There is a ratio
`ν > 0` such that for every repainting of a block of side `n`, every scale `t` with `8 t < n`,
every unmodified guide, every corner `v` of the block and every homogenizing label among the final
label and the labels of the blocks next to the repainted one (or none), the guide point-treated
on the open square of radius `t` about `v` has the two-owner condition with working set the closed
square of radius `2 t` about `v`, holes at its true vertices within `3 t` of `v`, inner radius
`ε₀ t` and footprint radius `ν t`. For `ε₀ ≤ 1` holes centered farther than `3 t` from `v` do not
meet the working set. So the patch ratio `ν` near a mark does not depend on the scale, the block,
its labels, the guide or the mark.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:464–479, 481–505`. -/
theorem exists_pointTreatment_footprintRatio {ε₀ : ℝ} (hε : 0 < ε₀) :
    ∃ ν > 0, ∀ {ι : Type u} {n t : ℝ} (hn : 0 < n), 0 < t → 8 * t < n →
      ∀ {lab : ℤ × ℤ → ι} {S : ℤ × ℤ} {B : ι} {g : ℝ × ℝ → ι},
      (blockBaseline hn lab S B).IsUnmodifiedGuide g → ∀ {Q : ℤ × ℤ}, IsBlockCornerOf S Q →
      ∀ P : Option ι, (∀ x ∈ P, x = B ∨ ∃ R ∈ windowBlocks, x = lab (R + S)) →
      TwoOwnerFootprints (pointTreated (blockCorner n Q) t P (shiftGuide (blockCorner n S) g))
        (closedBall (blockCorner n Q) (2 * t))
        {c | c ∈ closedBall (blockCorner n Q) (3 * t) ∧
          IsTrueVertex (pointTreated (blockCorner n Q) t P (shiftGuide (blockCorner n S) g)) c}
        (ε₀ * t) (ν * t) := by
  obtain ⟨ν, hν, H⟩ := exists_footprintRatio.{0, 0, u} (I := TemplateIndex) (g := template)
    (fun _ => Set.toFinite _) (W := fun _ => closedBall 0 2) (fun _ => isCompact_closedBall 0 2)
    (H := fun i => {u | u ∈ closedBall (0 : ℝ × ℝ) 3 ∧ IsTrueVertex (template i) u})
    (r₀ := ε₀) (r₁ := ε₀) (fun _ c hc htv =>
      ⟨c, ⟨closedBall_subset_closedBall (by norm_num) hc, htv⟩, mem_ball_self hε⟩)
  refine ⟨ν, hν, fun {ι n t} hn ht htn {lab S B g} hg {Q} hQ P hP => ?_⟩
  set σ := windowLabel (fun R => lab (R + S)) B
  set v := blockCorner n Q
  obtain ⟨Pκ, rfl⟩ : ∃ Pκ : Option WindowSlot, P = Pκ.map σ := by
    cases P with
    | none => exact ⟨none, rfl⟩
    | some x =>
      rcases hP x rfl with rfl | ⟨R, hR, rfl⟩
      · exact ⟨some none, rfl⟩
      · exact ⟨some (some ⟨R, hR⟩), rfl⟩
  obtain ⟨i, -, -, hπ, heq⟩ := exists_template_eq hn hg hQ ht htn Pκ
  have hinj : InjOn σ (range (template i)) := (injOn_range_classRep σ).mono (by
    rintro _ ⟨w, rfl⟩
    simp only [template, hπ]
    exact mem_range_self _)
  have key := TwoOwnerFootprints.of_template (ρ₁ := 2) (ρ₂ := 3) (ρ₃ := 4) hinj ht
    (by norm_num) (by norm_num) (fun q hq => heq q (by rwa [mul_comm] at hq))
    (H i σ v ht ε₀ ⟨le_rfl, le_rfl⟩)
  rwa [mul_comm t 2, mul_comm t 3, mul_comm t ε₀] at key

end TNLean.PEPS.Approximation
