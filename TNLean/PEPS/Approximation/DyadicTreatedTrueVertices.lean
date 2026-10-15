/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicLargeRepaintingGates
import TNLean.PEPS.Approximation.DyadicLevelTrueVertices
import TNLean.PEPS.Approximation.DyadicPointTreatmentRewrite

/-!
# The true vertices of a temporary guide as a finite set

During the repainting of a block, the frames of the point treatments have their holes at the true
vertices of the readings of the temporary guides: unmodified guides homogenized on the open
squares of radius `t` about finitely many marks (`06-geometry.tex`, lines 328–351). Such a true
vertex is a grid corner or a point of the rim pattern of a mark
(`isTrueVertex_homogenize_cases`). When the labels of the level are the placeholder outside the
root square, the grid corners that are true vertices lie in a fixed box, so the true vertices of a
temporary guide form a finite set (`treatedTrueVertices`, `mem_treatedTrueVertices`), the set of
hole centers of its frame. With no marks this is the set of true vertices of an unmodified guide.

The true vertices within `t` of a mark are the mark and points of its rim pattern
(`mem_insert_rimFinset_of_isTrueVertex`), at most `53` of them (`card_rimFinset_le`); a treatment
or its removal at that mark changes the guide only on the closed square of radius `t` about the
mark (`reading_homogenize_eq_of_lt_dist`), so the true vertices farther than `t` from it are the
same before and after (`isTrueVertex_reading_homogenize_iff`).

## Main definitions

* `Approximation.rimFinset`: the rim pattern as a finite set.
* `Approximation.treatedTrueVertices`.

## Main results

* `Approximation.RepaintingBaseline.IsUnmodifiedGuide.eq_of_notMem_thickening`: away from the
  square, an unmodified guide is the starting guide or constant.
* `Approximation.mem_treatedTrueVertices`.
* `Approximation.mem_insert_rimFinset_of_isTrueVertex`, `Approximation.card_rimFinset_le`.
* `Approximation.isTrueVertex_reading_homogenize_iff`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), §7, `06-geometry.tex`: the root square and the
  placeholder outside it (lines 62–67 and 82–100), the holes at true vertices (lines 109–118), the
  point treatments and the rim patterns (lines 328–351).
-/

open Set Metric Filter Topology

noncomputable section

namespace TNLean.PEPS.Approximation

/-! ### The rim pattern as a finite set -/

/-- The rim pattern about `v` at radius `t` as a finite set: the thirteen points at offset
`j t / 1000`, `|j| ≤ 6`, from the midpoint of each side of the rim of the square of radius `t`
about `v`. -/
def rimFinset (v : ℝ × ℝ) (t : ℝ) : Finset (ℝ × ℝ) :=
  ((({1, -1} : Finset ℝ) ×ˢ (Finset.Icc (-6 : ℤ) 6 ×ˢ (Finset.univ : Finset Bool))).image
    fun x => if x.2.2 then v + (x.1 * t, x.2.1 * t / 1000) else v + (x.2.1 * t / 1000, x.1 * t))

theorem mem_rimFinset {v c : ℝ × ℝ} {t : ℝ} : c ∈ rimFinset v t ↔ c ∈ rimPattern v t := by
  simp only [rimFinset, Finset.mem_image, Finset.mem_product, Finset.mem_insert,
    Finset.mem_singleton, Finset.mem_Icc, Finset.mem_univ, and_true, Prod.exists]
  constructor
  · rintro ⟨σ, j, b, ⟨hσ, hj⟩, rfl⟩
    refine ⟨σ, hσ, j, abs_le.2 hj, ?_⟩
    cases b
    · exact Or.inr (by simp)
    · exact Or.inl (by simp)
  · rintro ⟨σ, hσ, j, hj, rfl | rfl⟩
    · exact ⟨σ, j, true, ⟨hσ, abs_le.1 hj⟩, by simp⟩
    · exact ⟨σ, j, false, ⟨hσ, abs_le.1 hj⟩, by simp⟩

/-- The rim pattern has at most `52` points. -/
theorem card_rimFinset_le (v : ℝ × ℝ) (t : ℝ) : (rimFinset v t).card ≤ 52 := by
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_product, Finset.card_product, Finset.card_univ, Fintype.card_bool,
    Int.card_Icc]
  norm_num

/-! ### Unmodified guides away from the square -/

namespace RepaintingBaseline

variable {ι : Type*} {R : RepaintingBaseline ι}

/-- **Unmodified guides away from the square.** Outside the `n / 2`-neighborhood of the closed
square, an unmodified guide is the starting guide, or it is the uniform label `C_e` of an
auxiliary sheet.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 155–241 and 585–596. -/
theorem IsUnmodifiedGuide.eq_of_notMem_thickening {g : ℝ × ℝ → ι} (h : R.IsUnmodifiedGuide g) :
    (∀ p ∉ thickening (R.n / 2) (closedSquare R.n), g p = R.guide p) ∨
      ∃ e, ∀ p ∉ thickening (R.n / 2) (closedSquare R.n), g p = R.nbrLabel e := by
  rcases h with rfl | rfl | ⟨E, rfl⟩ | ⟨E, e, W, -, rfl⟩ | ⟨e, W, -, rfl⟩
  · exact Or.inl fun _ _ => rfl
  · exact Or.inl R.isLocalGuide_centralGuide.2
  · exact Or.inl (R.isLocalGuide_completedGuide E).2
  · refine Or.inl fun p hp => ?_
    rw [mainGuide, bandUpdate_of_notMem fun h => hp (edgeBand_subset_thickening R.n_pos e h)]
    exact (R.isLocalGuide_completedGuide E).2 p hp
  · exact Or.inr ⟨e, fun p hp => by
      rw [auxGuide, bandUpdate_of_notMem fun h => hp (edgeBand_subset_thickening R.n_pos e h)]⟩

end RepaintingBaseline

/-! ### Finitely many true vertices -/

variable {κ : Type}

/-- Every point within `n / 2` of a grid corner outside the box `[0, M + 1]²` lies outside the
`n / 2`-neighborhood of a block `S` of the root square, moved to the origin. -/
private theorem sub_notMem_thickening {n : ℝ} (hn : 0 < n) {M : ℤ} {S Q : ℤ × ℤ}
    (hS : InRoot M S) (hQ : ¬ (Q.1 ∈ Finset.Icc 0 (M + 1) ∧ Q.2 ∈ Finset.Icc 0 (M + 1)))
    {p : ℝ × ℝ} (hp : dist p (blockCorner n Q) < n / 2) :
    p - blockCorner n S ∉ thickening (n / 2) (closedSquare n) := by
  intro hmem
  obtain ⟨y, hy, hpy⟩ := mem_thickening_iff.1 hmem
  obtain ⟨h1, h2, h3, h4⟩ := mem_closedSquare.1 hy
  have hd : dist (blockCorner n Q - blockCorner n S) y < n := by
    have e : dist (blockCorner n Q - blockCorner n S) (p - blockCorner n S) =
        dist p (blockCorner n Q) := by rw [dist_sub_right, dist_comm]
    linarith [dist_triangle (blockCorner n Q - blockCorner n S) (p - blockCorner n S) y]
  rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, abs_lt, abs_lt] at hd
  simp only [blockCorner, Prod.fst_sub, Prod.snd_sub] at hd
  obtain ⟨⟨a1, a2⟩, a3, a4⟩ := hd
  have k1 : ((Q.1 - S.1 : ℤ) : ℝ) < 2 := by
    push_cast; nlinarith
  have k2 : (-1 : ℝ) < ((Q.1 - S.1 : ℤ) : ℝ) := by
    push_cast; nlinarith
  have k3 : ((Q.2 - S.2 : ℤ) : ℝ) < 2 := by
    push_cast; nlinarith
  have k4 : (-1 : ℝ) < ((Q.2 - S.2 : ℤ) : ℝ) := by
    push_cast; nlinarith
  have k1' : Q.1 - S.1 < 2 := by exact_mod_cast k1
  have k2' : -1 < Q.1 - S.1 := by exact_mod_cast k2
  have k3' : Q.2 - S.2 < 2 := by exact_mod_cast k3
  have k4' : -1 < Q.2 - S.2 := by exact_mod_cast k4
  obtain ⟨s1, s2, s3, s4⟩ := hS
  simp only [Finset.mem_Icc] at hQ
  omega

/-- Near a grid corner outside the box `[0, M + 1]²`, every block lies outside the root square. -/
private theorem not_inRoot_blockIndex {n : ℝ} (hn : 0 < n) {M : ℤ} {Q : ℤ × ℤ}
    (hQ : ¬ (Q.1 ∈ Finset.Icc 0 (M + 1) ∧ Q.2 ∈ Finset.Icc 0 (M + 1))) {p : ℝ × ℝ}
    (hp : dist p (blockCorner n Q) < n) : ¬ InRoot M (blockIndex n p) := by
  obtain ⟨a, b⟩ := abs_blockIndex_sub_le hn (blockCorner_mem_closedBlock_sub_one hn Q) hp
  rw [abs_le] at a b
  simp only [Finset.mem_Icc] at hQ
  simp only [InRoot]
  omega

/-- The true vertices of a labelling among the grid corners `blockCorner n Q` with
`0 ≤ Q.1, Q.2 ≤ M + 1` and the rim patterns of radius `t` about the marks. -/
def treatedTrueVertices (n t : ℝ) (M : ℤ) (marks : Finset (ℤ × ℤ)) (f : ℝ × ℝ → κ) :
    Finset (ℝ × ℝ) :=
  open Classical in
  (((Finset.Icc 0 (M + 1) ×ˢ Finset.Icc 0 (M + 1)).image (blockCorner n)) ∪
    marks.biUnion fun Q => rimFinset (blockCorner n Q) t).filter (IsTrueVertex f)

/-- **The true vertices of a temporary guide.** Let `2 t < n`, let the labels `lab` of the level
be the placeholder `ph` outside the root square of `M × M` blocks, and let `S` be a block of the
root square. Let `f` be the reading along `v` of an unmodified guide of the repainting of `S`,
moved to `S` and homogenized to any label on the open squares of radius `t` about the grid
corners of `marks`. Then the true vertices of `f` are exactly the points of
`treatedTrueVertices n t M marks f`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 62–67, 82–100, 109–118 and 328–351. -/
theorem mem_treatedTrueVertices {n t : ℝ} (hn : 0 < n) (htn : 2 * t < n) {M : ℤ}
    {lab : ℤ × ℤ → κ} {ph : κ} (hout : ∀ Q, ¬InRoot M Q → lab Q = ph) {S : ℤ × ℤ}
    (hS : InRoot M S) {B : κ} {g : ℝ × ℝ → κ}
    (hg : (blockBaseline hn lab S B).IsUnmodifiedGuide g) (marks : Finset (ℤ × ℤ)) (P : κ)
    {v : ℝ × ℝ} {f : ℝ × ℝ → κ}
    (hf : IsDisplacedReading f (homogenize (⋃ Q ∈ marks, ball (blockCorner n Q) t) P
      (shiftGuide (blockCorner n S) g)) v) {c : ℝ × ℝ} :
    c ∈ treatedTrueVertices n t M marks f ↔ IsTrueVertex f c := by
  classical
  simp only [treatedTrueVertices, Finset.mem_filter, and_iff_right_iff_imp]
  intro hc
  have hc' := hf.isTrueVertex hc
  rcases isTrueVertex_homogenize_cases hn htn hg marks P hc' with ⟨Q, rfl⟩ | ⟨Q, hQ, hcQ⟩
  · refine Finset.mem_union_left _ (Finset.mem_image.2 ⟨Q, ?_, rfl⟩)
    rw [Finset.mem_product]
    by_contra hQ
    have hconst : ∃ C : κ, ∀ p ∈ ball (blockCorner n Q) (n / 2),
        shiftGuide (blockCorner n S) g p = C := by
      have hfar := fun p (hp : p ∈ ball (blockCorner n Q) (n / 2)) =>
        sub_notMem_thickening hn hS hQ (mem_ball.1 hp)
      rcases hg.eq_of_notMem_thickening with h | ⟨e, h⟩
      · refine ⟨ph, fun p hp => ?_⟩
        change g (p - blockCorner n S) = ph
        rw [h _ (hfar p hp)]
        change lab (blockIndex n (p - blockCorner n S + blockCorner n S)) = ph
        rw [sub_add_cancel]
        exact hout _ (not_inRoot_blockIndex hn hQ (by linarith [mem_ball.1 hp]))
      · exact ⟨_, fun p hp => h _ (hfar p hp)⟩
    obtain ⟨C, hC⟩ := hconst
    refine HasTwoLabelsNear.not_isTrueVertex ?_ hc'
    refine ⟨P, C, ?_⟩
    filter_upwards [ball_mem_nhds (blockCorner n Q) (half_pos hn)] with p hp
    by_cases hpU : p ∈ ⋃ Q ∈ marks, ball (blockCorner n Q) t
    · rw [homogenize_of_mem hpU]
      exact mem_insert _ _
    · rw [homogenize_of_notMem hpU, hC p hp]
      exact mem_insert_of_mem _ rfl
  · exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨Q, hQ, mem_rimFinset.2 hcQ⟩)

/-- **True vertices near a mark.** Let `0 ≤ t` and `2 t < n`. A true vertex of a temporary guide
of the repainting of a block within `t` of the grid corner `Q₀` is that corner or a point of its
rim pattern.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 341–351 and 486–490. -/
theorem mem_insert_rimFinset_of_isTrueVertex {n t : ℝ} (hn : 0 < n) (ht : 0 ≤ t)
    (htn : 2 * t < n) {lab : ℤ × ℤ → κ} {S : ℤ × ℤ} {B : κ} {g : ℝ × ℝ → κ}
    (hg : (blockBaseline hn lab S B).IsUnmodifiedGuide g) (marks : Finset (ℤ × ℤ)) (P : κ)
    {v : ℝ × ℝ} {f : ℝ × ℝ → κ}
    (hf : IsDisplacedReading f (homogenize (⋃ Q ∈ marks, ball (blockCorner n Q) t) P
      (shiftGuide (blockCorner n S) g)) v) (Q₀ : ℤ × ℤ) {a : ℝ × ℝ} (ha : IsTrueVertex f a)
    (hd : dist a (blockCorner n Q₀) ≤ t) :
    a ∈ insert (blockCorner n Q₀) (rimFinset (blockCorner n Q₀) t) := by
  rcases isTrueVertex_homogenize_cases hn htn hg marks P (hf.isTrueVertex ha) with
    ⟨Q, rfl⟩ | ⟨Q, -, hcQ⟩
  · by_cases hQ : Q = Q₀
    · subst hQ
      exact Finset.mem_insert_self _ _
    · have := le_dist_blockCorner_of_ne hn hQ
      linarith
  · by_cases hQ : Q = Q₀
    · subst hQ
      exact Finset.mem_insert_of_mem (mem_rimFinset.2 hcQ)
    · have h₁ := dist_of_mem_rimPattern ht hcQ
      have := le_dist_blockCorner_of_ne hn hQ
      have := dist_triangle (blockCorner n Q) a (blockCorner n Q₀)
      rw [dist_comm] at h₁
      linarith

/-! ### True vertices away from a treated mark -/

/-- **A treatment changes the guide only near its mark.** If two sets of marks differ at most at
`Q₀`, the readings along `v` of a labelling homogenized to `P` on the open squares of radius `t`
about the two sets of marks agree at every point at distance more than `t` from `Q₀`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 328–339 and 481–505. -/
theorem reading_homogenize_eq_of_lt_dist {n t : ℝ} {M₁ M₂ : Finset (ℤ × ℤ)} {Q₀ : ℤ × ℤ}
    (hM : ∀ Q, Q ≠ Q₀ → (Q ∈ M₁ ↔ Q ∈ M₂)) (P : κ) (h : ℝ × ℝ → κ) {v : ℝ × ℝ}
    {g₁ g₂ : ℝ × ℝ → κ}
    (hg₁ : IsDisplacedReading g₁ (homogenize (⋃ Q ∈ M₁, ball (blockCorner n Q) t) P h) v)
    (hg₂ : IsDisplacedReading g₂ (homogenize (⋃ Q ∈ M₂, ball (blockCorner n Q) t) P h) v)
    {p : ℝ × ℝ} (hp : t < dist p (blockCorner n Q₀)) : g₁ p = g₂ p := by
  by_contra hne
  have hcl := hg₁.ne_subset_closure hg₂ hne
  have hsub : {x | homogenize (⋃ Q ∈ M₁, ball (blockCorner n Q) t) P h x ≠
      homogenize (⋃ Q ∈ M₂, ball (blockCorner n Q) t) P h x} ⊆
      closedBall (blockCorner n Q₀) t := by
    intro x hx
    by_contra hxc
    have hxb : x ∉ ball (blockCorner n Q₀) t := fun h => hxc (ball_subset_closedBall h)
    refine hx ?_
    have hiff : x ∈ (⋃ Q ∈ M₁, ball (blockCorner n Q) t) ↔
        x ∈ (⋃ Q ∈ M₂, ball (blockCorner n Q) t) := by
      simp only [mem_iUnion, exists_prop]
      constructor
      · rintro ⟨Q, hQ, h⟩
        exact ⟨Q, (hM Q fun e => hxb (e ▸ h)).1 hQ, h⟩
      · rintro ⟨Q, hQ, h⟩
        exact ⟨Q, (hM Q fun e => hxb (e ▸ h)).2 hQ, h⟩
    by_cases hx₁ : x ∈ (⋃ Q ∈ M₁, ball (blockCorner n Q) t)
    · rw [homogenize_of_mem hx₁, homogenize_of_mem (hiff.1 hx₁)]
    · rw [homogenize_of_notMem hx₁, homogenize_of_notMem fun h => hx₁ (hiff.2 h)]
  exact (not_le.2 hp) (mem_closedBall.1 (closure_minimal hsub isClosed_closedBall hcl))

/-- **True vertices away from a treated mark.** In the setting of
`reading_homogenize_eq_of_lt_dist`, the two readings have the same true vertices at distance
more than `t` from `Q₀`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 328–339 and 481–505. -/
theorem isTrueVertex_reading_homogenize_iff {n t : ℝ} {M₁ M₂ : Finset (ℤ × ℤ)} {Q₀ : ℤ × ℤ}
    (hM : ∀ Q, Q ≠ Q₀ → (Q ∈ M₁ ↔ Q ∈ M₂)) (P : κ) (h : ℝ × ℝ → κ) {v : ℝ × ℝ}
    {g₁ g₂ : ℝ × ℝ → κ}
    (hg₁ : IsDisplacedReading g₁ (homogenize (⋃ Q ∈ M₁, ball (blockCorner n Q) t) P h) v)
    (hg₂ : IsDisplacedReading g₂ (homogenize (⋃ Q ∈ M₂, ball (blockCorner n Q) t) P h) v)
    {c : ℝ × ℝ} (hc : t < dist c (blockCorner n Q₀)) : IsTrueVertex g₁ c ↔ IsTrueVertex g₂ c := by
  have heq : g₁ =ᶠ[𝓝 c] g₂ := by
    filter_upwards [(isOpen_lt continuous_const
      (continuous_id.dist continuous_const)).mem_nhds hc] with p hp
    exact reading_homogenize_eq_of_lt_dist hM P h hg₁ hg₂ hp
  rw [isTrueVertex_iff_incidentLabels, isTrueVertex_iff_incidentLabels, incidentLabels_congr heq]

end TNLean.PEPS.Approximation
