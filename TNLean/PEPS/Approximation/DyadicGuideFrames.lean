/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.AdaptivePatchSupply
import TNLean.PEPS.Approximation.DyadicSmallPatchCovers

/-!
# Encoded frames of guides

A guide of the dyadic protocol is a labelling of the plane; its labels name the parties owning
the raw registers at the sampled sites. The encoded frame of a guide has

* the raw owner `own (g (pos x))` at every site `x`, for the reading `g` of the guide;
* one hole at every point of a given finite set `V` of centers, in practice the true vertices,
  with the square patch chosen at that center;
* the tag of the hole at `c` held by the party of a canonical tag holder: the incident label at
  `c`, other than the placeholder, of least rank in a fixed ranking of the labels.

The tag holder depends on the guide only through its incident labels at the center, so guides
with the same incident labels, such as the two sides of an exchange, give the same tag holder.
With the patches supplied by Proposition 4.1, a given center and radius receive the same patch on
every sheet.

## Main definitions

* `Approximation.tagHolder`: the canonical tag holder of a point of a guide.
* `Approximation.guideFrame`: the encoded frame of a guide with holes at a finite set of centers.

## Main results

* `Approximation.isTagHolder_tagHolder`, `Approximation.tagHolder_ne`: at a true vertex the
  canonical tag holder is an incident label other than the placeholder.
* `Approximation.tagHolder_congr`: guides with the same incident labels at a point have the same
  canonical tag holder there.
* `Approximation.disjoint_outer_of_disjoint_closedBall`: patches whose closed outer squares are
  disjoint in the plane have disjoint outer samples.
* `Approximation.disjoint_outerHoles_guideFrame`: a set separated from every outer hole square
  misses the outer holes of the guide frame.
* `Approximation.one_sub_mul_le_norm_refVec_guideFrame`: `1 - |V| ε ≤ ‖Ω_F‖ ≤ 1`.
* `Approximation.outer_eq_empty_of_isCellCenter`, `Approximation.guideFrame_unitLevel`: at the
  last level `n = 1`, holes at block corners with outer radius below `1/2` have empty physical
  outer samples, and the reference vector of the frame has the norm of `Ω`.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), §7, `06-geometry.tex`: sites at cell centers and
  guides read at sites (lines 62–80), holes at true vertices with the same adaptive choice on
  every sheet (lines 109–118), the canonical tag holder (lines 119–125), and the trivial holes
  at `n = 1` (lines 669–672). Definition 6.1 `def:frame` and `eq:frame-norm`,
  `05-frames.tex`, lines 71–94.
-/

open Set Metric Matrix

noncomputable section

namespace TNLean.PEPS.Approximation

open EncodedFrame

/-! ### The canonical tag holder -/

section TagHolder

variable {X κ : Type*} [TopologicalSpace X] (rank : κ → ℕ) (g g' : X → κ) (ph : κ) (c : X)

/-- **Canonical tag holder.** At a point `c` of a guide `g`, the incident label other than the
placeholder `ph` of least rank; the placeholder when there is none. For a ranking injective on
the genuine labels the choice is unique.

Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:119–125`. -/
def tagHolder : κ :=
  open Classical in
  if h : {l | IsTagHolder g ph c l}.Nonempty then Function.argminOn rank _ h else ph

variable {rank g g' ph c}

theorem isTagHolder_tagHolder_of_nonempty (h : {l | IsTagHolder g ph c l}.Nonempty) :
    IsTagHolder g ph c (tagHolder rank g ph c) := by
  rw [tagHolder, dite_eq_left_of_eq_true (eq_true h)]
  exact Function.argminOn_mem rank _ h

/-- At a true vertex, the canonical tag holder is an incident label other than the placeholder.

Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:119–123`. -/
theorem isTagHolder_tagHolder (h : IsTrueVertex g c) :
    IsTagHolder g ph c (tagHolder rank g ph c) := by
  obtain ⟨l, -, -, hl, -⟩ := h.exists_isTagHolder ph
  exact isTagHolder_tagHolder_of_nonempty ⟨l, hl⟩

/-- At a true vertex, the placeholder never holds the tag. -/
theorem tagHolder_ne (h : IsTrueVertex g c) : tagHolder rank g ph c ≠ ph :=
  (isTagHolder_tagHolder h).2

/-- The canonical tag holder has least rank among the possible tag holders. -/
theorem rank_tagHolder_le {l : κ} (hl : IsTagHolder g ph c l) :
    rank (tagHolder rank g ph c) ≤ rank l := by
  rw [tagHolder, dite_eq_left_of_eq_true (eq_true ⟨l, hl⟩)]
  exact Function.argminOn_le rank _ hl

/-- Guides with the same incident labels at `c` have the same canonical tag holder there. The tag
of a hole thus accompanies it through every operation that keeps the incident labels.

Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:123–125, 381–382, 417–419`. -/
theorem tagHolder_congr (h : incidentLabels g c = incidentLabels g' c) :
    tagHolder rank g ph c = tagHolder rank g' ph c := by
  have hs : {l | IsTagHolder g ph c l} = {l | IsTagHolder g' ph c l} :=
    Set.ext fun _ => isTagHolder_congr h
  unfold tagHolder
  generalize {l | IsTagHolder g ph c l} = s at hs ⊢
  subst hs
  rfl

end TagHolder

/-! ### Disjoint outer samples -/

section Frames

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ} {pos : ι → ℝ × ℝ}

/-- Two patches whose closed outer squares are disjoint in the plane have disjoint outer
samples. -/
theorem disjoint_outer_of_disjoint_closedBall {p p' : SquarePatch pos q}
    (h : Disjoint (closedBall p.center (2 * p.scale)) (closedBall p'.center (2 * p'.scale))) :
    Disjoint p.outer p'.outer := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [SquarePatch.outer, squareSample, Finset.mem_filter, Finset.mem_univ,
    true_and] at hx hx'
  exact Set.disjoint_left.mp h (mem_closedBall.mpr hx) (mem_closedBall.mpr hx')

/-- The supplied patches at the points of a set whose closed squares of radius `2r` are pairwise
disjoint have pairwise disjoint outer samples.

Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:113–114, 341–355`. -/
theorem pairwise_disjoint_outer_patchAt {Ω : EuclideanSpace ℂ (ι → Fin q)} {B₀ C c p : ℝ}
    {L : ℕ} (S : AdaptivePatchSupply pos Ω B₀ C c p L) {r : ℝ}
    (hr : 0 < r ∧ r ≤ B₀ * Real.log L) {V : Set (ℝ × ℝ)}
    (hV : V.Pairwise fun z z' => Disjoint (closedBall z (2 * r)) (closedBall z' (2 * r))) :
    V.Pairwise fun z z' => Disjoint (patchAt S z hr).outer (patchAt S z' hr).outer :=
  fun z hz z' hz' hne => disjoint_outer_of_disjoint_closedBall (by simpa using hV hz hz' hne)

/-! ### The encoded frame of a guide -/

variable {κ Party : Type*}

/-- **Encoded frame of a guide.** The raw owner of a site is the party of the label read at its
position; there is one hole at every center of `V`, in the fixed order `V.toList`, with the patch
`patch z` and its tag held by the party of the canonical tag holder of `z`.

Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:69–80, 109–125`, and Definition 6.1
`def:frame`, `05-frames.tex:71–82`. -/
def guideFrame (pos : ι → ℝ × ℝ) (q : ℕ) (g : ℝ × ℝ → κ) (own : κ → Party) (ph : κ)
    (rank : κ → ℕ) (V : Finset (ℝ × ℝ)) (patch : ℝ × ℝ → SquarePatch pos q)
    (hV : (V : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (patch z).outer (patch z').outer) :
    Frame pos q Party where
  owner x := own (g (pos x))
  holes := V.toList.map fun z => ⟨patch z, own (tagHolder rank g ph z)⟩
  disjoint := by
    rw [List.map_map]
    exact List.Pairwise.map _ (fun z z' h => h)
      (V.nodup_toList.pairwise_of_forall_ne fun z hz z' hz' hne =>
        hV (Finset.mem_toList.mp hz) (Finset.mem_toList.mp hz') hne)

variable {g : ℝ × ℝ → κ} {own : κ → Party} {ph : κ} {rank : κ → ℕ} {V : Finset (ℝ × ℝ)}
  {patch : ℝ × ℝ → SquarePatch pos q}
  {hV : (V : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (patch z).outer (patch z').outer}

@[simp] theorem guideFrame_owner (x : ι) :
    (guideFrame pos q g own ph rank V patch hV).owner x = own (g (pos x)) := rfl

theorem mem_holes_guideFrame {h : Hole pos q Party} :
    h ∈ (guideFrame pos q g own ph rank V patch hV).holes ↔
      ∃ z ∈ V, h = ⟨patch z, own (tagHolder rank g ph z)⟩ := by
  simp only [guideFrame, List.mem_map, Finset.mem_toList]
  exact ⟨fun ⟨z, hz, he⟩ => ⟨z, hz, he.symm⟩, fun ⟨z, hz, he⟩ => ⟨z, hz, he.symm⟩⟩

/-- A site set farther than twice each patch's scale from that patch's center is disjoint from
the outer holes of the guide frame. The outer patch samples are assumed pairwise disjoint on
the finite center set; the guide and owners are arbitrary. No true-vertex, supplied-patch or
positive local-dimension assumption is required. -/
lemma disjoint_outerHoles_guideFrame {T : Set ι}
    (hfar : ∀ z ∈ V, ∀ x ∈ T, 2 * (patch z).scale < dist (patch z).center (pos x)) :
    Disjoint T (guideFrame pos q g own ph rank V patch hV).outerHoles := by
  apply Disjoint.symm
  apply disjoint_footprint_of_forall
  intro p hp
  obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hp
  obtain ⟨z, hz, rfl⟩ := mem_holes_guideFrame.1 hh
  refine Set.disjoint_left.2 fun x hxp hx => ?_
  have hd : dist (pos x) (patch z).center ≤ 2 * (patch z).scale := by
    simpa [SquarePatch.outer, squareSample] using hxp
  have := hfar z hz x hx
  rw [dist_comm] at this
  exact (not_lt_of_ge hd) this

@[simp] theorem length_holes_guideFrame :
    (guideFrame pos q g own ph rank V patch hV).holes.length = V.card := by
  simp [guideFrame]

/-- **`eq:frame-norm` for the frame of a guide.** If `‖Ω‖ = 1` and the projector of every patch
at a center of `V` has error at most `ε` on `Ω`, then `1 - |V| ε ≤ ‖Ω_F‖ ≤ 1`.

Polynomial-PEPS manuscript (Sept 24 2026), `05-frames.tex:84–94`. -/
theorem one_sub_mul_le_norm_refVec_guideFrame [NeZero q] {Ω : EuclideanSpace ℂ (ι → Fin q)}
    (hΩ : ‖Ω‖ = 1) {ε : ℝ} (hε : ∀ z ∈ V, ‖act (patch z).proj Ω - Ω‖ ≤ ε) :
    1 - V.card * ε ≤ ‖(guideFrame pos q g own ph rank V patch hV).refVec Ω‖ ∧
      ‖(guideFrame pos q g own ph rank V patch hV).refVec Ω‖ ≤ 1 := by
  have h := Frame.one_sub_mul_le_norm_refVec (guideFrame pos q g own ph rank V patch hV) hΩ
    (ε := ε) fun h hh => by
    obtain ⟨z, hz, rfl⟩ := mem_holes_guideFrame.mp hh
    exact hε z hz
  rwa [length_holes_guideFrame] at h

/-- With patches supplied by Proposition 4.1 at accuracy `L^{-p}`, the reference vector of the
frame of a guide satisfies `1 - |V| L^{-p} ≤ ‖Ω_F‖ ≤ 1`.

Polynomial-PEPS manuscript (Sept 24 2026), `05-frames.tex:84–94`, `06-geometry.tex:113–118`. -/
theorem one_sub_mul_le_norm_refVec_guideFrame_patchAt [NeZero q]
    {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1) {B₀ C c p : ℝ} {L : ℕ}
    (S : AdaptivePatchSupply pos Ω B₀ C c p L) {r : ℝ} (hr : 0 < r ∧ r ≤ B₀ * Real.log L)
    {hV : (V : Set (ℝ × ℝ)).Pairwise fun z z' =>
      Disjoint (patchAt S z hr).outer (patchAt S z' hr).outer} :
    1 - V.card * (L : ℝ) ^ (-p) ≤
        ‖(guideFrame pos q g own ph rank V (fun z => patchAt S z hr) hV).refVec Ω‖ ∧
      ‖(guideFrame pos q g own ph rank V (fun z => patchAt S z hr) hV).refVec Ω‖ ≤ 1 :=
  one_sub_mul_le_norm_refVec_guideFrame hΩ fun _ _ => norm_act_proj_patchAt_sub_le S _ hr

/-! ### Trivial holes at the last level -/

/-- **Empty outer samples at `n = 1`.** If every site lies at a cell center, a patch centered at
a corner of a unit block with outer radius `2h < 1/2` has empty physical outer sample.

Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:669–672`. -/
theorem outer_eq_empty_of_isCellCenter (hpos : ∀ x, IsCellCenter (pos x))
    {P : SquarePatch pos q} {Q : ℤ × ℤ} (hc : P.center = blockCorner 1 Q)
    (hs : 2 * P.scale < 1 / 2) : P.outer = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro x hx
  simp only [SquarePatch.outer, squareSample, Finset.mem_filter, Finset.mem_univ, true_and,
    hc] at hx
  exact (hpos x).notMem_closedBall_blockCorner Q hs (mem_closedBall.mpr hx)

/-- **Trivial holes at `n = 1`.** If every site lies at a cell center and every center of `V` is
a corner of a unit block carrying a patch of outer radius below `1/2`, then every hole of the
frame of a guide has empty physical outer sample, its encoding is an isometry, and the reference
vector has the norm of `Ω`.

Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:669–672`. -/
theorem guideFrame_unitLevel [NeZero q] (hpos : ∀ x, IsCellCenter (pos x))
    (hc : ∀ z ∈ V, (patch z).center = z) (hcorner : ∀ z ∈ V, ∃ Q, z = blockCorner 1 Q)
    (hs : ∀ z ∈ V, 2 * (patch z).scale < 1 / 2) :
    (∀ h ∈ (guideFrame pos q g own ph rank V patch hV).holes, h.patch.outer = ∅) ∧
      (guideFrame pos q g own ph rank V patch hV).encoderᴴ *
          (guideFrame pos q g own ph rank V patch hV).encoder = 1 ∧
      ∀ Ω : EuclideanSpace ℂ (ι → Fin q),
        ‖(guideFrame pos q g own ph rank V patch hV).refVec Ω‖ = ‖Ω‖ := by
  set F := guideFrame pos q g own ph rank V patch hV
  have hempty : ∀ h ∈ F.holes, h.patch.outer = ∅ := by
    intro h hh
    obtain ⟨z, hz, rfl⟩ := mem_holes_guideFrame.mp hh
    obtain ⟨Q, hQ⟩ := hcorner z hz
    exact outer_eq_empty_of_isCellCenter hpos ((hc z hz).trans hQ) (hs z hz)
  have hprod : projProd F.patches = 1 := by
    rw [projProd]
    refine List.prod_eq_one fun A hA => ?_
    obtain ⟨P, hP, rfl⟩ := List.mem_map.mp hA
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hP
    exact h.patch.proj_of_outer_eq_empty (hempty h hh)
  refine ⟨hempty, by rw [F.encoder_conjTranspose_mul_self, hprod], fun Ω => ?_⟩
  rw [F.norm_refVec_eq, hprod, act_one]

end Frames

end TNLean.PEPS.Approximation
