/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicTreatedFrameDescriptions
import TNLean.PEPS.Approximation.DyadicTreatedFrames
import TNLean.PEPS.Approximation.DyadicProtocolStateTransitions

/-!
# The frames of a bulk birth or death

An elementary birth or death of a large-scale repainting in the protocol of Proposition 7.1 of
the polynomial-PEPS manuscript changes the owner of the raw registers of its target and keeps
every hole, its encoding and its tag (`06-geometry.tex`, lines 375–387): the closure of the
changed region stays at distance `a₀ t` from every true vertex. This file proves this for the
sampled guides of the protocol:

* `readings_isTrueVertex_iff_of_far` : if two labellings have the same true vertices, each at a
  positive distance from the closure of the set where they differ, then their readings have the
  same true vertices with the same incident labels;
* `guideFrame_eq_changeOwner` : the encoded frame of the second reading is the frame of the first
  with the owners of the sites where they differ changed.

## References

* Polynomial-PEPS manuscript (September 24, 2026), §7, `06-geometry.tex`: guides and their
  sampling (lines 69–80), the holes and tags (lines 109–125), and the bulk recoloring without
  changed true vertices (lines 375–387).
-/

noncomputable section

open Set Metric Filter Topology

namespace TNLean.PEPS.Approximation

open EncodedFrame PairEffect

/-- The sites of the square sit at the lattice positions translated by `(-1/2, -1/2)`. -/
theorem cellCenterPos_eq_sitePosition_add {L : ℕ} (v : SquareLatticeVertex L L) :
    cellCenterPos L v = sitePosition L v + (-(1 / 2 : ℝ), -(1 / 2 : ℝ)) :=
  (congrFun (latticePos_add_eq_cellCenterPos L) v).symm

section Readings

variable {κ : Type*} {Gb Ga fb fa : ℝ × ℝ → κ} {v : ℝ × ℝ} {δ : ℝ}

/-- **Readings of a far change.** Let two labellings `Gb`, `Ga` have the same true vertices, each
at distance at least `δ > 0` from the closure of the set where they differ. Then their readings
along `v` agree on the open square of radius `δ` about every true vertex of the first reading,
have the same true vertices, and have the same incident labels at them.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 76–80 and 375–387. -/
theorem readings_isTrueVertex_iff_of_far (hb : IsDisplacedReading fb Gb v)
    (ha : IsDisplacedReading fa Ga v) (hiff : ∀ c, IsTrueVertex Gb c ↔ IsTrueVertex Ga c)
    (hfar : ∀ c, IsTrueVertex Gb c → ∀ y ∈ closure {p | Gb p ≠ Ga p}, δ ≤ dist c y)
    (hδ : 0 < δ) :
    (∀ c, IsTrueVertex fb c ↔ IsTrueVertex fa c) ∧
      ∀ c, IsTrueVertex fb c → incidentLabels fb c = incidentLabels fa c := by
  have heq : ∀ c, IsTrueVertex Gb c → fb =ᶠ[𝓝 c] fa := fun c hc => by
    filter_upwards [ball_mem_nhds c hδ] with p hp
    by_contra hne
    have := hfar c hc p (hb.ne_subset_closure ha hne)
    rw [mem_ball, dist_comm] at hp
    linarith
  have hb' : ∀ c, IsTrueVertex fb c → incidentLabels fb c = incidentLabels fa c :=
    fun c hc => incidentLabels_congr (heq c (hb.isTrueVertex hc))
  refine ⟨fun c => ⟨fun hc => ?_, fun hc => ?_⟩, hb'⟩
  · rw [isTrueVertex_iff_incidentLabels, ← hb' c hc, ← isTrueVertex_iff_incidentLabels]
    exact hc
  · have hG := (hiff c).2 (ha.isTrueVertex hc)
    rw [isTrueVertex_iff_incidentLabels, incidentLabels_congr (heq c hG),
      ← isTrueVertex_iff_incidentLabels]
    exact hc

end Readings

/-- **The frame after a change of owners.** If the owners read from `g'` at the sites agree with
those read from `g` off `T` and are `Q` on `T`, and the two guides have the same tag holders at the
centers of `V`, then the encoded frame of `g'` is the encoded frame of `g` with the owners of `T`
changed to `Q`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 375–387. -/
theorem guideFrame_eq_changeOwner {ι κ Party : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}
    {pos : ι → ℝ × ℝ} {g g' : ℝ × ℝ → κ} {own : κ → Party} {ph : κ} {rank : κ → ℕ}
    {V : Finset (ℝ × ℝ)} {patch : ℝ × ℝ → SquarePatch pos q}
    {hV : (V : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (patch z).outer (patch z').outer}
    {hV' : (V : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (patch z).outer (patch z').outer}
    {T : Finset ι} {Q : Party}
    (howner : ∀ x, own (g' (pos x)) = if x ∈ T then Q else own (g (pos x)))
    (htag : ∀ z ∈ V, tagHolder rank g' ph z = tagHolder rank g ph z) :
    guideFrame pos q g' own ph rank V patch hV' =
      (guideFrame pos q g own ph rank V patch hV).changeOwner T Q := by
  refine frame_eq_of_owner_holes (funext fun x => ?_) ?_
  · simp only [guideFrame_owner, howner]
  · simp only [guideFrame]
    exact List.map_congr_left fun z hz => by rw [htag z (Finset.mem_toList.1 hz)]

end TNLean.PEPS.Approximation
