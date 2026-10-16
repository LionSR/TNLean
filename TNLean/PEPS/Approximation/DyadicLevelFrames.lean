/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicLevelTrueVertices
import TNLean.PEPS.Approximation.DyadicOwnerSwitch
import TNLean.PEPS.Approximation.DyadicProtocolInitialStep
import TNLean.PEPS.Approximation.DyadicProtocolStack
import TNLean.PEPS.Approximation.DyadicSuppliedPatchSteps

/-!
# The main frame between repaintings

Between two repaintings of the protocol of Proposition 7.1 of the polynomial-PEPS manuscript the
main guide is a block guide of a level: every `2 ^ j`-block of the root square carries its old or
its new label and the exterior of the root square carries the placeholder (`06-geometry.tex`,
lines 82–100). Its labels are read at the sites after one fixed generic displacement (lines
69–80), its holes sit at its true vertices, with the patch supplied by Proposition 4.1 at the
center and the radius of the hole, and its tags are held by the canonical tag holders
(lines 109–125). This file defines this frame and proves the facts about it that do not depend
on the change being made.

* `levelGuide`, `levelVertices` : the sampled block guide of a stage of a level and the finite set
  of its true vertices.
* `levelFrame` : the encoded frame of that guide, with hole radii given by a function of the
  center.
* `levelFrame_eq` : when the outer squares of the holes are disjoint, the frame is the encoded
  frame of the sampled guide.
* `levelFrame_congr` : the frame depends on the hole radii only at the true vertices.
* `pairwise_disjoint_levelHoles` : outer squares of patches of radius at most `r` at distinct
  grid corners of the level are disjoint when `4 r < 2 ^ j`.
* `isTrueVertex_levelGuide_insert_iff` : repainting one block of a level changes the true vertices
  of the sampled guide only at the four corners of that block.

## References

* Polynomial-PEPS manuscript (September 24, 2026), §7, `06-geometry.tex`: the hierarchy and
  guides (lines 60–80), the repainting by levels and the placeholder (lines 82–100), the holes and
  their tags (lines 102–125), the direct repainting (lines 507–527).
-/

noncomputable section

open Set Metric Filter Topology

namespace TNLean.PEPS.Approximation

open EncodedFrame

variable {k : ℕ}

/-! ### The sampled guide of a level -/

/-- The block guide of the pass to level `2 ^ j`, with the blocks of `done` repainted, read at
every point after the displacement `(1, 1)`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 69–100. -/
abbrev levelGuide (k j : ℕ) (done : Set (ℤ × ℤ)) : ℝ × ℝ → GuideLabel :=
  sampleGuide (blockGuide ((2 : ℝ) ^ j) (protocolLevelLabels k j done))

/-- The sampled guide reads the block labels after the same generic displacement `(1, 1)`. -/
theorem isDisplacedReading_levelGuide (j : ℕ) (done : Set (ℤ × ℤ)) :
    IsDisplacedReading (levelGuide k j done)
      (blockGuide ((2 : ℝ) ^ j) (protocolLevelLabels k j done)) ((1 : ℝ), (1 : ℝ)) :=
  (isRayConstant_blockGuide _ _).isDisplacedReading_sampleGuide

/-- The true vertices of the sampled guide of a stage of a level: grid corners of the level
within the closed root square.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 109–118. -/
abbrev levelVertices (k j : ℕ) (done : Set (ℤ × ℤ)) : Finset (ℝ × ℝ) :=
  levelTrueVertices ((2 : ℝ) ^ j) ((2 : ℤ) ^ (k - j)) (levelGuide k j done)

/-- The finite set of level vertices consists exactly of the true vertices of the sampled guide. -/
theorem mem_levelVertices {j : ℕ} {done : Set (ℤ × ℤ)} {c : ℝ × ℝ} :
    c ∈ levelVertices k j done ↔ IsTrueVertex (levelGuide k j done) c := by
  classical
  refine mem_levelTrueVertices (ph := guidePlaceholder) (by positivity) (fun Q hQ => ?_)
    (isDisplacedReading_levelGuide j done)
  simp only [protocolLevelLabels, levelLabels, hQ, ite_false]

/-! ### The frame -/

variable {L q : ℕ} {Ω : StateSpace L q} {B₀ C c : ℝ}

open Classical in
/-- **The main frame of a stage of a level.** The encoded frame of the sampled block guide of the
pass to level `2 ^ j` with the blocks of `done` repainted, read through the party map of the
repainting `R₀`, with a hole at every true vertex `z` carrying the patch supplied at `z` with
radius `ρ z`, and the canonical tag holders. When the outer squares of these holes are not
disjoint the frame is not defined by the source, and a raw frame stands in for it.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 69–125. -/
def levelFrame (P : AdaptivePatchSupply (cellCenterPos L) Ω B₀ C c 60 L)
    (rank : GuideLabel → ℕ) (R₀ : RepaintedSquare k) (j : ℕ) (done : Set (ℤ × ℤ))
    (ρ : ℝ × ℝ → ℝ) (hρ : ∀ z, 0 < ρ z ∧ ρ z ≤ B₀ * Real.log L) :
    Frame (cellCenterPos L) q (ProtocolParty k) :=
  if h : ((levelVertices k j done : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)).Pairwise fun z z' =>
      Disjoint (suppliedPatch P ρ hρ z).outer (suppliedPatch P ρ hρ z').outer then
    guideFrame (cellCenterPos L) q (levelGuide k j done) (labelParty R₀) guidePlaceholder rank
      (levelVertices k j done) (suppliedPatch P ρ hρ) h
  else Frame.raw fun _ => .inl (rootSquare k)

variable (P : AdaptivePatchSupply (cellCenterPos L) Ω B₀ C c 60 L) (rank : GuideLabel → ℕ)
  (R₀ : RepaintedSquare k)

/-- With pairwise disjoint outer patches, the level frame is the encoded frame of its guide. -/
theorem levelFrame_eq {j : ℕ} {done : Set (ℤ × ℤ)} {ρ : ℝ × ℝ → ℝ}
    {hρ : ∀ z, 0 < ρ z ∧ ρ z ≤ B₀ * Real.log L}
    (h : ((levelVertices k j done : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)).Pairwise fun z z' =>
      Disjoint (suppliedPatch P ρ hρ z).outer (suppliedPatch P ρ hρ z').outer) :
    levelFrame (q := q) P rank R₀ j done ρ hρ =
      guideFrame (cellCenterPos L) q (levelGuide k j done) (labelParty R₀) guidePlaceholder rank
        (levelVertices k j done) (suppliedPatch P ρ hρ) h :=
  dite_eq_left h

/-- Two encoded frames of one guide with the same owners and the same patches at the hole
centers are equal. -/
theorem guideFrame_congr_patch {ι κ Party : Type*} [Fintype ι] [DecidableEq ι] {pos : ι → ℝ × ℝ}
    {g : ℝ × ℝ → κ} {own : κ → Party} {ph : κ} {rank : κ → ℕ} {V : Finset (ℝ × ℝ)}
    {patch patch' : ℝ × ℝ → SquarePatch pos q}
    {hV : (V : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (patch z).outer (patch z').outer}
    {hV' : (V : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (patch' z).outer (patch' z').outer}
    (h : ∀ z ∈ V, patch z = patch' z) :
    guideFrame pos q g own ph rank V patch hV = guideFrame pos q g own ph rank V patch' hV' := by
  have hh : (V.toList.map fun z => (⟨patch z, own (tagHolder rank g ph z)⟩ : Hole pos q Party)) =
      V.toList.map fun z => ⟨patch' z, own (tagHolder rank g ph z)⟩ :=
    List.map_congr_left fun z hz => by rw [h z (Finset.mem_toList.1 hz)]
  unfold guideFrame
  congr 1

/-- Encoded frames of equal guides with equal centers and the same patches at the centers are
equal. -/
theorem guideFrame_congr_guide {ι κ Party : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}
    {pos : ι → ℝ × ℝ} {g g' : ℝ × ℝ → κ} {own : κ → Party} {ph : κ} {rank : κ → ℕ}
    {V V' : Finset (ℝ × ℝ)} {patch patch' : ℝ × ℝ → SquarePatch pos q}
    {hV : (V : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (patch z).outer (patch z').outer}
    {hV' : (V' : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (patch' z).outer (patch' z').outer}
    (hg : g = g') (hVV : V = V') (h : ∀ z ∈ V, patch z = patch' z) :
    guideFrame pos q g own ph rank V patch hV = guideFrame pos q g' own ph rank V' patch' hV' := by
  subst hg hVV
  exact guideFrame_congr_patch h

/-- **Frames of equal guides.** Two main frames whose sampled guides are equal and whose radii
agree at the true vertices are equal, whatever the levels and repainted blocks that describe
them. -/
theorem levelFrame_eq_of_levelGuide_eq {j j' : ℕ} {done done' : Set (ℤ × ℤ)}
    {ρ ρ' : ℝ × ℝ → ℝ} (hρ : ∀ z, 0 < ρ z ∧ ρ z ≤ B₀ * Real.log L)
    (hρ' : ∀ z, 0 < ρ' z ∧ ρ' z ≤ B₀ * Real.log L)
    (hg : levelGuide k j done = levelGuide k j' done')
    (h : ∀ z ∈ levelVertices k j done, ρ z = ρ' z) :
    levelFrame (q := q) P rank R₀ j done ρ hρ = levelFrame P rank R₀ j' done' ρ' hρ' := by
  have hV : levelVertices k j done = levelVertices k j' done' :=
    Finset.ext fun z => by rw [mem_levelVertices, mem_levelVertices, hg]
  have hp : ∀ z ∈ levelVertices k j done, suppliedPatch P ρ hρ z = suppliedPatch P ρ' hρ' z :=
    fun z hz => suppliedPatch_congr P hρ hρ' (h z hz)
  have hiff : (((levelVertices k j done : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)).Pairwise fun z z' =>
      Disjoint (suppliedPatch P ρ hρ z).outer (suppliedPatch P ρ hρ z').outer) ↔
      (((levelVertices k j' done' : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)).Pairwise fun z z' =>
        Disjoint (suppliedPatch P ρ' hρ' z).outer (suppliedPatch P ρ' hρ' z').outer) := by
    rw [← hV]
    refine ⟨fun H z hz z' hz' hne => ?_, fun H z hz z' hz' hne => ?_⟩
    · change Disjoint (suppliedPatch P ρ' hρ' z).outer (suppliedPatch P ρ' hρ' z').outer
      rw [← hp z hz, ← hp z' hz']; exact H hz hz' hne
    · change Disjoint (suppliedPatch P ρ hρ z).outer (suppliedPatch P ρ hρ z').outer
      rw [hp z hz, hp z' hz']; exact H hz hz' hne
  by_cases hd : ((levelVertices k j done : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)).Pairwise fun z z' =>
      Disjoint (suppliedPatch P ρ hρ z).outer (suppliedPatch P ρ hρ z').outer
  · rw [levelFrame_eq P rank R₀ hd, levelFrame_eq P rank R₀ (hiff.1 hd)]
    exact guideFrame_congr_guide hg hV hp
  · unfold levelFrame
    rw [dite_eq_right hd, dite_eq_right (fun h => hd (hiff.2 h))]

/-- **The frame depends on the radii only at the true vertices.** -/
theorem levelFrame_congr {j : ℕ} {done : Set (ℤ × ℤ)} {ρ ρ' : ℝ × ℝ → ℝ}
    (hρ : ∀ z, 0 < ρ z ∧ ρ z ≤ B₀ * Real.log L) (hρ' : ∀ z, 0 < ρ' z ∧ ρ' z ≤ B₀ * Real.log L)
    (h : ∀ z ∈ levelVertices k j done, ρ z = ρ' z) :
    levelFrame (q := q) P rank R₀ j done ρ hρ = levelFrame P rank R₀ j done ρ' hρ' :=
  levelFrame_eq_of_levelGuide_eq P rank R₀ hρ hρ' rfl h

/-- **Disjoint outer squares at the grid corners.** If every patch radius is at most `r` with
`4 r < 2 ^ j`, the outer squares of the supplied patches at distinct grid corners of the level
are disjoint.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 113–114 and 341–355. -/
theorem pairwise_disjoint_levelHoles {j : ℕ} {done : Set (ℤ × ℤ)} {ρ : ℝ × ℝ → ℝ}
    (hρ : ∀ z, 0 < ρ z ∧ ρ z ≤ B₀ * Real.log L) {r : ℝ} (hr : ∀ z, ρ z ≤ r)
    (h4 : 4 * r < (2 : ℝ) ^ j) :
    ((levelVertices k j done : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)).Pairwise fun z z' =>
      Disjoint (suppliedPatch P ρ hρ z).outer (suppliedPatch P ρ hρ z').outer := by
  classical
  intro z hz z' hz' hne
  have hn : (0 : ℝ) < 2 ^ j := by positivity
  simp only [levelTrueVertices, Finset.coe_filter, Finset.mem_image] at hz hz'
  obtain ⟨⟨Q, -, rfl⟩, -⟩ := hz
  obtain ⟨⟨Q', -, rfl⟩, -⟩ := hz'
  have hQ : Q ≠ Q' := fun h => hne (h ▸ rfl)
  have hd := le_dist_blockCorner_of_ne hn hQ
  refine disjoint_outer_of_disjoint_closedBall (closedBall_disjoint_closedBall ?_)
  simp only [suppliedPatch_center, suppliedPatch_scale]
  linarith [hr (blockCorner ((2 : ℝ) ^ j) Q), hr (blockCorner ((2 : ℝ) ^ j) Q')]

/-! ### Repainting one block -/

/-- **A direct repainting changes the true vertices only at the corners of the block.** Repainting
a block `S` at level `2 ^ j` changes the true vertices of the sampled guide
only at the four corners of `S`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 507–511. -/
theorem isTrueVertex_levelGuide_insert_iff {j : ℕ} (done : Set (ℤ × ℤ)) {S : ℤ × ℤ}
    {c' : ℝ × ℝ}
    (hc : c' ∉ squareCorners ((2 : ℝ) ^ j) S) :
    IsTrueVertex (levelGuide k j (insert S done)) c' ↔ IsTrueVertex (levelGuide k j done) c' := by
  have hn : (0 : ℝ) < 2 ^ j := by positivity
  set K := (fun p => p - blockCorner ((2 : ℝ) ^ j) S) ⁻¹' closedSquare ((2 : ℝ) ^ j)
  have hK : IsClosed K := (isClosed_Icc.prod isClosed_Icc).preimage
    (continuous_id.sub continuous_const)
  by_cases hcK : c' ∈ K
  · have no (d : Set (ℤ × ℤ)) : ¬ IsTrueVertex (levelGuide k j d) c' := fun h => by
      obtain ⟨Q, rfl⟩ := ((isDisplacedReading_levelGuide j d).isTrueVertex h).eq_blockCorner hn
      exact hc ((mem_squareCorners_iff hn).2 (isBlockCornerOf_of_mem_closedSquare hn hcK))
    exact iff_of_false (no _) (no _)
  · have hsub : {p | blockGuide ((2 : ℝ) ^ j) (protocolLevelLabels k j (insert S done)) p ≠
        blockGuide ((2 : ℝ) ^ j) (protocolLevelLabels k j done) p} ⊆ K := by
      intro p hp
      by_contra hpK
      have hne := blockIndex_ne_of_notMem_closedSquare hn S (p := p - blockCorner _ S) hpK
      rw [sub_add_cancel] at hne
      exact hp (by simp only [blockGuide, protocolLevelLabels, levelLabels_insert_of_ne _ _ _ _
        hne])
    have heq : levelGuide k j (insert S done) =ᶠ[𝓝 c'] levelGuide k j done := by
      filter_upwards [hK.isOpen_compl.mem_nhds hcK] with p hp
      by_contra hne
      exact hp (closure_minimal hsub hK
        ((isDisplacedReading_levelGuide j (insert S done)).ne_subset_closure
          (isDisplacedReading_levelGuide j done) hne))
    rw [isTrueVertex_iff_incidentLabels, isTrueVertex_iff_incidentLabels,
      incidentLabels_congr heq]

end TNLean.PEPS.Approximation
