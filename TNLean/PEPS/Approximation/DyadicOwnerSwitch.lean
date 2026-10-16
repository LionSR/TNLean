/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicGuideOwners
import TNLean.PEPS.Approximation.SheetStackChange

/-!
# Switching the party map between events

The frames of the dyadic protocol read the labels of a guide as parties through the party map
`labelParty R` of a repainting `R` (`DyadicProtocolChanges`). The map sends a block label to its
block party, the same for every `R`, and the placeholder label to the fresh placeholder party of
`R`. Consecutive events may read their frames through the party maps of different repaintings.
This file shows that the switch is harmless at the transition times between repaintings.

At those times the placeholder owns no physical main-sheet site and holds no tag
(`06-geometry.tex`, lines 91–100). Here, if a guide takes only valid labels, no site carries the
placeholder, and every hole is centered at a true vertex, then the frame of the guide is the same
for the party maps of any two repaintings (`guideFrame_labelParty_eq`). The change from one to the
other is the identity change, a bounded change for all participants and all bounds
(`exists_isBoundedChange_labelParty_switch`).

A reading of a block guide of a level, which is the guide at the start and at the end of every
repainting, does not carry the placeholder at any point of the open root square
(`IsDisplacedReading.ne_guidePlaceholder`). The sites `(i + 1/2, j + 1/2)` with `0 ≤ i, j < L`
lie there when `L ≤ 2 ^ k`. So the fresh placeholder `.inr R` owns nothing in the frame before
and after the repainting of `R`, and the party map may be switched there
(`guideFrame_levelLabels_labelParty_eq`,
`exists_isBoundedChange_levelLabels_labelParty_switch`).

## Main results

* `TNLean.PEPS.Approximation.labelParty_eq_of_ne_guidePlaceholder`.
* `TNLean.PEPS.Approximation.guideFrame_labelParty_eq`,
  `TNLean.PEPS.Approximation.exists_isBoundedChange_labelParty_switch`.
* `TNLean.PEPS.Approximation.blockGuide_protocolLevelLabels_ne_guidePlaceholder`,
  `TNLean.PEPS.Approximation.IsDisplacedReading.ne_guidePlaceholder`,
  `TNLean.PEPS.Approximation.cellCenterPos_mem_openRoot`.
* `TNLean.PEPS.Approximation.guideFrame_levelLabels_labelParty_eq`,
  `TNLean.PEPS.Approximation.exists_isBoundedChange_levelLabels_labelParty_switch`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), §7, `06-geometry.tex`: the level schedule and
  the placeholder (lines 82–100), the canonical tag holder (lines 119–125), and the retired
  placeholder (lines 627–630).
-/

noncomputable section

namespace TNLean.PEPS.Approximation

open Set Filter Topology EncodedFrame PairEffect

variable {k : ℕ}

/-! ### The party maps of two repaintings -/

/-- **Block labels have the same party for every repainting.** A valid label other than the
placeholder is the label of a square of the hierarchy, held by its block party whatever the
repainting whose party map reads it.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 82–100. -/
theorem labelParty_eq_of_ne_guidePlaceholder (R R' : RepaintedSquare k) {l : GuideLabel}
    (hl : l ∈ validLabels k) (hne : l ≠ guidePlaceholder) : labelParty R l = labelParty R' l := by
  rcases hl with rfl | ⟨S, rfl⟩
  · exact absurd rfl hne
  · simp

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} {pos : ι → ℝ × ℝ}

/-- **The frame does not depend on the party map of the repainting.** Let a guide take only
valid labels, carry no placeholder at the sites, and have a true vertex at every hole center.
Then its encoded frame is the same for the party maps of any two repaintings: the raw owners are
block parties, and so are the tag holders, which are incident labels other than the placeholder.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 91–100 (“at those transition times the
placeholder owns no physical main-sheet site … it holds no persistent main-sheet tag”) and
119–125. -/
theorem guideFrame_labelParty_eq (R R' : RepaintedSquare k) {g : ℝ × ℝ → GuideLabel}
    (hg : ∀ p, g p ∈ validLabels k) (hsite : ∀ x, g (pos x) ≠ guidePlaceholder)
    (rank : GuideLabel → ℕ) {V : Finset (ℝ × ℝ)} (hV : ∀ z ∈ V, IsTrueVertex g z)
    (patch : ℝ × ℝ → SquarePatch pos q)
    (hpV : (V : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (patch z).outer (patch z').outer) :
    guideFrame pos q g (labelParty R) guidePlaceholder rank V patch hpV =
      guideFrame pos q g (labelParty R') guidePlaceholder rank V patch hpV := by
  have ho : (fun x => labelParty R (g (pos x))) = fun x => labelParty R' (g (pos x)) :=
    funext fun x => labelParty_eq_of_ne_guidePlaceholder R R' (hg _) (hsite x)
  have hh : (V.toList.map fun z =>
        (⟨patch z, labelParty R (tagHolder rank g guidePlaceholder z)⟩ :
          Hole pos q (ProtocolParty k))) =
      V.toList.map fun z => ⟨patch z, labelParty R' (tagHolder rank g guidePlaceholder z)⟩ := by
    refine List.map_congr_left fun z hz => ?_
    have ht := isTagHolder_tagHolder (rank := rank) (ph := guidePlaceholder)
      (hV z (Finset.mem_toList.1 hz))
    rw [labelParty_eq_of_ne_guidePlaceholder R R'
      (ht.mem_of_forall fun p => Set.mem_insert_of_mem _ (hg p)) ht.2]
  simp only [guideFrame, ho, hh]

/-- **Switching the party map is an identity change.** Under the hypotheses of
`guideFrame_labelParty_eq`, passing from the frame read through the party map of `R` to the
frame read through that of `R'` is the identity change, a bounded change for every set of
participants and all bounds.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 91–100 and 627–630. -/
theorem exists_isBoundedChange_labelParty_switch [NeZero q] {Ω : EuclideanSpace ℂ (ι → Fin q)}
    (R R' : RepaintedSquare k) {g : ℝ × ℝ → GuideLabel} (hg : ∀ p, g p ∈ validLabels k)
    (hsite : ∀ x, g (pos x) ≠ guidePlaceholder) (rank : GuideLabel → ℕ) {V : Finset (ℝ × ℝ)}
    (hV : ∀ z ∈ V, IsTrueVertex g z) (patch : ℝ × ℝ → SquarePatch pos q)
    (hpV : (V : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (patch z).outer (patch z').outer)
    (S : Set (ProtocolParty k)) (r K : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ c : OriginalCircuit
        (guideFrame pos q g (labelParty R) guidePlaceholder rank V patch hpV).regs
        (guideFrame pos q g (labelParty R') guidePlaceholder rank V patch hpV).regs,
      c.IsBoundedChange S r K ε
        ((guideFrame pos q g (labelParty R) guidePlaceholder rank V patch hpV).regRef Ω)
        ((guideFrame pos q g (labelParty R') guidePlaceholder rank V patch hpV).regRef Ω) :=
  exists_isBoundedChange_of_frame_eq (guideFrame_labelParty_eq R R' hg hsite rank hV patch hpV)
    S r K hε

/-! ### No placeholder at the sites between repaintings -/

/-- The open root square `(0, 2 ^ k) ^ 2`. -/
def openRoot (k : ℕ) : Set (ℝ × ℝ) := Ioo 0 ((2 : ℝ) ^ k) ×ˢ Ioo 0 ((2 : ℝ) ^ k)

/-- **Block labels inside the root square.** At every level `2 ^ j'` with `j' ≤ k` and at any
stage of the pass to the level, the block guide of the level labels carries a block label, not
the placeholder, at every point of the root square `[0, 2 ^ k) ^ 2`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 82–95: “the exterior of `[0,N]^2` has one
placeholder label”. -/
theorem blockGuide_protocolLevelLabels_ne_guidePlaceholder {j' : ℕ} (hj : j' ≤ k)
    (done : Set (ℤ × ℤ)) {p : ℝ × ℝ} (h1 : 0 ≤ p.1) (h2 : p.1 < 2 ^ k) (h3 : 0 ≤ p.2)
    (h4 : p.2 < 2 ^ k) :
    blockGuide (2 ^ j') (protocolLevelLabels k j' done) p ≠ guidePlaceholder := by
  classical
  have hpow : (0 : ℝ) < 2 ^ j' := by positivity
  have hM : ((((2 : ℤ) ^ (k - j') : ℤ)) : ℝ) = 2 ^ k / 2 ^ j' := by
    rw [Int.cast_pow, Int.cast_ofNat, eq_div_iff hpow.ne', ← pow_add, Nat.sub_add_cancel hj]
  have hin : InRoot ((2 : ℤ) ^ (k - j')) (blockIndex (2 ^ j') p) := by
    refine ⟨Int.floor_nonneg.2 (div_nonneg h1 hpow.le), Int.floor_lt.2 ?_,
      Int.floor_nonneg.2 (div_nonneg h3 hpow.le), Int.floor_lt.2 ?_⟩ <;> rw [hM] <;>
      exact div_lt_div_of_pos_right ‹_› hpow
  simp only [blockGuide, protocolLevelLabels, levelLabels, hin, ↓reduceIte]
  split_ifs <;> exact Sum.inl_ne_inr

/-- **Readings carry no placeholder inside the root square.** A reading of the block guide of
a level, at any stage of the pass to the level, carries a block label at every point of the open
root square.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 71–77 and 91–95. -/
theorem IsDisplacedReading.ne_guidePlaceholder {j' : ℕ} (hj : j' ≤ k) {done : Set (ℤ × ℤ)}
    {g : ℝ × ℝ → GuideLabel} {v : ℝ × ℝ}
    (hg : IsDisplacedReading g (blockGuide (2 ^ j') (protocolLevelLabels k j' done)) v)
    {p : ℝ × ℝ} (hp : p ∈ openRoot k) : g p ≠ guidePlaceholder := by
  have hU : IsOpen (openRoot k) := isOpen_Ioo.prod isOpen_Ioo
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), p + ε • v ∈ openRoot k :=
    tendsto_add_smul_nhdsGT p v (hU.mem_nhds hp)
  obtain ⟨ε, he, hmem⟩ := ((hg p).and hev).exists
  obtain ⟨⟨a1, a2⟩, a3, a4⟩ := hmem
  rw [he]
  exact blockGuide_protocolLevelLabels_ne_guidePlaceholder hj done a1.le a2 a3.le a4

/-- The sites `(i + 1/2, j + 1/2)`, `0 ≤ i, j < L`, lie in the open root square when
`L ≤ 2 ^ k`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 62–67. -/
theorem cellCenterPos_mem_openRoot {L : ℕ} (hk : L ≤ 2 ^ k) (x : SquareLatticeVertex L L) :
    cellCenterPos L x ∈ openRoot k := by
  have hL : (L : ℝ) ≤ 2 ^ k := by exact_mod_cast hk
  have h1 : ((x.1 : ℕ) : ℝ) + 1 ≤ L := by exact_mod_cast x.1.isLt
  have h2 : ((x.2 : ℕ) : ℝ) + 1 ≤ L := by exact_mod_cast x.2.isLt
  simp only [openRoot, cellCenterPos, Set.mem_prod, Set.mem_Ioo]
  refine ⟨⟨by positivity, by linarith⟩, by positivity, by linarith⟩

/-- **The party map at a transition time.** At the start and at the end of every repainting of
level `2 ^ j'`, `j' < k`, the frame of a reading of the block guide of the level, with sites at
the cell centers of `[0, L] ^ 2`, `L ≤ 2 ^ k`, and holes at true vertices, is the same for the
party maps of any two repaintings. In particular the fresh placeholder party of a repainting owns
no site and no tag of the frame before and after that repainting.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 82–100 and 627–630. -/
theorem guideFrame_levelLabels_labelParty_eq {L : ℕ} (hk : L ≤ 2 ^ k) {j' : ℕ} (hj : j' < k)
    {done : Set (ℤ × ℤ)} {g : ℝ × ℝ → GuideLabel} {v : ℝ × ℝ}
    (hg : IsDisplacedReading g (blockGuide (2 ^ j') (protocolLevelLabels k j' done)) v)
    (R R' : RepaintedSquare k) (rank : GuideLabel → ℕ) {V : Finset (ℝ × ℝ)}
    (hV : ∀ z ∈ V, IsTrueVertex g z) (patch : ℝ × ℝ → SquarePatch (cellCenterPos L) q)
    (hpV : (V : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (patch z).outer (patch z').outer) :
    guideFrame (cellCenterPos L) q g (labelParty R) guidePlaceholder rank V patch hpV =
      guideFrame (cellCenterPos L) q g (labelParty R') guidePlaceholder rank V patch hpV :=
  guideFrame_labelParty_eq R R' (hg.mem fun p => blockGuide_mem_validLabels hj _ done p)
    (fun x => hg.ne_guidePlaceholder hj.le (cellCenterPos_mem_openRoot hk x)) rank hV patch hpV

/-- **Switching the party map at a transition time.** Under the hypotheses of
`guideFrame_levelLabels_labelParty_eq`, passing from the party map of one repainting to that of
another is the identity change, a bounded change for every set of participants and all bounds.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 82–100 and 627–630. -/
theorem exists_isBoundedChange_levelLabels_labelParty_switch [NeZero q] {L : ℕ}
    {Ω : EuclideanSpace ℂ (SquareLatticeVertex L L → Fin q)} (hk : L ≤ 2 ^ k) {j' : ℕ}
    (hj : j' < k) {done : Set (ℤ × ℤ)} {g : ℝ × ℝ → GuideLabel} {v : ℝ × ℝ}
    (hg : IsDisplacedReading g (blockGuide (2 ^ j') (protocolLevelLabels k j' done)) v)
    (R R' : RepaintedSquare k) (rank : GuideLabel → ℕ) {V : Finset (ℝ × ℝ)}
    (hV : ∀ z ∈ V, IsTrueVertex g z) (patch : ℝ × ℝ → SquarePatch (cellCenterPos L) q)
    (hpV : (V : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (patch z).outer (patch z').outer)
    (S : Set (ProtocolParty k)) (r K : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ c : OriginalCircuit
        (guideFrame (cellCenterPos L) q g (labelParty R) guidePlaceholder rank V patch hpV).regs
        (guideFrame (cellCenterPos L) q g (labelParty R') guidePlaceholder rank V patch hpV).regs,
      c.IsBoundedChange S r K ε
        ((guideFrame (cellCenterPos L) q g (labelParty R) guidePlaceholder rank V patch
          hpV).regRef Ω)
        ((guideFrame (cellCenterPos L) q g (labelParty R') guidePlaceholder rank V patch
          hpV).regRef Ω) :=
  exists_isBoundedChange_of_frame_eq
    (guideFrame_levelLabels_labelParty_eq hk hj hg R R' rank hV patch hpV) S r K hε

end TNLean.PEPS.Approximation
