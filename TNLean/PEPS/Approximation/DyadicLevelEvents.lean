/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicLevelFrames
import TNLean.PEPS.Approximation.DyadicProtocolChanges

/-!
# Direct repaintings and resizes as changes of the protocol

Two kinds of events of the protocol of Proposition 7.1 of the polynomial-PEPS manuscript change
only the main frame of a level, by one small-patch rewrite (`06-geometry.tex`, lines 127–131 and
507–541):

* the direct repainting of a square of side `n ≤ K₀ t` (`directRepainting_hasSourceBoundedChange`);
* the resize of the hole at a grid corner, entering a level, from the radius `h_{2n}` to the
  radius `h_n` (`exists_resize_hasSourceBoundedChange`). When the two radii agree, or the corner
  is not a true vertex, the resize is the identity change.

In both cases the change of the memory is a bounded change with at most `2 b` pair sources in
each monomial, whose participants the event uses, with the auxiliary frames as spectators.

The parties of a resize read the labels of the nine blocks about the junction. A label of a block
outside the root square is the placeholder; between repaintings the placeholder holds no site and
no tag, so the frame may read it as any party (`guideFrame_eq_of_owner_eq`). The resize reads it
as the party of a block of the root square next to the junction, which the resize uses.

## References

* Polynomial-PEPS manuscript (September 24, 2026), §7, `06-geometry.tex`: the placeholder (lines
  91–100), the holes and their resizes (lines 102–133), the direct repainting and the hole
  resizing (lines 507–541), the counts (lines 572–583), and the parties of an event (lines
  585–596); Lemma 6.3 `lem:small-rewrite`, `05-frames.tex`, lines 188–218.
-/

noncomputable section

open Set Metric Filter Topology

namespace TNLean.PEPS.Approximation

open EncodedFrame PairEffect

variable {k : ℕ}

/-! ### Reading the placeholder as another party -/

/-- **Owners that agree off the placeholder.** Let a guide take only valid labels, carry no
placeholder at the sites, and have a true vertex at every hole center. Then its encoded frame is
the same for any two party maps that agree on the valid labels other than the placeholder.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 91–100 and 119–125. -/
theorem guideFrame_eq_of_owner_eq {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ}
    {pos : ι → ℝ × ℝ} {own own' : GuideLabel → ProtocolParty k}
    (hown : ∀ l ∈ validLabels k, l ≠ guidePlaceholder → own l = own' l) {g : ℝ × ℝ → GuideLabel}
    (hg : ∀ p, g p ∈ validLabels k) (hsite : ∀ x, g (pos x) ≠ guidePlaceholder)
    (rank : GuideLabel → ℕ) {V : Finset (ℝ × ℝ)} (hV : ∀ z ∈ V, IsTrueVertex g z)
    (patch : ℝ × ℝ → SquarePatch pos q)
    (hpV : (V : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (patch z).outer (patch z').outer) :
    guideFrame pos q g own guidePlaceholder rank V patch hpV =
      guideFrame pos q g own' guidePlaceholder rank V patch hpV := by
  have ho : (fun x => own (g (pos x))) = fun x => own' (g (pos x)) :=
    funext fun x => hown _ (hg _) (hsite x)
  have hh : (V.toList.map fun z =>
        (⟨patch z, own (tagHolder rank g guidePlaceholder z)⟩ : Hole pos q (ProtocolParty k))) =
      V.toList.map fun z => ⟨patch z, own' (tagHolder rank g guidePlaceholder z)⟩ := by
    refine List.map_congr_left fun z hz => ?_
    have ht := isTagHolder_tagHolder (rank := rank) (ph := guidePlaceholder)
      (hV z (Finset.mem_toList.1 hz))
    rw [hown _ (ht.mem_of_forall fun p => Set.mem_insert_of_mem _ (hg p)) ht.2]
  simp only [guideFrame, ho, hh]

/-! ### Direct repaintings -/

/-- The bound on the number of monomials and on the coefficient sum of the gate of a small-patch
rewrite with `b` patches, tag counts at most `C' L ^ c'` and test exponent `60`
(`directRepainting_step`, `resize_step`, `pointTreatment_step`).

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 572–583; Lemma 6.3 `lem:small-rewrite`,
`05-frames.tex`, lines 188–218. -/
abbrev rewriteGateBound (C' c' b L : ℕ) : ℕ :=
  (C' + 1) ^ (3 * b) * (16 * b ^ 2 * (C' + 1) ^ (6 * b) + 1) ^ (2 * b) *
    L ^ (3 * b * c' + 4 * b * (3 * b * c' + 30))

variable {L q : ℕ} [NeZero q] {Ω : StateSpace L q} {B₀ C c : ℝ}

/-- **A direct repainting as a change of the protocol.** At the constants of the protocol, let a
square `R` of side `n = 2 ^ j ≤ K₀ t` be repainted directly, from the main frame of its level
with the blocks of `done` repainted to the frame with `R` repainted as well, all holes of radius
`h_n` and patches supplied by Proposition 4.1. Then the change of the memory, with any auxiliary
frames as spectators, is a bounded change whose participants the repainting uses, with at most
`2 b` pair effects and pair sources in each monomial, at most `rewriteGateBound C' c' b L`
monomials and coefficient sum, and error `(2 b + 1) L⁻²⁰`, for `b = protocolPatchBound ε₀ ν`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 91–100, 507–527 and 572–596. -/
theorem directRepainting_hasSourceBoundedChange {K₀ ε₀ ν a D : ℝ}
    (hc : IsProtocolConstants K₀ ε₀ ν a D B₀) (hm : IsDirectRepaintingRatio K₀ ε₀ ν)
    (hL : 2 ≤ L) (hkL : L ≤ 2 ^ k) (hΩ : ‖Ω‖ = 1)
    (P : AdaptivePatchSupply (cellCenterPos L) Ω B₀ C c 60 L) (rank : GuideLabel → ℕ)
    (R₀ R : RepaintedSquare k) (hK : (2 : ℝ) ^ (R.1.1 : ℕ) ≤ K₀ * (D * Real.log L))
    (done : Set (ℤ × ℤ))
    (hρ : ∀ _ : ℝ × ℝ, 0 < holeRadius ε₀ ((2 : ℝ) ^ (R.1.1 : ℕ)) (D * Real.log L) ∧
      holeRadius ε₀ ((2 : ℝ) ^ (R.1.1 : ℕ)) (D * Real.log L) ≤ B₀ * Real.log L)
    {C' c' : ℕ} (hC : C ≤ C') (hC' : 1 ≤ C') (hcc : c ≤ c')
    (Fs : List (Frame (cellCenterPos L) q (ProtocolParty k))) :
    HasSourceBoundedChange Ω
      (levelFrame P rank R₀ R.1.1 done
        (fun _ => holeRadius ε₀ ((2 : ℝ) ^ (R.1.1 : ℕ)) (D * Real.log L)) hρ :: Fs)
      (levelFrame P rank R₀ R.1.1 (insert R.1.index done)
        (fun _ => holeRadius ε₀ ((2 : ℝ) ^ (R.1.1 : ℕ)) (D * Real.log L)) hρ :: Fs)
      (ℓ := []) (1 : ℂ) {p | EventUses (.inl R.1) p} (2 * protocolPatchBound ε₀ ν)
      (rewriteGateBound C' c' (protocolPatchBound ε₀ ν) L) (2 * protocolPatchBound ε₀ ν)
      ((2 * protocolPatchBound ε₀ ν + 1) * ((L : ℝ) ^ 20)⁻¹) := by
  set n : ℝ := (2 : ℝ) ^ (R.1.1 : ℕ) with hn_def
  set t := D * Real.log L with ht_def
  have hℓ : 0 < Real.log L := Real.log_pos (by exact_mod_cast hL)
  have hs := hc.protocolSeparations hℓ
  have hn : 0 < n := by positivity
  have h4 : 4 * holeRadius ε₀ n t < n := by
    have := holeRadius_le_mul (n := n) (t := t) hc.ε₀_pos.le
    have := hc.ε₀_lt
    nlinarith
  have hdisj : ∀ d : Set (ℤ × ℤ), ((levelVertices k R.1.1 d : Finset (ℝ × ℝ)) :
      Set (ℝ × ℝ)).Pairwise fun z z' =>
        Disjoint (suppliedPatch P _ hρ z).outer (suppliedPatch P _ hρ z').outer :=
    fun d => pairwise_disjoint_levelHoles P hρ (fun _ => le_rfl) h4
  have hu : ∀ _ : ℝ × ℝ, 0 < patchRadius ν n ∧ patchRadius ν n ≤ B₀ * Real.log L := by
    obtain ⟨-, hu, -⟩ := hs.direct n hn
    have := hs.patch_le n hK
    exact fun _ => ⟨hu, by linarith⟩
  obtain ⟨hcH, hεH, htag⟩ := suppliedPatch_data hρ P hΩ hL hC hC' hcc
  obtain ⟨hcP, hεP, -⟩ := suppliedPatch_data hu P hΩ hL hC hC' hcc
  rw [levelFrame_eq P rank R₀ (hdisj done), levelFrame_eq P rank R₀ (hdisj _),
    guideFrame_levelLabels_labelParty_eq hkL R.2 (isDisplacedReading_levelGuide _ done) R₀ R
      rank (fun z hz => mem_levelVertices.1 hz) _ (hdisj done),
    guideFrame_levelLabels_labelParty_eq hkL R.2 (isDisplacedReading_levelGuide _ _) R₀ R rank
      (fun z hz => mem_levelVertices.1 hz) _ (hdisj _)]
  obtain ⟨w, hw, hws⟩ := directRepainting_isBoundedChange hc hm hL hn hK
    isGenericDisplacement_one_one R done (isDisplacedReading_levelGuide _ done)
    (isDisplacedReading_levelGuide _ (insert R.1.index done)) rank
    (fun z hz => mem_levelVertices.1 hz) (fun z hz => mem_levelVertices.1 hz)
    (fun z _ hz => mem_levelVertices.2 hz) (fun z _ hz => mem_levelVertices.2 hz)
    (fun z hz => by rw [mem_levelVertices, mem_levelVertices,
      isTrueVertex_levelGuide_insert_iff done hz])
    (suppliedPatch P _ hρ) (suppliedPatch P _ hu)
    (fun z => ⟨suppliedPatch_center P hρ z, suppliedPatch_scale P hρ z⟩)
    (fun z => ⟨suppliedPatch_center P hu z, suppliedPatch_scale P hu z⟩) (hdisj _) (hdisj _)
    hcH hcP hΩ.le hεP hεH htag
  exact hasSourceBoundedChange_main Fs hw hws hΩ.le (by simp)

end TNLean.PEPS.Approximation
