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

/-! ### Resizes -/

/-- **No true vertex at the root level.** The guide of the root level carries one label inside
the root square and the placeholder outside, so it has no true vertex.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 109–111 and 661–662: "At the beginning the
main guide has only the root label and the exterior placeholder, so it has no true vertex". -/
theorem levelVertices_self (done : Set (ℤ × ℤ)) : levelVertices k k done = ∅ := by
  ext z
  simp only [Finset.notMem_empty, iff_false]
  rw [mem_levelVertices]
  rintro ⟨l₁, l₂, l₃, h12, h13, h23, h1, h2, h3⟩
  have hlab : ∀ Q, protocolLevelLabels k k done Q = protocolLevelLabels k k done (0, 0) ∨
      protocolLevelLabels k k done Q = guidePlaceholder := by
    classical
    intro Q
    by_cases hQ : InRoot ((2 : ℤ) ^ (k - k)) Q
    · left
      have hQ0 : Q = (0, 0) := by
        simp only [InRoot, Nat.sub_self, pow_zero] at hQ
        ext <;> simp <;> omega
      rw [hQ0]
    · right
      simp only [protocolLevelLabels, levelLabels, hQ, ite_false]
  have key : ∀ l, z ∈ closure (levelGuide k k done ⁻¹' {l}) →
      l = protocolLevelLabels k k done (0, 0) ∨ l = guidePlaceholder := by
    intro l hl
    obtain ⟨p, rfl⟩ := mem_range_of_mem_incidentLabels (f := levelGuide k k done) hl
    obtain ⟨ε, hε⟩ := ((isDisplacedReading_levelGuide k done) p).exists
    rw [hε]
    exact hlab _
  rcases key _ h1 with rfl | rfl <;> rcases key _ h2 with h | h <;> rcases key _ h3 with h' | h' <;>
    simp_all

/-- The hole radius at the grid corner `z` while the holes of the guide uniform on the
`2 n`-blocks are resized one at a time: `h_n` at the corners of `A`, already resized, and
`h_{2n}` elsewhere.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 127–131 and 529–541. -/
noncomputable def resizeRadius (ε₀ t n : ℝ) (A : Set (ℝ × ℝ)) (z : ℝ × ℝ) : ℝ :=
  open Classical in if z ∈ A then holeRadius ε₀ n t else holeRadius ε₀ (2 * n) t

/-- A block of the root square among the nine blocks about the junction `J`. -/
def DyadicJunction.rootNbr (J : DyadicJunction k) : ℤ × ℤ :=
  (if (J.2.1 : ℕ) = 0 then 1 else 0, if (J.2.2 : ℕ) = 0 then 1 else 0)

theorem DyadicJunction.rootNbr_mem (J : DyadicJunction k) : J.rootNbr ∈ blockWindow 1 := by
  simp only [DyadicJunction.rootNbr, blockWindow, Finset.mem_product, Finset.mem_Icc]
  constructor <;> split_ifs <;> norm_num

theorem DyadicJunction.inRoot_rootNbr (J : DyadicJunction k) :
    InRoot ((2 : ℤ) ^ (k - (J.1 : ℕ))) (J.rootNbr + (J.index.1 - 1, J.index.2 - 1)) := by
  have h1 := J.2.1.isLt
  have h2 := J.2.2.isLt
  have hM : (1 : ℤ) ≤ 2 ^ (k - (J.1 : ℕ)) := one_le_pow₀ (by norm_num)
  have e : ((2 ^ (k - (J.1 : ℕ)) : ℕ) : ℤ) = (2 : ℤ) ^ (k - (J.1 : ℕ)) := by push_cast; rfl
  simp only [DyadicJunction.rootNbr, DyadicJunction.index, InRoot, Prod.fst_add, Prod.snd_add]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> split_ifs <;> omega

/-- **The party map of a resize.** The party map of the repainting `R₀`, except that the
placeholder is read as the party of a block of the root square next to the junction `J`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 91–100 and 127–131. -/
def resizeParty (R₀ : RepaintedSquare k) (J : DyadicJunction k) (l : GuideLabel) :
    ProtocolParty k :=
  open Classical in
  if l = guidePlaceholder then
    labelParty R₀ (protocolLevelLabels k J.1 univ (J.rootNbr + (J.index.1 - 1, J.index.2 - 1)))
  else labelParty R₀ l

/-- **The parties of a resize are used by it.** Every party of the resize step at the junction
`J`, the party under `resizeParty` of the label of one of the nine blocks about `J` at the end of
the pass to the level of `J`, is used by the resize at `J`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 127–131 and 594. -/
theorem eventUses_resizeParty (R₀ : RepaintedSquare k) (J : DyadicJunction k) {R' : ℤ × ℤ}
    (hR' : R' ∈ blockWindow 1) :
    EventUses (.inr J) (resizeParty R₀ J
      (protocolLevelLabels k J.1 univ (R' + (J.index.1 - 1, J.index.2 - 1)))) := by
  classical
  have hd : {Q | InRoot ((2 : ℤ) ^ (k - (J.1 : ℕ))) Q} ⊆ univ := subset_univ _
  by_cases hin : InRoot ((2 : ℤ) ^ (k - (J.1 : ℕ))) (R' + (J.index.1 - 1, J.index.2 - 1))
  · have hne : protocolLevelLabels k J.1 univ (R' + (J.index.1 - 1, J.index.2 - 1)) ≠
        guidePlaceholder := by
      simp only [protocolLevelLabels, levelLabels, hin, mem_univ, ite_true]
      exact inl_ne_guidePlaceholder _
    simp only [resizeParty, hne, ite_false]
    exact eventUses_labelParty_protocolLevelLabels_junction R₀ J hd hR' hin
  · have he : protocolLevelLabels k J.1 univ (R' + (J.index.1 - 1, J.index.2 - 1)) =
        guidePlaceholder := by
      simp only [protocolLevelLabels, levelLabels, hin, ite_false]
    simp only [resizeParty, he, ite_true]
    exact eventUses_labelParty_protocolLevelLabels_junction R₀ J hd J.rootNbr_mem J.inRoot_rootNbr

/-- **A resize as a change of the protocol.** Fix `0 < ε₀ ≤ 1/16`. There is a threshold `ν' > 0`
such that for every mesh ratio `0 < ν ≤ ν'` and constants of the protocol the following holds.
Entering the level `n = 2 ^ (j - 1)`, with the main guide uniform on the `2 n`-blocks, let the
holes at the grid corners of `A` already have radius `h_n` and the others radius `h_{2n}`. Then
resizing the hole at the corner of the junction `J` of scale `j ≥ 1` is a change of the memory,
with any auxiliary frames as spectators, that is a bounded change whose participants the resize
uses, with the bounds of a small-patch rewrite with `b = protocolPatchBound ε₀ ν` patches.

When the two radii agree or the corner is not a true vertex, the frame does not change, and the
change is the identity.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 102–133, 529–541, 559–570 and 572–596. -/
theorem exists_resize_hasSourceBoundedChange {ε₀ : ℝ} (hε : 0 < ε₀) (hε₀ : ε₀ ≤ 1 / 16) :
    ∃ ν' > 0, ∀ ν : ℝ, 0 < ν → ν ≤ ν' → ∀ {K₀ a D B₀ : ℝ},
      IsProtocolConstants K₀ ε₀ ν a D B₀ → ∀ {L q : ℕ} [NeZero q] {Ω : StateSpace L q} {C c : ℝ},
      2 ≤ L → L ≤ 2 ^ k → ‖Ω‖ = 1 →
      ∀ (P : AdaptivePatchSupply (cellCenterPos L) Ω B₀ C c 60 L) (rank : GuideLabel → ℕ)
        (R₀ : RepaintedSquare k) (J : DyadicJunction k), 0 < (J.1 : ℕ) →
      ∀ (A : Set (ℝ × ℝ))
        (hρ : ∀ z, 0 < resizeRadius ε₀ (D * Real.log L) ((2 : ℝ) ^ ((J.1 : ℕ) - 1)) A z ∧
          resizeRadius ε₀ (D * Real.log L) ((2 : ℝ) ^ ((J.1 : ℕ) - 1)) A z ≤ B₀ * Real.log L)
        (hρ' : ∀ z, 0 < resizeRadius ε₀ (D * Real.log L) ((2 : ℝ) ^ ((J.1 : ℕ) - 1))
            (insert (blockCorner ((2 : ℝ) ^ (J.1 : ℕ)) J.index) A) z ∧
          resizeRadius ε₀ (D * Real.log L) ((2 : ℝ) ^ ((J.1 : ℕ) - 1))
            (insert (blockCorner ((2 : ℝ) ^ (J.1 : ℕ)) J.index) A) z ≤ B₀ * Real.log L)
        {C' c' : ℕ}, C ≤ C' → 1 ≤ C' → c ≤ c' →
      ∀ Fs : List (Frame (cellCenterPos L) q (ProtocolParty k)),
      HasSourceBoundedChange Ω
        (levelFrame P rank R₀ J.1 univ _ hρ :: Fs) (levelFrame P rank R₀ J.1 univ _ hρ' :: Fs)
        (ℓ := []) (1 : ℂ) {p | EventUses (.inr J) p} (2 * protocolPatchBound ε₀ ν)
        (rewriteGateBound C' c' (protocolPatchBound ε₀ ν) L) (2 * protocolPatchBound ε₀ ν)
        ((2 * protocolPatchBound ε₀ ν + 1) * ((L : ℝ) ^ 20)⁻¹) := by
  obtain ⟨ν', hν', H⟩ := exists_resize_step_supplied hε hε₀
  refine ⟨ν', hν', fun ν hν hνν' {K₀ a D B₀} hc {L q} _ {Ω C c} hL hkL hΩ P rank R₀ J hJ A hρ
    hρ' {C' c'} hC hC' hcc Fs => ?_⟩
  set n : ℝ := (2 : ℝ) ^ ((J.1 : ℕ) - 1) with hn_def
  set t := D * Real.log L with ht_def
  have hn : 0 < n := by positivity
  have h2n : (2 : ℝ) ^ (J.1 : ℕ) = 2 * n := by
    rw [hn_def, ← pow_succ']
    congr 1
    omega
  set z₀ := blockCorner ((2 : ℝ) ^ (J.1 : ℕ)) J.index
  have hε0 : (0 : ℝ) ≤ (2 * protocolPatchBound ε₀ ν + 1) * ((L : ℝ) ^ 20)⁻¹ := by positivity
  -- the identity cases
  by_cases hmain : z₀ ∈ levelVertices k J.1 univ ∧ n < t
  swap
  · have heq : levelFrame (q := q) P rank R₀ J.1 univ _ hρ =
        levelFrame P rank R₀ J.1 univ _ hρ' := by
      refine levelFrame_congr P rank R₀ hρ hρ' fun z hz => ?_
      classical
      by_cases hz₀ : z = z₀
      · subst hz₀
        have hnt : ¬n < t := fun h => hmain ⟨hz, h⟩
        simp only [resizeRadius, mem_insert_iff, true_or, ite_true]
        split_ifs
        · rfl
        · rw [holeRadius, holeRadius, min_eq_right (not_lt.1 hnt),
            min_eq_right (by linarith [not_lt.1 hnt])]
      · simp only [resizeRadius, mem_insert_iff, hz₀, false_or]
    rw [heq]
    exact hasSourceBoundedChange_refl _ _ _ _ _ _ hε0
  obtain ⟨hz₀V, hnt⟩ := hmain
  have hℓ : 0 < Real.log L := Real.log_pos (by exact_mod_cast hL)
  have hk : (J.1 : ℕ) < k := by
    rcases (Nat.lt_succ_iff.1 J.1.isLt).lt_or_eq with h | h
    · exact h
    · rw [h, levelVertices_self] at hz₀V
      exact absurd hz₀V (Finset.notMem_empty _)
  -- disjoint outer holes
  have hr : ∀ B : Set (ℝ × ℝ), ∀ z, resizeRadius ε₀ t n B z ≤ ε₀ * (2 : ℝ) ^ (J.1 : ℕ) := by
    intro B z
    rw [h2n]
    classical
    unfold resizeRadius
    split_ifs
    · have := holeRadius_le_mul (n := n) (t := t) hε.le; nlinarith
    · exact holeRadius_le_mul hε.le
  have h4 : 4 * (ε₀ * (2 : ℝ) ^ (J.1 : ℕ)) < (2 : ℝ) ^ (J.1 : ℕ) := by
    have := hc.ε₀_lt
    have : (0 : ℝ) < 2 ^ (J.1 : ℕ) := by positivity
    nlinarith
  have hpOld := pairwise_disjoint_levelHoles (k := k) (done := univ) P hρ (hr A) h4
  have hpNew := pairwise_disjoint_levelHoles (k := k) (done := univ) P hρ' (hr _) h4
  -- the frames read through the party map of the resize
  have hg : IsDisplacedReading (levelGuide k J.1 univ)
      (blockGuide ((2 : ℝ) ^ (J.1 : ℕ)) (protocolLevelLabels k J.1 univ)) ((1 : ℝ), (1 : ℝ)) :=
    isDisplacedReading_levelGuide _ _
  have hown : ∀ l ∈ validLabels k, l ≠ guidePlaceholder → labelParty R₀ l = resizeParty R₀ J l :=
    fun l _ hl => by simp only [resizeParty, hl, ite_false]
  have hvalid : ∀ p, levelGuide k J.1 univ p ∈ validLabels k :=
    hg.mem fun p => blockGuide_mem_validLabels hk _ _ p
  have hsite : ∀ x, levelGuide k J.1 univ (cellCenterPos L x) ≠ guidePlaceholder :=
    fun x => hg.ne_guidePlaceholder hk.le (cellCenterPos_mem_openRoot hkL x)
  rw [levelFrame_eq P rank R₀ hpOld, levelFrame_eq P rank R₀ hpNew,
    guideFrame_eq_of_owner_eq hown hvalid hsite rank (fun z hz => mem_levelVertices.1 hz) _ hpOld,
    guideFrame_eq_of_owner_eq hown hvalid hsite rank (fun z hz => mem_levelVertices.1 hz) _ hpNew]
  -- the step
  have hg2 : IsDisplacedReading (levelGuide k J.1 univ)
      (blockGuide (2 * n) (protocolLevelLabels k J.1 univ)) ((1 : ℝ), (1 : ℝ)) := by
    rw [← h2n]; exact hg
  have hc₀ : blockCorner (2 * n) J.index ∈ levelVertices k J.1 univ := by rw [← h2n]; exact hz₀V
  have hu : ∀ _ : ℝ × ℝ, 0 < ν * n ∧ ν * n ≤ B₀ * Real.log L := by
    have hD : D ≤ B₀ := by nlinarith [hc.B₀_ge, hc.twenty_le_K₀, hc.D_pos]
    have hν1 := hc.ν_lt_one
    refine fun _ => ⟨by positivity, ?_⟩
    calc ν * n ≤ n := by nlinarith
      _ ≤ t := hnt.le
      _ ≤ B₀ * Real.log L := mul_le_mul_of_nonneg_right hD hℓ.le
  have hscale : ∀ z, (resizeRadius ε₀ t n A z = holeRadius ε₀ n t ∨
      resizeRadius ε₀ t n A z = holeRadius ε₀ (2 * n) t) ∧
      (resizeRadius ε₀ t n (insert z₀ A) z = holeRadius ε₀ n t ∨
        resizeRadius ε₀ t n (insert z₀ A) z = holeRadius ε₀ (2 * n) t) := by
    classical
    intro z
    unfold resizeRadius
    constructor <;> split_ifs <;> simp
  have hsame : ∀ z, z ≠ blockCorner (2 * n) J.index →
      resizeRadius ε₀ t n A z = resizeRadius ε₀ t n (insert z₀ A) z := by
    classical
    intro z hz
    have hz' : z ≠ z₀ := by rwa [show z₀ = blockCorner (2 * n) J.index by rw [← h2n]]
    simp only [resizeRadius, mem_insert_iff, hz', false_or]
  have hb : (2 * (4 * ε₀ + ν) / ν + 1) ^ 2 ≤ (protocolPatchBound ε₀ ν : ℝ) := by
    refine sq_le_protocolPatchBound (by positivity) (add_le_add ?_ le_rfl)
    rw [div_le_div_iff_of_pos_right hν]
    linarith
  obtain ⟨P', -, hP', w, h₁, h₂, h₃, h₄, h₅, h₆⟩ := H ν hν hνν' isGenericDisplacement_one_one hn
    hnt hg2 (resizeParty R₀ J) guidePlaceholder rank (fun z hz => mem_levelVertices.1 hz) hc₀
    (fun z _ hz => mem_levelVertices.2 hz) P hΩ hL hρ hρ' hu hscale hsame hpOld hpNew hC hC' hcc
    hb (by have := eighteen_le_protocolPatchBound ε₀ ν; omega)
  refine hasSourceBoundedChange_main Fs ⟨h₁, fun γ x hx => ?_, h₃, h₄, h₅⟩ h₆ hΩ.le (by simp)
  obtain ⟨R', hR', rfl⟩ := hP' x (h₂ γ hx)
  exact eventUses_resizeParty R₀ J hR'

end TNLean.PEPS.Approximation
