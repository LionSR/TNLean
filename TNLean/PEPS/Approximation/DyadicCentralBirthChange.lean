/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicBandStepChanges

/-!
# The central birth as a change of the main sheet

The large-scale repainting of a square `S` in the protocol of Proposition 7.1 of the
polynomial-PEPS manuscript starts by giving the central part of `S` its final label, after
homogenizing the main sheet to the old label on the squares of radius `t` about the four corners
of `S` (`06-geometry.tex`, lines 155–160 and 328–387). This file proves that this central birth is
a bounded change between the frames of the treated guides before and after it, conditional on
Proposition 3.4 through `IsAngularScale`:

* `RepaintingBaseline.central_treated_mem`, `RepaintingBaseline.central_treated_ne_subset` : the
  values of the treated guides near the change and the location of the change;
* `centralBirth_hasFrameChange_of` : for the frames of sampled guides of any repainting baseline;
* `centralBirth_hasFrameChange` : for the treated frames of the protocol.

## References

* Polynomial-PEPS manuscript (September 24, 2026), §7, `06-geometry.tex`: the central birth
  (lines 155–160), the point treatment and the bulk operations (lines 328–387 and 440–445);
  Lemma 6.5 `lem:birth`, `05-frames.tex`.
-/

noncomputable section

open Set Metric Filter Topology

namespace TNLean.PEPS.Approximation

open EncodedFrame PairEffect

/-! ### The central birth -/

/-- The changed region of the treated central birth lies in the closed square.

A formalization lemma for the central-birth support and point-treatment discussion in the
polynomial-PEPS manuscript, `06-geometry.tex`, lines 155–160 and 357–360. -/
theorem RepaintingBaseline.central_treated_ne_subset {ι : Type*} (R : RepaintingBaseline ι)
    (t : ℝ) :
    {p | homogenize (cornerTreated R.n t) R.oldLabel R.guide p ≠
        homogenize (cornerTreated R.n t) R.oldLabel R.centralGuide p} ⊆ closedSquare R.n := by
  intro p hpS
  have hpU : p ∉ cornerTreated R.n t := fun h => hpS (by simp only [homogenize_of_mem h])
  by_contra hc
  have hc' : p ∉ centralRegion R.n := fun h =>
    hc (openSquare_subset_closedSquare _ (centralRegion_subset_openSquare _ h))
  exact hpS (by simp only [homogenize_of_notMem hpU, R.centralGuide_of_notMem hc'])

section Changes

variable {k q : ℕ} [NeZero q] {a A₀ D L₀' : ℝ} {m₀ : ℕ} {L : ℕ}
  {G : ∀ L : ℕ, StateSpace L q → Prop} {Ω : StateSpace L q} {K₀ ε₀ ν B₀ C c : ℝ}

/-- **The central birth for the frames of sampled guides.** Assume `q ≥ 1`, a unit state of the
family `G`, and the exponent-`60` angular-scale condition with `L₀' ≤ L`, `m₀ ≥ 4`, `A₀ ≥ 1`
and `a ≤ angularConstant / 2`. Take any guide-label repainting baseline `Bl`, translation `d`,
`0 < t = D log L ≤ Bl.n ≤ A₀ * L`, and `2 * ε₀ ≤ angularConstant / 2`. Let `fb, fa` read the
translated starting and central guides, homogenized to the old label on the four corner squares.
Use their exact finite true-vertex sets, an exponent-`60` adaptive patch supply, and radius
`0 < ε₀ * t ≤ B₀ * log L`, with pairwise-disjoint outer samples within each set. For any owner
map and rank, the supplied frames admit a bounded change with participants in any set containing
the old and final owners, error `L⁻³⁰`, arbitrary natural pair-effect bound `r`, and any
`K, rs ≥ 1`.
Both the monomial count and absolute coefficient sum are bounded by `K`; one pair source suffices.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 155–160, 328–387 and 440–445. -/
theorem centralBirth_hasFrameChange_of (hD : IsAngularScale q G a A₀ m₀ 60 D L₀')
    (hLL : L₀' ≤ L) (hΩ : G L Ω) (hΩ₁ : ‖Ω‖ = 1) (hm₀ : 4 ≤ m₀) (hA₀ : 1 ≤ A₀)
    (ha : a ≤ angularConstant / 2) (Bl : RepaintingBaseline GuideLabel) (d : ℝ × ℝ) {t : ℝ}
    (ht : 0 < t) (htD : t = D * Real.log L) (htn : t ≤ Bl.n) (hnL : Bl.n ≤ A₀ * L)
    (hε2 : 2 * ε₀ ≤ angularConstant / 2) {fb fa : ℝ × ℝ → GuideLabel}
    (hfb : IsDisplacedReading fb (shiftGuide d (homogenize (cornerTreated Bl.n t) Bl.oldLabel
      Bl.guide)) ((1 : ℝ), (1 : ℝ)))
    (hfa : IsDisplacedReading fa (shiftGuide d (homogenize (cornerTreated Bl.n t) Bl.oldLabel
      Bl.centralGuide)) ((1 : ℝ), (1 : ℝ)))
    {Vb Va : Finset (ℝ × ℝ)} (hmb : ∀ z, z ∈ Vb ↔ IsTrueVertex fb z)
    (hma : ∀ z, z ∈ Va ↔ IsTrueVertex fa z)
    (P : AdaptivePatchSupply (cellCenterPos L) Ω B₀ C c 60 L)
    (hr : ∀ _ : ℝ × ℝ, 0 < ε₀ * t ∧ ε₀ * t ≤ B₀ * Real.log L)
    (hdb : (Vb : Set (ℝ × ℝ)).Pairwise fun z z' =>
      Disjoint (suppliedPatch P _ hr z).outer (suppliedPatch P _ hr z').outer)
    (hda : (Va : Set (ℝ × ℝ)).Pairwise fun z z' =>
      Disjoint (suppliedPatch P _ hr z).outer (suppliedPatch P _ hr z').outer)
    (own : GuideLabel → ProtocolParty k) (rank : GuideLabel → ℕ)
    {S : Set (ProtocolParty k)} (hPS : own Bl.oldLabel ∈ S) (hQS : own Bl.finalLabel ∈ S)
    {r K rs : ℕ} (hK : 1 ≤ K) (hrs : 1 ≤ rs) :
    HasFrameChange Ω
      (guideFrame (cellCenterPos L) q fb own guidePlaceholder rank Vb (suppliedPatch P _ hr) hdb)
      (guideFrame (cellCenterPos L) q fa own guidePlaceholder rank Va (suppliedPatch P _ hr) hda)
      S r K rs ((L : ℝ) ^ (-30 : ℤ)) := by
  classical
  have hδ : 0 < angularConstant * t := mul_pos angularConstant_pos ht
  have hiff : ∀ z, IsTrueVertex (shiftGuide d (homogenize (cornerTreated Bl.n t) Bl.oldLabel
      Bl.guide)) z ↔ IsTrueVertex (shiftGuide d (homogenize (cornerTreated Bl.n t) Bl.oldLabel
        Bl.centralGuide)) z := fun z => by
    rw [isTrueVertex_shiftGuide_iff, isTrueVertex_shiftGuide_iff]
    exact (Bl.isTrueVertex_central_treated ht htn (z - d)).1
  have hfar : ∀ z, IsTrueVertex (shiftGuide d (homogenize (cornerTreated Bl.n t) Bl.oldLabel
      Bl.guide)) z → ∀ y ∈ closure {p | shiftGuide d (homogenize (cornerTreated Bl.n t)
        Bl.oldLabel Bl.guide) p ≠ shiftGuide d (homogenize (cornerTreated Bl.n t) Bl.oldLabel
          Bl.centralGuide) p}, angularConstant * t ≤ dist z y := fun z hz y hy => by
    rw [isTrueVertex_shiftGuide_iff] at hz
    have := ((Bl.isTrueVertex_central_treated ht htn (z - d)).2 hz).2 (y - d)
      (sub_mem_closure hy)
    rwa [dist_sub_right] at this
  obtain ⟨hV, hinc⟩ := readings_isTrueVertex_iff_of_far hfb hfa hiff hfar hδ
  have hkey : ∀ p, fb p ≠ fa p → fb p = Bl.oldLabel ∧ fa p = Bl.finalLabel := fun p hp =>
    hfb.values_of_ne hδ hfa (fun x hx => by
      obtain ⟨m1, m2⟩ := Bl.central_treated_mem htn hx
      exact ⟨m1, m2⟩) hp
  have hTfar : ∀ z, IsTrueVertex fb z → ∀ p, fb p ≠ fa p → 2 * ε₀ * t < dist z p :=
    fun z hz p hp => by
      have := hfar z (hfb.isTrueVertex hz) p (hfb.ne_subset_closure hfa hp)
      nlinarith [angularConstant_pos]
  have hTdiam : ∀ p p', fb p ≠ fa p → fb p' ≠ fa p' → dist p p' ≤ Bl.n := fun p p' hp hp' => by
    have hsub : ∀ x, fb x ≠ fa x → x - d ∈ closedSquare Bl.n := fun x hx =>
      closure_minimal (Bl.central_treated_ne_subset t) (isClosed_Icc.prod isClosed_Icc)
        (sub_mem_closure_ne_of_reading_ne hfb hfa hx)
    obtain ⟨⟨a1, a2⟩, a3, a4⟩ := hsub p hp
    obtain ⟨⟨b1, b2⟩, b3, b4⟩ := hsub p' hp'
    rw [← dist_sub_right p p' d, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    simp only [Prod.fst_sub, Prod.snd_sub] at *
    exact max_le (abs_le.2 ⟨by linarith, by linarith⟩) (abs_le.2 ⟨by linarith, by linarith⟩)
  have hVV : Va = Vb := Finset.ext fun z => by rw [hma, hmb, hV]
  set T : Finset (SquareLatticeVertex L L) :=
    Finset.univ.filter fun x => fb (cellCenterPos L x) ≠ fa (cellCenterPos L x)
  have hafter : guideFrame (cellCenterPos L) q fa own guidePlaceholder rank Va
      (suppliedPatch P _ hr) hda =
      (guideFrame (cellCenterPos L) q fb own guidePlaceholder rank Vb
        (suppliedPatch P _ hr) hdb).changeOwner T (own Bl.finalLabel) :=
    guideFrame_eq_changeOwner_of_ne (fun x => by simp [T]) hVV (fun x hx => (hkey _ hx).2)
      fun z hz => (hinc z ((hmb z).1 hz)).symm
  rw [hafter]
  subst htD
  obtain ⟨w, hw, hu, hs, herr⟩ := centralBirth_step_guideFrame (L := L)
    (hole := suppliedPatch P _ hr)
    (V := Vb) (hV := hdb) (own := own) (ph := guidePlaceholder) (rank := rank)
    hD hLL hΩ hΩ₁ (fun v => cellCenterPos_eq_sitePosition_add v) hm₀ ha Bl d
    ((1 : ℝ), (1 : ℝ)) ht.le htn hnL hε2 hfb hfa (fun z hz => (hmb z).1 hz)
    (fun z _ => ⟨suppliedPatch_center P hr z, by simp⟩) (T := T)
    (Q := own Bl.finalLabel)
    (fun x hx => by
      have hx' : fb (cellCenterPos L x) ≠ fa (cellCenterPos L x) := by simpa [T] using hx
      rw [(hkey _ hx').1])
    (disjoint_outerHoles_guideFrame (g := fb) (V := Vb) (hV := hdb)
      (T := (T : Set _)) fun z hz x hx => by
      have hx' : fb (cellCenterPos L x) ≠ fa (cellCenterPos L x) := by simpa [T] using hx
      simpa only [suppliedPatch_center, suppliedPatch_scale, mul_assoc] using
        hTfar z ((hmb z).1 hz) _ hx')
    (fun x hx y hy => by
      have hx' : fb (cellCenterPos L x) ≠ fa (cellCenterPos L x) := by simpa [T] using hx
      have hy' : fb (cellCenterPos L y) ≠ fa (cellCenterPos L y) := by simpa [T] using hy
      exact (hTdiam _ _ hx' hy').trans (le_mul_of_one_le_left (ht.le.trans htn) hA₀))
    (fun x hx => by simpa [T] using hx)
  refine ⟨w.toOriginalCircuit hw, (Word.isBoundedChange_toOriginalCircuit hw hu hs hK
    (by exact herr)).mono ?_ le_rfl le_rfl le_rfl,
    w.isSourceBounded_toOriginalCircuit_of_one_le hw hrs⟩
  rintro x (rfl | rfl)
  exacts [hPS, hQS]

/-- **The central birth as a change of the main sheet, conditional on Proposition 3.4.** Assume
`q ≥ 1`, a unit state of the family `G`, and the exponent-`60` angular-scale condition with
`L₀' ≤ L`, `m₀ ≥ 4` and `A₀ ≥ 1`. At the protocol constants, take `L ≥ 2`, `2 ^ k < 2 * L`, an
exponent-`60` adaptive patch supply, any rank and any already-repainted set. For a repaintable
square `R` of side `n = 2 ^ j > K₀ t`, where `t = D log L`, pass from its starting frame to its
central frame, both treated with the old label about the four corners. This has participants
in any set containing the old and final parties, error `L⁻³⁰`, arbitrary natural pair-effect
bound `r`, and any `K, rs ≥ 1`. Both the monomial count and absolute coefficient sum are
bounded by `K`; one pair source suffices. There is no premise that `R` is absent from the
already-repainted set.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 155–160, 328–387 and 440–445; Lemma 6.5
`lem:birth`, `05-frames.tex`. -/
theorem centralBirth_hasFrameChange (hD : IsAngularScale q G a A₀ m₀ 60 D L₀') (hLL : L₀' ≤ L)
    (hΩ : G L Ω) (hΩ₁ : ‖Ω‖ = 1) (hm₀ : 4 ≤ m₀) (hA₀ : 1 ≤ A₀)
    (hc : IsProtocolConstants K₀ ε₀ ν a D B₀) (hL : 2 ≤ L) (hk2 : 2 ^ k < 2 * L)
    (P : AdaptivePatchSupply (cellCenterPos L) Ω B₀ C c 60 L) (rank : GuideLabel → ℕ)
    (R : RepaintedSquare k) (hlarge : K₀ * (D * Real.log L) < (2 : ℝ) ^ (R.1.1 : ℕ))
    (done : Set (ℤ × ℤ))
    {S : Set (ProtocolParty k)}
    (hPS : labelParty R (protocolLevelLabels k R.1.1 done R.1.index) ∈ S)
    (hQS : labelParty R (newParty Sum.inl R.1.1 R.1.index) ∈ S)
    {r K rs : ℕ} (hK : 1 ≤ K) (hrs : 1 ≤ rs) :
    HasFrameChange Ω
      (treatedFrame (q := q) P rank R (hc.treatedRadius_bounds hL) (cornerBlocks R.1.index)
        (protocolLevelLabels k R.1.1 done R.1.index)
        (blockBaseline (n := (2 : ℝ) ^ (R.1.1 : ℕ)) (by positivity)
          (protocolLevelLabels k R.1.1 done) R.1.index (newParty Sum.inl R.1.1 R.1.index)).guide)
      (treatedFrame (q := q) P rank R (hc.treatedRadius_bounds hL) (cornerBlocks R.1.index)
        (protocolLevelLabels k R.1.1 done R.1.index)
        (blockBaseline (n := (2 : ℝ) ^ (R.1.1 : ℕ)) (by positivity)
          (protocolLevelLabels k R.1.1 done) R.1.index
          (newParty Sum.inl R.1.1 R.1.index)).centralGuide) S r K rs
      ((L : ℝ) ^ (-30 : ℤ)) := by
  have hr := hc.treatedRadius_bounds hL
  have hn : (0 : ℝ) < 2 ^ (R.1.1 : ℕ) := by positivity
  have hℓ : 0 < Real.log L := Real.log_pos (by exact_mod_cast hL)
  have ht : 0 < D * Real.log L := mul_pos hc.D_pos hℓ
  have hε2 : 2 * ε₀ ≤ angularConstant / 2 := by
    have := hc.ε₀_small; have := hc.ε₀_pos; nlinarith [angularConstant_pos]
  obtain ⟨hfb, hmb, hdb, hFb⟩ := treatedFrame_spec (q := q) P rank R hc hL hlarge done
    (Or.inl rfl) (cornerBlocks R.1.index) (protocolLevelLabels k R.1.1 done R.1.index)
  obtain ⟨hfa, hma, hda, hFa⟩ := treatedFrame_spec (q := q) P rank R hc hL hlarge done
    (Or.inr (Or.inl rfl)) (cornerBlocks R.1.index) (protocolLevelLabels k R.1.1 done R.1.index)
  rw [homogenize_cornerBlocks] at hfb hfa
  rw [hFb, hFa]
  exact centralBirth_hasFrameChange_of hD hLL hΩ hΩ₁ hm₀ hA₀ hc.a_le
    (blockBaseline (n := (2 : ℝ) ^ (R.1.1 : ℕ)) (by positivity)
      (protocolLevelLabels k R.1.1 done) R.1.index (newParty Sum.inl R.1.1 R.1.index))
    (blockCorner ((2 : ℝ) ^ (R.1.1 : ℕ)) R.1.index) ht rfl
    (by change D * Real.log L ≤ (2 : ℝ) ^ (R.1.1 : ℕ); nlinarith [hc.twenty_le_K₀, hlarge, ht])
    (le_mul_of_one_le_left (by positivity) hA₀ |>.trans' (R.side_le hk2))
    hε2 hfb hfa hmb hma P hr hdb hda _ rank hPS hQS hK hrs

end Changes

end TNLean.PEPS.Approximation
