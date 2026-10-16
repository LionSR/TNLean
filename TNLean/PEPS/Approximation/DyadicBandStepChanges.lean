/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicBulkFrames

/-!
# Births and deaths along an edge as changes of a treated sheet

Along an edge `e` of a square `S` repainted at scale `n > K₀ t`, the protocol of Proposition 7.1
of the polynomial-PEPS manuscript performs elementary births and deaths on a sheet whose guide is
`bandUpdate n e W g₀`, after homogenizing it to the surrounding label `P∘` on the squares of
radius `t` about the two endpoints of `e` (`06-geometry.tex`, lines 183–221 and 328–387). This
file proves that such a birth or death is a bounded change between the frames of the treated
guides before and after it, conditional on Proposition 3.4 through `IsAngularScale`:

* `BandOperation.treated_mem` : near the closed changed region the two treated guides take only
  the surrounding label and the inserted label, and the surrounding guide is `P∘`;
* `bandBirth_hasFrameChange` : a birth;
* `bandDeath_hasFrameChange` : a death.

## References

* Polynomial-PEPS manuscript (September 24, 2026), §7, `06-geometry.tex`: guides and sampling
  (lines 69–80), the holes and tags (lines 109–125), the edge construction (lines 183–221), the
  point treatment and the bulk operations (lines 328–387 and 440–445); Lemma 6.5 `lem:birth`,
  `05-frames.tex`.
-/

noncomputable section

open Set Metric Filter Topology

namespace TNLean.PEPS.Approximation

open EncodedFrame PairEffect

/-- **Values of readings near a change.** If on the open `δ`-neighborhood of the set where two
labellings differ the first is `A` and the second takes only `A` and `B`, then at every point where
their readings, moved by `d`, differ, the first reading is `A` and the second `B`. -/
theorem IsDisplacedReading.values_of_ne {κ : Type*} {Hb Ha fb fa : ℝ × ℝ → κ} {d : ℝ × ℝ}
    {δ : ℝ} (hδ : 0 < δ) {A B : κ}
    (hfb : IsDisplacedReading fb (shiftGuide d Hb) ((1 : ℝ), (1 : ℝ)))
    (hfa : IsDisplacedReading fa (shiftGuide d Ha) ((1 : ℝ), (1 : ℝ)))
    (hval : ∀ x ∈ thickening δ {x | Hb x ≠ Ha x}, Hb x = A ∧ (Ha x = A ∨ Ha x = B))
    {p : ℝ × ℝ} (hp : fb p ≠ fa p) : fb p = A ∧ fa p = B := by
  have hcl : p - d ∈ closure {x | Hb x ≠ Ha x} := sub_mem_closure (hfb.ne_subset_closure hfa hp)
  have h1 : p - d ∈ thickening δ {x | Hb x ≠ Ha x} := closure_subset_thickening hδ _ hcl
  have hO : IsOpen ((fun x : ℝ × ℝ => x - d) ⁻¹' thickening δ {x | Hb x ≠ Ha x}) :=
    isOpen_thickening.preimage (continuous_id.sub continuous_const)
  have hU : (fun x => x - d) ⁻¹' thickening δ {x | Hb x ≠ Ha x} ∈ 𝓝 p := hO.mem_nhds h1
  obtain ⟨ε, e1, e2, hmem⟩ :=
    ((hfb p).and ((hfa p).and (tendsto_add_smul_nhdsGT p _ hU))).exists
  obtain ⟨m1, m2⟩ := hval _ hmem
  have h1 : fb p = A := e1.trans m1
  refine ⟨h1, ?_⟩
  rcases m2 with m2 | m2
  · exact absurd (h1.trans (e2.trans m2).symm) hp
  · exact e2.trans m2

section Values

variable {ι : Type*} {op : BandOperation ι} {Q : ι} {n t : ℝ} {e : SquareEdge}
  {g : ℝ × ℝ → ι}

/-- **Values near the change.** Near the closure of the remaining changed region of a treated
birth or death that inserts the single label `Q`, the treated guides before and after take only
the surrounding label `P∘` and `Q`, and the treated surrounding guide is `P∘`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 375–382. -/
theorem BandOperation.treated_mem (hop : op.InsertsOne Q) (htn : t ≤ n) {p : ℝ × ℝ}
    (hp : p ∈ thickening (angularConstant * t)
      {p | homogenize (edgeTreated n e t) op.label (bandUpdate n e op.before g) p ≠
        homogenize (edgeTreated n e t) op.label (bandUpdate n e op.after g) p}) :
    homogenize (edgeTreated n e t) op.label (bandUpdate n e op.before g) p ∈
        ({op.label, Q} : Set ι) ∧
      homogenize (edgeTreated n e t) op.label (bandUpdate n e op.after g) p ∈
        ({op.label, Q} : Set ι) ∧
      homogenize (edgeTreated n e t) op.label (bandUpdate n e op.surrounding g) p = op.label := by
  have hs := op.treated_surrounding_eq htn e g hp
  refine ⟨?_, ?_, hs⟩ <;>
  · by_cases hpR : homogenize (edgeTreated n e t) op.label (bandUpdate n e op.before g) p ≠
        homogenize (edgeTreated n e t) op.label (bandUpdate n e op.after g) p
    · have hpU : p ∉ edgeTreated n e t := fun h => hpR (by simp only [homogenize_of_mem h])
      have hpB : p ∈ edgeBand n e (-8) 2 := by
        by_contra hb
        exact hpR (by simp only [homogenize_of_notMem hpU, bandUpdate_of_notMem hb])
      have hne : op.before (bandCoord n e p) ≠ op.after (bandCoord n e p) := by
        simpa only [homogenize_of_notMem hpU, bandUpdate_of_mem hpB] using hpR
      simp only [homogenize_of_notMem hpU, bandUpdate_of_mem hpB]
      first
        | exact (hop.changed_mem _ hne).1
        | exact (hop.changed_mem _ hne).2
    · have heq := not_not.1 hpR
      rcases hop.surrounding_eq with h | h
      · rw [h] at hs
        first | exact Or.inl hs | exact Or.inl (heq ▸ hs)
      · rw [h] at hs
        first | exact Or.inl (heq.trans hs) | exact Or.inl hs

/-- The changed region of a treated birth or death lies in the band of its edge. -/
theorem BandOperation.treated_ne_subset (op : BandOperation ι) :
    {p | homogenize (edgeTreated n e t) op.label (bandUpdate n e op.before g) p ≠
        homogenize (edgeTreated n e t) op.label (bandUpdate n e op.after g) p} ⊆
      edgeBand n e (-8) 2 := by
  intro p hpR
  have hpU : p ∉ edgeTreated n e t := fun h => hpR (by simp only [homogenize_of_mem h])
  by_contra hb
  exact hpR (by simp only [homogenize_of_notMem hpU, bandUpdate_of_notMem hb])

end Values


section Changes

variable {k q : ℕ} [NeZero q] {J Δ a A₀ D L₀' : ℝ} {m₀ : ℕ} {L : ℕ}
  {h : SquareHamiltonian L q J} {E₀ : ℝ} {Ω : StateSpace L q} {K₀ ε₀ ν B₀ C c : ℝ}

/-- **The sites of a treated birth or death.** In the setting of `bandBirth_hasFrameChange`, at a
point where the readings of the treated guides before and after an elementary birth or death that
inserts `Q` differ, the reading of the treated surrounding guide is the surrounding label `P∘`, and
the reading of the other guide is `Q`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 76–80 and 375–387. -/
theorem BandOperation.readings_of_ne {op : BandOperation GuideLabel} {Q : GuideLabel}
    (hop : op.InsertsOne Q) {n t : ℝ} (ht : 0 < t) (htn : t ≤ n) (e : SquareEdge)
    (g₀ : ℝ × ℝ → GuideLabel) (d : ℝ × ℝ) {fb fa fs : ℝ × ℝ → GuideLabel}
    (hfb : IsDisplacedReading fb (shiftGuide d
      (homogenize (edgeTreated n e t) op.label (bandUpdate n e op.before g₀))) ((1 : ℝ), (1 : ℝ)))
    (hfa : IsDisplacedReading fa (shiftGuide d
      (homogenize (edgeTreated n e t) op.label (bandUpdate n e op.after g₀))) ((1 : ℝ), (1 : ℝ)))
    (hfs : IsDisplacedReading fs (shiftGuide d
      (homogenize (edgeTreated n e t) op.label (bandUpdate n e op.surrounding g₀)))
        ((1 : ℝ), (1 : ℝ)))
    {p : ℝ × ℝ} (hp : fb p ≠ fa p) :
    fs p = op.label ∧ fb p ∈ ({op.label, Q} : Set GuideLabel) ∧
      fa p ∈ ({op.label, Q} : Set GuideLabel) := by
  set R := {p | homogenize (edgeTreated n e t) op.label (bandUpdate n e op.before g₀) p ≠
    homogenize (edgeTreated n e t) op.label (bandUpdate n e op.after g₀) p}
  have hδ : 0 < angularConstant * t := mul_pos angularConstant_pos ht
  have hcl := hfb.ne_subset_closure hfa hp
  have hpre : {x | shiftGuide d (homogenize (edgeTreated n e t) op.label
      (bandUpdate n e op.before g₀)) x ≠ shiftGuide d (homogenize (edgeTreated n e t) op.label
      (bandUpdate n e op.after g₀)) x} = (· - d) ⁻¹' R := rfl
  rw [hpre] at hcl
  have hU : (· - d) ⁻¹' thickening (angularConstant * t) R ∈ 𝓝 p :=
    (isOpen_thickening.preimage (continuous_id.sub continuous_const)).mem_nhds
      (closure_subset_thickening hδ R (sub_mem_closure hcl))
  obtain ⟨ε, e1, e2, e3, hmem⟩ :=
    ((hfb p).and ((hfa p).and ((hfs p).and (tendsto_add_smul_nhdsGT p _ hU)))).exists
  obtain ⟨m1, m2, m3⟩ := op.treated_mem hop htn hmem
  refine ⟨?_, ?_, ?_⟩
  · rw [e3]; exact m3
  · rw [e1]; exact m1
  · rw [e2]; exact m2

/-- **The facts shared by a birth and a death.** In the setting of `bandBirth_hasFrameChange`, the
readings of the treated guides before and after have the same true vertices with the same incident
labels, their sites of change lie outside every outer hole and within distance `n` of each other,
and at those sites the surrounding guide reads `P∘` and the other guide `Q`. -/
theorem BandOperation.treated_frame_facts {op : BandOperation GuideLabel} {Q : GuideLabel}
    (hop : op.InsertsOne Q) {n t ε₀ : ℝ} (ht : 0 < t) (htn : t ≤ n)
    (hε : 2 * ε₀ < angularConstant) (e : SquareEdge) (g₀ : ℝ × ℝ → GuideLabel) (d : ℝ × ℝ)
    {fb fa : ℝ × ℝ → GuideLabel}
    (hfb : IsDisplacedReading fb (shiftGuide d
      (homogenize (edgeTreated n e t) op.label (bandUpdate n e op.before g₀))) ((1 : ℝ), (1 : ℝ)))
    (hfa : IsDisplacedReading fa (shiftGuide d
      (homogenize (edgeTreated n e t) op.label (bandUpdate n e op.after g₀))) ((1 : ℝ), (1 : ℝ))) :
    (∀ z, IsTrueVertex fb z ↔ IsTrueVertex fa z) ∧
      (∀ z, IsTrueVertex fb z → incidentLabels fb z = incidentLabels fa z) ∧
      (∀ z, IsTrueVertex fb z → ∀ p, fb p ≠ fa p → 2 * ε₀ * t < dist z p) ∧
      (∀ p p', fb p ≠ fa p → fb p' ≠ fa p' → dist p p' ≤ n) := by
  set Hb := homogenize (edgeTreated n e t) op.label (bandUpdate n e op.before g₀)
  set Ha := homogenize (edgeTreated n e t) op.label (bandUpdate n e op.after g₀)
  have hδ : 0 < angularConstant * t := mul_pos angularConstant_pos ht
  have hiff : ∀ z, IsTrueVertex (shiftGuide d Hb) z ↔ IsTrueVertex (shiftGuide d Ha) z :=
    fun z => by
      rw [isTrueVertex_shiftGuide_iff, isTrueVertex_shiftGuide_iff]
      exact (op.isTrueVertex_treated hop ht htn e g₀ (z - d)).1
  have hfar : ∀ z, IsTrueVertex (shiftGuide d Hb) z →
      ∀ y ∈ closure {p | shiftGuide d Hb p ≠ shiftGuide d Ha p},
        angularConstant * t ≤ dist z y := fun z hz y hy => by
    rw [isTrueVertex_shiftGuide_iff] at hz
    have := ((op.isTrueVertex_treated hop ht htn e g₀ (z - d)).2 hz).2 (y - d)
      (sub_mem_closure hy)
    rwa [dist_sub_right] at this
  obtain ⟨hV, hinc⟩ := readings_isTrueVertex_iff_of_far hfb hfa hiff hfar hδ
  refine ⟨hV, hinc, fun z hz p hp => ?_, fun p p' hp hp' => ?_⟩
  · have := hfar z (hfb.isTrueVertex hz) p (hfb.ne_subset_closure hfa hp)
    nlinarith
  · have hsub : ∀ x, fb x ≠ fa x → x - d ∈ closedEdgeBand n e (-8) 2 := fun x hx =>
      closure_edgeBand_subset n e (-8) 2 (closure_mono (op.treated_ne_subset (n := n) (t := t)
        (e := e) (g := g₀)) (sub_mem_closure (hfb.ne_subset_closure hfa hx)))
    have := dist_le_of_mem_closedEdgeBand (by norm_num) (by norm_num) (hsub p hp) (hsub p' hp')
    rwa [dist_sub_right] at this

/-- **A birth along an edge as a change of a treated sheet, conditional on Proposition 3.4.** At
the constants of the protocol, in the repainting of a square `R` of side `n = 2 ^ j > K₀ t`,
`t = D log L`, let an elementary birth inserting the label `Q` change the guide
`bandUpdate n e op.before g₀` of a sheet into `bandUpdate n e op.after g₀`, both unmodified guides
of the repainting, with the surrounding guide the guide before. If the parties of the surrounding
label and of `Q` lie in `S`, then passing from the frame of the guide before, treated about the
endpoints of `e`, to that of the guide after is a bounded change with participants in `S`, with
at most one pair source and error `L⁻³⁰`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 183–221, 328–387 and 440–445; Lemma 6.5
`lem:birth`, `05-frames.tex`. -/
theorem bandBirth_hasFrameChange (hD : IsAngularScale q J Δ a A₀ m₀ 60 D L₀') (hLL : L₀' ≤ L)
    (hΩ : h.IsGappedGroundState E₀ Ω Δ) (hm₀ : 2 ≤ m₀) (hA₀ : 1 ≤ A₀)
    (hc : IsProtocolConstants K₀ ε₀ ν a D B₀) (hL : 2 ≤ L) (hk2 : 2 ^ k < 2 * L)
    (P : AdaptivePatchSupply (cellCenterPos L) Ω B₀ C c 60 L) (rank : GuideLabel → ℕ)
    (R : RepaintedSquare k) (hlarge : K₀ * (D * Real.log L) < (2 : ℝ) ^ (R.1.1 : ℕ))
    (done : Set (ℤ × ℤ)) {op : BandOperation GuideLabel} {Q : GuideLabel} (hop : op.InsertsOne Q)
    (hbirth : op.surrounding = op.before) (e : SquareEdge) {g₀ : ℝ × ℝ → GuideLabel}
    (hgb : (blockBaseline (n := (2 : ℝ) ^ (R.1.1 : ℕ)) (by positivity)
      (protocolLevelLabels k R.1.1 done) R.1.index
      (newParty Sum.inl R.1.1 R.1.index)).IsUnmodifiedGuide
        (bandUpdate ((2 : ℝ) ^ (R.1.1 : ℕ)) e op.before g₀))
    (hga : (blockBaseline (n := (2 : ℝ) ^ (R.1.1 : ℕ)) (by positivity)
      (protocolLevelLabels k R.1.1 done) R.1.index
      (newParty Sum.inl R.1.1 R.1.index)).IsUnmodifiedGuide
        (bandUpdate ((2 : ℝ) ^ (R.1.1 : ℕ)) e op.after g₀))
    {S : Set (ProtocolParty k)} (hPS : labelParty R op.label ∈ S) (hQS : labelParty R Q ∈ S)
    {r K rs : ℕ} (hK : 1 ≤ K) (hrs : 1 ≤ rs) :
    HasFrameChange Ω
      (treatedFrame (q := q) P rank R (hc.treatedRadius_bounds hL)
        (e.endpointBlocks R.1.index) op.label
        (bandUpdate ((2 : ℝ) ^ (R.1.1 : ℕ)) e op.before g₀))
      (treatedFrame (q := q) P rank R (hc.treatedRadius_bounds hL)
        (e.endpointBlocks R.1.index) op.label
        (bandUpdate ((2 : ℝ) ^ (R.1.1 : ℕ)) e op.after g₀)) S r K rs ((L : ℝ) ^ (-30 : ℤ)) := by
  have hr := hc.treatedRadius_bounds hL
  classical
  set n : ℝ := (2 : ℝ) ^ (R.1.1 : ℕ) with hn_def
  set t := D * Real.log L with ht_def
  set d := blockCorner n R.1.index with hd_def
  have hn : 0 < n := by positivity
  have hℓ : 0 < Real.log L := Real.log_pos (by exact_mod_cast hL)
  have ht : 0 < t := mul_pos hc.D_pos hℓ
  have htn : t ≤ n := by nlinarith [hc.twenty_le_K₀]
  have hε2 : 2 * ε₀ ≤ angularConstant / 2 := by
    have := hc.ε₀_small; have := hc.ε₀_pos; nlinarith [angularConstant_pos]
  obtain ⟨hfb, hmb, hdb, hFb⟩ := treatedFrame_spec (q := q) P rank R hc hL hlarge done hgb
    (e.endpointBlocks R.1.index) op.label hr
  obtain ⟨hfa, hma, hda, hFa⟩ := treatedFrame_spec (q := q) P rank R hc hL hlarge done hga
    (e.endpointBlocks R.1.index) op.label hr
  rw [homogenize_endpointBlocks] at hfb hfa
  set fb := treatedGuide R.1.1 R.1.index t (e.endpointBlocks R.1.index) op.label
    (bandUpdate n e op.before g₀)
  set fa := treatedGuide R.1.1 R.1.index t (e.endpointBlocks R.1.index) op.label
    (bandUpdate n e op.after g₀)
  obtain ⟨hV, hinc, hTfar, hTdiam⟩ := op.treated_frame_facts (ε₀ := ε₀) hop ht htn
    (by linarith [angularConstant_pos]) e g₀ d hfb hfa
  have hfs : IsDisplacedReading fb (shiftGuide d (homogenize (edgeTreated n e t) op.label
      (bandUpdate n e op.surrounding g₀))) ((1 : ℝ), (1 : ℝ)) := by rw [hbirth]; exact hfb
  have hkey : ∀ p, fb p ≠ fa p → fb p = op.label ∧ fa p = Q := fun p hp => by
    obtain ⟨h1, -, h3⟩ := op.readings_of_ne hop ht htn e g₀ d hfb hfa hfs hp
    refine ⟨h1, ?_⟩
    rcases h3 with h3 | h3
    · exact absurd (h1.trans h3.symm) hp
    · exact h3
  set Vb := treatedVertices k R.1.1 t (e.endpointBlocks R.1.index) fb
  set Va := treatedVertices k R.1.1 t (e.endpointBlocks R.1.index) fa
  have hVV : Va = Vb := Finset.ext fun z => by rw [hma, hmb, hV]
  set T : Finset (SquareLatticeVertex L L) :=
    Finset.univ.filter fun x => fb (cellCenterPos L x) ≠ fa (cellCenterPos L x)
  have hafter : guideFrame (cellCenterPos L) q fa (labelParty R) guidePlaceholder rank Va
      (suppliedPatch P _ hr) hda =
      (guideFrame (cellCenterPos L) q fb (labelParty R) guidePlaceholder rank Vb
        (suppliedPatch P _ hr) hdb).changeOwner T (labelParty R Q) := by
    rw [guideFrame_congr_guide (g' := fa) (hV' := by rw [← hVV]; exact hda) rfl hVV
      (fun _ _ => rfl)]
    refine guideFrame_eq_changeOwner (fun x => ?_) (fun z hz => ?_)
    · by_cases hx : fb (cellCenterPos L x) = fa (cellCenterPos L x)
      · have : x ∉ T := by simp [T, hx]
        rw [ite_eq_right this, hx]
      · have : x ∈ T := by simp [T, hx]
        rw [ite_eq_left this, (hkey _ hx).2]
    · exact (tagHolder_congr (hinc z ((hmb z).1 hz))).symm
  rw [hFb, hFa, hafter]
  obtain ⟨w, hw, hu, hs, herr⟩ := bandBirth_step_guideFrame (L := L) (hole := suppliedPatch P _ hr)
    (V := Vb) (hV := hdb) (own := labelParty R) (ph := guidePlaceholder) (rank := rank)
    hD hLL hΩ (fun v => cellCenterPos_eq_sitePosition_add v) hm₀ hc.a_le op e g₀ d
    ((1 : ℝ), (1 : ℝ)) ht.le htn (le_mul_of_one_le_left (by positivity) hA₀ |>.trans' (by
      have hk : (R.1.1 : ℕ) + 1 ≤ k := R.2
      have h1 : n * 2 ≤ 2 ^ k := by
        rw [hn_def, ← pow_succ]; exact pow_le_pow_right₀ (by norm_num) hk
      have h2 : (2 : ℝ) ^ k < 2 * L := by exact_mod_cast hk2
      linarith)) hε2 hfs hfb hfa (fun z hz => (hmb z).1 hz)
    (fun z _ => ⟨suppliedPatch_center P hr z, by simp [ht_def]⟩) (T := T) (Q := labelParty R Q)
    (fun x hx => by
      have hx' : fb (cellCenterPos L x) ≠ fa (cellCenterPos L x) := by simpa [T] using hx
      rw [(hkey _ hx').1])
    (Set.disjoint_left.2 fun x hx hxo => by
      have hx' : fb (cellCenterPos L x) ≠ fa (cellCenterPos L x) := by simpa [T] using hx
      obtain ⟨p, hp, hxp⟩ := hxo
      obtain ⟨hl, hhl, rfl⟩ := List.mem_map.1 hp
      obtain ⟨z, hz, rfl⟩ := mem_holes_guideFrame.1 hhl
      have hd : dist (cellCenterPos L x) z ≤ 2 * (ε₀ * t) := by
        simpa [SquarePatch.outer, squareSample] using hxp
      have := hTfar z ((hmb z).1 hz) _ hx'
      rw [dist_comm] at this
      linarith)
    (fun x hx y hy => by
      have hx' : fb (cellCenterPos L x) ≠ fa (cellCenterPos L x) := by simpa [T] using hx
      have hy' : fb (cellCenterPos L y) ≠ fa (cellCenterPos L y) := by simpa [T] using hy
      exact (hTdiam _ _ hx' hy').trans (le_mul_of_one_le_left hn.le hA₀))
    (fun x hx => by simpa [T] using hx)
  refine ⟨w.toOriginalCircuit hw, (Word.isBoundedChange_toOriginalCircuit hw hu hs hK
    (by exact herr)).mono ?_ le_rfl le_rfl le_rfl,
    w.isSourceBounded_toOriginalCircuit_of_one_le hw hrs⟩
  rintro x (rfl | rfl)
  exacts [hPS, hQS]

/-- **A death along an edge as a change of a treated sheet, conditional on Proposition 3.4.** At
the constants of the protocol, in the repainting of a square `R` of side `n = 2 ^ j > K₀ t`,
`t = D log L`, let an elementary death removing the label `Q` change the guide
`bandUpdate n e op.before g₀` of a sheet into `bandUpdate n e op.after g₀`, both unmodified guides
of the repainting, with the surrounding guide the guide after. If the parties of the surrounding
label and of `Q` lie in `S`, then passing from the frame of the guide before, treated about the
endpoints of `e`, to that of the guide after is a bounded change with participants in `S`, with
at most one pair source and error `L⁻³⁰`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 183–221, 328–387 and 440–445; Lemma 6.5
`lem:birth`, `05-frames.tex`. -/
theorem bandDeath_hasFrameChange (hD : IsAngularScale q J Δ a A₀ m₀ 60 D L₀') (hLL : L₀' ≤ L)
    (hΩ : h.IsGappedGroundState E₀ Ω Δ) (hm₀ : 2 ≤ m₀) (hA₀ : 1 ≤ A₀)
    (hc : IsProtocolConstants K₀ ε₀ ν a D B₀) (hL : 2 ≤ L) (hk2 : 2 ^ k < 2 * L)
    (P : AdaptivePatchSupply (cellCenterPos L) Ω B₀ C c 60 L) (rank : GuideLabel → ℕ)
    (R : RepaintedSquare k) (hlarge : K₀ * (D * Real.log L) < (2 : ℝ) ^ (R.1.1 : ℕ))
    (done : Set (ℤ × ℤ)) {op : BandOperation GuideLabel} {Q : GuideLabel} (hop : op.InsertsOne Q)
    (hdeath : op.surrounding = op.after) (e : SquareEdge) {g₀ : ℝ × ℝ → GuideLabel}
    (hgb : (blockBaseline (n := (2 : ℝ) ^ (R.1.1 : ℕ)) (by positivity)
      (protocolLevelLabels k R.1.1 done) R.1.index
      (newParty Sum.inl R.1.1 R.1.index)).IsUnmodifiedGuide
        (bandUpdate ((2 : ℝ) ^ (R.1.1 : ℕ)) e op.before g₀))
    (hga : (blockBaseline (n := (2 : ℝ) ^ (R.1.1 : ℕ)) (by positivity)
      (protocolLevelLabels k R.1.1 done) R.1.index
      (newParty Sum.inl R.1.1 R.1.index)).IsUnmodifiedGuide
        (bandUpdate ((2 : ℝ) ^ (R.1.1 : ℕ)) e op.after g₀))
    {S : Set (ProtocolParty k)} (hPS : labelParty R op.label ∈ S) (hQS : labelParty R Q ∈ S)
    {r K rs : ℕ} (hr1 : 1 ≤ r) (hK : 1 ≤ K) (hrs : 1 ≤ rs) :
    HasFrameChange Ω
      (treatedFrame (q := q) P rank R (hc.treatedRadius_bounds hL)
        (e.endpointBlocks R.1.index) op.label
        (bandUpdate ((2 : ℝ) ^ (R.1.1 : ℕ)) e op.before g₀))
      (treatedFrame (q := q) P rank R (hc.treatedRadius_bounds hL)
        (e.endpointBlocks R.1.index) op.label
        (bandUpdate ((2 : ℝ) ^ (R.1.1 : ℕ)) e op.after g₀)) S r K rs ((L : ℝ) ^ (-30 : ℤ)) := by
  have hr := hc.treatedRadius_bounds hL
  classical
  set n : ℝ := (2 : ℝ) ^ (R.1.1 : ℕ) with hn_def
  set t := D * Real.log L with ht_def
  set d := blockCorner n R.1.index with hd_def
  have hn : 0 < n := by positivity
  have hℓ : 0 < Real.log L := Real.log_pos (by exact_mod_cast hL)
  have ht : 0 < t := mul_pos hc.D_pos hℓ
  have htn : t ≤ n := by nlinarith [hc.twenty_le_K₀]
  have hε2 : 2 * ε₀ ≤ angularConstant / 2 := by
    have := hc.ε₀_small; have := hc.ε₀_pos; nlinarith [angularConstant_pos]
  obtain ⟨hfb, hmb, hdb, hFb⟩ := treatedFrame_spec (q := q) P rank R hc hL hlarge done hgb
    (e.endpointBlocks R.1.index) op.label hr
  obtain ⟨hfa, hma, hda, hFa⟩ := treatedFrame_spec (q := q) P rank R hc hL hlarge done hga
    (e.endpointBlocks R.1.index) op.label hr
  rw [homogenize_endpointBlocks] at hfb hfa
  set fb := treatedGuide R.1.1 R.1.index t (e.endpointBlocks R.1.index) op.label
    (bandUpdate n e op.before g₀)
  set fa := treatedGuide R.1.1 R.1.index t (e.endpointBlocks R.1.index) op.label
    (bandUpdate n e op.after g₀)
  obtain ⟨hV, hinc, hTfar, hTdiam⟩ := op.treated_frame_facts (ε₀ := ε₀) hop ht htn
    (by linarith [angularConstant_pos]) e g₀ d hfb hfa
  have hfs : IsDisplacedReading fa (shiftGuide d (homogenize (edgeTreated n e t) op.label
      (bandUpdate n e op.surrounding g₀))) ((1 : ℝ), (1 : ℝ)) := by rw [hdeath]; exact hfa
  have hkey : ∀ p, fb p ≠ fa p → fa p = op.label ∧ fb p = Q := fun p hp => by
    obtain ⟨h1, h2, -⟩ := op.readings_of_ne hop ht htn e g₀ d hfb hfa hfs hp
    refine ⟨h1, ?_⟩
    rcases h2 with h2 | h2
    · exact absurd (h2.trans h1.symm) hp
    · exact h2
  set Vb := treatedVertices k R.1.1 t (e.endpointBlocks R.1.index) fb
  set Va := treatedVertices k R.1.1 t (e.endpointBlocks R.1.index) fa
  have hVV : Vb = Va := Finset.ext fun z => by rw [hma, hmb, hV]
  set T : Finset (SquareLatticeVertex L L) :=
    Finset.univ.filter fun x => fb (cellCenterPos L x) ≠ fa (cellCenterPos L x)
  have hbefore : guideFrame (cellCenterPos L) q fb (labelParty R) guidePlaceholder rank Vb
      (suppliedPatch P _ hr) hdb =
      (guideFrame (cellCenterPos L) q fa (labelParty R) guidePlaceholder rank Va
        (suppliedPatch P _ hr) hda).changeOwner T (labelParty R Q) := by
    rw [guideFrame_congr_guide (g' := fb) (hV' := by rw [← hVV]; exact hdb) rfl hVV
      (fun _ _ => rfl)]
    refine guideFrame_eq_changeOwner (fun x => ?_) (fun z hz => ?_)
    · by_cases hx : fb (cellCenterPos L x) = fa (cellCenterPos L x)
      · have : x ∉ T := by simp [T, hx]
        rw [ite_eq_right this, hx]
      · have : x ∈ T := by simp [T, hx]
        rw [ite_eq_left this, (hkey _ hx).2]
    · exact tagHolder_congr (hinc z ((hV z).2 ((hma z).1 hz)))
  rw [hFb, hFa, hbefore]
  obtain ⟨M, hM, hu, hs, hf, herr⟩ := bandDeath_step_guideFrame (L := L)
    (hole := suppliedPatch P _ hr)
    (V := Va) (hV := hda) (own := labelParty R) (ph := guidePlaceholder) (rank := rank)
    hD hLL hΩ (fun v => cellCenterPos_eq_sitePosition_add v) hm₀ hc.a_le op e g₀ d
    ((1 : ℝ), (1 : ℝ)) ht.le htn (le_mul_of_one_le_left (by positivity) hA₀ |>.trans' (by
      have hk : (R.1.1 : ℕ) + 1 ≤ k := R.2
      have h1 : n * 2 ≤ 2 ^ k := by
        rw [hn_def, ← pow_succ]; exact pow_le_pow_right₀ (by norm_num) hk
      have h2 : (2 : ℝ) ^ k < 2 * L := by exact_mod_cast hk2
      linarith)) hε2 hfs hfb hfa (fun z hz => (hma z).1 hz)
    (fun z _ => ⟨suppliedPatch_center P hr z, by simp [ht_def]⟩) (T := T) (Q := labelParty R Q)
    (fun x hx => by
      have hx' : fb (cellCenterPos L x) ≠ fa (cellCenterPos L x) := by simpa [T] using hx
      rw [(hkey _ hx').1])
    (Set.disjoint_left.2 fun x hx hxo => by
      have hx' : fb (cellCenterPos L x) ≠ fa (cellCenterPos L x) := by simpa [T] using hx
      obtain ⟨p, hp, hxp⟩ := hxo
      obtain ⟨hl, hhl, rfl⟩ := List.mem_map.1 hp
      obtain ⟨z, hz, rfl⟩ := mem_holes_guideFrame.1 hhl
      have hd : dist (cellCenterPos L x) z ≤ 2 * (ε₀ * t) := by
        simpa [SquarePatch.outer, squareSample] using hxp
      have := hTfar z ((hV z).2 ((hma z).1 hz)) _ hx'
      rw [dist_comm] at this
      linarith)
    (fun x hx y hy => by
      have hx' : fb (cellCenterPos L x) ≠ fa (cellCenterPos L x) := by simpa [T] using hx
      have hy' : fb (cellCenterPos L y) ≠ fa (cellCenterPos L y) := by simpa [T] using hy
      exact (hTdiam _ _ hx' hy').trans (le_mul_of_one_le_left hn.le hA₀))
    (fun x hx => by simpa [T] using hx)
  refine ⟨M.toOriginalCircuit hM, (PartyChain.isBoundedChange_toOriginalCircuit hM hu hs hf hr1 hK
    (by exact herr)).mono ?_ le_rfl le_rfl le_rfl,
    M.isSourceBounded_toOriginalCircuit_of_one_le hM hrs⟩
  rintro x (rfl | rfl)
  exacts [hPS, hQS]


end Changes

end TNLean.PEPS.Approximation
