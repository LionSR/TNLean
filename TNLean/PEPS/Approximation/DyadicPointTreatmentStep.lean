/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicTreatedTrueVertices
import TNLean.PEPS.Approximation.GuideFrameRewriteCircuit

/-!
# The point treatment of a mark as one gate

A point treatment homogenizes the guide of one sheet near a mark at a corner of the repainted
block, and its removal changes back to the target guide; each is a small-patch rewrite whose raw
owners and affected tag holders "are among the bounded list of parties in this local diagram"
(`06-geometry.tex`, lines 481–505). This file makes that list explicit and proves the rewrite to be
one gate.

Every value of an unmodified guide of the repainting of a block is a value of the starting guide,
the old label `A`, the final label `B` or a neighbouring label `C_e`
(`RepaintingBaseline.IsUnmodifiedGuide.apply_mem`). For the repainting of the block `S` of a block
guide, the labels of a temporary guide within `n` of the closed block, and its tag holders there,
are therefore `B` or labels of the nine blocks around `S` (`reading_mem_blockLabels`,
`tagHolder_mem_blockLabels`), provided the homogenizing label is one of these. The parties of these
at most ten labels (`blockParties`) are the specified parties of the point treatment and of its
removal, which is one original circuit with at most one nonprivate gate whose participants are
among them (`pointTreatment_step`).

## Main definitions

* `Approximation.blockParties`.

## Main results

* `Approximation.RepaintingBaseline.IsUnmodifiedGuide.apply_mem`.
* `Approximation.reading_mem_blockLabels`, `Approximation.tagHolder_mem_blockLabels`.
* `Approximation.pointTreatment_step_isSourceBounded`, `Approximation.pointTreatment_step`: with
  and without the bound of `2b` pair sources in every monomial.

## References

* Polynomial-PEPS manuscript (September 24, 2026), §7, `06-geometry.tex`: the point treatments
  (lines 328–339), the rim patterns (lines 341–351), the point-treatment covers (lines 481–505),
  the gates of a repainting (lines 574–583) and their parties (lines 585–596); Lemma 6.3
  `lem:small-rewrite`, `05-frames.tex`, lines 188–218.
-/

open Set Metric Filter Topology

noncomputable section

namespace TNLean.PEPS.Approximation

/-! ### The labels of an unmodified guide -/

namespace RepaintingBaseline

variable {ι : Type*} {R : RepaintingBaseline ι}

/-- **The labels of an unmodified guide.** Every value of an unmodified guide is the value of the
starting guide at that point, the old label `A`, the final label `B` or a label `C_e` across an
edge.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 155–241 and 585–596. -/
theorem IsUnmodifiedGuide.apply_mem {g : ℝ × ℝ → ι} (h : R.IsUnmodifiedGuide g) (p : ℝ × ℝ) :
    g p = R.guide p ∨ g p = R.oldLabel ∨ g p = R.finalLabel ∨ ∃ e, g p = R.nbrLabel e := by
  set s : Set ι := {x | x = R.oldLabel ∨ x = R.finalLabel ∨ ∃ e, x = R.nbrLabel e}
  suffices g p = R.guide p ∨ g p ∈ s from this
  have hA : R.oldLabel ∈ s := Or.inl rfl
  have hB : R.finalLabel ∈ s := Or.inr (Or.inl rfl)
  have hw : ∀ e (W : ℝ → ι), (W ∈ mainWords R.oldLabel R.finalLabel (R.nbrLabel e) ∨
      W ∈ auxWords R.oldLabel R.finalLabel (R.nbrLabel e)) → ∀ x, W x ∈ s := by
    intro e W hW x
    have hC : R.nbrLabel e ∈ s := Or.inr (Or.inr ⟨e, rfl⟩)
    simp only [mainWords, auxWords, mem_insert_iff, mem_singleton_iff] at hW
    rcases hW with (rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl) <;>
      (try simp only [edgeStartWord, mainWordOne, mainWordTwo, mainWordThree, mainWordFour,
        mainWordFive, auxWordOne, auxWordTwo, auxWord, auxWordExchanged]) <;>
      exact bandWord_mem hC (by simp [hA, hB, hC]) x
  have hc : ∀ E p, R.completedGuide E p = R.guide p ∨ R.completedGuide E p ∈ s := by
    intro E
    induction E with
    | nil =>
      intro p
      by_cases hp : p ∈ centralRegion R.n
      · exact Or.inr (by change R.centralGuide p ∈ s; rw [R.centralGuide_of_mem hp]; exact hB)
      · exact Or.inl (R.centralGuide_of_notMem hp)
    | cons e E ih =>
      intro p
      change bandUpdate R.n e (mainWordFive R.finalLabel (R.nbrLabel e)) (R.completedGuide E) p =
        _ ∨ bandUpdate R.n e (mainWordFive R.finalLabel (R.nbrLabel e)) (R.completedGuide E) p ∈ s
      by_cases hp : p ∈ edgeBand R.n e (-8) 2
      · rw [bandUpdate_of_mem hp]
        exact Or.inr (hw e _ (Or.inl (by simp [mainWords])) _)
      · rw [bandUpdate_of_notMem hp]
        exact ih p
  rcases h with rfl | rfl | ⟨E, rfl⟩ | ⟨E, e, W, hW, rfl⟩ | ⟨e, W, hW, rfl⟩
  · exact Or.inl rfl
  · exact hc [] p
  · exact hc E p
  · by_cases hp : p ∈ edgeBand R.n e (-8) 2
    · rw [mainGuide, bandUpdate_of_mem hp]
      exact Or.inr (hw e W (Or.inl hW) _)
    · rw [mainGuide, bandUpdate_of_notMem hp]
      exact hc E p
  · by_cases hp : p ∈ edgeBand R.n e (-8) 2
    · rw [auxGuide, bandUpdate_of_mem hp]
      exact Or.inr (hw e W (Or.inr hW) _)
    · rw [auxGuide, bandUpdate_of_notMem hp]
      exact Or.inr (Or.inr (Or.inr ⟨e, rfl⟩))

end RepaintingBaseline

/-! ### The labels of a temporary guide near the block -/

variable {κ : Type}

/-- The labels of an unmodified guide of the repainting of the block `S` to `B`, moved to `S`,
within `n` of the closed block are `B` and the labels of the nine blocks around `S`. -/
theorem shiftGuide_mem_blockLabels {n : ℝ} (hn : 0 < n) {lab : ℤ × ℤ → κ} {S : ℤ × ℤ} {B : κ}
    {g : ℝ × ℝ → κ} (hg : (blockBaseline hn lab S B).IsUnmodifiedGuide g) {p y : ℝ × ℝ}
    (hy : y ∈ closedBlock n S) (hp : dist p y < n) :
    shiftGuide (blockCorner n S) g p = B ∨
      ∃ R ∈ blockWindow 1, shiftGuide (blockCorner n S) g p = lab (R + S) := by
  change g (p - blockCorner n S) = B ∨ ∃ R ∈ blockWindow 1, g (p - blockCorner n S) = lab (R + S)
  rcases hg.apply_mem (p - blockCorner n S) with h | h | h | ⟨e, h⟩
  · right
    rw [h]
    change ∃ R ∈ blockWindow 1,
      lab (blockIndex n (p - blockCorner n S + blockCorner n S)) = lab (R + S)
    rw [sub_add_cancel]
    obtain ⟨a, b⟩ := abs_blockIndex_sub_le hn hy hp
    refine ⟨blockIndex n p - S, ?_, by rw [sub_add_cancel]⟩
    rw [abs_le] at a b
    simp only [blockWindow, Finset.mem_product, Finset.mem_Icc, Prod.fst_sub, Prod.snd_sub]
    push_cast
    omega
  · exact Or.inr ⟨0, by decide, by rw [h, zero_add]; rfl⟩
  · exact Or.inl h
  · right
    refine ⟨e.nbrBlock S - S, ?_, by rw [h, sub_add_cancel]; rfl⟩
    cases e <;>
      simp only [SquareEdge.nbrBlock, blockWindow, Finset.mem_product, Finset.mem_Icc,
        Prod.fst_sub, Prod.snd_sub] <;> push_cast <;> omega

/-- **The labels of a temporary guide near the block.** Let `f` be the reading along `v` of an
unmodified guide of the repainting of the block `S` of the block guide `lab` to `B`, moved to `S`
and homogenized on a set `U` to a label `L₀` that is `B` or the label of one of the nine blocks
around `S`. Then the label of `f` at every point within `n` of the closed block is `B` or the label
of one of the nine blocks around `S`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 328–339, 497–502 and 585–596. -/
theorem reading_mem_blockLabels {n : ℝ} (hn : 0 < n) {lab : ℤ × ℤ → κ} {S : ℤ × ℤ} {B : κ}
    {g : ℝ × ℝ → κ} (hg : (blockBaseline hn lab S B).IsUnmodifiedGuide g) (U : Set (ℝ × ℝ))
    {L₀ : κ} (hL₀ : L₀ = B ∨ ∃ R ∈ blockWindow 1, L₀ = lab (R + S)) {v : ℝ × ℝ}
    {f : ℝ × ℝ → κ} (hf : IsDisplacedReading f (homogenize U L₀ (shiftGuide (blockCorner n S) g)) v)
    {p y : ℝ × ℝ} (hy : y ∈ closedBlock n S) (hp : dist p y < n) :
    f p = B ∨ ∃ R ∈ blockWindow 1, f p = lab (R + S) := by
  have hε := (tendsto_add_smul_nhdsGT p v).eventually
    ((isOpen_lt (continuous_id.dist continuous_const) continuous_const).mem_nhds
      (show dist p y < n from hp))
  obtain ⟨ε, e₁, e₂⟩ := ((hf p).and hε).exists
  rw [e₁]
  by_cases hU : p + ε • v ∈ U
  · rw [homogenize_of_mem hU]
    exact hL₀
  · rw [homogenize_of_notMem hU]
    exact shiftGuide_mem_blockLabels hn hg hy e₂

/-- **The tag holders of a temporary guide near the block.** In the setting of
`reading_mem_blockLabels`, the canonical tag holder at a true vertex of `f` within `n` of the
closed block is `B` or the label of one of the nine blocks around `S`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 119–125, 497–502 and 585–596. -/
theorem tagHolder_mem_blockLabels {n : ℝ} (hn : 0 < n) {lab : ℤ × ℤ → κ} {S : ℤ × ℤ} {B : κ}
    {g : ℝ × ℝ → κ} (hg : (blockBaseline hn lab S B).IsUnmodifiedGuide g) (U : Set (ℝ × ℝ))
    {L₀ : κ} (hL₀ : L₀ = B ∨ ∃ R ∈ blockWindow 1, L₀ = lab (R + S)) {v : ℝ × ℝ}
    {f : ℝ × ℝ → κ} (hf : IsDisplacedReading f (homogenize U L₀ (shiftGuide (blockCorner n S) g)) v)
    (rank : κ → ℕ) (ph : κ) {a y : ℝ × ℝ} (ha : IsTrueVertex f a) (hy : y ∈ closedBlock n S)
    (hay : dist a y < n) :
    tagHolder rank f ph a = B ∨ ∃ R ∈ blockWindow 1, tagHolder rank f ph a = lab (R + S) := by
  have hl := (isTagHolder_tagHolder (rank := rank) (ph := ph) ha).1
  obtain ⟨p, hp, hap⟩ := Metric.mem_closure_iff.1 hl (n - dist a y) (sub_pos.2 hay)
  have hpy : dist p y < n := by linarith [dist_triangle p a y, dist_comm a p]
  rw [← (mem_singleton_iff.1 hp : f p = _)]
  exact reading_mem_blockLabels hn hg U hL₀ hf hy hpy

/-! ### The parties of a point treatment -/

open Classical in
/-- The parties of the labels `B` and of the nine blocks around `S`: the specified parties of a
small-patch rewrite of the repainting of `S` to `B`. -/
def blockParties {Party : Type} (own : κ → Party) (lab : ℤ × ℤ → κ) (S : ℤ × ℤ) (B : κ) :
    Finset Party :=
  insert (own B) ((blockWindow 1).image fun R => own (lab (R + S)))

variable {Party : Type}

theorem mem_blockParties {own : κ → Party} {lab : ℤ × ℤ → κ} {S : ℤ × ℤ} {B : κ} {x : Party} :
    x ∈ blockParties own lab S B ↔ x = own B ∨ ∃ R ∈ blockWindow 1, x = own (lab (R + S)) := by
  simp only [blockParties, Finset.mem_insert, Finset.mem_image]
  exact or_congr Iff.rfl ⟨fun ⟨R, hR, e⟩ => ⟨R, hR, e.symm⟩, fun ⟨R, hR, e⟩ => ⟨R, hR, e.symm⟩⟩

theorem own_mem_blockParties {own : κ → Party} {lab : ℤ × ℤ → κ} {S : ℤ × ℤ} {B l : κ}
    (h : l = B ∨ ∃ R ∈ blockWindow 1, l = lab (R + S)) : own l ∈ blockParties own lab S B := by
  rw [mem_blockParties]
  rcases h with rfl | ⟨R, hR, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨R, hR, rfl⟩

/-- There are at most ten parties of a block and its neighbours. -/
theorem card_blockParties_le (own : κ → Party) (lab : ℤ × ℤ → κ) (S : ℤ × ℤ) (B : κ) :
    (blockParties own lab S B).card ≤ 10 := by
  classical
  refine (Finset.card_insert_le _ _).trans ?_
  have := (Finset.card_image_le (s := blockWindow 1) (f := fun R => own (lab (R + S))))
  rw [card_blockWindow_one] at this
  convert Nat.succ_le_succ this

/-! ### The point treatment as one gate -/

open EncodedFrame TNLean.Lattice.Sheet TNLean.Lattice.PartyCircuit

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} {pos : ι → ℝ × ℝ}

/-- **The point treatment of a mark as one gate, with its pair sources.** The conclusion of
`pointTreatment_step`, together with the bound of `2b` pair sources in every monomial of the gate.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 481–505 and 574–583; Lemma 6.3
`lem:small-rewrite`, `05-frames.tex`, lines 188–218; Theorem 5.2, item 3, `04-compression.tex`,
lines 143–147. -/
theorem pointTreatment_step_isSourceBounded [NeZero q] {n t r u : ℝ} (hn : 0 < n) (ht : 0 < t)
    (hr : 0 < r) (hu : 0 < u) (hsep : 2 * t + 6 * r + 3 * u < n) {lab : ℤ × ℤ → κ} {S : ℤ × ℤ}
    {B : κ}
    {g : ℝ × ℝ → κ} (hg : (blockBaseline hn lab S B).IsUnmodifiedGuide g)
    {M₁ M₂ : Finset (ℤ × ℤ)} (Q₀ : ℤ × ℤ) (hQ₀ : blockCorner n Q₀ ∈ closedBlock n S)
    (hM : ∀ Q, Q ≠ Q₀ → (Q ∈ M₁ ↔ Q ∈ M₂)) (L₀ : κ)
    (hL₀ : L₀ = B ∨ ∃ R ∈ blockWindow 1, L₀ = lab (R + S)) {v : ℝ × ℝ} {g₁ g₂ : ℝ × ℝ → κ}
    (hg₁ : IsDisplacedReading g₁ (homogenize (⋃ Q ∈ M₁, ball (blockCorner n Q) t) L₀
      (shiftGuide (blockCorner n S) g)) v)
    (hg₂ : IsDisplacedReading g₂ (homogenize (⋃ Q ∈ M₂, ball (blockCorner n Q) t) L₀
      (shiftGuide (blockCorner n S) g)) v) (own : κ → Party) (ph : κ) (rank : κ → ℕ)
    {V V' : Finset (ℝ × ℝ)} (hV : ∀ c ∈ V, IsTrueVertex g₁ c) (hV' : ∀ c ∈ V', IsTrueVertex g₂ c)
    (hVV' : ∀ c, n - t ≤ dist c (blockCorner n Q₀) → (c ∈ V ↔ c ∈ V'))
    (hole patch : ℝ × ℝ → SquarePatch pos q)
    (hhole : ∀ z, (hole z).center = z ∧ (hole z).scale = r)
    (hpatch : ∀ z, (patch z).center = z ∧ (patch z).scale = u)
    (hpV : (V : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (hole z).outer (hole z').outer)
    (hpV' : (V' : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (hole z).outer (hole z').outer)
    {W H H' : Set (ℝ × ℝ)} (hW : closedBall (blockCorner n Q₀) (t + 2 * r + 3 * u) ⊆ W)
    (hH : ∀ c ∈ H, c ∈ V) (hH' : ∀ c ∈ H', c ∈ V')
    (htwo : HasTwoOwnerFootprints g₁ W H r (2 * u))
    (htwo' : HasTwoOwnerFootprints g₂ W H' r (2 * u))
    {C c b L : ℕ} (hL : 1 ≤ L) (hcardHole : ∀ z, Fintype.card (hole z).Tag ≤ C * L ^ c)
    (hcardPatch : ∀ z, Fintype.card (patch z).Tag ≤ C * L ^ c)
    (hb : (2 * (t + 2 * r + u) / u + 1) ^ 2 ≤ b) (hb53 : 53 ≤ b)
    {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ ≤ 1)
    (hεpatch : ∀ z, ‖act (patch z).proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹)
    (hεhole : ∀ z, ‖act (hole z).proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹)
    (htag : ∀ z, Nonempty (hole z).Tag) :
    ∃ w : OriginalCircuit (guideFrame pos q g₁ own ph rank V hole hpV).regs
        (guideFrame pos q g₂ own ph rank V' hole hpV').regs,
      w.nonprivateCount ≤ 1 ∧
      (∀ γ, (↑(w.participants γ) : Set Party) ⊆ ↑(blockParties own lab S B)) ∧
      w.IsExpansionBounded (2 * b) ((C + 1) ^ (3 * b) * (16 * b ^ 2 * (C + 1) ^ (6 * b) + 1) ^
        (2 * b) * L ^ (3 * b * c + 4 * b * (3 * b * c + 30)) : ℕ) ∧
      w.IsMonomialBounded ((C + 1) ^ (3 * b) * (16 * b ^ 2 * (C + 1) ^ (6 * b) + 1) ^ (2 * b) *
        L ^ (3 * b * c + 4 * b * (3 * b * c + 30))) ∧
      ‖w.eval ((guideFrame pos q g₁ own ph rank V hole hpV).regIso.symm
          ((guideFrame pos q g₁ own ph rank V hole hpV).refVec Ω)) -
        (guideFrame pos q g₂ own ph rank V' hole hpV').regIso.symm
          ((guideFrame pos q g₂ own ph rank V' hole hpV').refVec Ω)‖ ≤
        (2 * b + 1) * ((L : ℝ) ^ 20)⁻¹ ∧
      w.IsSourceBounded (2 * b) := by
  have htn : 2 * t < n := by linarith
  have hP : ∀ p, dist p (blockCorner n Q₀) ≤ t + 2 * r + 3 * u →
      own (g₁ p) ∈ blockParties own lab S B ∧ own (g₂ p) ∈ blockParties own lab S B :=
    fun p hp => ⟨own_mem_blockParties (reading_mem_blockLabels hn hg _ hL₀ hg₁ hQ₀
      (by linarith)), own_mem_blockParties (reading_mem_blockLabels hn hg _ hL₀ hg₂ hQ₀
      (by linarith))⟩
  obtain ⟨G, hG, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄⟩ :=
    exists_pointTreatment_planeConditions hn ht hr hu hsep hg Q₀ hM L₀ hg₁ hg₂ own ph rank hV hV'
      hVV' hole patch hhole hpatch hpV hpV' hW hH hH' htwo htwo' _ hP
      (fun a ha hd => own_mem_blockParties (tagHolder_mem_blockLabels hn hg _ hL₀ hg₁ rank ph
        (hV a ha) hQ₀ (by linarith)))
      (fun a ha hd => own_mem_blockParties (tagHolder_mem_blockLabels hn hg _ hL₀ hg₂ rank ph
        (hV' a ha) hQ₀ (by linarith)))
  have hsub : G.oldAffected ⊆ insert (blockCorner n Q₀) (rimFinset (blockCorner n Q₀) t) :=
    fun a ha => mem_insert_rimFinset_of_isTrueVertex hn ht.le htn hg M₁ L₀ hg₁ Q₀
      (hV a (h₁₀ ▸ Finset.mem_union_right _ ha)) (h₁₂ a ha)
  have hsub' : G.newAffected ⊆ insert (blockCorner n Q₀) (rimFinset (blockCorner n Q₀) t) :=
    fun a ha => mem_insert_rimFinset_of_isTrueVertex hn ht.le htn hg M₂ L₀ hg₂ Q₀
      (hV' a (h₁₁ ▸ Finset.mem_union_right _ ha)) (h₁₃ a ha)
  have hcard := (Finset.card_insert_le (blockCorner n Q₀) (rimFinset (blockCorner n Q₀) t)).trans
    (Nat.succ_le_succ (card_rimFinset_le (blockCorner n Q₀) t))
  have hold : G.oldAffected.card ≤ b := (Finset.card_le_card hsub).trans (hcard.trans hb53)
  have hnew : G.newAffected.card ≤ b := (Finset.card_le_card hsub').trans (hcard.trans hb53)
  subst h₁ h₂ h₃ h₄ h₅ h₆ h₈
  have hparties : G.parties.card ≤ b :=
    h₉ ▸ (card_blockParties_le _ _ _ _).trans (by omega)
  obtain ⟨w, w₁, w₂, w₃, w₄, w₅, w₆⟩ := hG.exists_originalCircuit_isSourceBounded (C := C)
    (c := c) (b := b) hL
    (fun a _ => h₇ ▸ hcardHole a) (fun z _ => hcardPatch z) (fun a _ => hcardHole a)
    (by exact_mod_cast h₁₄.trans hb) hold hnew hparties hΩ (fun z _ => hεpatch z)
    (fun a _ => hεhole a) (by rw [h₉]; exact ⟨_, mem_blockParties.2 (Or.inl rfl)⟩)
    (fun z _ => htag z)
  have e₂ : G.newFrame = guideFrame pos q G.new G.own G.ph G.rank V' G.holeOld hpV' :=
    guideFrame_congr h₁₁ h₇ _ _
  rw [← G.oldFrame_eq h₁₀ hpV, ← e₂]
  exact ⟨w, w₁, h₉ ▸ w₂, w₃, w₄, w₅, w₆⟩

/-- **The point treatment of a mark as one gate.** In the setting of
`exists_pointTreatment_planeConditions`, let the mark `Q₀` be a corner of the closed block `S`,
and the homogenizing label `L₀` be `B` or the label of one of the nine blocks around `S`. Suppose
moreover that every hole and every patch has at most `C L^c` cylinder terms and error at most
`L^{-60}` on `Ω`, with `‖Ω‖ ≤ 1`, that every hole has a tag, and that `b` is at least `53` and the
number `(2 (t + 2 r + u) / u + 1)²` of net patches. Then there is an original circuit from the
registers of the frame of `g₁` with holes at `V` to those of the frame of `g₂` with holes at
`V'`, with at most one nonprivate gate, all participants among the parties of `B` and of the
nine blocks around `S`, expansion bounds as in
`GuideFrameRewrite.PlaneConditions.exists_originalCircuit`, and reference-vector error at most
`(2b + 1) L^{-20}`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 328–339, 481–505 and 574–583; Lemma 6.3
`lem:small-rewrite`, `05-frames.tex`, lines 188–218. -/
theorem pointTreatment_step [NeZero q] {n t r u : ℝ} (hn : 0 < n) (ht : 0 < t) (hr : 0 < r)
    (hu : 0 < u) (hsep : 2 * t + 6 * r + 3 * u < n) {lab : ℤ × ℤ → κ} {S : ℤ × ℤ} {B : κ}
    {g : ℝ × ℝ → κ} (hg : (blockBaseline hn lab S B).IsUnmodifiedGuide g)
    {M₁ M₂ : Finset (ℤ × ℤ)} (Q₀ : ℤ × ℤ) (hQ₀ : blockCorner n Q₀ ∈ closedBlock n S)
    (hM : ∀ Q, Q ≠ Q₀ → (Q ∈ M₁ ↔ Q ∈ M₂)) (L₀ : κ)
    (hL₀ : L₀ = B ∨ ∃ R ∈ blockWindow 1, L₀ = lab (R + S)) {v : ℝ × ℝ} {g₁ g₂ : ℝ × ℝ → κ}
    (hg₁ : IsDisplacedReading g₁ (homogenize (⋃ Q ∈ M₁, ball (blockCorner n Q) t) L₀
      (shiftGuide (blockCorner n S) g)) v)
    (hg₂ : IsDisplacedReading g₂ (homogenize (⋃ Q ∈ M₂, ball (blockCorner n Q) t) L₀
      (shiftGuide (blockCorner n S) g)) v) (own : κ → Party) (ph : κ) (rank : κ → ℕ)
    {V V' : Finset (ℝ × ℝ)} (hV : ∀ c ∈ V, IsTrueVertex g₁ c) (hV' : ∀ c ∈ V', IsTrueVertex g₂ c)
    (hVV' : ∀ c, n - t ≤ dist c (blockCorner n Q₀) → (c ∈ V ↔ c ∈ V'))
    (hole patch : ℝ × ℝ → SquarePatch pos q)
    (hhole : ∀ z, (hole z).center = z ∧ (hole z).scale = r)
    (hpatch : ∀ z, (patch z).center = z ∧ (patch z).scale = u)
    (hpV : (V : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (hole z).outer (hole z').outer)
    (hpV' : (V' : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (hole z).outer (hole z').outer)
    {W H H' : Set (ℝ × ℝ)} (hW : closedBall (blockCorner n Q₀) (t + 2 * r + 3 * u) ⊆ W)
    (hH : ∀ c ∈ H, c ∈ V) (hH' : ∀ c ∈ H', c ∈ V')
    (htwo : HasTwoOwnerFootprints g₁ W H r (2 * u))
    (htwo' : HasTwoOwnerFootprints g₂ W H' r (2 * u))
    {C c b L : ℕ} (hL : 1 ≤ L) (hcardHole : ∀ z, Fintype.card (hole z).Tag ≤ C * L ^ c)
    (hcardPatch : ∀ z, Fintype.card (patch z).Tag ≤ C * L ^ c)
    (hb : (2 * (t + 2 * r + u) / u + 1) ^ 2 ≤ b) (hb53 : 53 ≤ b)
    {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ ≤ 1)
    (hεpatch : ∀ z, ‖act (patch z).proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹)
    (hεhole : ∀ z, ‖act (hole z).proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹)
    (htag : ∀ z, Nonempty (hole z).Tag) :
    ∃ w : OriginalCircuit (guideFrame pos q g₁ own ph rank V hole hpV).regs
        (guideFrame pos q g₂ own ph rank V' hole hpV').regs,
      w.nonprivateCount ≤ 1 ∧
      (∀ γ, (↑(w.participants γ) : Set Party) ⊆ ↑(blockParties own lab S B)) ∧
      w.IsExpansionBounded (2 * b) ((C + 1) ^ (3 * b) * (16 * b ^ 2 * (C + 1) ^ (6 * b) + 1) ^
        (2 * b) * L ^ (3 * b * c + 4 * b * (3 * b * c + 30)) : ℕ) ∧
      w.IsMonomialBounded ((C + 1) ^ (3 * b) * (16 * b ^ 2 * (C + 1) ^ (6 * b) + 1) ^ (2 * b) *
        L ^ (3 * b * c + 4 * b * (3 * b * c + 30))) ∧
      ‖w.eval ((guideFrame pos q g₁ own ph rank V hole hpV).regIso.symm
          ((guideFrame pos q g₁ own ph rank V hole hpV).refVec Ω)) -
        (guideFrame pos q g₂ own ph rank V' hole hpV').regIso.symm
          ((guideFrame pos q g₂ own ph rank V' hole hpV').refVec Ω)‖ ≤
        (2 * b + 1) * ((L : ℝ) ^ 20)⁻¹ := by
  obtain ⟨w, h₁, h₂, h₃, h₄, h₅, -⟩ := pointTreatment_step_isSourceBounded hn ht hr hu hsep hg Q₀
    hQ₀ hM L₀ hL₀ hg₁ hg₂ own ph rank hV hV' hVV' hole patch hhole hpatch hpV hpV' hW hH hH' htwo
    htwo' hL hcardHole hcardPatch hb hb53 hΩ hεpatch hεhole htag
  exact ⟨w, h₁, h₂, h₃, h₄, h₅⟩

end TNLean.PEPS.Approximation
