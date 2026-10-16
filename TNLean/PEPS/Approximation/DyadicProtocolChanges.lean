/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicDirectRepaintingConstants
import TNLean.PEPS.Approximation.DyadicPointTreatmentStep
import TNLean.PEPS.Approximation.DyadicProtocolOwners
import TNLean.PEPS.Approximation.SheetStackChange

/-!
# The changes of the dyadic protocol as bounded changes

Each change of the schedule of Proposition 7.1 of the polynomial-PEPS manuscript is one of the
following operations on the sheets (`06-geometry.tex`, lines 135–241, 328–339 and 507–541):
a direct repainting, the resize of one hole, the point treatment of one mark of a bulk
operation or its removal, a birth or death on one sheet, and the lens exchange of two sheets.
The step theorems of these operations each produce an original circuit, a word or a chain of
pair resources on the registers of the encoded frames. This file turns each of them into a
bounded change (`PairEffect.OriginalCircuit.IsBoundedChange`) whose participants are parties
used by the event of the change (`Approximation.EventUses`), with the raw owners of the frames
read through the party map of the repainting (`Approximation.labelParty`). The placeholder label
of a repainting is read as the fresh placeholder party of that repainting
(`06-geometry.tex`, lines 91–100).

* `Approximation.eventUses_labelParty_protocolLevelLabels`,
  `Approximation.eventUses_labelParty_newParty`,
  `Approximation.eventUses_labelParty_guidePlaceholder` : the labels that a repainting reads,
  those of the nine blocks around the repainted block, its new label and the placeholder, are held
  by parties the repainting uses.
* `Approximation.eventUses_labelParty_protocolLevelLabels_junction`,
  `Approximation.coe_subset_eventUses_of_junctionWindow`,
  `Approximation.coe_subset_eventUses_of_junctionWindow_placeholder` : the labels of the blocks
  of the root square among the nine blocks that a resize reads are held by parties the resize
  uses; a block outside the root square carries the placeholder label.
* `Approximation.isBoundedChange_of_step` : the small-patch rewrites (direct repaintings, resizes
  and point treatments) as bounded changes.
* `Approximation.isBoundedChange_of_birth`, `Approximation.isBoundedChange_of_death`,
  `Approximation.isBoundedChange_of_exchange` : the bulk births, deaths and lens exchanges as
  bounded changes.

The frames of the sheets and the premises of the step theorems are those of the step theorems;
this file does not construct them.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Proposition 7.1 `prop:protocol`,
  `06-geometry.tex`, lines 25–41 (statement), 91–100 (the fresh placeholder party), 328–541 (the
  operations), 572–596 (bounded gates and the parties of each change); Lemmas 6.3, 6.5 and 6.6,
  `05-frames.tex`.
-/

noncomputable section

namespace TNLean.PEPS.Approximation

open EncodedFrame PairEffect Metric

/-! ### The parties used by a repainting -/

/-- The block indices of a square of the hierarchy, as a block of its level. -/
def DyadicSquare.index {k : ℕ} (S : DyadicSquare k) : ℤ × ℤ :=
  (((S.2.1 : ℕ) : ℤ), ((S.2.2 : ℕ) : ℤ))

variable {k : ℕ}

/-- **Block labels of a repainting.** In the repainting of a square `R` of level `2 ^ j'`, the
label of a block that differs from `R` by at most one in each index, at any stage of the pass to
the level, is held by a party that the repainting uses: the block party of a square of the
hierarchy next to `R`, or the fresh placeholder party of `R`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 82–100 and 585–609
(`eq:geometry-active-labels`). -/
theorem eventUses_labelParty_protocolLevelLabels (R : RepaintedSquare k) (done : Set (ℤ × ℤ))
    {Q : ℤ × ℤ} (hQ : |Q.1 - R.1.index.1| ≤ 1 ∧ |Q.2 - R.1.index.2| ≤ 1) :
    EventUses (.inl R.1) (labelParty R (protocolLevelLabels k R.1.1 done Q)) := by
  rcases levelLabels_mem_validLabels R.2 done Q with h | ⟨Q', h⟩
  · unfold protocolLevelLabels
    rw [h, labelParty_guidePlaceholder]
    rfl
  · unfold protocolLevelLabels
    rw [← h]
    dsimp only
    rw [labelParty_toTriple]
    have hu := repaintingUses_of_levelLabels Sum.inl_injective inl_ne_guidePlaceholder _ R.1.1
      done hQ h.symm
    simp only [DyadicSquare.index, Int.toNat_natCast] at hu
    exact hu

/-- **The new label of a repainting.** The new label of the repainted square is held by its own
block party, which the repainting uses.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 82–100. -/
theorem eventUses_labelParty_newParty (R : RepaintedSquare k) :
    EventUses (.inl R.1) (labelParty R (newParty Sum.inl R.1.1 R.1.index)) := by
  have h : (newParty Sum.inl R.1.1 R.1.index : GuideLabel) = .inl R.1.toTriple := by
    simp [newParty, DyadicSquare.index, DyadicSquare.toTriple]
  rw [h, labelParty_toTriple]
  exact ⟨R.1.2.1, R.1.2.2, by omega, by omega, by omega, by omega, Or.inl rfl⟩

/-- **The placeholder of a repainting.** The placeholder label is held by the fresh placeholder
party of the repainting, which only that repainting uses.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 91–100 and 627–630. -/
theorem eventUses_labelParty_guidePlaceholder (R : RepaintedSquare k) :
    EventUses (.inl R.1) (labelParty R guidePlaceholder) := by
  rw [labelParty_guidePlaceholder]
  rfl

/-- A block of the window of radius one about a block differs from it by at most one in each
index. -/
theorem abs_sub_le_one_of_mem_blockWindow {R' S : ℤ × ℤ} (h : R' ∈ blockWindow 1) :
    |(R' + S).1 - S.1| ≤ 1 ∧ |(R' + S).2 - S.2| ≤ 1 := by
  simp only [blockWindow, Finset.mem_product, Finset.mem_Icc, Nat.cast_one] at h
  simp only [Prod.fst_add, Prod.snd_add, add_sub_cancel_right, abs_le]
  omega

/-- **Parties of a direct repainting.** The parties of the step theorem of a direct repainting,
the owners of the labels of the nine blocks around the repainted square before or after it, are
used by the repainting.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 507–527 and 585–596. -/
theorem coe_subset_eventUses_of_window (R : RepaintedSquare k) (done done' : Set (ℤ × ℤ))
    {P : Finset (ProtocolParty k)}
    (hP : ∀ x ∈ P, ∃ R' ∈ blockWindow 1,
      x = labelParty R (protocolLevelLabels k R.1.1 done (R' + R.1.index)) ∨
        x = labelParty R (protocolLevelLabels k R.1.1 done' (R' + R.1.index))) :
    (↑P : Set (ProtocolParty k)) ⊆ {p | EventUses (.inl R.1) p} := by
  intro x hx
  obtain ⟨R', hR', rfl | rfl⟩ := hP x hx
  · exact eventUses_labelParty_protocolLevelLabels R done (abs_sub_le_one_of_mem_blockWindow hR')
  · exact eventUses_labelParty_protocolLevelLabels R done' (abs_sub_le_one_of_mem_blockWindow hR')

/-- **Parties of a point treatment.** The parties of the step theorem of a point treatment, the
owners of the new label and of the labels of the nine blocks around the repainted square, are
used by the repainting.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 328–339, 481–505 and 585–596. -/
theorem coe_blockParties_subset_eventUses (R : RepaintedSquare k) (done : Set (ℤ × ℤ)) :
    (↑(blockParties (labelParty R) (protocolLevelLabels k R.1.1 done) R.1.index
        (newParty Sum.inl R.1.1 R.1.index)) : Set (ProtocolParty k)) ⊆
      {p | EventUses (.inl R.1) p} := by
  intro x hx
  rcases mem_blockParties.1 hx with rfl | ⟨R', hR', rfl⟩
  · exact eventUses_labelParty_newParty R
  · exact eventUses_labelParty_protocolLevelLabels R done (abs_sub_le_one_of_mem_blockWindow hR')

/-! ### The parties used by a junction resize -/

/-- The indices of a grid corner of the hierarchy, as a corner of its level. -/
def DyadicJunction.index {k : ℕ} (J : DyadicJunction k) : ℤ × ℤ :=
  (((J.2.1 : ℕ) : ℤ), ((J.2.2 : ℕ) : ℤ))

/-- **Block labels of a junction resize.** At the end of the pass to level `2 ^ j`, when every
block of the root square carries its new label, the label of a block of the root square among
the nine blocks around the block below and to the left of the junction `J` of scale `j` is held
by a block party that the resize at `J` uses, whatever the repainting `R` whose party map reads
the labels.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 127–131 and 594: “Resizing uses the
current block labels near its junction”. -/
theorem eventUses_labelParty_protocolLevelLabels_junction (R : RepaintedSquare k)
    (J : DyadicJunction k) {done : Set (ℤ × ℤ)}
    (hd : {Q | InRoot ((2 : ℤ) ^ (k - (J.1 : ℕ))) Q} ⊆ done) {R' : ℤ × ℤ}
    (hR' : R' ∈ blockWindow 1)
    (hin : InRoot ((2 : ℤ) ^ (k - (J.1 : ℕ))) (R' + (J.index.1 - 1, J.index.2 - 1))) :
    EventUses (.inr J)
      (labelParty R (protocolLevelLabels k J.1 done (R' + (J.index.1 - 1, J.index.2 - 1)))) := by
  set Q := R' + (J.index.1 - 1, J.index.2 - 1) with hQ
  have hM : (2 : ℤ) ^ (k - (J.1 : ℕ)) = ((2 ^ (k - (J.1 : ℕ)) : ℕ) : ℤ) := by push_cast; rfl
  obtain ⟨h1, h2, h3, h4⟩ := hin
  rw [hM] at h2 h4
  let S : DyadicSquare k := ⟨J.1, ⟨Q.1.toNat, by omega⟩, ⟨Q.2.toNat, by omega⟩⟩
  have hl : protocolLevelLabels k J.1 done Q = .inl S.toTriple := by
    have hin' : InRoot ((2 : ℤ) ^ (k - (J.1 : ℕ))) Q := ⟨h1, hM ▸ h2, h3, hM ▸ h4⟩
    simp only [protocolLevelLabels, levelLabels, hin', hd hin', ↓reduceIte, newParty,
      DyadicSquare.toTriple, S]
  rw [hl, labelParty_toTriple]
  simp only [blockWindow, Finset.mem_product, Finset.mem_Icc, Nat.cast_one] at hR'
  simp only [hQ, DyadicJunction.index, Prod.fst_add, Prod.snd_add] at h1 h3 ⊢
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> simp only [DyadicSquare.toTriple, S, hQ,
    DyadicJunction.index, Prod.fst_add, Prod.snd_add] <;> omega

/-- **Parties of a junction resize, in-root labels.** If every party of a set `P` is the party,
under the party map of a repainting `R`, of the label of a block of the root square among the nine
blocks around the block below and to the left of the junction `J`, at the end of the pass to the
level of `J`, then every party of `P` is used by the resize at `J`. This is the form of the
parties of `resize_step` once the blocks outside the root square are discarded.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 127–131, 529–541 and 594. -/
theorem coe_subset_eventUses_of_junctionWindow (R : RepaintedSquare k) (J : DyadicJunction k)
    {done : Set (ℤ × ℤ)} (hd : {Q | InRoot ((2 : ℤ) ^ (k - (J.1 : ℕ))) Q} ⊆ done)
    {P : Finset (ProtocolParty k)}
    (hP : ∀ x ∈ P, ∃ R' ∈ blockWindow 1,
      InRoot ((2 : ℤ) ^ (k - (J.1 : ℕ))) (R' + (J.index.1 - 1, J.index.2 - 1)) ∧
        x = labelParty R (protocolLevelLabels k J.1 done (R' + (J.index.1 - 1, J.index.2 - 1)))) :
    (↑P : Set (ProtocolParty k)) ⊆ {p | EventUses (.inr J) p} := by
  intro x hx
  obtain ⟨R', hR', hin, rfl⟩ := hP x hx
  exact eventUses_labelParty_protocolLevelLabels_junction R J hd hR' hin

/-- **Parties of a junction resize.** The parties of `resize_step` at the junction `J`, read
through the party map of a repainting `R` at the end of the pass to the level of `J`, are used
by the resize at `J`, except possibly the placeholder party of `R`, which holds the label of the
blocks outside the root square.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 91–100, 127–131, 529–541 and 594. -/
theorem coe_subset_eventUses_of_junctionWindow_placeholder (R : RepaintedSquare k)
    (J : DyadicJunction k) {done : Set (ℤ × ℤ)}
    (hd : {Q | InRoot ((2 : ℤ) ^ (k - (J.1 : ℕ))) Q} ⊆ done) {P : Finset (ProtocolParty k)}
    (hP : ∀ x ∈ P, ∃ R' ∈ blockWindow 1,
      x = labelParty R (protocolLevelLabels k J.1 done (R' + (J.index.1 - 1, J.index.2 - 1)))) :
    (↑P : Set (ProtocolParty k)) ⊆
      {p | EventUses (.inr J) p ∨ p = labelParty R guidePlaceholder} := by
  classical
  intro x hx
  obtain ⟨R', hR', rfl⟩ := hP x hx
  by_cases hin : InRoot ((2 : ℤ) ^ (k - (J.1 : ℕ))) (R' + (J.index.1 - 1, J.index.2 - 1))
  · exact Or.inl (eventUses_labelParty_protocolLevelLabels_junction R J hd hR' hin)
  · right
    simp only [protocolLevelLabels, levelLabels, hin, ↓reduceIte]

/-! ### The operations as bounded changes -/

/-- **The hole ratio of the protocol is below `1/4000`.** The smallness of `ε₀` in the constants
of the protocol, `2 ε₀ (a₀ + 1) ≤ a₀ / 2` with `a₀ = 1/5000`, gives `ε₀ < 1/4000`, the condition
under which the outer holes of the treated guides are disjoint
(`homogenize_reading_outerHoles_disjoint`).

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 341–355 and 559–570. -/
theorem IsProtocolConstants.lt_one_div_four_thousand {K₀ ε₀ ν a D B₀ : ℝ}
    (hc : IsProtocolConstants K₀ ε₀ ν a D B₀) :
    ε₀ < 1 / 4000 := by
  have h := hc.ε₀_small
  have h0 := hc.ε₀_pos
  rw [angularConstant] at h
  nlinarith

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} [NeZero q] {pos : ι → ℝ × ℝ}
  {Party : Type} {Ω : EuclideanSpace ℂ (ι → Fin q)} {S : Set Party} {r K : ℕ} {ε : ℝ}

/-- **A small-patch rewrite as a bounded change.** The conclusion of the step theorems of the
direct repaintings, resizes and point treatments (`directRepainting_step`, `resize_step`,
`pointTreatment_step` and their forms for readings): a circuit with at most one nonprivate gate,
participants in a set `P` of parties, and expansion bounds, is a bounded change from `Ω_F` to
`Ω_{F'}` with participants in any set containing `P`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 481–541 and 572–583; Lemma 6.3
`lem:small-rewrite`, `05-frames.tex`, lines 188–218. -/
theorem isBoundedChange_of_step {F F' : Frame pos q Party} {P : Finset Party} (hP : ↑P ⊆ S)
    (h : ∃ w : OriginalCircuit F.regs F'.regs, w.nonprivateCount ≤ 1 ∧
      (∀ γ, (↑(w.participants γ) : Set Party) ⊆ ↑P) ∧ w.IsExpansionBounded r (K : ℝ) ∧
      w.IsMonomialBounded K ∧
      ‖w.eval (F.regIso.symm (F.refVec Ω)) - F'.regIso.symm (F'.refVec Ω)‖ ≤ ε) :
    ∃ c : OriginalCircuit F.regs F'.regs, c.IsBoundedChange S r K ε (F.regRef Ω) (F'.regRef Ω) :=
  let ⟨w, h₁, h₂, h₃, h₄, h₅⟩ := h
  ⟨w, h₁, fun γ => (h₂ γ).trans hP, h₃, h₄, h₅⟩

/-- **A direct repainting of the protocol as a bounded change.** At the constants of the protocol,
the direct repainting of a square `R` of level `n ≤ K₀ t`, from the reading of the level labels
with the blocks of `done` repainted to the reading with `R` repainted as well, with raw owners
read through the party map of `R` and the fresh placeholder party of `R`, is a bounded change whose
participants are used by the repainting, with error `(2 b + 1) L⁻²⁰` for
`b = protocolPatchBound ε₀ ν`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 91–100, 507–527, 559–570 and 572–596;
Lemma 6.3 `lem:small-rewrite`, `05-frames.tex`, lines 188–218. -/
theorem directRepainting_isBoundedChange {K₀ ε₀ ν a D B₀ : ℝ}
    (hc : IsProtocolConstants K₀ ε₀ ν a D B₀) (hm : IsDirectRepaintingRatio K₀ ε₀ ν) {L : ℕ}
    (hL : 2 ≤ L) {n : ℝ} (hn : 0 < n) (hK : n ≤ K₀ * (D * Real.log L)) {v : ℝ × ℝ}
    (hv : IsGenericDisplacement v) (R : RepaintedSquare k) (done : Set (ℤ × ℤ))
    {g g' : ℝ × ℝ → GuideLabel}
    (hg : IsDisplacedReading g (blockGuide n (protocolLevelLabels k R.1.1 done)) v)
    (hg' : IsDisplacedReading g'
      (blockGuide n (protocolLevelLabels k R.1.1 (insert R.1.index done))) v)
    (rank : GuideLabel → ℕ) {V V' : Finset (ℝ × ℝ)} (hV : ∀ c ∈ V, IsTrueVertex g c)
    (hV' : ∀ c ∈ V', IsTrueVertex g' c)
    (hVc : ∀ c ∈ closedBall (blockCorner n R.1.index) (3 * n), IsTrueVertex g c → c ∈ V)
    (hVc' : ∀ c ∈ closedBall (blockCorner n R.1.index) (3 * n), IsTrueVertex g' c → c ∈ V')
    (hVV' : ∀ c ∉ squareCorners n R.1.index, (c ∈ V ↔ c ∈ V'))
    (hole patch : ℝ × ℝ → SquarePatch pos q)
    (hhole : ∀ z, (hole z).center = z ∧ (hole z).scale = holeRadius ε₀ n (D * Real.log L))
    (hpatch : ∀ z, (patch z).center = z ∧ (patch z).scale = patchRadius ν n)
    (hpV : (V : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (hole z).outer (hole z').outer)
    (hpV' : (V' : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (hole z).outer (hole z').outer)
    {C c : ℕ} (hcardHole : ∀ z, Fintype.card (hole z).Tag ≤ C * L ^ c)
    (hcardPatch : ∀ z, Fintype.card (patch z).Tag ≤ C * L ^ c) (hΩ : ‖Ω‖ ≤ 1)
    (hεpatch : ∀ z, ‖act (patch z).proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹)
    (hεhole : ∀ z, ‖act (hole z).proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹)
    (htag : ∀ z, Nonempty (hole z).Tag) :
    ∃ w : OriginalCircuit
        (guideFrame pos q g (labelParty R) guidePlaceholder rank V hole hpV).regs
        (guideFrame pos q g' (labelParty R) guidePlaceholder rank V' hole hpV').regs,
      w.IsBoundedChange {p | EventUses (.inl R.1) p} (2 * protocolPatchBound ε₀ ν)
        ((C + 1) ^ (3 * protocolPatchBound ε₀ ν) *
          (16 * protocolPatchBound ε₀ ν ^ 2 * (C + 1) ^ (6 * protocolPatchBound ε₀ ν) + 1) ^
            (2 * protocolPatchBound ε₀ ν) *
          L ^ (3 * protocolPatchBound ε₀ ν * c +
            4 * protocolPatchBound ε₀ ν * (3 * protocolPatchBound ε₀ ν * c + 30)))
        ((2 * protocolPatchBound ε₀ ν + 1) * ((L : ℝ) ^ 20)⁻¹)
        ((guideFrame pos q g (labelParty R) guidePlaceholder rank V hole hpV).regRef Ω)
        ((guideFrame pos q g' (labelParty R) guidePlaceholder rank V' hole hpV').regRef Ω) := by
  obtain ⟨P, -, hP, h⟩ := hc.directRepainting_step hm hL hn hK hv
    (fun Q hQ => levelLabels_insert_of_ne _ _ _ _ hQ) hg hg' (labelParty R) guidePlaceholder
    rank hV hV' hVc hVc' hVV' hole patch hhole hpatch hpV hpV' hcardHole hcardPatch hΩ hεpatch
    hεhole htag
  exact isBoundedChange_of_step (coe_subset_eventUses_of_window R done _ hP) (by exact_mod_cast h)

/-- **A birth as a bounded change.** The conclusion of the step theorems of the bulk births
(`bandBirth_step`, `centralBirth_step`): an allowed word using only the old and the new owner
`P∘`, `Q∘`, with at most one pair source and error `ε`, is a bounded change from `Ω_F` to
`Ω_{F'}`, for every `r` and every `K ≥ 1`, with participants in any set containing `P∘` and
`Q∘`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 155–221, 357–387 and 440–445; Lemma 6.5
`lem:birth`, `05-frames.tex`. -/
theorem isBoundedChange_of_birth {F F' : Frame pos q Party} {P Q : Party} (hP : P ∈ S)
    (hQ : Q ∈ S) (hK : 1 ≤ K)
    (h : ∃ w : Word F.regs F'.regs, w.IsAllowed ∧ w.UsesOnly {P, Q} ∧ w.sourceCount ≤ 1 ∧
      ‖w.eval (F.regIso.symm (F.refVec Ω)) - F'.regIso.symm (F'.refVec Ω)‖ ≤ ε) :
    ∃ c : OriginalCircuit F.regs F'.regs, c.IsBoundedChange S r K ε (F.regRef Ω) (F'.regRef Ω) := by
  obtain ⟨w, hw, hu, hs, he⟩ := h
  refine ⟨_, (Word.isBoundedChange_toOriginalCircuit hw hu hs hK he).mono ?_ le_rfl le_rfl
    le_rfl⟩
  rintro x (rfl | rfl)
  exacts [hP, hQ]

/-- **A death as a bounded change.** The conclusion of the step theorem of the bulk deaths
(`bandDeath_step`): an allowed chain using only `P∘` and `Q∘`, without pair sources, with at
most one pair effect and error `ε`, is a bounded change from `Ω_F` to `Ω_{F'}`, for every
`r ≥ 1` and every `K ≥ 1`, with participants in any set containing `P∘` and `Q∘`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 183–221, 357–387 and 440–445; Lemma 6.5
`lem:birth`, `05-frames.tex`. -/
theorem isBoundedChange_of_death {F F' : Frame pos q Party} {P Q : Party} (hP : P ∈ S)
    (hQ : Q ∈ S) (hr : 1 ≤ r) (hK : 1 ≤ K)
    (h : ∃ M : PartyChain F.regs F'.regs, M.IsAllowed ∧ M.UsesOnly {P, Q} ∧ M.sourceCount = 0 ∧
      M.toEffectChain.effectCount ≤ 1 ∧
      ‖M.toEffectChain.eval (F.regIso.symm (F.refVec Ω)) - F'.regIso.symm (F'.refVec Ω)‖ ≤ ε) :
    ∃ c : OriginalCircuit F.regs F'.regs, c.IsBoundedChange S r K ε (F.regRef Ω) (F'.regRef Ω) := by
  obtain ⟨M, hM, hu, hs, hf, he⟩ := h
  refine ⟨_, (PartyChain.isBoundedChange_toOriginalCircuit hM hu hs hf hr hK he).mono ?_ le_rfl
    le_rfl le_rfl⟩
  rintro x (rfl | rfl)
  exacts [hP, hQ]

/-- **The lens exchange as a bounded change.** The conclusion of the step theorem of the lens
exchange (`edgeExchange_step`): an allowed word on the registers of two sheets using only the
neighbouring owner `C`, without pair sources and with error `ε` on the product of the reference
vectors, is a bounded change of the two sheets, without nonprivate gate, for every `r` and every
`K ≥ 1`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 183–221, 389–430 and 440–445; Lemma 6.6
`lem:exchange`, `05-frames.tex`. -/
theorem isBoundedChange_of_exchange {F₁ F₂ F₁' F₂' : Frame pos q Party} {C : Party} (hC : C ∈ S)
    (hK : 1 ≤ K)
    (h : ∃ w : Word (F₁.regs ++ F₂.regs) (F₁'.regs ++ F₂'.regs), w.IsAllowed ∧ w.UsesOnly {C} ∧
      w.sourceCount = 0 ∧
      ‖w.eval ((twoLayoutIso _ _ F₁.owner F₂.owner).symm
          (EuclideanSpace.vecKron (F₁.refVec Ω) (F₂.refVec Ω))) -
        (twoLayoutIso _ _ F₁'.owner F₂'.owner).symm
          (EuclideanSpace.vecKron (F₁'.refVec Ω) (F₂'.refVec Ω))‖ ≤ ε) :
    ∃ c : OriginalCircuit (F₁.regs ++ F₂.regs) (F₁'.regs ++ F₂'.regs),
      c.nonprivateCount = 0 ∧
        c.IsBoundedChange S r K ε (pairRef F₁ F₂ Ω) (pairRef F₁' F₂' Ω) := by
  obtain ⟨w, hw, hu, hs, he⟩ := h
  rw [← pairRef_eq_twoLayoutIso_symm, ← pairRef_eq_twoLayoutIso_symm] at he
  refine ⟨_, (w.nonprivateCount_toOriginalCircuit hw).trans hs,
    (Word.isBoundedChange_toOriginalCircuit hw hu ((le_of_eq hs).trans zero_le_one) hK
      he).mono ?_ le_rfl le_rfl le_rfl⟩
  rintro x rfl
  exact hC

end TNLean.PEPS.Approximation
