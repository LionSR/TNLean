/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicCentralBirthChange
import TNLean.PEPS.Approximation.DyadicSheetOperationChains

/-!
# The central birth and the births and deaths along an edge as chains of changes

In the large-scale repainting of a square `R` in the protocol of Proposition 7.1 of the
polynomial-PEPS manuscript, the central birth changes the main sheet in `9` changes and each
elementary birth or death along an edge changes one sheet in `5` changes: the point treatments of
the marks, the bulk step, and the removal of the treatments (`06-geometry.tex`, lines 155–221 and
328–339). This file assembles these chains, conditional on Proposition 3.4 through
`IsAngularScale`, with the bounds of the small-patch rewrites of the protocol.

* `isStepChain_centralBirth` : the central birth;
* `isStepChain_bandOperation` : an elementary birth or death along an edge.

## References

* Polynomial-PEPS manuscript (September 24, 2026), §7, `06-geometry.tex`: the central birth and
  the edge construction (lines 155–221), the point treatment (lines 328–339), the bulk steps
  (lines 375–387 and 440–445) and the bounds of the changes (lines 572–583).
-/

noncomputable section

namespace TNLean.PEPS.Approximation

open EncodedFrame PairEffect

variable {k q : ℕ} [NeZero q] {J Δ a A₀ D L₀' : ℝ} {m₀ : ℕ} {L : ℕ}
  {h : SquareHamiltonian L q J} {E₀ : ℝ} {Ω : StateSpace L q} {K₀ ε₀ ν B₀ C c : ℝ}

/-- The party of a local label is used by the repainting. -/
theorem IsLocalLabel.eventUses {R : RepaintedSquare k} {done : Set (ℤ × ℤ)} {l : GuideLabel}
    (hl : IsLocalLabel R done l) : labelParty R l ∈ {p | EventUses (.inl R.1) p} :=
  coe_blockParties_subset_eventUses R done (own_mem_blockParties hl)

/-- **The central birth as a chain of changes, conditional on Proposition 3.4.** At the
constants of the protocol, in the repainting of a square `R` of side `n = 2 ^ j > K₀ t`, the four
point treatments with the old label, the central birth and the removal of the treatments are `9`
bounded changes from the frame of the starting guide to that of the guide after the central birth,
with the bounds of the small-patch rewrites.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 155–160 and 328–339. -/
theorem isStepChain_centralBirth (hD : IsAngularScale q J Δ a A₀ m₀ 60 D L₀') (hLL : L₀' ≤ L)
    (hΩ : h.IsGappedGroundState E₀ Ω Δ) (hm₀ : 4 ≤ m₀) (hA₀ : 1 ≤ A₀)
    (hc : IsProtocolConstants K₀ ε₀ ν a D B₀) (hL : 2 ≤ L) (hk2 : 2 ^ k < 2 * L)
    (P : AdaptivePatchSupply (cellCenterPos L) Ω B₀ C c 60 L) (rank : GuideLabel → ℕ)
    (R : RepaintedSquare k) (hlarge : K₀ * (D * Real.log L) < (2 : ℝ) ^ (R.1.1 : ℕ))
    (done : Set (ℤ × ℤ))
    (hr : ∀ _ : ℝ × ℝ, 0 < ε₀ * (D * Real.log L) ∧ ε₀ * (D * Real.log L) ≤ B₀ * Real.log L)
    {b K : ℕ} (hb : 1 ≤ b) (hK : 1 ≤ K)
    (hpt : IsPointTreatable P rank R hr done {p | EventUses (.inl R.1) p} (2 * b) K (2 * b)
      ((2 * b + 1) * ((L : ℝ) ^ 20)⁻¹)) :
    IsStepChain (fun F F' => HasFrameChange Ω F F' {p | EventUses (.inl R.1) p} (2 * b) K (2 * b)
        ((2 * b + 1) * ((L : ℝ) ^ 20)⁻¹)) 9
      (treatedFrame (q := q) P rank R hr ∅ (repaintBaseline R done).oldLabel
        (repaintBaseline R done).guide)
      (treatedFrame P rank R hr ∅ (repaintBaseline R done).oldLabel
        (repaintBaseline R done).centralGuide) := by
  have hb := centralBirth_hasFrameChange hD hLL hΩ hm₀ hA₀ hc hL hk2 P rank R hlarge done
    (S := {p | EventUses (.inl R.1) p}) (IsLocalLabel.eventUses (isHomogenizing_oldLabel R done))
    (IsLocalLabel.eventUses (isHomogenizing_finalLabel R done)) (r := 2 * b) (rs := 2 * b) hK
    (by omega)
  rw [← toFinset_cornerList] at hb
  exact isStepChain_sheetOperation P rank R hpt (Or.inl rfl) (Or.inr (Or.inl rfl))
    (isHomogenizing_oldLabel R done) (cornerList R.1.index)
    (fun Q hQ => isBlockCornerOf_of_mem_cornerList hQ)
    (hb.mono_error (zpow_neg_thirty_le (by omega) b))

/-- **A birth or death along an edge as a chain of changes, conditional on Proposition 3.4.** At
the constants of the protocol, in the repainting of a square `R` of side `n = 2 ^ j > K₀ t`, let
an elementary birth or death along the edge `e`, inserting or removing a local label `Q` with a
local surrounding label, change one unmodified guide of the repainting into another. The two
point treatments with the surrounding label, the bulk step and the removal of the treatments are
`5` bounded changes, with the bounds of the small-patch rewrites.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 183–221, 328–339 and 375–387. -/
theorem isStepChain_bandOperation (hD : IsAngularScale q J Δ a A₀ m₀ 60 D L₀') (hLL : L₀' ≤ L)
    (hΩ : h.IsGappedGroundState E₀ Ω Δ) (hm₀ : 2 ≤ m₀) (hA₀ : 1 ≤ A₀)
    (hc : IsProtocolConstants K₀ ε₀ ν a D B₀) (hL : 2 ≤ L) (hk2 : 2 ^ k < 2 * L)
    (P : AdaptivePatchSupply (cellCenterPos L) Ω B₀ C c 60 L) (rank : GuideLabel → ℕ)
    (R : RepaintedSquare k) (hlarge : K₀ * (D * Real.log L) < (2 : ℝ) ^ (R.1.1 : ℕ))
    (done : Set (ℤ × ℤ)) {op : BandOperation GuideLabel} {Q : GuideLabel}
    (hop : op.InsertsOne Q) (hlab : IsLocalLabel R done op.label) (hQ : IsLocalLabel R done Q)
    (e : SquareEdge) {g₀ : ℝ × ℝ → GuideLabel}
    (hgb : (repaintBaseline R done).IsUnmodifiedGuide
      (bandUpdate ((2 : ℝ) ^ (R.1.1 : ℕ)) e op.before g₀))
    (hga : (repaintBaseline R done).IsUnmodifiedGuide
      (bandUpdate ((2 : ℝ) ^ (R.1.1 : ℕ)) e op.after g₀))
    (hr : ∀ _ : ℝ × ℝ, 0 < ε₀ * (D * Real.log L) ∧ ε₀ * (D * Real.log L) ≤ B₀ * Real.log L)
    {b K : ℕ} (hb : 1 ≤ b) (hK : 1 ≤ K)
    (hpt : IsPointTreatable P rank R hr done {p | EventUses (.inl R.1) p} (2 * b) K (2 * b)
      ((2 * b + 1) * ((L : ℝ) ^ 20)⁻¹)) :
    IsStepChain (fun F F' => HasFrameChange Ω F F' {p | EventUses (.inl R.1) p} (2 * b) K (2 * b)
        ((2 * b + 1) * ((L : ℝ) ^ 20)⁻¹)) 5
      (treatedFrame (q := q) P rank R hr ∅ op.label
        (bandUpdate ((2 : ℝ) ^ (R.1.1 : ℕ)) e op.before g₀))
      (treatedFrame P rank R hr ∅ op.label
        (bandUpdate ((2 : ℝ) ^ (R.1.1 : ℕ)) e op.after g₀)) := by
  have hbulk : HasFrameChange Ω
      (treatedFrame (q := q) P rank R hr (e.endpointBlocks R.1.index) op.label
        (bandUpdate ((2 : ℝ) ^ (R.1.1 : ℕ)) e op.before g₀))
      (treatedFrame P rank R hr (e.endpointBlocks R.1.index) op.label
        (bandUpdate ((2 : ℝ) ^ (R.1.1 : ℕ)) e op.after g₀)) {p | EventUses (.inl R.1) p}
      (2 * b) K (2 * b) ((L : ℝ) ^ (-30 : ℤ)) := by
    rcases hop.surrounding_eq with hs | hs
    · exact bandBirth_hasFrameChange hD hLL hΩ hm₀ hA₀ hc hL hk2 P rank R hlarge done hop hs e
        hgb hga hlab.eventUses hQ.eventUses hK (by omega)
    · exact bandDeath_hasFrameChange hD hLL hΩ hm₀ hA₀ hc hL hk2 P rank R hlarge done hop hs e
        hgb hga hlab.eventUses hQ.eventUses (by omega) hK (by omega)
  rw [← e.toFinset_endpointList] at hbulk
  have h := isStepChain_sheetOperation P rank R hpt hgb hga hlab (e.endpointList R.1.index)
    (fun Q hQ => e.isBlockCornerOf_of_mem_endpointList hQ)
    (hbulk.mono_error (zpow_neg_thirty_le (by omega) b))
  exact h.cast_length (by cases e <;> rfl)

end TNLean.PEPS.Approximation
