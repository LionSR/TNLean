/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.Protocol.DyadicCentralBirthChange
import TNLean.PEPS.Approximation.Protocol.DyadicSheetOperationChains

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

## The auxiliary births and the main births and deaths along an edge

Along an edge `e` of a square repainted at a large scale, the protocol of Proposition 7.1 of the
polynomial-PEPS manuscript performs three births on the auxiliary sheet before the lens exchange,
and two deaths, a birth and a death on the main sheet after it (`06-geometry.tex`, lines
183–221). With their point treatments these are `15` and `20` changes of one sheet. This file
assembles the two chains, conditional on Proposition 3.4 through `IsAngularScale`.

* `isStepChain_auxBirths` : the three auxiliary births;
* `isStepChain_mainSteps` : the four operations of the main sheet.

### References

* Polynomial-PEPS manuscript (September 24, 2026), §7, `06-geometry.tex`: the edge construction
  (lines 183–221) and the point treatment (lines 328–339).

## The edge construction as a chain of changes of the memory

Along an edge `e` of a square repainted at a large scale, the protocol of Proposition 7.1 of the
polynomial-PEPS manuscript initializes a fresh auxiliary sheet held by the party of `C_e`, performs
three births on it, exchanges the two sheets on the lens, and completes `e` on the main sheet by
four births and deaths (`06-geometry.tex`, lines 183–221). With their point treatments these are
`45` changes of the memory, the main frame followed by the auxiliary frames. This file assembles
them, conditional on Proposition 3.4 through `IsAngularScale`.

* `isStepChain_lensExchange` : the `9` changes of the lens exchange with its point treatments;
* `isStepChain_edgeConstruction` : the `45` changes along one edge.

### References

* Polynomial-PEPS manuscript (September 24, 2026), §7, `06-geometry.tex`: the edge construction
  (lines 183–221), the point treatment (lines 328–339), the lens exchange (lines 389–430) and the
  changes of the memory (lines 572–583 and 658–667).

## A large-scale repainting as a chain of changes of the memory

The protocol of Proposition 7.1 of the polynomial-PEPS manuscript repaints a square of side
`n > K₀ t` by the central birth followed by the edge construction along its four edges
(`06-geometry.tex`, lines 142–221). With their point treatments these are `9 + 4 · 45 = 189`
changes of the memory. This file assembles them, conditional on Proposition 3.4 through
`IsAngularScale`.

* `auxFinal` : the auxiliary sheet of an edge after its construction;
* `isStepChain_largeRepainting` : the `189` changes.

### References

* Polynomial-PEPS manuscript (September 24, 2026), §7, `06-geometry.tex`: the edge construction
  (lines 142–221), the point treatment (lines 328–339) and the changes of the memory
  (lines 572–583).
-/

open ManyBody (Config Qudits SquareLatticeVertex)

section

noncomputable section

namespace TNLean.PEPS.Approximation

open EncodedFrame PairEffect

variable {k q : ℕ} [NeZero q] {a A₀ D L₀' : ℝ} {m₀ : ℕ} {L : ℕ}
  {G : ∀ L : ℕ, EuclideanSpace ℂ (Config (Qudits (SquareLatticeVertex L L) q)) → Prop}
  {Ω : EuclideanSpace ℂ (Config (Qudits (SquareLatticeVertex L L) q))} {K₀ ε₀ ν B₀ C c : ℝ}

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
theorem isStepChain_centralBirth (hD : IsAngularScale q G a A₀ m₀ 60 D L₀') (hLL : L₀' ≤ L)
    (hΩ : G L Ω) (hΩ₁ : ‖Ω‖ = 1) (hm₀ : 4 ≤ m₀) (hA₀ : 1 ≤ A₀)
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
  have hb := centralBirth_hasFrameChange hD hLL hΩ hΩ₁ hm₀ hA₀ hc hL hk2 P rank R hlarge done
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
theorem isStepChain_bandOperation (hD : IsAngularScale q G a A₀ m₀ 60 D L₀') (hLL : L₀' ≤ L)
    (hΩ : G L Ω) (hΩ₁ : ‖Ω‖ = 1) (hm₀ : 2 ≤ m₀) (hA₀ : 1 ≤ A₀)
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
    · exact bandBirth_hasFrameChange hD hLL hΩ hΩ₁ hm₀ hA₀ hc hL hk2 P rank R hlarge done hop hs e
        hgb hga hlab.eventUses hQ.eventUses hK (by omega)
    · exact bandDeath_hasFrameChange hD hLL hΩ hΩ₁ hm₀ hA₀ hc hL hk2 P rank R hlarge done hop hs e
        hgb hga hlab.eventUses hQ.eventUses (by omega) hK (by omega)
  rw [← e.toFinset_endpointList] at hbulk
  have h := isStepChain_sheetOperation P rank R hpt hgb hga hlab (e.endpointList R.1.index)
    (fun Q hQ => e.isBlockCornerOf_of_mem_endpointList hQ)
    (hbulk.mono_error (zpow_neg_thirty_le (by omega) b))
  exact h.cast_length (by cases e <;> rfl)

end TNLean.PEPS.Approximation
end

end

section

noncomputable section

namespace TNLean.PEPS.Approximation

open EncodedFrame PairEffect

/-! ### The chains of one sheet along an edge -/

variable {k q : ℕ} [NeZero q] {a A₀ D L₀' : ℝ} {m₀ : ℕ} {L : ℕ}
  {G : ∀ L : ℕ, EuclideanSpace ℂ (Config (Qudits (SquareLatticeVertex L L) q)) → Prop}
  {Ω : EuclideanSpace ℂ (Config (Qudits (SquareLatticeVertex L L) q))} {K₀ ε₀ ν B₀ C c : ℝ}

/-- **The three auxiliary births, conditional on Proposition 3.4.** At the constants of the
protocol, in the repainting of a square `R` of side `n = 2 ^ j > K₀ t`, the auxiliary sheet of an
edge `e` passes from the uniform guide `C_e` to the auxiliary guide with the word
`eq:geometry-aux-word` by `15` bounded changes with the bounds of the small-patch rewrites; its
frames at both ends are treated at no mark.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 187–197 and 328–339. -/
theorem isStepChain_auxBirths (hD : IsAngularScale q G a A₀ m₀ 60 D L₀') (hLL : L₀' ≤ L)
    (hΩ : G L Ω) (hΩ₁ : ‖Ω‖ = 1) (hm₀ : 2 ≤ m₀) (hA₀ : 1 ≤ A₀)
    (hc : IsProtocolConstants K₀ ε₀ ν a D B₀) (hL : 2 ≤ L) (hk2 : 2 ^ k < 2 * L)
    (P : AdaptivePatchSupply (cellCenterPos L) Ω B₀ C c 60 L) (rank : GuideLabel → ℕ)
    (R : RepaintedSquare k) (hlarge : K₀ * (D * Real.log L) < (2 : ℝ) ^ (R.1.1 : ℕ))
    (done : Set (ℤ × ℤ)) (e : SquareEdge)
    (hr : ∀ _ : ℝ × ℝ, 0 < ε₀ * (D * Real.log L) ∧ ε₀ * (D * Real.log L) ≤ B₀ * Real.log L)
    {b K : ℕ} (hb : 1 ≤ b) (hK : 1 ≤ K)
    (hpt : IsPointTreatable P rank R hr done {p | EventUses (.inl R.1) p} (2 * b) K (2 * b)
      ((2 * b + 1) * ((L : ℝ) ^ 20)⁻¹)) (L₀ : GuideLabel) :
    IsStepChain (fun F F' => HasFrameChange Ω F F' {p | EventUses (.inl R.1) p} (2 * b) K (2 * b)
        ((2 * b + 1) * ((L : ℝ) ^ 20)⁻¹)) 15
      (treatedFrame (q := q) P rank R hr ∅ L₀ ((repaintBaseline R done).auxGuide e
        (bandWord ((repaintBaseline R done).nbrLabel e) [])))
      (treatedFrame P rank R hr ∅ L₀ ((repaintBaseline R done).auxGuide e
        (auxWord (repaintBaseline R done).oldLabel (repaintBaseline R done).finalLabel
          ((repaintBaseline R done).nbrLabel e)))) := by
  set Bl := repaintBaseline R done
  have hA : IsLocalLabel R done Bl.oldLabel := isHomogenizing_oldLabel R done
  have hB : IsLocalLabel R done Bl.finalLabel := isHomogenizing_finalLabel R done
  have hC : IsLocalLabel R done (Bl.nbrLabel e) := isHomogenizing_nbrLabel R done e
  have hU : ∀ W ∈ auxWords Bl.oldLabel Bl.finalLabel (Bl.nbrLabel e),
      Bl.IsUnmodifiedGuide (Bl.auxGuide e W) := fun W hW =>
    Or.inr (Or.inr (Or.inr (Or.inr ⟨e, W, hW, rfl⟩)))
  have h₁ := isStepChain_bandOperation hD hLL hΩ hΩ₁ hm₀ hA₀ hc hL hk2 P rank R hlarge done
    (auxBirthB_insertsOne Bl.finalLabel (Bl.nbrLabel e)) hC hB e
    (g₀ := fun _ => Bl.nbrLabel e) (hU _ (Or.inl rfl))
    (hU _ (Or.inr (Or.inl rfl))) hr hb
    hK hpt
  have h₂ := isStepChain_bandOperation hD hLL hΩ hΩ₁ hm₀ hA₀ hc hL hk2 P rank R hlarge done
    (auxBirthA_insertsOne Bl.oldLabel Bl.finalLabel (Bl.nbrLabel e)) hB hA e
    (g₀ := fun _ => Bl.nbrLabel e) (hU _ (Or.inr (Or.inl rfl)))
    (hU _ (Or.inr (Or.inr (Or.inl rfl)))) hr hb
    hK hpt
  have h₃ := isStepChain_bandOperation hD hLL hΩ hΩ₁ hm₀ hA₀ hc hL hk2 P rank R hlarge done
    (auxBirthC_insertsOne Bl.oldLabel Bl.finalLabel (Bl.nbrLabel e)) hA hC e
    (g₀ := fun _ => Bl.nbrLabel e) (hU _ (Or.inr (Or.inr (Or.inl rfl))))
    (hU _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hr hb
    hK hpt
  simp only [treatedFrame_empty_congr P rank R _ L₀] at h₁ h₂ h₃
  exact (h₁.trans h₂).trans h₃

/-- **The four operations of the main sheet, conditional on Proposition 3.4.** At the constants
of the protocol, in the repainting of a square `R` of side `n = 2 ^ j > K₀ t`, for any edge
list `E` and edge `e`, the main sheet passes from the main guide with the first main word
to the guide with `e` completed by `20` bounded changes with the bounds of the small-patch
rewrites; its frames at both ends are treated at no mark.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 207–221 and 328–339. -/
theorem isStepChain_mainSteps (hD : IsAngularScale q G a A₀ m₀ 60 D L₀') (hLL : L₀' ≤ L)
    (hΩ : G L Ω) (hΩ₁ : ‖Ω‖ = 1) (hm₀ : 2 ≤ m₀) (hA₀ : 1 ≤ A₀)
    (hc : IsProtocolConstants K₀ ε₀ ν a D B₀) (hL : 2 ≤ L) (hk2 : 2 ^ k < 2 * L)
    (P : AdaptivePatchSupply (cellCenterPos L) Ω B₀ C c 60 L) (rank : GuideLabel → ℕ)
    (R : RepaintedSquare k) (hlarge : K₀ * (D * Real.log L) < (2 : ℝ) ^ (R.1.1 : ℕ))
    (done : Set (ℤ × ℤ)) (E : List SquareEdge) (e : SquareEdge)
    (hr : ∀ _ : ℝ × ℝ, 0 < ε₀ * (D * Real.log L) ∧ ε₀ * (D * Real.log L) ≤ B₀ * Real.log L)
    {b K : ℕ} (hb : 1 ≤ b) (hK : 1 ≤ K)
    (hpt : IsPointTreatable P rank R hr done {p | EventUses (.inl R.1) p} (2 * b) K (2 * b)
      ((2 * b + 1) * ((L : ℝ) ^ 20)⁻¹)) (L₀ : GuideLabel) :
    IsStepChain (fun F F' => HasFrameChange Ω F F' {p | EventUses (.inl R.1) p} (2 * b) K (2 * b)
        ((2 * b + 1) * ((L : ℝ) ^ 20)⁻¹)) 20
      (treatedFrame (q := q) P rank R hr ∅ L₀ ((repaintBaseline R done).mainGuide E e
        (mainWordOne (repaintBaseline R done).oldLabel (repaintBaseline R done).finalLabel
          ((repaintBaseline R done).nbrLabel e))))
      (treatedFrame P rank R hr ∅ L₀ ((repaintBaseline R done).completedGuide (e :: E))) := by
  set Bl := repaintBaseline R done
  have hA : IsLocalLabel R done Bl.oldLabel := isHomogenizing_oldLabel R done
  have hB : IsLocalLabel R done Bl.finalLabel := isHomogenizing_finalLabel R done
  have hC : IsLocalLabel R done (Bl.nbrLabel e) := isHomogenizing_nbrLabel R done e
  have hU : ∀ W ∈ mainWords Bl.oldLabel Bl.finalLabel (Bl.nbrLabel e),
      Bl.IsUnmodifiedGuide (Bl.mainGuide E e W) := fun W hW =>
    Or.inr (Or.inr (Or.inr (Or.inl ⟨E, e, W, hW, rfl⟩)))
  have h₁ := isStepChain_bandOperation hD hLL hΩ hΩ₁ hm₀ hA₀ hc hL hk2 P rank R hlarge done
    (mainDeathC_insertsOne Bl.oldLabel Bl.finalLabel (Bl.nbrLabel e)) hA hC e
    (g₀ := Bl.completedGuide E) (hU _ (Or.inr (Or.inl rfl)))
    (hU _ (Or.inr (Or.inr (Or.inl rfl)))) hr hb
    hK hpt
  have h₂ := isStepChain_bandOperation hD hLL hΩ hΩ₁ hm₀ hA₀ hc hL hk2 P rank R hlarge done
    (mainDeathA_insertsOne Bl.oldLabel Bl.finalLabel (Bl.nbrLabel e)) hB hA e
    (g₀ := Bl.completedGuide E) (hU _ (Or.inr (Or.inr (Or.inl rfl))))
    (hU _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hr hb
    hK hpt
  have h₃ := isStepChain_bandOperation hD hLL hΩ hΩ₁ hm₀ hA₀ hc hL hk2 P rank R hlarge done
    (mainBirthC_insertsOne Bl.finalLabel (Bl.nbrLabel e)) hB hC e
    (g₀ := Bl.completedGuide E) (hU _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (hU _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) hr hb
    hK hpt
  have h₄ := isStepChain_bandOperation hD hLL hΩ hΩ₁ hm₀ hA₀ hc hL hk2 P rank R hlarge done
    (mainDeathB_insertsOne Bl.finalLabel (Bl.nbrLabel e)) hC hB e
    (g₀ := Bl.completedGuide E) (hU _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (hU _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))) hr hb
    hK hpt
  simp only [treatedFrame_empty_congr P rank R _ L₀] at h₁ h₂ h₃ h₄
  exact ((h₁.trans h₂).trans h₃).trans h₄

end TNLean.PEPS.Approximation
end

end

section

noncomputable section

namespace TNLean.PEPS.Approximation

open EncodedFrame PairEffect

variable {k q : ℕ} [NeZero q] {a A₀ D L₀' : ℝ} {m₀ : ℕ} {L : ℕ}
  {G : ∀ L : ℕ, EuclideanSpace ℂ (Config (Qudits (SquareLatticeVertex L L) q)) → Prop}
  {Ω : EuclideanSpace ℂ (Config (Qudits (SquareLatticeVertex L L) q))} {K₀ ε₀ ν B₀ C c : ℝ}
  {X : Type*} [DecidableEq X]

/-- **The lens exchange with its point treatments, conditional on Proposition 3.4.** At the
constants of the protocol, in the repainting of a square `R` of side `n = 2 ^ j > K₀ t`, let the
memory carry the main sheet with the starting word for any edge list `E` and edge `e` and,
at the index `x`, the auxiliary sheet of `e` with the auxiliary word, both treated at no mark.
The point treatments of both sheets about the endpoints of `e`, the lens exchange and removal
of the treatments are `9` bounded changes of the memory, with the small-patch rewrite bounds.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 198–212, 328–339 and 389–430. -/
theorem isStepChain_lensExchange (hD : IsAngularScale q G a A₀ m₀ 60 D L₀') (hLL : L₀' ≤ L)
    (hΩ : G L Ω) (hΩ₁ : ‖Ω‖ = 1) (hm₀ : 2 ≤ m₀) (hA₀ : 1 ≤ A₀)
    (hc : IsProtocolConstants K₀ ε₀ ν a D B₀) (hL : 2 ≤ L) (hk2 : 2 ^ k < 2 * L)
    (P : AdaptivePatchSupply (cellCenterPos L) Ω B₀ C c 60 L) (rank : GuideLabel → ℕ)
    (R : RepaintedSquare k) (hlarge : K₀ * (D * Real.log L) < (2 : ℝ) ^ (R.1.1 : ℕ))
    (done : Set (ℤ × ℤ)) (E : List SquareEdge) (e : SquareEdge)
    (hr : ∀ _ : ℝ × ℝ, 0 < ε₀ * (D * Real.log L) ∧ ε₀ * (D * Real.log L) ≤ B₀ * Real.log L)
    {b K : ℕ} (hb : 2 ≤ b)
    (hpt : IsPointTreatable P rank R hr done {p | EventUses (.inl R.1) p} (2 * b) K (2 * b)
      ((2 * b + 1) * ((L : ℝ) ^ 20)⁻¹))
    {l : List X} (hl : l.Nodup) {x : X} (hx : x ∈ l) (A : X → Frame (cellCenterPos L) q
      (ProtocolParty k)) :
    let Bl := repaintBaseline R done
    IsStepChain (fun Fs Fs' => HasSourceBoundedChange Ω Fs Fs'
      (EuclideanSpace.single (fun _ ↦ ()) 1)
        {p | EventUses (.inl R.1) p} (2 * b) K (2 * b) ((2 * b + 1) * ((L : ℝ) ^ 20)⁻¹) ∧
          Fs' ≠ []) 9
      (treatedFrame (q := q) P rank R hr ∅ (Bl.nbrLabel e)
          (Bl.mainGuide E e (edgeStartWord Bl.oldLabel Bl.finalLabel (Bl.nbrLabel e))) ::
        l.map (Function.update A x (treatedFrame P rank R hr ∅ (Bl.nbrLabel e)
          (Bl.auxGuide e (auxWord Bl.oldLabel Bl.finalLabel (Bl.nbrLabel e))))))
      (treatedFrame P rank R hr ∅ (Bl.nbrLabel e)
          (Bl.mainGuide E e (mainWordOne Bl.oldLabel Bl.finalLabel (Bl.nbrLabel e))) ::
        l.map (Function.update A x (treatedFrame P rank R hr ∅ (Bl.nbrLabel e)
          (Bl.auxGuide e (auxWordExchanged Bl.oldLabel Bl.finalLabel (Bl.nbrLabel e)))))) := by
  have hΩ1 : ‖Ω‖ ≤ 1 := hΩ₁.le
  intro Bl
  classical
  set Ce := Bl.nbrLabel e
  have hC : IsLocalLabel R done Ce := isHomogenizing_nbrLabel R done e
  set ms := e.endpointList R.1.index
  have hms : ∀ Q ∈ ms, IsBlockCornerOf R.1.index Q :=
    fun Q hQ => e.isBlockCornerOf_of_mem_endpointList hQ
  have hdiff : ∀ (M : Finset (ℤ × ℤ)) Q₀ Q, Q ≠ Q₀ → (Q ∈ M ↔ Q ∈ insert Q₀ M) :=
    fun M Q₀ Q hQ => by simp [hQ]
  set gm := Bl.mainGuide E e (edgeStartWord Bl.oldLabel Bl.finalLabel Ce)
  set gm' := Bl.mainGuide E e (mainWordOne Bl.oldLabel Bl.finalLabel Ce)
  set ga := Bl.auxGuide e (auxWord Bl.oldLabel Bl.finalLabel Ce)
  set ga' := Bl.auxGuide e (auxWordExchanged Bl.oldLabel Bl.finalLabel Ce)
  have hum : Bl.IsUnmodifiedGuide gm := Or.inr (Or.inr (Or.inr (Or.inl ⟨E, e, _, Or.inl rfl, rfl⟩)))
  have hum' : Bl.IsUnmodifiedGuide gm' :=
    Or.inr (Or.inr (Or.inr (Or.inl ⟨E, e, _, Or.inr (Or.inl rfl), rfl⟩)))
  have hua : Bl.IsUnmodifiedGuide ga :=
    Or.inr (Or.inr (Or.inr (Or.inr ⟨e, _, Or.inr (Or.inr (Or.inr (Or.inl rfl))), rfl⟩)))
  have hua' : Bl.IsUnmodifiedGuide ga' :=
    Or.inr (Or.inr (Or.inr (Or.inr ⟨e, _, Or.inr (Or.inr (Or.inr (Or.inr rfl))), rfl⟩)))
  set T : (ℝ × ℝ → GuideLabel) → Finset (ℤ × ℤ) → Frame (cellCenterPos L) q (ProtocolParty k) :=
    fun g M => treatedFrame (q := q) P rank R hr M Ce g
  have htreat : ∀ {g}, Bl.IsUnmodifiedGuide g →
      IsStepChain (fun F F' => HasFrameChange Ω F F' {p | EventUses (.inl R.1) p} (2 * b) K
        (2 * b) ((2 * b + 1) * ((L : ℝ) ^ 20)⁻¹)) ms.length (T g ∅) (T g ms.toFinset) :=
    fun hg => IsStepChain.treat (T _) ms fun M Q hQ => hpt hg Q (hms Q hQ) (hdiff M Q) Ce hC
  have huntreat : ∀ {g}, Bl.IsUnmodifiedGuide g →
      IsStepChain (fun F F' => HasFrameChange Ω F F' {p | EventUses (.inl R.1) p} (2 * b) K
        (2 * b) ((2 * b + 1) * ((L : ℝ) ^ 20)⁻¹)) ms.length (T g ms.toFinset) (T g ∅) :=
    fun hg => IsStepChain.untreat (T _) ms fun M Q hQ =>
      hpt hg Q (hms Q hQ) (fun Q' hQ' => (hdiff M Q Q' hQ').symm) Ce hC
  have hlen : ms.length = 2 := by cases e <;> rfl
  -- the lens exchange on the treated sheets
  have hpair := (edgeExchange_hasPairChange hD hLL hΩ hΩ₁ hm₀ hA₀ hc hL hk2 P rank R hlarge done E e
    (S := {p | EventUses (.inl R.1) p}) (r := 2 * b) (K := K) (rs := 2 * b)).mono_error
    (four_mul_zpow_neg_thirty_le (by omega) hb)
  rw [← e.toFinset_endpointList] at hpair
  have h₃ : HasSourceBoundedChange Ω
      (T gm ms.toFinset :: l.map (Function.update A x (T ga ms.toFinset)))
      (T gm' ms.toFinset :: l.map (Function.update A x (T ga' ms.toFinset)))
        (EuclideanSpace.single (fun _ ↦ ()) 1)
      {p | EventUses (.inl R.1) p} (2 * b) K (2 * b) ((2 * b + 1) * ((L : ℝ) ^ 20)⁻¹) := by
    have := hasSourceBoundedChange_of_hasPairChange hl hx
      (A := Function.update A x (T ga ms.toFinset)) (Function.update_self x _ A) hΩ1 hpair
    rwa [Function.update_idem] at this
  have c₁ := isStepChain_main l (Function.update A x (T ga ∅)) hΩ1 (htreat hum)
  have c₂ := isStepChain_aux (T gm ms.toFinset) hl hx A hΩ1 (htreat hua)
  have c₄ := isStepChain_main l (Function.update A x (T ga' ms.toFinset)) hΩ1
    (huntreat hum')
  have c₅ := isStepChain_aux (T gm' ∅) hl hx A hΩ1 (huntreat hua')
  have c₃ := IsStepChain.single (Rel := fun Fs Fs' => HasSourceBoundedChange Ω Fs Fs'
    (EuclideanSpace.single (fun _ ↦ ()) 1) {p | EventUses (.inl R.1) p} (2 * b) K (2 * b)
      ((2 * b + 1) * ((L : ℝ) ^ 20)⁻¹) ∧ Fs' ≠ []) ⟨h₃, List.cons_ne_nil _ _⟩
  exact ((((c₁.trans c₂).trans c₃).trans c₄).trans c₅).cast_length (by rw [hlen])

/-- **The edge construction as a chain of changes, conditional on Proposition 3.4.** At the
constants of the protocol, in the repainting of a square `R` of side `n = 2 ^ j > K₀ t`, let the
memory carry the main sheet with the central birth and the edges of `E` done, treated at no mark,
and, at the index `x`, the raw copy held by the party of the label `C_e` across an edge `e ∉ E`.
The initialization of the auxiliary sheet of `e`, its three births, the lens exchange and the four
operations of the main sheet, with their point treatments, are `45` bounded changes of the memory
with the bounds of the small-patch rewrites. They complete `e` on the main sheet and leave the
auxiliary sheet of `e` with the exchanged auxiliary word.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 183–221, 328–339 and 572–583. -/
theorem isStepChain_edgeConstruction (hD : IsAngularScale q G a A₀ m₀ 60 D L₀')
    (hLL : L₀' ≤ L) (hΩ : G L Ω) (hΩ₁ : ‖Ω‖ = 1) (hm₀ : 2 ≤ m₀)
    (hA₀ : 1 ≤ A₀) (hc : IsProtocolConstants K₀ ε₀ ν a D B₀) (hL : 2 ≤ L) (hk2 : 2 ^ k < 2 * L)
    (P : AdaptivePatchSupply (cellCenterPos L) Ω B₀ C c 60 L) (rank : GuideLabel → ℕ)
    (R : RepaintedSquare k) (hlarge : K₀ * (D * Real.log L) < (2 : ℝ) ^ (R.1.1 : ℕ))
    (done : Set (ℤ × ℤ)) {E : List SquareEdge} {e : SquareEdge} (he : e ∉ E)
    (hr : ∀ _ : ℝ × ℝ, 0 < ε₀ * (D * Real.log L) ∧ ε₀ * (D * Real.log L) ≤ B₀ * Real.log L)
    {b K : ℕ} (hb : 2 ≤ b) (hK : 1 ≤ K)
    (hpt : IsPointTreatable P rank R hr done {p | EventUses (.inl R.1) p} (2 * b) K (2 * b)
      ((2 * b + 1) * ((L : ℝ) ^ 20)⁻¹))
    {l : List X} (hl : l.Nodup) {x : X} (hx : x ∈ l)
    {A : X → Frame (cellCenterPos L) q (ProtocolParty k)}
    (hA : A x = Frame.raw fun _ => labelParty R ((repaintBaseline R done).nbrLabel e))
    (L₁ L₂ : GuideLabel) :
    let Bl := repaintBaseline R done
    IsStepChain (fun Fs Fs' => HasSourceBoundedChange Ω Fs Fs'
      (EuclideanSpace.single (fun _ ↦ ()) 1)
        {p | EventUses (.inl R.1) p} (2 * b) K (2 * b) ((2 * b + 1) * ((L : ℝ) ^ 20)⁻¹) ∧
          Fs' ≠ []) 45
      (treatedFrame (q := q) P rank R hr ∅ L₁ (Bl.completedGuide E) :: l.map A)
      (treatedFrame P rank R hr ∅ L₂ (Bl.completedGuide (e :: E)) ::
        l.map (Function.update A x (treatedFrame P rank R hr ∅ (Bl.nbrLabel e)
          (Bl.auxGuide e (auxWordExchanged Bl.oldLabel Bl.finalLabel (Bl.nbrLabel e)))))) := by
  have hΩ1 : ‖Ω‖ ≤ 1 := hΩ₁.le
  intro Bl
  set Ce := Bl.nbrLabel e
  have hε0 : (0 : ℝ) ≤ (2 * b + 1) * ((L : ℝ) ^ 20)⁻¹ := by positivity
  have haux0 : treatedFrame (q := q) P rank R hr ∅ Ce (Bl.auxGuide e (bandWord Ce [])) = A x :=
    (treatedFrame_auxStart_eq_raw P rank R hr done e Ce).trans hA.symm
  have hstart := treatedFrame_edgeStart (q := q) P rank R hc hL hlarge done he Ce Ce
  have c₀ : IsStepChain (fun Fs Fs' => HasSourceBoundedChange Ω Fs Fs'
    (EuclideanSpace.single (fun _ ↦ ()) 1)
      {p | EventUses (.inl R.1) p} (2 * b) K (2 * b) ((2 * b + 1) * ((L : ℝ) ^ 20)⁻¹) ∧
        Fs' ≠ []) 1
      (treatedFrame (q := q) P rank R hr ∅ L₁ (Bl.completedGuide E) :: l.map A)
      (treatedFrame (q := q) P rank R hr ∅ Ce (Bl.completedGuide E) ::
        l.map (Function.update A x
          (treatedFrame (q := q) P rank R hr ∅ Ce (Bl.auxGuide e (bandWord Ce []))))) := by
    rw [haux0, Function.update_eq_self, treatedFrame_empty_congr P rank R L₁ Ce]
    exact IsStepChain.single ⟨hasSourceBoundedChange_refl _ _ _ _ _ _ hε0, List.cons_ne_nil _ _⟩
  have c₁ := isStepChain_aux (treatedFrame (q := q) P rank R hr ∅ Ce (Bl.completedGuide E)) hl
    hx A hΩ1 (isStepChain_auxBirths hD hLL hΩ hΩ₁ hm₀ hA₀ hc hL hk2 P rank R hlarge done e hr
      (by omega) hK hpt Ce)
  have c₂ := isStepChain_lensExchange hD hLL hΩ hΩ₁ hm₀ hA₀ hc hL hk2 P rank R hlarge done E e hr
    hb hpt hl hx A
  have c₃ := isStepChain_main l (Function.update A x (treatedFrame P rank R hr ∅ Ce
    (Bl.auxGuide e (auxWordExchanged Bl.oldLabel Bl.finalLabel Ce)))) hΩ1
    (isStepChain_mainSteps hD hLL hΩ hΩ₁ hm₀ hA₀ hc hL hk2 P rank R hlarge done E e hr (by omega) hK
      hpt Ce)
  dsimp only at c₂
  rw [← hstart] at c₂
  rw [treatedFrame_empty_congr P rank R L₂ Ce]
  exact ((c₀.trans c₁).trans c₂).trans c₃

end TNLean.PEPS.Approximation
end

end

section

noncomputable section

namespace TNLean.PEPS.Approximation

open EncodedFrame

variable {k q : ℕ} [NeZero q] {a A₀ D L₀' : ℝ} {m₀ : ℕ} {L : ℕ}
  {G : ∀ L : ℕ, EuclideanSpace ℂ (Config (Qudits (SquareLatticeVertex L L) q)) → Prop}
  {Ω : EuclideanSpace ℂ (Config (Qudits (SquareLatticeVertex L L) q))} {K₀ ε₀ ν B₀ C c : ℝ}
  {X : Type*} [DecidableEq X]

/-- The frame of the auxiliary sheet of the edge `e` after the edge construction: the auxiliary
guide with the exchanged auxiliary word, treated at no mark.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 198–214 and 620–624. -/
def auxFinal (P : AdaptivePatchSupply (cellCenterPos L) Ω B₀ C c 60 L) (rank : GuideLabel → ℕ)
    (R : RepaintedSquare k)
    (hr : ∀ _ : ℝ × ℝ, 0 < ε₀ * (D * Real.log L) ∧ ε₀ * (D * Real.log L) ≤ B₀ * Real.log L)
    (done : Set (ℤ × ℤ)) (e : SquareEdge) : Frame (cellCenterPos L) q (ProtocolParty k) :=
  treatedFrame P rank R hr ∅ ((repaintBaseline R done).nbrLabel e)
    ((repaintBaseline R done).auxGuide e (auxWordExchanged (repaintBaseline R done).oldLabel
      (repaintBaseline R done).finalLabel ((repaintBaseline R done).nbrLabel e)))

/-- **A large-scale repainting as a chain of changes, conditional on Proposition 3.4.** At the
constants of the protocol, in the repainting of a square `R` of side `n = 2 ^ j > K₀ t`, let the
memory carry the main sheet with the starting guide, treated at no mark, and, at the distinct
indices `xs e` of the four edges, the raw copies held by the parties of the labels across them.
The central birth and the edge constructions along the four edges, with their point treatments,
are `189` bounded changes of the memory with the bounds of the small-patch rewrites. They leave
the main sheet with the four edges completed and the auxiliary sheets with the exchanged
auxiliary words.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 142–221, 328–339 and 572–583. -/
theorem isStepChain_largeRepainting (hD : IsAngularScale q G a A₀ m₀ 60 D L₀')
    (hLL : L₀' ≤ L) (hΩ : G L Ω) (hΩ₁ : ‖Ω‖ = 1) (hm₀ : 4 ≤ m₀)
    (hA₀ : 1 ≤ A₀) (hc : IsProtocolConstants K₀ ε₀ ν a D B₀) (hL : 2 ≤ L) (hk2 : 2 ^ k < 2 * L)
    (P : AdaptivePatchSupply (cellCenterPos L) Ω B₀ C c 60 L) (rank : GuideLabel → ℕ)
    (R : RepaintedSquare k) (hlarge : K₀ * (D * Real.log L) < (2 : ℝ) ^ (R.1.1 : ℕ))
    (done : Set (ℤ × ℤ))
    (hr : ∀ _ : ℝ × ℝ, 0 < ε₀ * (D * Real.log L) ∧ ε₀ * (D * Real.log L) ≤ B₀ * Real.log L)
    {b K : ℕ} (hb : 2 ≤ b) (hK : 1 ≤ K)
    (hpt : IsPointTreatable P rank R hr done {p | EventUses (.inl R.1) p} (2 * b) K (2 * b)
      ((2 * b + 1) * ((L : ℝ) ^ 20)⁻¹))
    {l : List X} (hl : l.Nodup) (xs : SquareEdge → X) (hxs : ∀ e, xs e ∈ l)
    (hinj : Function.Injective xs) {A : X → Frame (cellCenterPos L) q (ProtocolParty k)}
    (hA : ∀ e, A (xs e) = Frame.raw fun _ => labelParty R ((repaintBaseline R done).nbrLabel e))
    (L₁ L₂ : GuideLabel) :
    IsStepChain (fun Fs Fs' => HasSourceBoundedChange Ω Fs Fs'
      (EuclideanSpace.single (fun _ ↦ ()) 1)
        {p | EventUses (.inl R.1) p} (2 * b) K (2 * b) ((2 * b + 1) * ((L : ℝ) ^ 20)⁻¹) ∧
          Fs' ≠ []) 189
      (treatedFrame (q := q) P rank R hr ∅ L₁ (repaintBaseline R done).guide :: l.map A)
      (treatedFrame P rank R hr ∅ L₂ ((repaintBaseline R done).completedGuide
          [.left, .top, .right, .bottom]) ::
        l.map (Function.update (Function.update (Function.update (Function.update A
          (xs .bottom) (auxFinal P rank R hr done .bottom)) (xs .right)
            (auxFinal P rank R hr done .right)) (xs .top) (auxFinal P rank R hr done .top))
              (xs .left) (auxFinal P rank R hr done .left))) := by
  have hΩ1 : ‖Ω‖ ≤ 1 := hΩ₁.le
  set Bl := repaintBaseline R done
  have hne : ∀ {e e' : SquareEdge}, e ≠ e' → xs e ≠ xs e' := fun h h' => h (hinj h')
  have c₀ := isStepChain_main l A hΩ1 (isStepChain_centralBirth hD hLL hΩ hΩ₁ hm₀ hA₀ hc hL hk2 P
    rank R hlarge done hr (by omega) hK hpt)
  rw [← treatedFrame_empty_congr P rank R L₁] at c₀
  have edge := fun {E : List SquareEdge} {e : SquareEdge} (he : e ∉ E)
      {A' : X → Frame (cellCenterPos L) q (ProtocolParty k)}
      (hA' : A' (xs e) = Frame.raw fun _ => labelParty R (Bl.nbrLabel e)) (L₁ L₂ : GuideLabel) =>
    isStepChain_edgeConstruction hD hLL hΩ hΩ₁ (by omega) hA₀ hc hL hk2 P rank R hlarge done he
      hr hb hK hpt hl (hxs e) hA' L₁ L₂
  have c₁ := edge (E := []) (e := .bottom) (by simp) (hA .bottom) Bl.oldLabel Bl.oldLabel
  have c₂ := edge (E := [.bottom]) (e := .right) (by simp) (A' := Function.update A (xs .bottom)
    (auxFinal P rank R hr done .bottom))
    (by rw [Function.update_of_ne (hne (by decide))]; exact hA .right) Bl.oldLabel Bl.oldLabel
  have c₃ := edge (E := [.right, .bottom]) (e := .top) (by simp)
    (A' := Function.update (Function.update A (xs .bottom) (auxFinal P rank R hr done .bottom))
      (xs .right) (auxFinal P rank R hr done .right))
    (by rw [Function.update_of_ne (hne (by decide)), Function.update_of_ne (hne (by decide))]
        exact hA .top) Bl.oldLabel Bl.oldLabel
  have c₄ := edge (E := [.top, .right, .bottom]) (e := .left) (by simp)
    (A' := Function.update (Function.update (Function.update A (xs .bottom)
      (auxFinal P rank R hr done .bottom)) (xs .right) (auxFinal P rank R hr done .right))
        (xs .top) (auxFinal P rank R hr done .top))
    (by rw [Function.update_of_ne (hne (by decide)), Function.update_of_ne (hne (by decide)),
          Function.update_of_ne (hne (by decide))]
        exact hA .left) Bl.oldLabel L₂
  dsimp only at c₁ c₂ c₃ c₄
  exact (((c₀.trans c₁).trans c₂).trans c₃).trans c₄

end TNLean.PEPS.Approximation
end

end
