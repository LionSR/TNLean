/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicBulkOperationChains

/-!
# The auxiliary births and the main births and deaths along an edge

Along an edge `e` of a square repainted at a large scale, the protocol of Proposition 7.1 of the
polynomial-PEPS manuscript performs three births on the auxiliary sheet before the lens exchange,
and two deaths, a birth and a death on the main sheet after it (`06-geometry.tex`, lines
183–221). With their point treatments these are `15` and `20` changes of one sheet. This file
assembles the two chains, conditional on Proposition 3.4 through `IsAngularScale`.

* `auxBirthB_insertsOne`, …, `mainDeathB_insertsOne` : the label each operation introduces;
* `isStepChain_auxBirths` : the three auxiliary births;
* `isStepChain_mainSteps` : the four operations of the main sheet.

## References

* Polynomial-PEPS manuscript (September 24, 2026), §7, `06-geometry.tex`: the edge construction
  (lines 183–221) and the point treatment (lines 328–339).
-/

noncomputable section

namespace TNLean.PEPS.Approximation

open EncodedFrame PairEffect

/-! ### The chains of one sheet along an edge -/

variable {k q : ℕ} [NeZero q] {J Δ a A₀ D L₀' : ℝ} {m₀ : ℕ} {L : ℕ}
  {h : SquareHamiltonian L q J} {E₀ : ℝ} {Ω : StateSpace L q} {K₀ ε₀ ν B₀ C c : ℝ}

/-- **The three auxiliary births, conditional on Proposition 3.4.** At the constants of the
protocol, in the repainting of a square `R` of side `n = 2 ^ j > K₀ t`, the auxiliary sheet of an
edge `e` passes from the uniform guide `C_e` to the auxiliary guide with the word
`eq:geometry-aux-word` by `15` bounded changes with the bounds of the small-patch rewrites; its
frames at both ends are treated at no mark.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 187–197 and 328–339. -/
theorem isStepChain_auxBirths (hD : IsAngularScale q J Δ a A₀ m₀ 60 D L₀') (hLL : L₀' ≤ L)
    (hΩ : h.IsGappedGroundState E₀ Ω Δ) (hm₀ : 2 ≤ m₀) (hA₀ : 1 ≤ A₀)
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
  have h₁ := isStepChain_bandOperation hD hLL hΩ hm₀ hA₀ hc hL hk2 P rank R hlarge done
    (auxBirthB_insertsOne Bl.finalLabel (Bl.nbrLabel e)) hC hB e
    (g₀ := fun _ => Bl.nbrLabel e) (hU _ (Or.inl rfl))
    (hU _ (Or.inr (Or.inl rfl))) hr hb
    hK hpt
  have h₂ := isStepChain_bandOperation hD hLL hΩ hm₀ hA₀ hc hL hk2 P rank R hlarge done
    (auxBirthA_insertsOne Bl.oldLabel Bl.finalLabel (Bl.nbrLabel e)) hB hA e
    (g₀ := fun _ => Bl.nbrLabel e) (hU _ (Or.inr (Or.inl rfl)))
    (hU _ (Or.inr (Or.inr (Or.inl rfl)))) hr hb
    hK hpt
  have h₃ := isStepChain_bandOperation hD hLL hΩ hm₀ hA₀ hc hL hk2 P rank R hlarge done
    (auxBirthC_insertsOne Bl.oldLabel Bl.finalLabel (Bl.nbrLabel e)) hA hC e
    (g₀ := fun _ => Bl.nbrLabel e) (hU _ (Or.inr (Or.inr (Or.inl rfl))))
    (hU _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hr hb
    hK hpt
  simp only [treatedFrame_empty_congr P rank R _ L₀] at h₁ h₂ h₃
  exact (h₁.trans h₂).trans h₃

/-- **The four operations of the main sheet, conditional on Proposition 3.4.** At the constants
of the protocol, in the repainting of a square `R` of side `n = 2 ^ j > K₀ t`, after the lens
exchange along an edge `e ∉ E` the main sheet passes from the main guide with the first main word
to the guide with `e` completed by `20` bounded changes with the bounds of the small-patch
rewrites; its frames at both ends are treated at no mark.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 207–221 and 328–339. -/
theorem isStepChain_mainSteps (hD : IsAngularScale q J Δ a A₀ m₀ 60 D L₀') (hLL : L₀' ≤ L)
    (hΩ : h.IsGappedGroundState E₀ Ω Δ) (hm₀ : 2 ≤ m₀) (hA₀ : 1 ≤ A₀)
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
  have h₁ := isStepChain_bandOperation hD hLL hΩ hm₀ hA₀ hc hL hk2 P rank R hlarge done
    (mainDeathC_insertsOne Bl.oldLabel Bl.finalLabel (Bl.nbrLabel e)) hA hC e
    (g₀ := Bl.completedGuide E) (hU _ (Or.inr (Or.inl rfl)))
    (hU _ (Or.inr (Or.inr (Or.inl rfl)))) hr hb
    hK hpt
  have h₂ := isStepChain_bandOperation hD hLL hΩ hm₀ hA₀ hc hL hk2 P rank R hlarge done
    (mainDeathA_insertsOne Bl.oldLabel Bl.finalLabel (Bl.nbrLabel e)) hB hA e
    (g₀ := Bl.completedGuide E) (hU _ (Or.inr (Or.inr (Or.inl rfl))))
    (hU _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hr hb
    hK hpt
  have h₃ := isStepChain_bandOperation hD hLL hΩ hm₀ hA₀ hc hL hk2 P rank R hlarge done
    (mainBirthC_insertsOne Bl.finalLabel (Bl.nbrLabel e)) hB hC e
    (g₀ := Bl.completedGuide E) (hU _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (hU _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) hr hb
    hK hpt
  have h₄ := isStepChain_bandOperation hD hLL hΩ hm₀ hA₀ hc hL hk2 P rank R hlarge done
    (mainDeathB_insertsOne Bl.finalLabel (Bl.nbrLabel e)) hC hB e
    (g₀ := Bl.completedGuide E) (hU _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (hU _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))) hr hb
    hK hpt
  simp only [treatedFrame_empty_congr P rank R _ L₀] at h₁ h₂ h₃ h₄
  exact ((h₁.trans h₂).trans h₃).trans h₄

end TNLean.PEPS.Approximation
