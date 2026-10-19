/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicEdgeConstructionChain

/-!
# A large-scale repainting as a chain of changes of the memory

The protocol of Proposition 7.1 of the polynomial-PEPS manuscript repaints a square of side
`n > K₀ t` by the central birth followed by the edge construction along its four edges
(`06-geometry.tex`, lines 142–221). With their point treatments these are `9 + 4 · 45 = 189`
changes of the memory. This file assembles them, conditional on Proposition 3.4 through
`IsAngularScale`.

* `auxFinal` : the auxiliary sheet of an edge after its construction;
* `isStepChain_largeRepainting` : the `189` changes.

## References

* Polynomial-PEPS manuscript (September 24, 2026), §7, `06-geometry.tex`: the edge construction
  (lines 142–221), the point treatment (lines 328–339) and the changes of the memory
  (lines 572–583).
-/

noncomputable section

namespace TNLean.PEPS.Approximation

open EncodedFrame

variable {k q : ℕ} [NeZero q] {J Δ a A₀ D L₀' : ℝ} {m₀ : ℕ} {L : ℕ}
  {h : SquareHamiltonian L q J} {E₀ : ℝ} {Ω : StateSpace L q} {K₀ ε₀ ν B₀ C c : ℝ}
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
theorem isStepChain_largeRepainting (hD : IsAngularScale q J Δ a A₀ m₀ 60 D L₀')
    (hLL : L₀' ≤ L) (hΩ : h.IsGappedGroundState E₀ Ω Δ) (hm₀ : 4 ≤ m₀)
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
    IsStepChain (fun Fs Fs' => HasSourceBoundedChange Ω Fs Fs' (ℓ := []) (1 : ℂ)
        {p | EventUses (.inl R.1) p} (2 * b) K (2 * b) ((2 * b + 1) * ((L : ℝ) ^ 20)⁻¹) ∧
          Fs' ≠ []) 189
      (treatedFrame (q := q) P rank R hr ∅ L₁ (repaintBaseline R done).guide :: l.map A)
      (treatedFrame P rank R hr ∅ L₂ ((repaintBaseline R done).completedGuide
          [.left, .top, .right, .bottom]) ::
        l.map (Function.update (Function.update (Function.update (Function.update A
          (xs .bottom) (auxFinal P rank R hr done .bottom)) (xs .right)
            (auxFinal P rank R hr done .right)) (xs .top) (auxFinal P rank R hr done .top))
              (xs .left) (auxFinal P rank R hr done .left))) := by
  have hΩ1 : ‖Ω‖ ≤ 1 := hΩ.1.le
  set Bl := repaintBaseline R done
  have hne : ∀ {e e' : SquareEdge}, e ≠ e' → xs e ≠ xs e' := fun h h' => h (hinj h')
  have c₀ := isStepChain_main l A hΩ1 (isStepChain_centralBirth hD hLL hΩ hm₀ hA₀ hc hL hk2 P
    rank R hlarge done hr (by omega) hK hpt)
  rw [← treatedFrame_empty_congr P rank R L₁] at c₀
  have edge := fun {E : List SquareEdge} {e : SquareEdge} (he : e ∉ E)
      {A' : X → Frame (cellCenterPos L) q (ProtocolParty k)}
      (hA' : A' (xs e) = Frame.raw fun _ => labelParty R (Bl.nbrLabel e)) (L₁ L₂ : GuideLabel) =>
    isStepChain_edgeConstruction hD hLL hΩ (by omega) hA₀ hc hL hk2 P rank R hlarge done he
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
