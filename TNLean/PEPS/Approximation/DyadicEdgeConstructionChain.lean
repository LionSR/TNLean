/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicEdgeOperationChains

/-!
# The edge construction as a chain of changes of the memory

Along an edge `e` of a square repainted at a large scale, the protocol of Proposition 7.1 of the
polynomial-PEPS manuscript initializes a fresh auxiliary sheet held by the party of `C_e`, performs
three births on it, exchanges the two sheets on the lens, and completes `e` on the main sheet by
four births and deaths (`06-geometry.tex`, lines 183–221). With their point treatments these are
`45` changes of the memory, the main frame followed by the auxiliary frames. This file assembles
them, conditional on Proposition 3.4 through `IsAngularScale`.

* `isStepChain_lensExchange` : the `9` changes of the lens exchange with its point treatments;
* `isStepChain_edgeConstruction` : the `45` changes along one edge.

## References

* Polynomial-PEPS manuscript (September 24, 2026), §7, `06-geometry.tex`: the edge construction
  (lines 183–221), the point treatment (lines 328–339), the lens exchange (lines 389–430) and the
  changes of the memory (lines 572–583 and 658–667).
-/

noncomputable section

namespace TNLean.PEPS.Approximation

open EncodedFrame PairEffect

variable {k q : ℕ} [NeZero q] {J Δ a A₀ D L₀' : ℝ} {m₀ : ℕ} {L : ℕ}
  {h : SquareHamiltonian L q J} {E₀ : ℝ} {Ω : StateSpace L q} {K₀ ε₀ ν B₀ C c : ℝ}
  {X : Type*} [DecidableEq X]

/-- **The lens exchange with its point treatments, conditional on Proposition 3.4.** At the
constants of the protocol, in the repainting of a square `R` of side `n = 2 ^ j > K₀ t`, let the
memory carry the main sheet with the starting word along `e ∉ E` and, at the index `x`, the
auxiliary sheet of `e` with the auxiliary word, both treated at no mark. The point treatments of
both sheets about the endpoints of `e`, the lens exchange and the removal of the treatments are
`9` bounded changes of the memory, with the bounds of the small-patch rewrites.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 198–212, 328–339 and 389–430. -/
theorem isStepChain_lensExchange (hD : IsAngularScale q J Δ a A₀ m₀ 60 D L₀') (hLL : L₀' ≤ L)
    (hΩ : h.IsGappedGroundState E₀ Ω Δ) (hm₀ : 2 ≤ m₀) (hA₀ : 1 ≤ A₀)
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
    IsStepChain (fun Fs Fs' => HasSourceBoundedChange Ω Fs Fs' (ℓ := []) (1 : ℂ)
        {p | EventUses (.inl R.1) p} (2 * b) K (2 * b) ((2 * b + 1) * ((L : ℝ) ^ 20)⁻¹)) 9
      (treatedFrame (q := q) P rank R hr ∅ (Bl.nbrLabel e)
          (Bl.mainGuide E e (edgeStartWord Bl.oldLabel Bl.finalLabel (Bl.nbrLabel e))) ::
        l.map (Function.update A x (treatedFrame P rank R hr ∅ (Bl.nbrLabel e)
          (Bl.auxGuide e (auxWord Bl.oldLabel Bl.finalLabel (Bl.nbrLabel e))))))
      (treatedFrame P rank R hr ∅ (Bl.nbrLabel e)
          (Bl.mainGuide E e (mainWordOne Bl.oldLabel Bl.finalLabel (Bl.nbrLabel e))) ::
        l.map (Function.update A x (treatedFrame P rank R hr ∅ (Bl.nbrLabel e)
          (Bl.auxGuide e (auxWordExchanged Bl.oldLabel Bl.finalLabel (Bl.nbrLabel e)))))) := by
  have hΩ1 : ‖Ω‖ ≤ 1 := hΩ.1.le
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
  have hpair := (edgeExchange_hasPairChange hD hLL hΩ hm₀ hA₀ hc hL hk2 P rank R hlarge done E e
    (S := {p | EventUses (.inl R.1) p}) hC.eventUses (r := 2 * b) (K := K) (rs := 2 * b)).mono_error
    (four_mul_zpow_neg_thirty_le (by omega) hb)
  rw [← e.toFinset_endpointList] at hpair
  have h₃ : HasSourceBoundedChange Ω
      (T gm ms.toFinset :: l.map (Function.update A x (T ga ms.toFinset)))
      (T gm' ms.toFinset :: l.map (Function.update A x (T ga' ms.toFinset))) (ℓ := []) (1 : ℂ)
      {p | EventUses (.inl R.1) p} (2 * b) K (2 * b) ((2 * b + 1) * ((L : ℝ) ^ 20)⁻¹) := by
    have := hasSourceBoundedChange_of_hasPairChange hl hx
      (A := Function.update A x (T ga ms.toFinset)) (Function.update_self x _ A) hΩ1 hpair
    rwa [Function.update_idem] at this
  have c₁ := isStepChain_main l (Function.update A x (T ga ∅)) hΩ1 (htreat hum)
  have c₂ := isStepChain_aux (T gm ms.toFinset) hl hx A hΩ1 (htreat hua)
  have c₄ := isStepChain_main l (Function.update A x (T ga' ms.toFinset)) hΩ1
    (huntreat hum')
  have c₅ := isStepChain_aux (T gm' ∅) hl hx A hΩ1 (huntreat hua')
  exact ((((c₁.trans c₂).trans (IsStepChain.single h₃)).trans c₄).trans c₅).cast_length
    (by rw [hlen])

/-- **The edge construction as a chain of changes, conditional on Proposition 3.4.** At the
constants of the protocol, in the repainting of a square `R` of side `n = 2 ^ j > K₀ t`, let the
memory carry the main sheet with the central birth and the edges of `E` done, treated at no mark,
and, at the index `x`, the raw copy held by the party of the label `C_e` across an edge `e ∉ E`.
The initialization of the auxiliary sheet of `e`, its three births, the lens exchange and the four
operations of the main sheet, with their point treatments, are `45` bounded changes of the memory
with the bounds of the small-patch rewrites. They complete `e` on the main sheet and leave the
auxiliary sheet of `e` with the exchanged auxiliary word.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 183–221, 328–339 and 572–583. -/
theorem isStepChain_edgeConstruction (hD : IsAngularScale q J Δ a A₀ m₀ 60 D L₀')
    (hLL : L₀' ≤ L) (hΩ : h.IsGappedGroundState E₀ Ω Δ) (hm₀ : 2 ≤ m₀)
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
    IsStepChain (fun Fs Fs' => HasSourceBoundedChange Ω Fs Fs' (ℓ := []) (1 : ℂ)
        {p | EventUses (.inl R.1) p} (2 * b) K (2 * b) ((2 * b + 1) * ((L : ℝ) ^ 20)⁻¹)) 45
      (treatedFrame (q := q) P rank R hr ∅ L₁ (Bl.completedGuide E) :: l.map A)
      (treatedFrame P rank R hr ∅ L₂ (Bl.completedGuide (e :: E)) ::
        l.map (Function.update A x (treatedFrame P rank R hr ∅ (Bl.nbrLabel e)
          (Bl.auxGuide e (auxWordExchanged Bl.oldLabel Bl.finalLabel (Bl.nbrLabel e)))))) := by
  have hΩ1 : ‖Ω‖ ≤ 1 := hΩ.1.le
  intro Bl
  set Ce := Bl.nbrLabel e
  have hε0 : (0 : ℝ) ≤ (2 * b + 1) * ((L : ℝ) ^ 20)⁻¹ := by positivity
  have haux0 : treatedFrame (q := q) P rank R hr ∅ Ce (Bl.auxGuide e (bandWord Ce [])) = A x :=
    (treatedFrame_auxStart_eq_raw P rank R hr done e Ce).trans hA.symm
  have hstart := treatedFrame_edgeStart (q := q) P rank R hc hL hlarge done he Ce Ce
  have c₀ : IsStepChain (fun Fs Fs' => HasSourceBoundedChange Ω Fs Fs' (ℓ := []) (1 : ℂ)
      {p | EventUses (.inl R.1) p} (2 * b) K (2 * b) ((2 * b + 1) * ((L : ℝ) ^ 20)⁻¹)) 1
      (treatedFrame (q := q) P rank R hr ∅ L₁ (Bl.completedGuide E) :: l.map A)
      (treatedFrame (q := q) P rank R hr ∅ Ce (Bl.completedGuide E) ::
        l.map (Function.update A x
          (treatedFrame (q := q) P rank R hr ∅ Ce (Bl.auxGuide e (bandWord Ce []))))) := by
    rw [haux0, Function.update_eq_self, treatedFrame_empty_congr P rank R L₁ Ce]
    exact IsStepChain.single (hasSourceBoundedChange_refl _ _ _ _ _ _ hε0)
  have c₁ := isStepChain_aux (treatedFrame (q := q) P rank R hr ∅ Ce (Bl.completedGuide E)) hl
    hx A hΩ1 (isStepChain_auxBirths hD hLL hΩ hm₀ hA₀ hc hL hk2 P rank R hlarge done e hr
      (by omega) hK hpt Ce)
  have c₂ := isStepChain_lensExchange hD hLL hΩ hm₀ hA₀ hc hL hk2 P rank R hlarge done E e hr
    hb hpt hl hx A
  have c₃ := isStepChain_main l (Function.update A x (treatedFrame P rank R hr ∅ Ce
    (Bl.auxGuide e (auxWordExchanged Bl.oldLabel Bl.finalLabel Ce)))) hΩ1
    (isStepChain_mainSteps hD hLL hΩ hm₀ hA₀ hc hL hk2 P rank R hlarge done E e hr (by omega) hK
      hpt Ce)
  dsimp only at c₂
  rw [← hstart] at c₂
  rw [treatedFrame_empty_congr P rank R L₂ Ce]
  exact ((c₀.trans c₁).trans c₂).trans c₃

end TNLean.PEPS.Approximation
