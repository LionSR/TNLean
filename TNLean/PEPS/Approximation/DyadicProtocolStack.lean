/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicSampledGuides
import TNLean.PEPS.Approximation.SheetStackSourceBoundedChange

/-!
# The sheets of the dyadic protocol and the sampled guides

At every stage of the protocol of Proposition 7.1 of the polynomial-PEPS manuscript the memory
holds the main sheet and one copy of `Ω` for every auxiliary sheet of the schedule, idle, active or
frozen (`06-geometry.tex`, lines 21–23 and 658–667). This file writes such a memory as the main
frame followed by the frames of a fixed list of auxiliary indices, and lifts the changes of the
main sheet, of one auxiliary sheet, and of the main sheet together with one auxiliary sheet, to
the whole memory (`hasSourceBoundedChange_main`, `hasSourceBoundedChange_aux`,
`hasSourceBoundedChange_mainAux`).

The labels of a guide are read at the sites after one fixed small generic displacement
(`06-geometry.tex`, lines 69–80). The reading `sampleGuide G` after the displacement `(1, 1)` is
defined for every labelling, and it is the reading of every labelling that has one
(`IsDisplacedReading.eq_sampleGuide`).

## References

* Polynomial-PEPS manuscript (September 24, 2026), Proposition 7.1 `prop:protocol`,
  `06-geometry.tex`, lines 21–23, 39–41, 69–80, 183–186 and 658–667.
-/

noncomputable section

open Filter Topology

namespace TNLean.PEPS

namespace Approximation

/-! ### The sampled guide -/

open Classical in
/-- The reading of a labelling of the plane after the displacement `(1, 1)`: the label eventually
taken along the ray from each point, when there is one.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 71–77: "move a sampled point by an
arbitrarily small generic vector into an incident chamber, consistently across all descriptions,
and take the resulting label". -/
def sampleGuide {κ : Type*} (G : ℝ × ℝ → κ) : ℝ × ℝ → κ := fun p =>
  if h : ∃ l, ∀ᶠ ε in 𝓝[>] (0 : ℝ), G (p + ε • ((1 : ℝ), (1 : ℝ))) = l then h.choose else G p

/-- A reading after `(1, 1)` is the sampled guide. -/
theorem IsDisplacedReading.eq_sampleGuide {κ : Type*} {G g : ℝ × ℝ → κ}
    (hg : IsDisplacedReading g G ((1 : ℝ), (1 : ℝ))) : g = sampleGuide G := by
  funext p
  have h : ∃ l, ∀ᶠ ε in 𝓝[>] (0 : ℝ), G (p + ε • ((1 : ℝ), (1 : ℝ))) = l :=
    ⟨g p, (hg p).mono fun _ h => h.symm⟩
  simp only [sampleGuide, h, dite_true]
  obtain ⟨ε, e₁, e₂⟩ := ((hg p).and h.choose_spec).exists
  rw [e₁, e₂]

/-- A labelling constant along rays is read by its sampled guide. -/
theorem IsRayConstant.isDisplacedReading_sampleGuide {κ : Type*} {G : ℝ × ℝ → κ}
    (h : IsRayConstant G) : IsDisplacedReading (sampleGuide G) G ((1 : ℝ), (1 : ℝ)) := by
  obtain ⟨g, hg⟩ := h.exists_isDisplacedReading ((1 : ℝ), (1 : ℝ))
  rwa [← hg.eq_sampleGuide]

end Approximation

namespace EncodedFrame

open TNLean.Lattice.PartyCircuit

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} [NeZero q] {Party : Type}
  {pos : ι → ℝ × ℝ} {Ω : EuclideanSpace ℂ (ι → Fin q)} {ℓ : Layout Party} {ξ : Mem ℓ}
  {S : Set Party} {r K rs : ℕ} {ε : ℝ} {X : Type*} [DecidableEq X]

/-! ### The main sheet and the auxiliary sheets -/

/-- **A change of the main sheet.** A bounded change of the main frame with at most `rs` pair
sources in each monomial is such a change of the memory, with the auxiliary frames as spectators.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 39–41 and 574–583. -/
theorem hasSourceBoundedChange_main {M M' : Frame pos q Party} (Fs : List (Frame pos q Party))
    {c : OriginalCircuit M.regs M'.regs}
    (hc : c.IsBoundedChange S r K ε (M.regRef Ω) (M'.regRef Ω)) (hs : c.IsSourceBounded rs)
    (hΩ : ‖Ω‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1) :
    HasSourceBoundedChange Ω (M :: Fs) (M' :: Fs) ξ S r K rs ε :=
  hasSourceBoundedChange_liftOne [] Fs hc hs hΩ hξ

/-- **A change of one auxiliary sheet.** For a list `l` of distinct auxiliary indices and an
index `x` of `l`, a bounded change of the frame `A x` into `F` with at most `rs` pair sources in
each monomial is such a change of the memory `M :: l.map A` into
`M :: l.map (Function.update A x F)`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 39–41, 183–186 and 574–583. -/
theorem hasSourceBoundedChange_aux (M : Frame pos q Party) {l : List X} (hl : l.Nodup) {x : X}
    (hx : x ∈ l) (A : X → Frame pos q Party) {F : Frame pos q Party}
    {c : OriginalCircuit (A x).regs F.regs}
    (hc : c.IsBoundedChange S r K ε ((A x).regRef Ω) (F.regRef Ω)) (hs : c.IsSourceBounded rs)
    (hΩ : ‖Ω‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1) :
    HasSourceBoundedChange Ω (M :: l.map A) (M :: l.map (Function.update A x F)) ξ S r K rs ε :=
  ((hasSourceBoundedChange_liftOne [] (M :: (l.erase x).map A) hc hs hΩ hξ).perm_left
    (Lattice.perm_map_cons M hx A)).perm_right (Lattice.perm_map_update_cons M hl hx A F).symm

/-- **A change of the main sheet and one auxiliary sheet.** For a list `l` of distinct auxiliary
indices and an index `x` of `l`, a bounded change of the two frames `M`, `A x` into `M'`, `F` with
at most `rs` pair sources in each monomial is such a change of the memory `M :: l.map A` into
`M' :: l.map (Function.update A x F)`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 39–41, 183–186, 389–430 and 574–583. -/
theorem hasSourceBoundedChange_mainAux {M M' : Frame pos q Party} {l : List X} (hl : l.Nodup)
    {x : X} (hx : x ∈ l) (A : X → Frame pos q Party) {F : Frame pos q Party}
    {c : OriginalCircuit (M.regs ++ (A x).regs) (M'.regs ++ F.regs)}
    (hc : c.IsBoundedChange S r K ε (pairRef M (A x) Ω) (pairRef M' F Ω))
    (hs : c.IsSourceBounded rs) (hΩ : ‖Ω‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1) :
    HasSourceBoundedChange Ω (M :: l.map A) (M' :: l.map (Function.update A x F)) ξ S r K rs ε := by
  have hp : (M :: l.map A).Perm ([] ++ M :: A x :: (l.erase x).map A) := by
    have h := (Lattice.perm_map_cons M hx A)
    exact h.trans ((List.Perm.swap _ _ _).symm)
  have hp' : ([] ++ M' :: F :: (l.erase x).map A).Perm (M' :: l.map (Function.update A x F)) :=
    (((Lattice.perm_map_update_cons M' hl hx A F).trans (List.Perm.swap _ _ _)).symm)
  exact (hasSourceBoundedChange_activate hp hc hs hΩ hξ).perm_right hp'

end EncodedFrame

end TNLean.PEPS
