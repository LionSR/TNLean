/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SheetStackEndpoints

/-!
# The initial memory of raw copies of `Ω`

In the protocol of Proposition 7.1 of the polynomial-PEPS manuscript every copy of `Ω`, the main
copy at the root and each auxiliary copy at its future owner, is initialized privately. At the
beginning the main guide has only the root label and the exterior placeholder, so it has no
true vertex and no hole (`06-geometry.tex`, lines 658–667). Every initial sheet is therefore a
frame without holes, held entirely by one party.

A frame without holes has reference vector `Ω` on its raw registers, of norm `‖Ω‖`
(`EncodedFrame.Frame.norm_refVec_of_holes_eq_nil`). Hence, when `‖Ω‖ = 1`, the product of the
reference vectors of the frames held by any one party has norm one
(`EncodedFrame.norm_framesVec_of_holes_eq_nil`), which is the normalization hypothesis of the
initial private maps `EncodedFrame.exists_originalCircuit_initial`. The initial step of the
protocol follows (`EncodedFrame.exists_originalCircuit_initial_of_holes_eq_nil`).

## Main results

* `EncodedFrame.Frame.norm_refVec_of_holes_eq_nil`, `EncodedFrame.norm_framesVec_of_holes_eq_nil`.
* `EncodedFrame.exists_originalCircuit_initial_of_holes_eq_nil`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Proposition 7.1 `prop:protocol`, item 1,
  `06-geometry.tex`, lines 21–23, and its proof, lines 658–667; `eq:frame-norm`,
  `05-frames.tex`, lines 84–94.
-/

noncomputable section

namespace TNLean.PEPS.EncodedFrame

open PairEffect

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} [NeZero q] {Party : Type}
  {pos : ι → ℝ × ℝ}

/-- A frame without holes has the reference vector of the norm of `Ω`. -/
theorem Frame.norm_refVec_of_holes_eq_nil (F : Frame pos q Party) (h : F.holes = [])
    (Ω : EuclideanSpace ℂ (ι → Fin q)) : ‖F.refVec Ω‖ = ‖Ω‖ := by
  rw [F.norm_refVec_eq, Frame.patches, h, List.map_nil]
  simp [projProd, act_one]

/-- **Normalized raw copies.** If `‖Ω‖ = 1`, the reference vector of a list of frames without
holes has norm one. Polynomial-PEPS manuscript, `06-geometry.tex`, lines 658–667. -/
theorem norm_framesVec_of_holes_eq_nil {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1)
    (Fs : List (Frame pos q Party)) (h : ∀ F ∈ Fs, F.holes = []) :
    ‖framesVec Ω Fs‖ = 1 := by
  rw [norm_stackVec, List.map_congr_left fun F hF => by
    rw [F.norm_refVec_of_holes_eq_nil (h F hF), hΩ]]
  simp

/-- **The initial step from raw copies.** Let `‖Ω‖ = 1`, and let every frame `F` of the list `Fs`
have no hole and be held entirely by the party `holder F`: the main raw copy at the root and the
raw auxiliary copies at their future owners. Take as the whole initial memory of each party the
memory of its frames and as its initial vector the product of their reference vectors. These
initial vectors have norm one, and one private map per party followed by a reordering carries
the initial product vector exactly to the reference vector of `Fs`, with no nonprivate gate.

Polynomial-PEPS manuscript, Proposition 7.1 `prop:protocol`, item 1, `06-geometry.tex`,
lines 21–23, and its proof, lines 658–667. -/
theorem exists_originalCircuit_initial_of_holes_eq_nil [Fintype Party] [DecidableEq Party]
    {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1) (Fs : List (Frame pos q Party))
    (holder : Frame pos q Party → Party) (hraw : ∀ F ∈ Fs, F.holes = [])
    (hown : ∀ F ∈ Fs, ∀ x, F.owner x = holder F) :
    ∃ hx : ∀ p, ‖framesVec Ω (Fs.filter fun F => holder F = p)‖ = 1,
      ∃ c : OriginalCircuit
          (ProductInput.wholePartyLayout fun p => framesSpace (Fs.filter fun F => holder F = p))
          (stackRegs Fs []),
        c.nonprivateCount = 0 ∧ (∀ (S : Set Party) g, (↑(c.participants g) : Set Party) ⊆ S) ∧
        (∀ r s, c.IsExpansionBounded r s) ∧ (∀ K, c.IsMonomialBounded K) ∧
        c.eval (ProductInput.ofAllParties _ _ hx).vector = framesVec Ω Fs := by
  have hx : ∀ p, ‖framesVec Ω (Fs.filter fun F => holder F = p)‖ = 1 := fun p =>
    norm_framesVec_of_holes_eq_nil hΩ _ fun F hF => hraw F (List.mem_of_mem_filter hF)
  refine ⟨hx, exists_originalCircuit_initial Ω Fs holder (fun F hF r hr => ?_) hx⟩
  have hmem : r.owner ∈ F.regs.map Reg.owner := List.mem_map_of_mem hr
  rw [F.map_owner_regs, hraw F hF, List.map_nil, List.nil_append] at hmem
  obtain ⟨x, -, hxr⟩ := List.mem_map.1 hmem
  rw [← hxr, hown F hF x]

end TNLean.PEPS.EncodedFrame
