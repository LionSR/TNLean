/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Sheet.StackEndpoints
import TNLean.PEPS.Approximation.SheetStack

/-!
# Initialization and reordering of the sheets

In the protocol of Proposition 7.1 of the polynomial-PEPS manuscript the memory holds the main
sheet, the active auxiliary sheets, the frozen auxiliary sheets and the auxiliary copies of `Ω`
not yet in use. Every copy of `Ω`, including the main copy at the root, is initialized privately
at its future owner, so the initial vector is a pure product across parties
(`06-geometry.tex`, lines 658–667). The reordering of the sheets, the identity change and the
initial private maps hold for sheets of any type and are proved in
`TNLean.Lattice.Sheet.StackEndpoints`; this file reads them at the encoded frames, for the memory
of a list of frames (`EncodedFrame.stackRegs`, `EncodedFrame.stackVec`).

* **Reordering the sheets.** A permutation of the frames is implemented by a word of exchanges
  of tensor factors that carries the reference vector of the frames, in the old order, to the
  reference vector in the new order (`EncodedFrame.exists_reordering_stackVec`,
  `EncodedFrame.exists_originalCircuit_stackVec_of_perm`).
* **The initial private maps.** If each frame of a list is held entirely by one party, one
  private map per party carries the product of the frame reference vectors of the parties to
  the reference vector of all frames (`EncodedFrame.exists_originalCircuit_initial`).
* **The norm of the reference vector.** If every frame satisfies the frame constraint at
  accuracy `ε`, the reference vector has norm at least one minus `ε` times the total number of
  holes (`EncodedFrame.one_sub_mul_le_norm_stackVec`). With at most `C L³` holes in total and
  `ε = L⁻⁶⁰` this is the bound `1 - C L⁻⁵⁷ ≤ ‖Ξ‖ ≤ 1` for the product `Ξ` of the frozen
  auxiliary frames (`06-geometry.tex`, lines 674–678).

## Main results

* `EncodedFrame.exists_reordering_stackVec`,
  `EncodedFrame.exists_originalCircuit_stackVec_of_perm`.
* `EncodedFrame.stackVec_append`.
* `EncodedFrame.exists_originalCircuit_initial`.
* `EncodedFrame.one_sub_mul_le_norm_stackVec`,
  `EncodedFrame.one_sub_div_pow_le_norm_stackVec`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Proposition 7.1 `prop:protocol`,
  `06-geometry.tex`, lines 21–23 and 39–41 (statement), 653–667 (initialization and the
  reference vectors) and 669–681 (the final reference vector); `eq:frame-norm`,
  `05-frames.tex`, lines 84–94; private maps, `04-compression.tex`, lines 21–36 and 137–139.
-/

noncomputable section

open scoped TensorProduct
open ContinuousLinearMap

namespace TNLean.PEPS.EncodedFrame
open TNLean.Lattice.Sheet

open TNLean.Lattice.PartyCircuit

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} {Party : Type} {pos : ι → ℝ × ℝ}

/-! ### Registers of concatenated lists of frames -/

/-- The registers of a concatenated list of frames. -/
theorem stackRegs_append (A B : List (Frame pos q Party)) (ℓ : Layout Party) :
    stackRegs A [] ++ stackRegs B ℓ = stackRegs (A ++ B) ℓ :=
  Lattice.stackRegs_append Frame.regs A B ℓ

section Reference

variable [NeZero q]

/-- The reference vector of a list of frames, with no idle registers. -/
abbrev framesVec (Ω : EuclideanSpace ℂ (ι → Fin q)) (Fs : List (Frame pos q Party)) :
    Mem (stackRegs Fs []) :=
  stackVec Ω Fs (ℓ := []) (1 : ℂ)

/-- The reference vector of a concatenated list of frames is the product of the reference
vectors of the two lists. -/
theorem stackVec_append (Ω : EuclideanSpace ℂ (ι → Fin q)) (A B : List (Frame pos q Party))
    {ℓ : Layout Party} (ξ : Mem ℓ) :
    Layout.memCongr (stackRegs_append A B ℓ)
        ((appendIso (stackRegs A []) (stackRegs B ℓ)).symm
          (framesVec Ω A ⊗ₜ stackVec Ω B ξ)) =
      stackVec Ω (A ++ B) ξ :=
  Lattice.stackVec_append (fun F : Frame pos q Party => F.regRef Ω) A B ξ

/-! ### Reordering the sheets -/

/-- **Reordering the sheets.** A permutation of a list of frames is implemented on their
registers, followed by untouched registers `ℓ`, by a word of exchanges of tensor factors that
carries the reference vector of the frames in the old order to the reference vector in the new
order. Polynomial-PEPS manuscript, `06-geometry.tex`, lines 662–667, and allowed monomials,
`04-compression.tex`, lines 32–35. -/
theorem exists_reordering_stackVec (Ω : EuclideanSpace ℂ (ι → Fin q))
    {Fs Fs' : List (Frame pos q Party)} (h : Fs.Perm Fs') (ℓ : Layout Party) :
    ∃ w : Word (stackRegs Fs ℓ) (stackRegs Fs' ℓ), w.IsReordering ∧
      ∀ ξ : Mem ℓ, w.eval (stackVec Ω Fs ξ) = stackVec Ω Fs' ξ :=
  Lattice.exists_reordering_stackVec (fun F : Frame pos q Party => F.regRef Ω) h ℓ

/-- **Reordering the sheets, as an original circuit.** The reordering of
`exists_reordering_stackVec` has no nonprivate gate, so every participant condition holds
vacuously, and it carries the reference vector of the frames to the reference vector in the
new order. Polynomial-PEPS manuscript, `06-geometry.tex`, lines 662–667, and original circuits,
`04-compression.tex`, lines 199–208. -/
theorem exists_originalCircuit_stackVec_of_perm (Ω : EuclideanSpace ℂ (ι → Fin q))
    {Fs Fs' : List (Frame pos q Party)} (h : Fs.Perm Fs') (ℓ : Layout Party) :
    ∃ c : OriginalCircuit (stackRegs Fs ℓ) (stackRegs Fs' ℓ), c.nonprivateCount = 0 ∧
      (∀ (S : Set Party) g, (↑(c.participants g) : Set Party) ⊆ S) ∧
      (∀ r s, c.IsExpansionBounded r s) ∧ (∀ K, c.IsMonomialBounded K) ∧
      ∀ ξ : Mem ℓ, c.eval (stackVec Ω Fs ξ) = stackVec Ω Fs' ξ :=
  Lattice.exists_originalCircuit_stackVec_of_perm (fun F : Frame pos q Party => F.regRef Ω) h ℓ

/-! ### Identity changes -/

/-- **The identity change.** A change that leaves the frame unchanged, such as a birth or death
with empty target or the resize of a hole whose radius does not change, is the original circuit
without operations: it has no nonprivate gate and no reference error. It is kept as a change so
that the counts of changes per event do not depend on the geometry. Polynomial-PEPS manuscript,
`06-geometry.tex`, lines 432–438 and 529–541. -/
theorem exists_originalCircuit_of_frame_eq (Ω : EuclideanSpace ℂ (ι → Fin q))
    {F F' : Frame pos q Party} (h : F = F') :
    ∃ c : OriginalCircuit F.regs F'.regs, c.nonprivateCount = 0 ∧
      (∀ (S : Set Party) g, (↑(c.participants g) : Set Party) ⊆ S) ∧
      (∀ r s, c.IsExpansionBounded r s) ∧ (∀ K, c.IsMonomialBounded K) ∧
      c.eval (F.regRef Ω) = F'.regRef Ω :=
  Lattice.exists_originalCircuit_of_eq (fun F : Frame pos q Party => F.regRef Ω) h

/-! ### The initial private maps -/

/-- The whole initial private memory of a party that holds the list of frames `Fs`: the memory
of the registers of these frames. -/
abbrev framesSpace (Fs : List (Frame pos q Party)) : HSpace := Mem (stackRegs Fs [])

/-- **The initial private maps.** Let every frame `F` of the list `Fs` be held entirely by the
party `holder F`. Take as the whole initial memory of each party the memory of its frames, in
their order in `Fs`, and as its initial vector the product of their reference vectors, of norm
one. One private map per party splits the whole memories into the registers of the frames, and
a reordering puts the frames in the order of `Fs`. The resulting original circuit has no
nonprivate gate and carries the initial product vector exactly to the reference vector of `Fs`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 21–23 and 658–667 (“Initialize all
required copies of `Ω` privately at their future owners, including the main copy at the root.
This is a pure product initialization across parties”), and the product inputs of Theorem 5.2,
`04-compression.tex`, lines 137–139. -/
theorem exists_originalCircuit_initial [Fintype Party] [DecidableEq Party]
    (Ω : EuclideanSpace ℂ (ι → Fin q)) (Fs : List (Frame pos q Party))
    (holder : Frame pos q Party → Party) (hown : ∀ F ∈ Fs, ∀ r ∈ F.regs, r.owner = holder F)
    (hx : ∀ p, ‖framesVec Ω (Fs.filter fun F => holder F = p)‖ = 1) :
    ∃ c : OriginalCircuit
        (ProductInput.wholePartyLayout fun p => framesSpace (Fs.filter fun F => holder F = p))
        (stackRegs Fs []),
      c.nonprivateCount = 0 ∧ (∀ (S : Set Party) g, (↑(c.participants g) : Set Party) ⊆ S) ∧
      (∀ r s, c.IsExpansionBounded r s) ∧ (∀ K, c.IsMonomialBounded K) ∧
      c.eval (ProductInput.ofAllParties _ _ hx).vector = framesVec Ω Fs :=
  Lattice.exists_originalCircuit_initial (fun F : Frame pos q Party => F.regRef Ω) Fs holder hown
    hx

/-! ### The norm of the reference vector -/

/-- **The norm of the reference vector of several sheets.** If `‖Ω‖ = 1` and every hole of
every frame satisfies the frame constraint `‖P Ω - Ω‖ ≤ ε`, then the reference vector of the
frames has norm at least `1 - (number of holes) ε` times the norm of the idle vector.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 674–678, from `eq:frame-norm`,
`05-frames.tex`, lines 84–94. -/
theorem one_sub_mul_le_norm_stackVec {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1)
    {ε : ℝ} : (Fs : List (Frame pos q Party)) →
      (∀ F ∈ Fs, ∀ h ∈ F.holes, ‖act h.patch.proj Ω - Ω‖ ≤ ε) → {ℓ : Layout Party} →
      (ξ : Mem ℓ) →
        (1 - (Fs.map fun F => (F.holes.length : ℝ)).sum * ε) * ‖ξ‖ ≤ ‖stackVec Ω Fs ξ‖
  | [], _, _, ξ => by simp only [List.map_nil, List.sum_nil, zero_mul, sub_zero, one_mul]; rfl
  | F :: Fs, hε, ℓ, ξ => by
      obtain ⟨h1, h2⟩ := F.one_sub_mul_le_norm_refVec hΩ (hε F List.mem_cons_self)
      have ih := one_sub_mul_le_norm_stackVec hΩ Fs
        (fun G hG => hε G (List.mem_cons_of_mem _ hG)) ξ
      have hle : ‖stackVec Ω Fs ξ‖ ≤ ‖ξ‖ := norm_stackVec_le hΩ.le Fs ξ
      change _ ≤ ‖(appendIso F.regs (stackRegs Fs ℓ)).symm (F.regRef Ω ⊗ₜ stackVec Ω Fs ξ)‖
      rw [LinearIsometryEquiv.norm_map, TensorProduct.norm_tmul, F.norm_regRef, List.map_cons,
        List.sum_cons]
      have hy := mul_le_mul_of_nonneg_left hle (sub_nonneg.2 h2)
      have hz := mul_le_mul_of_nonneg_right (show 1 - ‖F.refVec Ω‖ ≤ F.holes.length * ε by
        linarith) (norm_nonneg ξ)
      nlinarith

/-- **The bound `1 - C L⁻⁵⁷ ≤ ‖Ξ‖ ≤ 1`.** If `‖Ω‖ = 1`, every hole of every frame satisfies the
frame constraint at accuracy `L⁻⁶⁰`, and the frames have at most `C L³` holes in total, then the
reference vector of the frames, with an idle vector of norm one, has norm between
`1 - C L⁻⁵⁷` and `1`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 653–656 (“Even the weaker total bound
`C L³` on frozen auxiliary holes will suffice”) and 674–678. -/
theorem one_sub_div_pow_le_norm_stackVec {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1)
    {L : ℕ} (hL : 0 < L) {C : ℝ} (Fs : List (Frame pos q Party))
    (hε : ∀ F ∈ Fs, ∀ h ∈ F.holes, ‖act h.patch.proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹)
    (hholes : (Fs.map fun F => (F.holes.length : ℝ)).sum ≤ C * (L : ℝ) ^ 3)
    {ℓ : Layout Party} {ξ : Mem ℓ} (hξ : ‖ξ‖ = 1) :
    1 - C / (L : ℝ) ^ 57 ≤ ‖stackVec Ω Fs ξ‖ ∧ ‖stackVec Ω Fs ξ‖ ≤ 1 := by
  refine ⟨?_, hξ ▸ norm_stackVec_le hΩ.le Fs ξ⟩
  have h := one_sub_mul_le_norm_stackVec hΩ Fs hε ξ
  rw [hξ, mul_one] at h
  refine le_trans ?_ h
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hpow : C / (L : ℝ) ^ 57 = C * (L : ℝ) ^ 3 * ((L : ℝ) ^ 60)⁻¹ := by
    field_simp
  rw [hpow]
  have := mul_le_mul_of_nonneg_right hholes (inv_nonneg.2 (pow_nonneg hL'.le 60))
  linarith

end Reference

end TNLean.PEPS.EncodedFrame
