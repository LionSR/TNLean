/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Circuit.Party.Sheet.StackChange
import TNLean.PEPS.Approximation.Frames.SheetStack

/-!
# Initialization and reordering of the sheets

In the protocol of Proposition 7.1 of the polynomial-PEPS manuscript the memory holds the main
sheet, the active auxiliary sheets, the frozen auxiliary sheets and the auxiliary copies of `Ω`
not yet in use. Every copy of `Ω`, including the main copy at the root, is initialized privately
at its future owner, so the initial vector is a pure product across parties
(`06-geometry.tex`, lines 658–667). The reordering of the sheets, the identity change and the
initial local operations hold for sheets of any type (`QuantumCircuit.Party`, the modules
`Sheet/Stack`, `Sheet/StackChange` and `Sheet/Initialization`); this file reads them at the
encoded frames, for the registers of a list of frames (`EncodedFrame.framesSystem`,
`EncodedFrame.stackRef`).

* **Reordering the sheets.** A permutation of the frames is a relabelling of the bases of every
  party that carries the reference vector of the frames, in the old order, to the reference
  vector in the new order (`EncodedFrame.exists_originalCircuit_stackRef_of_perm`).
* **The initial local operations.** If each frame of a list is held entirely by one party and
  has a reference vector of norm one, one local operation at every party prepares the reference
  vector of all frames (`EncodedFrame.exists_originalCircuit_initial`).
* **The norm of the reference vector.** If every frame satisfies the frame constraint at
  accuracy `ε`, the reference vector has norm at least one minus `ε` times the total number of
  holes (`EncodedFrame.one_sub_mul_le_norm_stackRef`). With at most `C L³` holes in total and
  `ε = L⁻⁶⁰` this is the bound `1 - C L⁻⁵⁷ ≤ ‖Ξ‖ ≤ 1` for the product `Ξ` of the frozen
  auxiliary frames (`06-geometry.tex`, lines 674–678).

## Main results

* `EncodedFrame.exists_originalCircuit_stackRef_of_perm`,
  `EncodedFrame.exists_originalCircuit_of_frame_eq`.
* `EncodedFrame.exists_originalCircuit_initial`.
* `EncodedFrame.one_sub_mul_le_norm_stackRef`,
  `EncodedFrame.one_sub_div_pow_le_norm_stackRef`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Proposition 7.1 `prop:protocol`,
  `06-geometry.tex`, lines 21–23 and 39–41 (statement), 653–667 (initialization and the
  reference vectors) and 669–681 (the final reference vector); `eq:frame-norm`,
  `05-frames.tex`, lines 84–94; private maps, `04-compression.tex`, lines 21–36 and 137–139.
-/

noncomputable section

namespace TNLean.PEPS.EncodedFrame

open ManyBody QuantumCircuit.Party Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} {Party : Type} [Fintype Party]
  [DecidableEq Party] {pos : ι → ℝ × ℝ} [NeZero q]

/-! ### Reordering the sheets -/

/-- **Reordering the sheets, as an original circuit.** A permutation of a list of frames is
implemented on their registers, followed by an idle system `W`, by a relabelling of the bases of
every party: an original circuit without nonprivate gate, so every participant condition holds
vacuously, that carries the reference vector of the frames to the reference vector in the new
order. Polynomial-PEPS manuscript, `06-geometry.tex`, lines 662–667, and original circuits,
`04-compression.tex`, lines 199–208. -/
theorem exists_originalCircuit_stackRef_of_perm (Ω : EuclideanSpace ℂ (ι → Fin q))
    {Fs Fs' : List (Frame pos q Party)} (h : Fs.Perm Fs') (W : Party → Type)
    [∀ p, Fintype (W p)] [∀ p, DecidableEq (W p)] :
    ∃ c : OriginalCircuit (framesSystem q pos Fs W) (framesSystem q pos Fs' W),
      c.nonprivateCount = 0 ∧ ∀ ξ : EuclideanSpace ℂ (Config W),
        toEuclideanLin c.op (stackRef Ω Fs ξ) = stackRef Ω Fs' ξ := by
  obtain ⟨e, he⟩ := exists_relabel_stackVec_of_perm W (fun F : Frame pos q Party ↦ F.regRef Ω) h
  exact ⟨OriginalCircuit.relabel e, OriginalCircuit.nonprivateCount_relabel _, he⟩

/-! ### Identity changes -/

/-- **The identity change.** A change that leaves the frame unchanged, such as a birth or death
with empty target or the resize of a hole whose radius does not change, is the original circuit
without operations: it has no nonprivate gate and no reference error. It is kept as a change so
that the counts of changes per event do not depend on the geometry. Polynomial-PEPS manuscript,
`06-geometry.tex`, lines 432–438 and 529–541. -/
theorem exists_originalCircuit_of_frame_eq (Ω : EuclideanSpace ℂ (ι → Fin q))
    {F F' : Frame pos q Party} (h : F = F') :
    ∃ c : OriginalCircuit F.system F'.system, c.nonprivateCount = 0 ∧
      toEuclideanLin c.op (F.regRef Ω) = F'.regRef Ω := by
  subst h
  exact ⟨OriginalCircuit.done _, rfl, by
    simp [OriginalCircuit.op_done]⟩

/-! ### The initial local operations -/

/-- **The initial local operations.** Let every frame `F` of the list `Fs` be held entirely by
the party `holder F` (the registers of every other party on `F` are a single point), with a
reference vector of norm one. One local operation at every party prepares, from the system with
one basis vector at every party, the reference vector of `Fs`: the product across the parties of
the reference vectors of the frames each party holds. The resulting original circuit has no
nonprivate gate.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 21–23 and 658–667 (“Initialize all
required copies of `Ω` privately at their future owners, including the main copy at the root.
This is a pure product initialization across parties”), and the product inputs of Theorem 5.2,
`04-compression.tex`, lines 137–139. -/
theorem exists_originalCircuit_initial (Ω : EuclideanSpace ℂ (ι → Fin q))
    (Fs : List (Frame pos q Party)) (holder : Frame pos q Party → Party)
    (hown : ∀ F ∈ Fs, ∀ p ≠ holder F, Fintype.card (F.system p) = 1)
    (hx : ∀ F ∈ Fs, ‖F.refVec Ω‖ = 1) :
    ∃ c : OriginalCircuit (fun _ : Party ↦ Unit) (framesSystem q pos Fs fun _ ↦ Unit),
      c.nonprivateCount = 0 ∧
        toEuclideanLin c.op (EuclideanSpace.single (fun _ ↦ ()) 1) = framesRef Ω Fs :=
  exists_originalCircuit_framesVec (fun F : Frame pos q Party ↦ F.regRef Ω) holder hown
    fun F hF ↦ (F.norm_regRef Ω).trans (hx F hF)

/-! ### The norm of the reference vector -/

/-- **The norm of the reference vector of several sheets.** If `‖Ω‖ = 1` and every hole of
every frame satisfies the frame constraint `‖P Ω - Ω‖ ≤ ε`, then the reference vector of the
frames has norm at least `1 - (number of holes) ε` times the norm of the idle vector.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 674–678, from `eq:frame-norm`,
`05-frames.tex`, lines 84–94. -/
theorem one_sub_mul_le_norm_stackRef {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1)
    {ε : ℝ} {W : Party → Type} [∀ p, Fintype (W p)] : (Fs : List (Frame pos q Party)) →
      (∀ F ∈ Fs, ∀ h ∈ F.holes, ‖toEuclideanLin h.patch.proj Ω - Ω‖ ≤ ε) →
      (ξ : EuclideanSpace ℂ (Config W)) →
        (1 - (Fs.map fun F ↦ (F.holes.length : ℝ)).sum * ε) * ‖ξ‖ ≤ ‖stackRef Ω Fs ξ‖
  | [], _, ξ => by simp only [List.map_nil, List.sum_nil, zero_mul, sub_zero, one_mul]; rfl
  | F :: Fs, hε, ξ => by
      obtain ⟨h1, h2⟩ := F.one_sub_mul_le_norm_refVec hΩ (hε F List.mem_cons_self)
      have ih := one_sub_mul_le_norm_stackRef hΩ Fs
        (fun G hG ↦ hε G (List.mem_cons_of_mem _ hG)) ξ
      have hle : ‖stackRef Ω Fs ξ‖ ≤ ‖ξ‖ := norm_stackRef_le hΩ.le Fs ξ
      change _ ≤ ‖prodVec (F.regRef Ω) (stackRef Ω Fs ξ)‖
      rw [norm_prodVec, F.norm_regRef, List.map_cons, List.sum_cons]
      have hy := mul_le_mul_of_nonneg_left hle (sub_nonneg.2 h2)
      have hz := mul_le_mul_of_nonneg_right (show 1 - ‖F.refVec Ω‖ ≤ F.holes.length * ε by
        linarith) (norm_nonneg ξ)
      nlinarith [norm_nonneg (stackRef Ω Fs ξ), norm_nonneg (F.refVec Ω)]

/-- **The bound `1 - C L⁻⁵⁷ ≤ ‖Ξ‖ ≤ 1`.** If `‖Ω‖ = 1`, every hole of every frame satisfies the
frame constraint at accuracy `L⁻⁶⁰`, and the frames have at most `C L³` holes in total, then the
reference vector of the frames, with an idle vector of norm one, has norm between
`1 - C L⁻⁵⁷` and `1`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 653–656 (“Even the weaker total bound
`C L³` on frozen auxiliary holes will suffice”) and 674–678. -/
theorem one_sub_div_pow_le_norm_stackRef {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1)
    {L : ℕ} (hL : 0 < L) {C : ℝ} (Fs : List (Frame pos q Party))
    (hε : ∀ F ∈ Fs, ∀ h ∈ F.holes, ‖toEuclideanLin h.patch.proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹)
    (hholes : (Fs.map fun F ↦ (F.holes.length : ℝ)).sum ≤ C * (L : ℝ) ^ 3)
    {W : Party → Type} [∀ p, Fintype (W p)] {ξ : EuclideanSpace ℂ (Config W)} (hξ : ‖ξ‖ = 1) :
    1 - C / (L : ℝ) ^ 57 ≤ ‖stackRef Ω Fs ξ‖ ∧ ‖stackRef Ω Fs ξ‖ ≤ 1 := by
  refine ⟨?_, hξ ▸ norm_stackRef_le hΩ.le Fs ξ⟩
  have h := one_sub_mul_le_norm_stackRef hΩ Fs hε ξ
  rw [hξ, mul_one] at h
  refine le_trans ?_ h
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hpow : C / (L : ℝ) ^ 57 = C * (L : ℝ) ^ 3 * ((L : ℝ) ^ 60)⁻¹ := by
    field_simp
  rw [hpow]
  have := mul_le_mul_of_nonneg_right hholes (inv_nonneg.2 (pow_nonneg hL'.le 60))
  linarith

end TNLean.PEPS.EncodedFrame
