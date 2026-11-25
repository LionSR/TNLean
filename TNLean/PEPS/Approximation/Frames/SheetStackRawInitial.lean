/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.Frames.SheetStackEndpoints

/-!
# The initial memory of raw copies of `Ω`

In the protocol of Proposition 7.1 of the polynomial-PEPS manuscript every copy of `Ω`, the main
copy at the root and each auxiliary copy at its future owner, is initialized privately. At the
beginning the main guide has only the root label and the exterior placeholder, so it has no
true vertex and no hole (`06-geometry.tex`, lines 658–667). Every initial sheet is therefore a
frame without holes, held entirely by one party.

A frame without holes has reference vector `Ω` on its raw registers, of norm `‖Ω‖`
(`EncodedFrame.Frame.norm_refVec_of_holes_eq_nil`). Hence, when `‖Ω‖ = 1`, the product of the
reference vectors of any list of such frames has norm one
(`EncodedFrame.norm_framesRef_of_holes_eq_nil`), and every such frame has a reference vector of
norm one, which is the normalization hypothesis of the initial local operations
`EncodedFrame.exists_originalCircuit_initial`. The initial step of the protocol follows
(`EncodedFrame.exists_originalCircuit_initial_of_holes_eq_nil`).

## Main results

* `EncodedFrame.Frame.norm_refVec_of_holes_eq_nil`, `EncodedFrame.norm_framesRef_of_holes_eq_nil`.
* `EncodedFrame.exists_originalCircuit_initial_of_holes_eq_nil`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Proposition 7.1 `prop:protocol`, item 1,
  `06-geometry.tex`, lines 21–23, and its proof, lines 658–667; `eq:frame-norm`,
  `05-frames.tex`, lines 84–94.
-/

noncomputable section

namespace TNLean.PEPS.EncodedFrame

open ManyBody QuantumCircuit.Party Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} [NeZero q] {Party : Type}
  {pos : ι → ℝ × ℝ}

/-- A frame without holes has the reference vector of the norm of `Ω`. -/
theorem Frame.norm_refVec_of_holes_eq_nil (F : Frame pos q Party) (h : F.holes = [])
    (Ω : EuclideanSpace ℂ (ι → Fin q)) : ‖F.refVec Ω‖ = ‖Ω‖ := by
  rw [F.norm_refVec_eq, Frame.patches, h, List.map_nil]
  simp [projProd]

variable [Fintype Party] [DecidableEq Party]

/-- **Normalized raw copies.** If `‖Ω‖ = 1`, the reference vector of a list of frames without
holes has norm one. Polynomial-PEPS manuscript, `06-geometry.tex`, lines 658–667. -/
theorem norm_framesRef_of_holes_eq_nil {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1)
    (Fs : List (Frame pos q Party)) (h : ∀ F ∈ Fs, F.holes = []) :
    ‖framesRef Ω Fs‖ = 1 := by
  rw [framesRef, norm_framesVec, List.map_congr_left fun F hF ↦ by
    rw [F.norm_regRef, F.norm_refVec_of_holes_eq_nil (h F hF), hΩ]]
  simp

/-- **The initial step from raw copies.** Let `‖Ω‖ = 1`, and let every frame `F` of the list `Fs`
have no hole and be held entirely by the party `holder F`: the main raw copy at the root and the
raw auxiliary copies at their future owners. One local operation at every party prepares, from
the system with one basis vector at every party, the reference vector of `Fs`, the product across
the parties of the reference vectors of the frames each party holds, with no nonprivate gate.

Polynomial-PEPS manuscript, Proposition 7.1 `prop:protocol`, item 1, `06-geometry.tex`,
lines 21–23, and its proof, lines 658–667. -/
theorem exists_originalCircuit_initial_of_holes_eq_nil {Ω : EuclideanSpace ℂ (ι → Fin q)}
    (hΩ : ‖Ω‖ = 1) (Fs : List (Frame pos q Party)) (holder : Frame pos q Party → Party)
    (hraw : ∀ F ∈ Fs, F.holes = []) (hown : ∀ F ∈ Fs, ∀ x, F.owner x = holder F) :
    ∃ c : OriginalCircuit (fun _ : Party ↦ Unit) (framesSystem q pos Fs fun _ ↦ Unit),
      c.nonprivateCount = 0 ∧
        toEuclideanLin c.op (EuclideanSpace.single (fun _ ↦ ()) 1) = framesRef Ω Fs := by
  refine exists_originalCircuit_initial Ω Fs holder (fun F hF p hp ↦ ?_)
    fun F hF ↦ (F.norm_refVec_of_holes_eq_nil (hraw F hF) Ω).trans hΩ
  have hown' := hown F hF
  have hraw' := hraw F hF
  obtain ⟨own, holes, hd⟩ := F
  simp only at hraw' hown'
  subst hraw'
  rw [Fintype.card_prod]
  simp only [Fintype.card_pi, Finset.prod_const, Fintype.card_fin]
  rw [Finset.card_univ, Fintype.card_coe,
    show blockPreimage own {p} = ∅ from Finset.filter_eq_empty_iff.mpr fun x _ ↦ by
      simpa using fun h ↦ hp (h.symm.trans (hown' x)), Finset.card_empty, pow_zero]
  rfl

end TNLean.PEPS.EncodedFrame
