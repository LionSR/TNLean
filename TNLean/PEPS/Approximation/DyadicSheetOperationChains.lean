/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicChangeChains

/-!
# The bulk operations of a large repainting with their point treatments

In the protocol of Proposition 7.1 of the polynomial-PEPS manuscript, every bulk operation of a
large-scale repainting is preceded by the homogenization of the involved sheet about each of its
marks, one mark at a time, and followed by the removal of these homogenizations
(`06-geometry.tex`, lines 328–339). This file assembles these chains of changes of one sheet for
the central birth and for the elementary births and deaths along an edge, with the bounds of the
small-patch rewrites of the protocol.

* `IsLocalLabel` : the final label of `R` or the label of a block next to `R`;
* `IsPointTreatable` : the point treatments of a repainting are bounded changes, as provided by
  `exists_pointTreatment_hasSourceBoundedChange`;
* `isStepChain_centralBirth` : the `9` changes of the central birth;
* `isStepChain_bandOperation` : the `5` changes of a birth or death along an edge.

## References

* Polynomial-PEPS manuscript (September 24, 2026), §7, `06-geometry.tex`: the central birth and
  the edge construction (lines 155–221), the point treatment (lines 328–339) and the bounds of the
  changes (lines 572–583).
-/

noncomputable section

namespace TNLean.PEPS.Approximation

open EncodedFrame PairEffect

/-! ### The marks of a bulk operation -/

/-- The four grid corners of the block `S`, in a fixed order. -/
def cornerList (S : ℤ × ℤ) : List (ℤ × ℤ) := [S, S + (1, 0), S + (0, 1), S + (1, 1)]

/-- The two grid corners at the ends of an edge of the block `S`, in a fixed order. -/
def SquareEdge.endpointList : SquareEdge → ℤ × ℤ → List (ℤ × ℤ)
  | .bottom, S => [S, S + (1, 0)]
  | .right, S => [S + (1, 0), S + (1, 1)]
  | .top, S => [S + (0, 1), S + (1, 1)]
  | .left, S => [S, S + (0, 1)]

theorem toFinset_cornerList (S : ℤ × ℤ) : (cornerList S).toFinset = cornerBlocks S := by
  ext Q
  simp [cornerList, cornerBlocks]

theorem SquareEdge.toFinset_endpointList (e : SquareEdge) (S : ℤ × ℤ) :
    (e.endpointList S).toFinset = e.endpointBlocks S := by
  ext Q
  cases e <;> simp [SquareEdge.endpointList, SquareEdge.endpointBlocks]

theorem isBlockCornerOf_of_mem_cornerList {S Q : ℤ × ℤ} (h : Q ∈ cornerList S) :
    IsBlockCornerOf S Q := by
  simp only [cornerList, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> simp [IsBlockCornerOf]

theorem SquareEdge.isBlockCornerOf_of_mem_endpointList {e : SquareEdge} {S Q : ℤ × ℤ}
    (h : Q ∈ e.endpointList S) : IsBlockCornerOf S Q :=
  isBlockCornerOf_of_mem_cornerList (by
    cases e <;> simp only [SquareEdge.endpointList, List.mem_cons, List.not_mem_nil,
      or_false] at h <;> rcases h with rfl | rfl <;> simp [cornerList])

/-! ### Bounds -/

/-- The error `L⁻³⁰` of a bulk step is at most the error of a small-patch rewrite. -/
theorem zpow_neg_thirty_le {L : ℕ} (hL : 1 ≤ L) (b : ℕ) :
    (L : ℝ) ^ (-30 : ℤ) ≤ (2 * b + 1) * ((L : ℝ) ^ 20)⁻¹ := by
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have h1 : (L : ℝ) ^ (-30 : ℤ) ≤ ((L : ℝ) ^ 20)⁻¹ := by
    rw [← zpow_natCast, ← zpow_neg]
    exact zpow_le_zpow_right₀ hL' (by norm_num)
  have h2 : (0 : ℝ) ≤ ((L : ℝ) ^ 20)⁻¹ := by positivity
  nlinarith

/-- The error `4 L⁻³⁰` of the lens exchange is at most the error of a small-patch rewrite once
`b ≥ 2`. -/
theorem four_mul_zpow_neg_thirty_le {L : ℕ} (hL : 1 ≤ L) {b : ℕ} (hb : 2 ≤ b) :
    4 * (L : ℝ) ^ (-30 : ℤ) ≤ (2 * b + 1) * ((L : ℝ) ^ 20)⁻¹ := by
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have h1 : (L : ℝ) ^ (-30 : ℤ) ≤ ((L : ℝ) ^ 20)⁻¹ := by
    rw [← zpow_natCast, ← zpow_neg]
    exact zpow_le_zpow_right₀ hL' (by norm_num)
  have h2 : (0 : ℝ) ≤ ((L : ℝ) ^ 20)⁻¹ := by positivity
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  nlinarith

/-! ### Chains of one sheet -/

variable {k : ℕ}

/-- A label used by the repainting of `R` at the stage `done`: its final label or the label of a
block next to `R`, possibly `R` itself.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 585–596. -/
def IsLocalLabel (R : RepaintedSquare k) (done : Set (ℤ × ℤ)) (l : GuideLabel) : Prop :=
  l = newParty Sum.inl R.1.1 R.1.index ∨
    ∃ R' ∈ blockWindow 1, l = protocolLevelLabels k R.1.1 done (R' + R.1.index)

variable {L q : ℕ} [NeZero q] {Ω : StateSpace L q} {B₀ C c : ℝ}
  (P : AdaptivePatchSupply (cellCenterPos L) Ω B₀ C c 60 L) (rank : GuideLabel → ℕ)
  (R : RepaintedSquare k)

/-- **The point treatments of a repainting are bounded changes.** In the repainting of the
square `R` at the stage `done` of its level, adding or removing one mark at a corner of `R`, for
an unmodified guide and a homogenizing label that is the final label or a label of a block next
to `R`, is a bounded change with the given participants and bounds. This is the conclusion of
`exists_pointTreatment_hasSourceBoundedChange` for one repainting.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 328–339 and 481–505. -/
def IsPointTreatable {ε₀ t : ℝ} (hr : ∀ _ : ℝ × ℝ, 0 < ε₀ * t ∧ ε₀ * t ≤ B₀ * Real.log L)
    (done : Set (ℤ × ℤ)) (S : Set (ProtocolParty k)) (r K rs : ℕ) (ε : ℝ) : Prop :=
  ∀ {g : ℝ × ℝ → GuideLabel}, (repaintBaseline R done).IsUnmodifiedGuide g →
    ∀ {M M' : Finset (ℤ × ℤ)} (Q₀ : ℤ × ℤ), IsBlockCornerOf R.1.index Q₀ →
      (∀ Q, Q ≠ Q₀ → (Q ∈ M ↔ Q ∈ M')) → ∀ L₀ : GuideLabel,
      IsLocalLabel R done L₀ →
      HasFrameChange Ω (treatedFrame (q := q) P rank R hr M L₀ g)
        (treatedFrame P rank R hr M' L₀ g) S r K rs ε

/-- The labels of the repainting of `R` that may homogenize: the final label, the old label and
the labels across the edges. -/
theorem isHomogenizing_oldLabel (done : Set (ℤ × ℤ)) :
    IsLocalLabel R done (repaintBaseline R done).oldLabel :=
  Or.inr ⟨0, by decide, by simp [repaintBaseline, blockBaseline]⟩

theorem isHomogenizing_finalLabel (done : Set (ℤ × ℤ)) :
    IsLocalLabel R done (repaintBaseline R done).finalLabel :=
  Or.inl rfl

theorem isHomogenizing_nbrLabel (done : Set (ℤ × ℤ)) (e : SquareEdge) :
    IsLocalLabel R done ((repaintBaseline R done).nbrLabel e) := by
  refine Or.inr ⟨e.nbrBlock (0, 0), nbrBlock_zero_mem_blockWindow e, ?_⟩
  change protocolLevelLabels k R.1.1 done (e.nbrBlock R.1.index) = _
  congr 1
  cases e <;> simp [SquareEdge.nbrBlock, Prod.ext_iff, add_comm] <;> ring

/-- **A bulk operation of one sheet with its point treatments.** For an unmodified guide `g`
changed into `g'` by a bulk step on the frames treated at all marks of a list of corners of `R`,
with a homogenizing label `L₀`, there is a chain of `2 m + 1` bounded changes, `m` the number of
marks, from the frame of `g` to that of `g'`, both treated at no mark.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 328–339. -/
theorem isStepChain_sheetOperation {ε₀ t : ℝ}
    {hr : ∀ _ : ℝ × ℝ, 0 < ε₀ * t ∧ ε₀ * t ≤ B₀ * Real.log L} {done : Set (ℤ × ℤ)}
    {S : Set (ProtocolParty k)} {r K rs : ℕ} {ε : ℝ}
    (hpt : IsPointTreatable P rank R hr done S r K rs ε) {g g' : ℝ × ℝ → GuideLabel}
    (hg : (repaintBaseline R done).IsUnmodifiedGuide g)
    (hg' : (repaintBaseline R done).IsUnmodifiedGuide g') {L₀ : GuideLabel}
    (hL₀ : IsLocalLabel R done L₀)
    (marks : List (ℤ × ℤ)) (hmarks : ∀ Q ∈ marks, IsBlockCornerOf R.1.index Q)
    (hb : HasFrameChange Ω (treatedFrame (q := q) P rank R hr marks.toFinset L₀ g)
      (treatedFrame P rank R hr marks.toFinset L₀ g') S r K rs ε) :
    IsStepChain (fun F F' => HasFrameChange Ω F F' S r K rs ε) (2 * marks.length + 1)
      (treatedFrame (q := q) P rank R hr ∅ L₀ g) (treatedFrame P rank R hr ∅ L₀ g') := by
  classical
  have hdiff : ∀ (M : Finset (ℤ × ℤ)) Q₀ Q, Q ≠ Q₀ → (Q ∈ M ↔ Q ∈ insert Q₀ M) :=
    fun M Q₀ Q hQ => by simp [hQ]
  refine IsStepChain.treatOperate (fun M => treatedFrame (q := q) P rank R hr M L₀ g)
    (fun M => treatedFrame (q := q) P rank R hr M L₀ g') marks
    (fun M Q hQ => hpt hg Q (hmarks Q hQ) (hdiff M Q) L₀ hL₀) hb
    (fun M Q hQ => hpt hg' Q (hmarks Q hQ) (fun Q' hQ' => (hdiff M Q Q' hQ').symm) L₀ hL₀)

end TNLean.PEPS.Approximation
