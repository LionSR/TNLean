/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BoundaryClosedness
import TNLean.MPS.MPDO.BoundaryRepresentation

/-!
# Representations from boundary closedness and compatibility

The length-independent boundary maps obtained from existential closedness or
compatibility induce non-unital representations of the block matrix algebra.
The only spanning hypothesis is simultaneous word spanning at one positive
length. The map sends each target letter tuple to the actual stacked or
acted-on letter, with no nilpotent remainder and no star assumption.

## References

* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, `algcond`,
  `eq:compatible`, and Appendix A, lines 2305--2455.
-/

open scoped Matrix BigOperators

noncomputable section

namespace MPSTensor

variable {d D r : ℕ} {dim : Fin r → ℕ}

/-- A boundary map to an unweighted direct sum determines a non-unital
representation of its block matrix algebra. Source: GLM23, Appendix A,
`decompopen` and the subsequent comparison at two chain lengths. -/
theorem exists_boundaryRepresentation_of_boundaryMap
    (B : MPSTensor d D) (A : (c : Fin r) → MPSTensor d (dim c))
    (b : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ]
      Matrix (Fin (∑ c : Fin r, dim c)) (Fin (∑ c : Fin r, dim c)) ℂ)
    (hb : ∀ (n : ℕ), 0 < n → ∀ X : Matrix (Fin D) (Fin D) ℂ,
      ∀ w : Fin n → Fin d,
        mpvWithBoundary B X w =
          mpvWithBoundary (toTensorFromBlocks (fun _ ↦ 1) A) (b X) w)
    {L : ℕ} (hL : 0 < L) (hSpan : WordTupleSpanTop A L) :
    ∃ ρ : ((c : Fin r) → Matrix (Fin (dim c)) (Fin (dim c)) ℂ) →ₙₐ[ℂ]
      Matrix (Fin D) (Fin D) ℂ,
      ∀ i : Fin d, ρ (fun c ↦ A c i) = B i := by
  let b' := Matrix.finSigmaDiagonalBlocks.comp b
  have hb' : ∀ (n : ℕ), 0 < n → ∀ X : Matrix (Fin D) (Fin D) ℂ,
      ∀ w : Fin n → Fin d,
        mpvWithBoundary B X w = ∑ c : Fin r, mpvWithBoundary (A c) (b' X c) w := by
    intro n hn X w
    rw [hb n hn X w, mpvWithBoundary_toTensorFromBlocks_one]
    rfl
  exact ⟨boundaryRepresentation B A b' hb' hL hSpan,
    boundaryRepresentation_letter B A b' hb' hL hSpan⟩

end MPSTensor

namespace MPOTensor

variable {d D r : ℕ} {dim : Fin r → ℕ}

/-- The arbitrary-boundary doubled-index vector is the corresponding
operator coefficient. -/
theorem mpvWithBoundary_toMPSTensor (T : MPOTensor d D)
    (X : Matrix (Fin D) (Fin D) ℂ) {L : ℕ} (w : Fin L → Fin (d * d)) :
    MPSTensor.mpvWithBoundary T.toMPSTensor X w =
      mpoWithBoundary T X L (fun k ↦ (w k).divNat) (fun k ↦ (w k).modNat) := by
  simp only [MPSTensor.mpvWithBoundary, mpoWithBoundary, evalWord_toMPSTensor_ofFn]

/-- Closedness with one boundary for all lengths induces a representation
of the target block matrix algebra on the stacked bond space. Its letter
identity is exact. Source: GLM23, `algcond`, `fusiontensors`, and Appendix A.

The representation need not preserve the ambient identity. Splitting it
into biorthogonal multiplicity blocks is a further algebraic step. -/
theorem IsBoundaryClosed.exists_boundaryRepresentation
    {T : MPOTensor d (∑ c : Fin r, dim c)} (hT : IsBoundaryClosed T)
    (A : (c : Fin r) → MPSTensor (d * d) (dim c))
    (hBlocks : T.toMPSTensor = MPSTensor.toTensorFromBlocks (fun _ ↦ 1) A)
    {L : ℕ} (hL : 0 < L) (hSpan : MPSTensor.WordTupleSpanTop A L) :
    ∃ ρ : ((c : Fin r) → Matrix (Fin (dim c)) (Fin (dim c)) ℂ) →ₙₐ[ℂ]
      Matrix (Fin ((∑ c : Fin r, dim c) * (∑ c : Fin r, dim c)))
        (Fin ((∑ c : Fin r, dim c) * (∑ c : Fin r, dim c))) ℂ,
      ∀ i : Fin (d * d), ρ (fun c ↦ A c i) = (mulTensor T T).toMPSTensor i := by
  obtain ⟨b, hb⟩ := (isBoundaryClosed_iff_exists_linearMap T).mp hT
  apply MPSTensor.exists_boundaryRepresentation_of_boundaryMap
    (mulTensor T T).toMPSTensor A b ?_ hL hSpan
  intro n hn X w
  rw [← hBlocks, mpvWithBoundary_toMPSTensor, mpvWithBoundary_toMPSTensor]
  exact congrArg (fun M ↦ M (fun k ↦ (w k).divNat) (fun k ↦ (w k).modNat))
    (hb n hn X)

/-- Arbitrary-boundary compatibility induces a representation of the state
block matrix algebra on the acted-on bond space, reconstructing the action
letters exactly. Source: GLM23, `eq:compatible`, `fusiontensors2`, and
Appendix A, final paragraph. -/
theorem IsBoundaryCompatible.exists_boundaryRepresentation
    {T : MPOTensor d D} {A : MPSTensor d (∑ c : Fin r, dim c)}
    (h : IsBoundaryCompatible T A)
    (B : (c : Fin r) → MPSTensor d (dim c))
    (hBlocks : A = MPSTensor.toTensorFromBlocks (fun _ ↦ 1) B)
    {L : ℕ} (hL : 0 < L) (hSpan : MPSTensor.WordTupleSpanTop B L) :
    ∃ ρ : ((c : Fin r) → Matrix (Fin (dim c)) (Fin (dim c)) ℂ) →ₙₐ[ℂ]
      Matrix (Fin (D * ∑ c : Fin r, dim c)) (Fin (D * ∑ c : Fin r, dim c)) ℂ,
      ∀ i : Fin d, ρ (fun c ↦ B c i) = actTensor T A i := by
  obtain ⟨b, hb⟩ := (isBoundaryCompatible_iff_exists_linearMap T A).mp h
  apply MPSTensor.exists_boundaryRepresentation_of_boundaryMap
    (actTensor T A) B b ?_ hL hSpan
  intro n hn X w
  rw [← hBlocks]
  exact congrFun (hb n hn X) w

end MPOTensor
