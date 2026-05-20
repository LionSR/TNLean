import TNLean.PEPS.Blocking

import Mathlib.Data.Matrix.Basic

/-!
# Identity edge insertions for PEPS coefficients

This file proves the finite reindexing step for the identity specialization of
an edge insertion. The inserted-boundary data split into diagonal and
off-diagonal parts; the identity matrix kills the off-diagonal part, while the
diagonal part is equivalent to the ordinary edge-boundary data.

## Main results

- `edgeInsertedCoeff_identity`: inserting the identity matrix on the
  distinguished edge recovers the edge-blocked coefficient.
- `edgeInsertedCoeff_identity_eq_stateCoeff`: the same coefficient is the
  original PEPS coefficient.
- `SameState.edgeInsertedCoeff_identity_eq`: equal PEPS states have equal
  identity-inserted edge coefficients.

## References

- [Molnár, Schuch, Verstraete, Cirac, *Fundamental Theorem for injective PEPS*,
  arXiv:1804.04964, Section 3](https://arxiv.org/abs/1804.04964)
-/

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- Inserting the identity matrix on the distinguished edge recovers the
ordinary edge-blocked coefficient.

The proof first splits the inserted-boundary sum into diagonal and off-diagonal
parts. The off-diagonal part vanishes by the identity matrix, and the diagonal
part reindexes through the equivalence with ordinary edge-boundary data. -/
theorem edgeInsertedCoeff_identity (A : Tensor G d) (e : Edge G) (σ : V → Fin d) :
    edgeInsertedCoeff (G := G) A e σ
        (1 : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) =
      edgeBlockedCoeff (G := G) A e σ := by
  classical
  let insertedSummand : EdgeInsertedBoundaryConfig (G := G) A e → ℂ := fun β =>
    A.component e.1.1 (edgeInsertedLeftLocalConfig (G := G) A e β) (σ e.1.1) *
      (1 : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)
        β.leftEdgeIndex β.rightEdgeIndex *
      edgeOpenMiddleWeight (G := G) A e σ β.leftResidual β.rightResidual *
      A.component e.1.2 (edgeInsertedRightLocalConfig (G := G) A e β) (σ e.1.2)
  let blockedSummand : EdgeBoundaryConfig (G := G) A e → ℂ := fun β =>
    A.component e.1.1 (edgeLeftLocalConfig (G := G) A e β) (σ e.1.1) *
      edgeMiddleWeight (G := G) A e σ β *
      A.component e.1.2 (edgeRightLocalConfig (G := G) A e β) (σ e.1.2)
  have hoffdiag :
      (∑ β : {β : EdgeInsertedBoundaryConfig (G := G) A e //
          ¬ β.leftEdgeIndex = β.rightEdgeIndex}, insertedSummand β.1) = 0 := by
    apply Fintype.sum_eq_zero
    intro β
    simpa only [insertedSummand] using
      edgeInsertedCoeff_identity_offDiagonal_summand (G := G) A e σ β.1 β.2
  have hdiag :
      (∑ β : EdgeDiagonalInsertedBoundaryConfig (G := G) A e, insertedSummand β.1) =
        ∑ β : EdgeBoundaryConfig (G := G) A e, blockedSummand β := by
    let φ := edgeBoundaryConfigEquivDiagonalInsertedBoundaryConfig (G := G) A e
    calc
      (∑ β : EdgeDiagonalInsertedBoundaryConfig (G := G) A e, insertedSummand β.1)
          = ∑ β : EdgeBoundaryConfig (G := G) A e, insertedSummand (φ β).1 := by
            exact (φ.sum_comp fun β => insertedSummand β.1).symm
      _ = ∑ β : EdgeBoundaryConfig (G := G) A e, blockedSummand β := by
            refine Finset.sum_congr rfl ?_
            intro β _
            change
              insertedSummand (edgeBoundaryToInsertedBoundaryConfig (G := G) A e β) =
                blockedSummand β
            simpa only [insertedSummand, blockedSummand] using
              edgeInsertedCoeff_identity_diagonal_summand (G := G) A e σ β
  calc
    edgeInsertedCoeff (G := G) A e σ
        (1 : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)
        = ∑ β : EdgeInsertedBoundaryConfig (G := G) A e, insertedSummand β := by
          rfl
    _ = ∑ β : EdgeDiagonalInsertedBoundaryConfig (G := G) A e, insertedSummand β.1 := by
          have hsplit :=
            Fintype.sum_subtype_add_sum_subtype
              (p := fun β : EdgeInsertedBoundaryConfig (G := G) A e =>
                β.leftEdgeIndex = β.rightEdgeIndex) insertedSummand
          rw [← hsplit, hoffdiag, add_zero]
    _ = ∑ β : EdgeBoundaryConfig (G := G) A e, blockedSummand β := hdiag
    _ = edgeBlockedCoeff (G := G) A e σ := by
          rfl

/-- Identity insertion on the distinguished edge recovers the original PEPS
coefficient. -/
theorem edgeInsertedCoeff_identity_eq_stateCoeff (A : Tensor G d) (e : Edge G)
    (σ : V → Fin d) :
    edgeInsertedCoeff (G := G) A e σ
        (1 : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) =
      stateCoeff A σ := by
  rw [edgeInsertedCoeff_identity, edgeBlockedCoeff_eq_stateCoeff]

/-- Equality of PEPS states gives equality of the identity-inserted
edge-centered coefficients at every edge. -/
theorem SameState.edgeInsertedCoeff_identity_eq {A B : Tensor G d} (hAB : SameState A B)
    (e : Edge G) (σ : V → Fin d) :
    edgeInsertedCoeff (G := G) A e σ
        (1 : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) =
      edgeInsertedCoeff (G := G) B e σ
        (1 : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ) := by
  rw [edgeInsertedCoeff_identity_eq_stateCoeff, edgeInsertedCoeff_identity_eq_stateCoeff]
  exact hAB σ

end PEPS
end TNLean
