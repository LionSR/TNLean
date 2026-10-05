/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BoundaryActionTrees
import TNLean.MPS.MPDO.BoundaryDecompositionCoordinates

/-!
# The full change between the two exact action trees

The actual fusion and action maps give two coordinate changes for the same
double-action tensor. Their inverse identities and synthesis equations follow
from the derived support equality, without assuming any L-symbol relation.

The two directions are named explicitly. The source's `V2` is an analysis
map, so `eq:F_symbol2` reads `H_sequential = L_printed * H_fusion`.
The printed L entries are the fixed-final multiplicity factor of the
fusion-to-sequential comparison, `H_sequential * S_fusion`. This module
retains the final bond indices and does not yet extract that factor.

## References

* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, `rawrels`,
  `eq:F_symbol2`, and `1Fsymbol`, lines 491--552.
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d r s : ℕ} {χ : Fin r → ℕ} {D : Fin s → ℕ}
  {N : Fin r → Fin r → Fin r → ℕ} {M : Fin r → Fin s → Fin s → ℕ}

/-- The full fusion-then-action coordinates include the final state bond. -/
abbrev FusionActionCoordinate (D : Fin s → ℕ)
    (N : Fin r → Fin r → Fin r → ℕ) (M : Fin r → Fin s → Fin s → ℕ)
    (a b : Fin r) (x : Fin s) :=
  (q : FusionActionPath N M a b x) × Fin (D q.2.1)

/-- The full sequential-action coordinates include the final state bond. -/
abbrev SequentialActionCoordinate (D : Fin s → ℕ)
    (M : Fin r → Fin s → Fin s → ℕ) (a b : Fin r) (x : Fin s) :=
  (q : SequentialActionPath M a b x) × Fin (D q.2.1)

variable
  (VF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ c)) (Fin (χ a * χ b)) ℂ)
  (WF : ∀ a b c, Fin (N a b c) → Matrix (Fin (χ a * χ b)) (Fin (χ c)) ℂ)
  (VA : ∀ a x y, Fin (M a x y) → Matrix (Fin (D y)) (Fin (χ a * D x)) ℂ)
  (WA : ∀ a x y, Fin (M a x y) → Matrix (Fin (χ a * D x)) (Fin (D y)) ℂ)

/-- Full coordinates from the fusion-then-action tree to the sequential
tree: sequential analysis applied to fusion-then-action synthesis. This
has the printed source L orientation in `1Fsymbol`. -/
noncomputable def fusionToSequentialComparison (a b : Fin r) (x : Fin s) :
    Matrix (SequentialActionCoordinate D M a b x) (FusionActionCoordinate D N M a b x) ℂ :=
  MPSTensor.decompositionAnalysis (sequentialActionAnalysis VA a b x) *
    MPSTensor.decompositionSynthesis (fusionThenActionSynthesis WF WA a b x)

/-- Full coordinates from the sequential tree to the fusion-then-action
tree. This is the inverse direction to the printed source L-matrix. -/
noncomputable def sequentialToFusionComparison (a b : Fin r) (x : Fin s) :
    Matrix (FusionActionCoordinate D N M a b x) (SequentialActionCoordinate D M a b x) ℂ :=
  MPSTensor.decompositionAnalysis (fusionThenActionAnalysis VF VA a b x) *
    MPSTensor.decompositionSynthesis (sequentialActionSynthesis WA a b x)

variable {O : ∀ a, MPOTensor d (χ a)} {A : ∀ x, MPSTensor d (D x)}
  (hF : ∀ a b,
    MPSTensor.IsBiorthogonalDecomposition (mulTensor (O a) (O b)).toMPSTensor
      (fun q : (c : Fin r) × Fin (N a b c) ↦ (O q.1).toMPSTensor)
      (fun q ↦ VF a b q.1 q.2) (fun q ↦ WF a b q.1 q.2))
  (hA : ∀ a x,
    MPSTensor.IsBiorthogonalDecomposition (actTensor (O a) (A x))
      (fun q : (y : Fin s) × Fin (M a x y) ↦ A q.1)
      (fun q ↦ VA a x q.1 q.2) (fun q ↦ WA a x q.1 q.2))

include hF hA in
/-- The two full action comparisons are inverse and reconstruct each tree's
synthesis from the other. The target span derives their common support;
no comparison or coherence equation is assumed. Source: GLM23 `1Fsymbol`. -/
theorem fullActionComparison_spec (a b : Fin r) (x : Fin s)
    {L : ℕ} (hL : 0 < L) (hSpan : MPSTensor.WordTupleSpanTop A L) :
    fusionToSequentialComparison WF VA WA a b x *
        sequentialToFusionComparison VF VA WA a b x = 1 ∧
      sequentialToFusionComparison VF VA WA a b x *
        fusionToSequentialComparison WF VA WA a b x = 1 ∧
      MPSTensor.decompositionSynthesis (sequentialActionSynthesis WA a b x) *
        fusionToSequentialComparison WF VA WA a b x =
          MPSTensor.decompositionSynthesis (fusionThenActionSynthesis WF WA a b x) ∧
      MPSTensor.decompositionSynthesis (fusionThenActionSynthesis WF WA a b x) *
        sequentialToFusionComparison VF VA WA a b x =
          MPSTensor.decompositionSynthesis (sequentialActionSynthesis WA a b x) := by
  exact MPSTensor.IsBiorthogonalDecomposition.fullComparison
    (A := A)
    (f := fun q : FusionActionPath N M a b x ↦ q.2.1)
    (g := fun q : SequentialActionPath M a b x ↦ q.2.1)
    (fusionThenAction_isBiorthogonal VF WF VA WA hF hA a b x)
    (sequentialAction_isBiorthogonal VA WA hA a b x) hL hSpan

include hF hA in
/-- The source-oriented full comparison carries fusion analysis to sequential
analysis. This is `eq:F_symbol2` before removing the final bond identity. -/
theorem fusionToSequentialComparison_mul_analysis (a b : Fin r) (x : Fin s)
    {L : ℕ} (hL : 0 < L) (hSpan : MPSTensor.WordTupleSpanTop A L) :
    fusionToSequentialComparison WF VA WA a b x *
      MPSTensor.decompositionAnalysis (fusionThenActionAnalysis VF VA a b x) =
        MPSTensor.decompositionAnalysis (sequentialActionAnalysis VA a b x) := by
  have hSupport :
      MPSTensor.decompositionSynthesis (fusionThenActionSynthesis WF WA a b x) *
        MPSTensor.decompositionAnalysis (fusionThenActionAnalysis VF VA a b x) =
      MPSTensor.decompositionSynthesis (sequentialActionSynthesis WA a b x) *
        MPSTensor.decompositionAnalysis (sequentialActionAnalysis VA a b x) := by
    rw [MPSTensor.decompositionSynthesis_mul_analysis,
      MPSTensor.decompositionSynthesis_mul_analysis]
    exact fusionThenAction_support_eq_sequentialAction VF WF VA WA hF hA a b x hL hSpan
  rw [fusionToSequentialComparison, Matrix.mul_assoc, hSupport, ← Matrix.mul_assoc,
    (sequentialAction_isBiorthogonal VA WA hA a b x).analysis_mul_synthesis,
    Matrix.one_mul]

end MPOTensor
