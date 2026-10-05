/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BoundaryBlockAction
import TNLean.MPS.MPDO.InjectiveBlockWordSpan

/-!
# Source-block fusion and action tensors from arbitrary-boundary closedness

The source assumptions are length-independent arbitrary-boundary closedness
or compatibility, an unweighted block decomposition, and injective,
positive-dimensional target blocks with no gauge-scalar duplicates.
The common simultaneous inverse is derived, not assumed. The resulting
fusion and action tensors are exact and biorthogonal on each incoming pair.

## References

* Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3, block assumptions at
  lines 317--323, `algcond`, `eq:compatible`, and Appendix A.
-/

open scoped Matrix BigOperators

namespace MPOTensor

/-- The arbitrary-boundary closedness and block hypotheses of GLM23 yield
exact fusion tensors for each pair of incoming blocks. The simultaneous
word-spanning length is derived from individual injectivity and block
separation. Source: `fusiontensors`, `eq:orthoW`, and Appendix A. -/
theorem IsBoundaryClosed.exists_blockFusionDecomposition_of_isInjective
    {d r : ℕ} {dim : Fin r → ℕ}
    {T : MPOTensor d (∑ c : Fin r, dim c)} (hT : IsBoundaryClosed T)
    (A : (c : Fin r) → MPOTensor d (dim c))
    (hBlocks : T.toMPSTensor = MPSTensor.toTensorFromBlocks (fun _ ↦ 1)
      (fun c ↦ (A c).toMPSTensor))
    (hInj : ∀ c, Kraus.IsInjective (A c).toMPSTensor)
    (hDim : ∀ c, 0 < dim c)
    (hDistinct : MPSTensor.BlocksNotGaugePhaseEquiv (fun c ↦ (A c).toMPSTensor))
    (a b : Fin r) :
    ∃ (m : Fin r → ℕ)
      (V : ∀ c, Fin (m c) → Matrix (Fin (dim c)) (Fin (dim a * dim b)) ℂ)
      (W : ∀ c, Fin (m c) → Matrix (Fin (dim a * dim b)) (Fin (dim c)) ℂ),
      MPSTensor.IsBiorthogonalDecomposition (mulTensor (A a) (A b)).toMPSTensor
        (fun q : (c : Fin r) × Fin (m c) ↦ (A q.1).toMPSTensor)
        (fun q ↦ V q.1 q.2) (fun q ↦ W q.1 q.2) := by
  obtain ⟨L, hL, hSpan⟩ :=
    MPSTensor.exists_positive_wordTupleSpanTop_of_isInjective hInj hDim hDistinct
  exact hT.exists_blockFusionDecomposition A hBlocks hL hSpan a b

/-- The arbitrary-boundary compatibility and block hypotheses of GLM23
yield exact action tensors for each operator/state incoming pair.
Only the target state blocks require injectivity and pairwise separation.
Source: `fusiontensors2`, `eq:orthoV`, and Appendix A, final paragraph. -/
theorem IsBoundaryCompatible.exists_blockActionDecomposition_of_isInjective
    {d r s : ℕ} {opDim : Fin r → ℕ} {dim : Fin s → ℕ}
    {T : MPOTensor d (∑ a : Fin r, opDim a)}
    {A : MPSTensor d (∑ c : Fin s, dim c)} (h : IsBoundaryCompatible T A)
    (S : (a : Fin r) → MPOTensor d (opDim a))
    (B : (c : Fin s) → MPSTensor d (dim c))
    (hT : T.toMPSTensor = MPSTensor.toTensorFromBlocks (fun _ ↦ 1)
      (fun a ↦ (S a).toMPSTensor))
    (hA : A = MPSTensor.toTensorFromBlocks (fun _ ↦ 1) B)
    (hInj : ∀ c, Kraus.IsInjective (B c)) (hDim : ∀ c, 0 < dim c)
    (hDistinct : MPSTensor.BlocksNotGaugePhaseEquiv B)
    (a : Fin r) (x : Fin s) :
    ∃ (m : Fin s → ℕ)
      (V : ∀ c, Fin (m c) → Matrix (Fin (dim c)) (Fin (opDim a * dim x)) ℂ)
      (W : ∀ c, Fin (m c) → Matrix (Fin (opDim a * dim x)) (Fin (dim c)) ℂ),
      MPSTensor.IsBiorthogonalDecomposition (actTensor (S a) (B x))
        (fun q : (c : Fin s) × Fin (m c) ↦ B q.1)
        (fun q ↦ V q.1 q.2) (fun q ↦ W q.1 q.2) := by
  obtain ⟨L, hL, hSpan⟩ :=
    MPSTensor.exists_positive_wordTupleSpanTop_of_isInjective hInj hDim hDistinct
  exact h.exists_blockActionDecomposition S B hT hA hL hSpan a x

end MPOTensor
