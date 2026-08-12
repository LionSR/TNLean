/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.FibonacciBoundaryRank
import TNLean.MPS.MPDO.PureRecovery
import TNLean.MPS.MPDO.StrongRFPRankGrowth

/-!
# Periodic operator rank of the Fibonacci boundary tensor

This file identifies the ordinary rank of the periodic MPO obtained from the
Fibonacci boundary tensor with the periodic transition count. It then derives
the golden-ratio formula and the failure of geometric rank growth.

The restriction to positive lengths is necessary: at length zero the periodic
MPO rank is one, whereas `periodicTransitionCount 0 = 2`.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix D, lines 2116--2176.
-/

open scoped Matrix
open Matrix Finset

namespace MPSTensor
namespace FibonacciBoundary

private lemma closed_endpoint_support_disjoint (W : FusionWeights) {N : ℕ}
    (hN : 0 < N) (σ : Fin N → Fin 8) :
    ¬(evalWord (tensor W) (List.ofFn σ) 0 0 ≠ 0 ∧
      evalWord (tensor W) (List.ofFn σ) 1 1 ≠ 0) := by
  cases N with
  | zero => simp at hN
  | succ n =>
      rw [List.ofFn_succ]
      exact evalWord_closed_endpoint_support_disjoint W (σ 0) (List.ofFn (Fin.tail σ))

private lemma mpv_ne_zero_iff_closed_endpoint (W : FusionWeights) {N : ℕ}
    (hN : 0 < N) (σ : Fin N → Fin 8) :
    mpv (tensor W) σ ≠ 0 ↔
      evalWord (tensor W) (List.ofFn σ) 0 0 ≠ 0 ∨
        evalWord (tensor W) (List.ofFn σ) 1 1 ≠ 0 := by
  rw [mpv, coeff, Matrix.trace_fin_two]
  have hdisjoint := closed_endpoint_support_disjoint W hN σ
  constructor
  · contrapose!
    simp_all
  · rintro (h | h)
    · have h1 : evalWord (tensor W) (List.ofFn σ) 1 1 = 0 := by
        by_contra h1
        exact hdisjoint ⟨h, h1⟩
      simp [h, h1]
    · have h0 : evalWord (tensor W) (List.ofFn σ) 0 0 = 0 := by
        by_contra h0
        exact hdisjoint ⟨h0, h⟩
      simp [h, h0]

/-- The ordinary rank of the positive-length periodic MPO is the periodic
transition count.

Source: arXiv:1606.00608, Appendix D, lines 2157--2176. -/
theorem rank_mpo_toMPOTensor_eq_periodicTransitionCount (W : FusionWeights) (N : ℕ)
    (hN : 0 < N) :
    (MPOTensor.mpo (tensor W).toMPOTensor N).rank = periodicTransitionCount N := by
  classical
  rw [rank_mpo_toMPOTensor, Fintype.card_subtype, periodicTransitionCount]
  simp only [mpv_ne_zero_iff_closed_endpoint W hN]
  rw [Finset.filter_or, Finset.card_union_of_disjoint]
  · rw [← Fintype.card_subtype, ← Fintype.card_subtype,
      ← rank_openBoundaryOperator_eq_x, ← rank_openBoundaryOperator_eq_x,
      openBoundaryOperator, openBoundaryOperator, Matrix.rank_diagonal, Matrix.rank_diagonal]
  · rw [Finset.disjoint_left]
    intro σ h0 h1
    exact closed_endpoint_support_disjoint W hN σ ⟨by simpa using h0, by simpa using h1⟩

/-- The positive-length Fibonacci periodic MPO rank is the sum of the even
powers of the golden ratio and its conjugate.

Source: arXiv:1606.00608, Appendix D, lines 2122--2125 and 2157--2176. -/
theorem rank_mpo_toMPOTensor_eq_goldenRatio (W : FusionWeights) (N : ℕ) (hN : 0 < N) :
    ((MPOTensor.mpo (tensor W).toMPOTensor N).rank : ℝ) =
      Real.goldenRatio ^ (2 * N) + Real.goldenConj ^ (2 * N) := by
  rw [rank_mpo_toMPOTensor_eq_periodicTransitionCount W N hN,
    periodicTransitionCount_eq_goldenRatio]

/-- The periodic MPO ranks of the Fibonacci boundary tensor are not geometric.

Source: arXiv:1606.00608, Appendix D, line 2125. -/
theorem rank_mpo_toMPOTensor_not_geometric (W : FusionWeights) :
    ¬∃ r s : ℕ, ∀ N : ℕ, 0 < N →
      (MPOTensor.mpo (tensor W).toMPOTensor N).rank = r * s ^ (N - 1) := by
  rintro ⟨r, s, h⟩
  exact periodicTransitionCount_not_geometric ⟨r, s, fun N hN ↦
    (rank_mpo_toMPOTensor_eq_periodicTransitionCount W N hN).symm.trans (h N hN)⟩

/-- The canonical Fibonacci diagonal MPO tensor is not a strong
renormalization fixed point.

Source: arXiv:1606.00608, Appendix D, lines 2109--2125. -/
theorem toMPOTensor_not_isStrongRFP (W : FusionWeights) :
    ¬MPOTensor.IsStrongRFP (tensor W).toMPOTensor := by
  intro hRFP
  obtain ⟨P, _, _, hgeom⟩ := hRFP.exists_periodic_rank_factor
  apply rank_mpo_toMPOTensor_not_geometric W
  exact ⟨(MPOTensor.mpo (tensor W).toMPOTensor 1).rank, P.rank, fun N hN ↦ by
    cases N with
    | zero => omega
    | succ n => simpa using hgeom n⟩

end FibonacciBoundary
end MPSTensor
