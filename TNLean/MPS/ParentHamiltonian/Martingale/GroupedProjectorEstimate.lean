/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.GroupedOpenGap
import TNLean.MPS.ParentHamiltonian.Martingale.GroupedSpectatorNorm
import TNLean.MPS.ParentHamiltonian.Martingale.WholeIncrementSpectatorTransport

/-!
# Grouped C3 from whole-interval projector errors

An open-chain kernel identity identifies the prefix ground projections with
matrix-product boundary spaces. A bound on the three-interval projector error
then bounds the grouped martingale product after adjoining right spectators.
The first two grouped indices vanish identically.

This is the passage from Nachtergaele's projector estimate in Section 6 to
condition C3-prime, arXiv:cond-mat/9410110, lines 1095--1107.
-/

open scoped ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

/-- A uniform three-interval projector error implies grouped C3 for the
range-\(2p\) parent Hamiltonian. The open-chain kernel identities are required
only from the interaction length onwards. This is Nachtergaele's condition
C3-prime with increment and overlap both equal to \(p\). -/
theorem grouped_martingaleDifference_norm_le_of_projector_defect
    (A : MPSTensor d D) {p M : ℕ} (hp : 0 < p) (hM : 2 ≤ M)
    (hKernel : ∀ n, 2 * p ≤ n →
      LinearMap.ker (openParentHamiltonianES A (2 * p) n) = groundSpaceES A n)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hDefect : ∀ K : ℕ,
      ‖(groundSpaceES A (K + p + p)).starProjection -
        (leftBoundaryMapES A (K + p) p).range.starProjection.comp
          (reassocTailBoundaryMapES A K p p).range.starProjection‖ ≤ ε) :
    ∀ n ∈ Finset.range M,
      ‖LinearMap.toContinuousLinearMap
        ((groupedIntervalGroundProjectionES A p (p * M) n).comp
          ((groupedNestedGroundProjectionsES A p (p * M)).martingaleDifference n))‖ ≤ ε := by
  apply grouped_martingaleDifference_norm_le_of_two_le A hp (by nlinarith) hε
  intro n hn2 hnM
  have hK : p * (n - 1) + p = p * n := by
    simpa only [Nat.mul_add, Nat.mul_one] using
      congrArg (p * ·) (Nat.sub_add_cancel (show 1 ≤ n by omega))
  have hactive := (norm_suffixProjection_comp_prefixDifference_eq_projector_defect
    A (K := p * (n - 1)) (L := p) (Q := p) (by omega)
    (by simpa only [← two_mul] using
      hKernel (p * (n - 1) + p) (by nlinarith [Nat.mul_le_mul_left p hn2]))
    (by simpa only [← two_mul] using
      hKernel (p * (n - 1) + p + p) (by nlinarith [Nat.mul_le_mul_left p hn2]))).trans_le
        (hDefect (p * (n - 1)))
  simp only [hK, ← two_mul] at hactive
  let F (N a b : ℕ) : ℝ :=
    ‖LinearMap.toContinuousLinearMap
      ((LinearMap.ker
        (openSuffixParentHamiltonianES A (2 * p) (2 * p) N b)).starProjection.toLinearMap.comp
        (openPrefixGroundProjectionES A (2 * p) N a - openPrefixGroundProjectionES A (2 * p) N b))‖
  change F (p * (n - 1) + p + p) (p * n) (p * n + p) ≤ ε at hactive
  rw [hK] at hactive
  have hspectator :
      F (p * n + p + (p * M - (p * n + p))) (p * n) (p * n + p) ≤
        F (p * n + p) (p * n) (p * n + p) :=
    norm_suffixGroundProjection_comp_prefixDifference_le_active A
      (R := 2 * p) (l := 2 * p) (n := p * n + p)
      (r := p * M - (p * n + p)) (p := p * n) (by omega) (by omega)
  have hbound : F (p * M) (p * n) (p * n + p) ≤ ε := by
    simpa only [Nat.add_sub_of_le (show p * n + p ≤ p * M by
      simpa only [Nat.mul_succ] using Nat.mul_le_mul_left p hnM)] using
        hspectator.trans hactive
  simpa only [F, groupedIntervalGroundProjectionES,
    FrustrationFree.NestedGroundProjections.martingaleDifference,
    groupedNestedGroundProjectionsES, Nat.mul_succ] using hbound

end MPSTensor
