/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Periodic.Overlap.Case3

/-!
# Periodic overlap dichotomy: main statement

This module contains the final Proposition 3.3 statement and its eventual
linear-independence corollary.

## Main declarations

* `periodicOverlapDichotomy`
* `periodicBasis_eventuallyLinearlyIndependent`

## References

* De las Cuevas, Cirac, Schuch, Perez-Garcia,
  *Irreducible forms of Matrix Product States: Theory and Applications*,
  arXiv:1708.00029, Proposition 3.3 and Appendix A.
-/

open scoped Matrix BigOperators ComplexOrder InnerProductSpace
open Filter Matrix

namespace MPSTensor

variable {d : ℕ}

/-! ## Main dichotomy (Proposition 3.3) -/

/-- **Periodic overlap dichotomy** (Proposition 3.3 of arXiv:1708.00029).

For two periodic tensors `A` and `B` with periods `m_a` and `m_b` in
irreducible form II, either their overlap decays to zero, or `D_a = D_b` and
they are related by a gauge transformation up to a unit-modulus phase (which
forces `m_a = m_b`).

This is the core technical result of the paper: all subsequent theorems
(proportional FT, equal FT with Z-gauge, symmetry corollary) depend on it. -/
theorem periodicOverlapDichotomy
    {D₁ D₂ : ℕ} [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    {m_a m_b : ℕ}
    (hA : IsPeriodic m_a A) (hB : IsPeriodic m_b B) :
    Tendsto (fun N => mpvOverlap A B N) atTop (nhds 0)
      ∨ ∃ (hdim : D₁ = D₂),
          RepeatedBlocks (cast (congr_arg (MPSTensor d) hdim) A) B := by
  -- PROOF STRUCTURE: see theorems
  -- `periodicOverlap_tendsto_zero_of_no_sector_match` and
  -- `periodicOverlap_gaugeEquiv_of_sector_match` for the same-period branches.
  -- Currently sorry-backed pending discharge of
  -- `exists_sector_match_of_gaugePhaseEquiv`,
  -- `sectorGaugePhaseEquiv_succ_of_cyclicTransport`, and
  -- `compressedTensor_adjointTransferMap_cornerBridge`.
  sorry

/-- **Eventual linear independence** (Corollary of Proposition 3.3):
Given a family of periodic tensors `{A_j}` whose periods all divide a common
period `p`, there exists `N₀` such that for all `N ≥ N₀` that are multiples
of `p`, the vectors `{|V_N(A_j)⟩}` are linearly independent.

The common-period restriction ensures all `mpvState (A k) N` are nonzero
simultaneously (a zero vector would prevent `LinearIndependent` from holding).

This is the "consequence" stated at the end of Proposition 3.3. -/
theorem periodicBasis_eventuallyLinearlyIndependent
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (period : Fin r → ℕ)
    (hPer : ∀ k, IsPeriodic (period k) (A k))
    (p : ℕ) [NeZero p]
    (hDiv : ∀ k, period k ∣ p)
    (hNonrep : ∀ i j, i ≠ j →
      ∀ (hdim : dim i = dim j),
        ¬ RepeatedBlocks (cast (congr_arg (MPSTensor d) hdim) (A i)) (A j)) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      LinearIndependent ℂ (fun k => mpvState (A k) (p * N)) := by
  -- PROOF STRUCTURE: see theorems
  -- `periodicSelfOverlap_tendsto` and `periodicOverlapDichotomy` for the
  -- Gram-matrix argument.
  -- Currently sorry-backed pending discharge of
  -- `primitive_and_irreducible_sectorBlocks_of_cyclicDecomp`,
  -- `exists_sector_match_of_gaugePhaseEquiv`, and
  -- `sectorGaugePhaseEquiv_succ_of_cyclicTransport`.
  sorry

end MPSTensor
