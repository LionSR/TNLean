/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.Overlap.SelfOverlapSetup

/-!
# The period of a tensor is at most its bond dimension

A tensor of period \(m\) has \(m\) nonzero cyclic sectors resolving the identity on its
\(D\)-dimensional bond space. The sector dimensions sum to \(D\), so \(m\le D\).
This sharpens the dimension count on the transfer operator's matrix space, which gives
only \(m\le D^2\).

## Main result

* `MPSTensor.IsPeriodic.period_le_bondDim` — the linear bound on the period.

## References

* arXiv:1708.00029, Lemma `lem:bdcf`, for the cyclic-sector decomposition.
* arXiv:quant-ph/0608197, Theorem 5, for the cyclic projections and the vanishing of the
  periodic vector at lengths not divisible by the period.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- The period is bounded by the bond dimension. The nonzero cyclic sectors resolve the
identity, so their positive dimensions sum to the bond dimension.

Source: arXiv:1708.00029, Lemma `lem:bdcf`, and the cyclic projections in
arXiv:quant-ph/0608197, Theorem 5. -/
theorem IsPeriodic.period_le_bondDim {m : ℕ} {A : MPSTensor d D}
    (hA : IsPeriodic m A) : m ≤ D := by
  have : NeZero D := ⟨hA.bondDim_ne_zero⟩
  obtain ⟨dim, _, P, _, V, _, _, _, hsum, _, _, _, _, _, _, hdim, _, hV, hP, _⟩ :=
    exists_cyclic_sector_decomp_with_letter_and_isometry_after_blocking_of_isPeriodic A hA
  have htrace (k : Fin m) : Matrix.trace (P k) = (dim k : ℂ) := by
    simpa only [hP k, hV k, Matrix.trace_one, Fintype.card_fin] using
      Matrix.trace_mul_comm (V k) (V k)ᴴ
  have hsumdim : ∑ k, dim k = D := Nat.cast_injective (by
    simpa only [Nat.cast_sum, Matrix.trace_sum, htrace, Matrix.trace_one, Fintype.card_fin]
      using congrArg Matrix.trace hsum : (↑(∑ k, dim k) : ℂ) = (D : ℂ))
  calc
    m = ∑ _k : Fin m, 1 := by simp
    _ ≤ ∑ k, dim k := Finset.sum_le_sum fun k _ ↦ Nat.pos_of_ne_zero (hdim k)
    _ = D := hsumdim

end MPSTensor
