/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixStabilization
import Mathlib.Algebra.Ring.Idempotent

/-!
# Commuting weighted traces of stabilized powers

The nilpotent transient of a stabilized matrix contributes zero even when
the trace is weighted by a commuting matrix. Thus the stabilized value of
the weighted trace already holds at every positive power. This supplies
the nilpotent-elimination step needed after the intrinsic MPU blocked-trace
identity; it does not assume that a particular twisted transfer stabilizes.

Source context: arXiv:1703.09188, elimination of the zero-primary transfer
component, lines 397--409, and the blocking-parity problem, lines 1633--1733.
-/

namespace Matrix.StabilizedRankOneData

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : Matrix ι ι ℂ} {bound : ℕ}

/-- Every positive power differs from the stabilized projector by a
nilpotent matrix. The complementary idempotent isolates the transient
without choosing a Jordan basis.

Source context: arXiv:1703.09188, lines 397--409. -/
theorem isNilpotent_pow_sub_power (data : StabilizedRankOneData E bound)
    (k : ℕ) (hk : 0 < k) : IsNilpotent (E ^ k - E ^ data.exponent) := by
  have hP : IsIdempotentElem (E ^ data.exponent) := data.projector_idempotent
  have hEP : E ^ k * E ^ data.exponent = E ^ data.exponent := by
    rw [← pow_add]
    exact data.stable _ (by omega)
  have hfactor : E ^ k - E ^ data.exponent =
      E ^ k * (1 - E ^ data.exponent) := by
    rw [mul_sub, mul_one, hEP]
  have hcomm : Commute (E ^ k) (1 - E ^ data.exponent) :=
    (Commute.one_right _).sub_right ((Commute.refl E).pow_pow k data.exponent)
  have hbound : data.exponent ≤ k * data.exponent := by
    simpa only [Nat.one_mul] using
      Nat.mul_le_mul (Nat.succ_le_of_lt hk) (le_refl data.exponent)
  refine ⟨data.exponent, ?_⟩
  rw [hfactor, hcomm.mul_pow,
    hP.one_sub.pow_eq (Nat.ne_of_gt data.exponent_pos), ← pow_mul,
    data.stable (k * data.exponent) hbound,
    hP.mul_one_sub_self]

/-- A weight commuting with a stabilized matrix annihilates the trace
contribution of its nilpotent transient. The weighted trace therefore has
its stabilized value at every positive power, not only large powers.

Source context: arXiv:1703.09188, lines 397--409 and 1633--1733.
This is a matrix-algebra prerequisite, not a blocking-parity assertion. -/
theorem trace_mul_pow_eq_of_commute (data : StabilizedRankOneData E bound)
    (F : Matrix ι ι ℂ) (hcomm : Commute F E) (k : ℕ) (hk : 0 < k) :
    Matrix.trace (F * E ^ k) = Matrix.trace (F * E ^ data.exponent) := by
  have hN := data.isNilpotent_pow_sub_power k hk
  have hFN : Commute F (E ^ k - E ^ data.exponent) :=
    (hcomm.pow_right k).sub_right (hcomm.pow_right data.exponent)
  have htrace : Matrix.trace (F * (E ^ k - E ^ data.exponent)) = 0 :=
    (Matrix.isNilpotent_trace_of_isNilpotent (hFN.isNilpotent_mul_left hN)).eq_zero
  rw [mul_sub, Matrix.trace_sub] at htrace
  exact sub_eq_zero.mp htrace

end Matrix.StabilizedRankOneData
