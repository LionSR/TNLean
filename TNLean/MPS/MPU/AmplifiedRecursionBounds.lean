/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.BondRegisterBounds
import TNLean.MPS.MPU.ExactAmplificationBudget
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Explicit gate-count bounds for the balanced amplification recursion

At a node, the pre-amplification circuit invokes two child circuits and a
joining primitive. The exact amplification formula therefore has child
factor at most `4D + 2` when every bond dimension is at most `D`. With one
uniform bound for the overhead of every node, a recursion of height
`ceil(log₂ N)` has polynomial cost in `N`, with exponent
`ceil(log₂(4D + 2)) ≤ ceil(log₂ D) + 3` for `D > 0`.

These are numerical implications of the stated gate-count recurrence;
they do not assume or assert existence of the corresponding circuits.
Source: the cost estimate in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.
-/

namespace MPUCircuit

/-- Two child calls and the exact amplification formula give the branching
factor `4D + 2`. The reflection and joining costs remain explicit.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem amplification_gateCount_le {ℓ D K T M B L F : ℕ}
    (hℓ : ℓ ≤ D) (hK : K ≤ 2 * T + M) (hB : B ≤ F) (hL : L ≤ F) :
    ℓ * (1 + (2 * K + B + L)) + K ≤
      (4 * D + 2) * T + (2 * D + 1) * M + D * (1 + 2 * F) := by
  calc
    _ ≤ D * (1 + (2 * (2 * T + M) + F + F)) + (2 * T + M) := by
      gcongr
    _ = _ := by ring

/-- The prescribed number of amplification rounds satisfies the same
branching bound when the actual bond dimension is at most `D`.
Source: Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem prescribed_amplification_gateCount_le {r D K T M B L F : ℕ}
    (hr : r ≤ D) (hK : K ≤ 2 * T + M) (hB : B ≤ F) (hL : L ≤ F) :
    amplificationRounds r * (1 + (2 * K + B + L)) + K ≤
      (4 * D + 2) * T + (2 * D + 1) * M + D * (1 + 2 * F) :=
  amplification_gateCount_le ((amplificationRounds_le r).trans hr) hK hB hL

/-- A constant-overhead integer recurrence has a geometric bound, including
the overhead term in the induction invariant. Source: the balanced cost
estimate in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem gateCount_add_overhead_le_pow (T : ℕ → ℕ) (a C R : ℕ) (hR : 2 ≤ R)
    (hbase : T 0 ≤ a) (hstep : ∀ j, T (j + 1) ≤ R * T j + C) (L : ℕ) :
    T L + C ≤ (a + C) * R ^ L := by
  induction L with
  | zero => simpa using Nat.add_le_add_right hbase C
  | succ L ih =>
    calc
      T (L + 1) + C ≤ R * T L + C + C := Nat.add_le_add_right (hstep L) C
      _ ≤ R * (T L + C) := by nlinarith
      _ ≤ R * ((a + C) * R ^ L) := Nat.mul_le_mul_left R ih
      _ = (a + C) * R ^ (L + 1) := by rw [pow_succ]; ring

/-- At balanced height `ceil(log₂ N)`, the numerical recurrence has an
explicit polynomial bound in the actual chain length. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem gateCount_le_polynomial_of_balanced_height (T : ℕ → ℕ) (a C R N : ℕ)
    (hR : 2 ≤ R) (hN : 0 < N) (hbase : T 0 ≤ a)
    (hstep : ∀ j, T (j + 1) ≤ R * T j + C) :
    T (Nat.clog 2 N) ≤ (a + C) * (2 * N) ^ Nat.clog 2 R := by
  have hRpow := Nat.le_pow_clog (by decide : 1 < 2) R
  have hNpow := (bond_register_dimension_bounds (by decide : 2 ≤ 2) hN).2
  calc
    T (Nat.clog 2 N) ≤ T (Nat.clog 2 N) + C := Nat.le_add_right _ _
    _ ≤ (a + C) * R ^ Nat.clog 2 N :=
      gateCount_add_overhead_le_pow T a C R hR hbase hstep _
    _ ≤ (a + C) * ((2 ^ Nat.clog 2 R) ^ Nat.clog 2 N) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hRpow _)
    _ = (a + C) * ((2 ^ Nat.clog 2 N) ^ Nat.clog 2 R) := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm (Nat.clog 2 R) (Nat.clog 2 N)]
    _ ≤ (a + C) * (2 * N) ^ Nat.clog 2 R :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hNpow _)

/-- The explicit branching exponent grows at most logarithmically in the
bond bound. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem amplification_branching_exponent_le {D : ℕ} (hD : 0 < D) :
    Nat.clog 2 (4 * D + 2) ≤ Nat.clog 2 D + 3 := by
  apply Nat.clog_le_of_le_pow
  have hDpow := Nat.le_pow_clog (by decide : 1 < 2) D
  calc
    4 * D + 2 ≤ 8 * D := by omega
    _ ≤ 8 * 2 ^ Nat.clog 2 D := Nat.mul_le_mul_left 8 hDpow
    _ = 2 ^ (Nat.clog 2 D + 3) := by rw [pow_add]; ring

end MPUCircuit
