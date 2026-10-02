/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.MinimalIntervalRootColumns

/-!
# Registers for the complete circuit, including one-site chains

The interval construction uses the physical chain, the logical auxiliaries,
and an equally sized reusable scratch pool. A one-site chain has no internal
cuts and hence no such auxiliaries. Append one identity padding qudit in that
case, so its physical unitary is one allowed neighboring-pair gate.

The physical basis inclusion initializes every auxiliary and padding qudit.
An implementation identity with this inclusion therefore expresses exact
physical action and exact auxiliary erasure, including the scalar phase.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5; the arbitrary
two-qudit gate model is specified in arXiv:2508.08160, local `main.tex`, line 820.
-/

open MPSTensor MPSPreparation

namespace MPUCircuit

/-- One identity padding qudit for a one-site chain, and none otherwise.

See the one-site case in §5 of the circuit manuscript. -/
def circuitPaddingCount (N : ℕ) : ℕ := if N = 1 then 1 else 0

/-- The complete site count, with the one-site padding included.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
def completeCircuitSiteCount (d D N : ℕ) : ℕ :=
  globalSiteCount d D N + circuitPaddingCount N

/-- The physical chain with all logical auxiliaries, scratch, and any one-site
padding initialized to zero.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
def completePhysicalConfigEmbedding {d D N : ℕ} [NeZero d] :
    Cfg d N ↪ Cfg d (completeCircuitSiteCount d D N) :=
  (physicalGlobalConfigEmbedding (d := d) (D := D) (N := N)).trans
    (zeroWorkspaceEmbedding (d := d) (n := globalSiteCount d D N)
      (a := circuitPaddingCount N))

/-- The padding uses at most one additional qudit.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem circuitPaddingCount_le_one (N : ℕ) : circuitPaddingCount N ≤ 1 := by
  unfold circuitPaddingCount
  split_ifs <;> omega

/-- The complete circuit register has the stated uniform size bound, including
the one-site case.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem completeCircuitSiteCount_le (d D N : ℕ) :
    completeCircuitSiteCount d D N ≤ 5 * N * (bondRegisterWidth d D + 1) + 1 :=
  Nat.add_le_add (globalSiteCount_le d D N) (circuitPaddingCount_le_one N)

/-- The physical inclusion appends zeros on each of the three auxiliary groups.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem completePhysicalConfigEmbedding_apply {d D N : ℕ} [NeZero d] (x : Cfg d N) :
    completePhysicalConfigEmbedding (D := D) x =
      Fin.append (Fin.append (Fin.append x 0) 0) 0 := rfl

end MPUCircuit
