/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.EncodedUniformMergingCircuit
import TNLean.MPS.MPU.UniformCircuitResourceBounds

/-!
# Uniform cost of a merger in the original interval coordinates

The two child coordinate changes and the final return are included in the
node budget. The joining packet and both reflections use the common scratch
pool. The resulting bound retains the two actual child gate counts, with
multiplier at most twice the bond bound plus one.

Source: the resource calculation in §5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.
-/

namespace MPUCircuit

open MPSPreparation

/-- The complete merger, including all three coordinate conjugations, satisfies
the uniform two-child recurrence. Source: the resource calculation in §5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem permutedEncodedUniformMergingGateCount_le_uniform
    {d D N b r : ℕ} (hd : 2 ≤ d) (hN : 2 ≤ N)
    (hb : b ≤ auxiliarySiteCount d D N) (hr : 0 < r) (hrD : r ≤ D)
    (K₁ K₂ : ℕ) :
    encodedUniformMergingGateCount d (bondRegisterWidth d D)
        (logicalSiteCount d D N) (auxiliarySiteCount d D N) b
        (K₁ + 4 * (globalSiteCount d D N) ^ 2)
        (K₂ + 4 * (globalSiteCount d D N) ^ 2) r +
        4 * (globalSiteCount d D N) ^ 2 ≤
      (2 * D + 1) * (K₁ + K₂) +
        amplificationTreeOverhead D (uniformNodeGateCount d D N)
          (uniformReflectionGateCount d D N) (uniformReflectionGateCount d D N) := by
  have hD : 0 < D := hr.trans_le hrD
  have hpool : 2 ≤ auxiliarySiteCount d D N := by
    dsimp [auxiliarySiteCount]
    have hfirst : 1 ≤ N - 1 := by omega
    have hsecond : 1 ≤ bondRegisterWidth d D + 1 := by omega
    have hprod := Nat.mul_le_mul hfirst hsecond
    nlinarith
  have hprep : mergingPreparationGateCount d (bondRegisterWidth d D)
      (logicalSiteCount d D N) (auxiliarySiteCount d D N) ≤
        uniformPacketGateCount d D N := by
    simpa only [mergingPreparationGateCount, globalSiteCount] using
      joiningPacketGateCount_le_uniform hd hD N
  have href₁ := selectedZeroRegisterReflectionPoolGateCount_le_uniform d D N b hb
  have href₂ := selectedZeroRegisterReflectionPoolGateCount_le_uniform d D N 2 hpool
  let M := uniformPacketGateCount d D N + 8 * (globalSiteCount d D N) ^ 2
  have hpre : mergingPreparationGateCount d (bondRegisterWidth d D)
        (logicalSiteCount d D N) (auxiliarySiteCount d D N) +
        ((K₁ + 4 * (globalSiteCount d D N) ^ 2) +
          (K₂ + 4 * (globalSiteCount d D N) ^ 2)) ≤ K₁ + K₂ + M := by
    calc
      _ ≤ uniformPacketGateCount d D N +
          ((K₁ + 4 * (globalSiteCount d D N) ^ 2) +
            (K₂ + 4 * (globalSiteCount d D N) ^ 2)) := Nat.add_le_add_right hprep _
      _ = _ := by dsimp [M]; ring
  have hcount : encodedUniformMergingGateCount d (bondRegisterWidth d D)
        (logicalSiteCount d D N) (auxiliarySiteCount d D N) b
        (K₁ + 4 * (globalSiteCount d D N) ^ 2)
        (K₂ + 4 * (globalSiteCount d D N) ^ 2) r ≤
      D * (1 + (2 * (K₁ + K₂ + M) +
        uniformReflectionGateCount d D N + uniformReflectionGateCount d D N)) +
        (K₁ + K₂ + M) := by
    dsimp [encodedUniformMergingGateCount]
    have hrounds := (amplificationRounds_le r).trans hrD
    gcongr
  have hreserve : amplificationTreeOverhead D M
        (uniformReflectionGateCount d D N) (uniformReflectionGateCount d D N) +
        4 * (globalSiteCount d D N) ^ 2 ≤
      amplificationTreeOverhead D (uniformNodeGateCount d D N)
        (uniformReflectionGateCount d D N) (uniformReflectionGateCount d D N) := by
    dsimp [amplificationTreeOverhead, M, uniformNodeGateCount]
    nlinarith
  calc
    _ ≤ (D * (1 + (2 * (K₁ + K₂ + M) +
        uniformReflectionGateCount d D N + uniformReflectionGateCount d D N)) +
        (K₁ + K₂ + M)) + 4 * (globalSiteCount d D N) ^ 2 :=
      Nat.add_le_add_right hcount _
    _ = (2 * D + 1) * (K₁ + K₂) +
        (amplificationTreeOverhead D M
          (uniformReflectionGateCount d D N) (uniformReflectionGateCount d D N) +
            4 * (globalSiteCount d D N) ^ 2) := by
      rw [amplificationTreeOverhead]
      ring
    _ ≤ _ := Nat.add_le_add_left hreserve _

end MPUCircuit
