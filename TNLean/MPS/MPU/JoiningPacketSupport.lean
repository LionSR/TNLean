/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.JoiningRegisterCoordinates

/-!
# Support of the actual joining packet

Every joining bond coordinate and both joining flags belong to the parent
interval support. The exact packet placement therefore acts within that
support.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5.
-/


namespace MPUCircuit

/-- Every typed joining packet site belongs to its parent interval.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem joiningPacketLogicalSites_mem_interval {d D N : ℕ}
    (c : Fin (N - 1)) {j k : ℕ}
    (hjm : j < (internalCutEmbedding N c).val)
    (hmk : (internalCutEmbedding N c).val < k)
    (i : Fin (2 * cutBondRegisterWidth d D N (internalCutEmbedding N c) + 2)) :
    joiningPacketLogicalSites d D N c i ∈ intervalLogicalSupport d D N j k := by
  unfold joiningPacketLogicalSites
  change Fin.append (joiningBondPacketSites d D N c) (joiningFlagPacketSites d D N c)
    ((finCongr _).toEmbedding i) ∈ _
  generalize (finCongr _).toEmbedding i = a
  induction a using Fin.addCases with
  | left b =>
    rw [Fin.append_left]
    unfold joiningBondPacketSites
    change Fin.append _ _ b ∈ _
    induction b using Fin.addCases with
    | left q =>
      rw [Fin.append_left]
      have h := cutBondRegisterWidth_internal q
      apply Or.inl
      change j < (internalCutEmbedding N c).val - 1 + 1 ∧
        (internalCutEmbedding N c).val - 1 + 1 < k
      exact ⟨by omega, by omega⟩
    | right q =>
      rw [Fin.append_right]
      have h := cutBondRegisterWidth_internal q
      apply Or.inl
      change j < (internalCutEmbedding N c).val - 1 + 1 ∧
        (internalCutEmbedding N c).val - 1 + 1 < k
      exact ⟨by omega, by omega⟩
  | right f =>
    rw [Fin.append_right]
    change j < (internalCutEmbedding N c).val ∧ (internalCutEmbedding N c).val < k
    exact ⟨hjm, hmk⟩

/-- The actual numbered joining packet is contained in the parent support.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem joiningPacketSites_range_subset_interval {d D N : ℕ}
    (c : Fin (N - 1)) {j k : ℕ}
    (hjm : j < (internalCutEmbedding N c).val)
    (hmk : (internalCutEmbedding N c).val < k) :
    Set.range (joiningPacketSites d D N c) ⊆ intervalConsecutiveSupport d D N j k := by
  rintro s ⟨i, rfl⟩
  exact ⟨_, joiningPacketLogicalSites_mem_interval c hjm hmk i, rfl⟩

end MPUCircuit
