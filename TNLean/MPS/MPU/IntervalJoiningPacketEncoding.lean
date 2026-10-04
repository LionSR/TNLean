/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.IntervalJointFlagInitialization
import TNLean.MPS.MPU.JoiningRegisterCoordinates
import TNLean.MPS.MPU.CompatibleBondDilationCircuit

/-!
# The actual joining packet encoding

The joining packet of the two child output columns carries the two given
bond labels and two zero flags, in the exact order of the compatible dilation.
This identity is derived from the prescribed child boundary configurations
and initialization of the joining flags.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5.
-/

open Matrix MPSTensor MPSPreparation

namespace MPUCircuit

/-- The actual joining packet agrees with the active branch of the compatible bond dilation.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem intervalJointOutputEmbedding_joiningPacket_active
    {d D N r l n : ℕ} [NeZero d] (hd : 2 ≤ d)
    (c : Fin (N - 1)) (j k : Fin (N + 1))
    (hjm : j.val < (internalCutEmbedding N c).val)
    (hmk : (internalCutEmbedding N c).val < k.val)
    (em : Fin r ↪ Cfg d (cutBondRegisterWidth d D N (internalCutEmbedding N c)))
    (ej : Fin l ↪ Cfg d (cutBondRegisterWidth d D N j))
    (ek : Fin n ↪ Cfg d (cutBondRegisterWidth d D N k))
    (p : (CutIntervalConfig d N j.val (internalCutEmbedding N c).val ×
      CutIntervalConfig d N (internalCutEmbedding N c).val k.val) × (Fin n × Fin l))
    (x y : Fin r)
    (z : {s // s ∉ intervalJointOutsideFlagSet (d := d) (D := D) j
      (internalCutEmbedding N c) k hjm hmk} → Fin d) :
    intervalJointOutputEmbedding j (internalCutEmbedding N c) k hjm hmk em ej ek
        (intervalJointInitializedOutsideEmbedding (d := d) (D := D) j
          (internalCutEmbedding N c) k hjm hmk)
        (((p.1.1, (x, p.2.2)), (p.1.2, (p.2.1, y))), z) ∘ joiningPacketSites d D N c =
      compatibleBondDilationCfg hd em (Sum.inl (y, x), 0) := by
  classical
  let q := cutBondRegisterWidth d D N (internalCutEmbedding N c)
  let E := intervalJointOutputEmbedding j (internalCutEmbedding N c) k hjm hmk em ej ek
    (intervalJointInitializedOutsideEmbedding (d := d) (D := D) j
      (internalCutEmbedding N c) k hjm hmk)
      (((p.1.1, (x, p.2.2)), (p.1.2, (p.2.1, y))), z)
  funext i
  change E (joiningPacketSites d D N c i) = _
  by_cases hL : i.val < q
  · let a : Fin q := ⟨i.val, hL⟩
    have hi : i = ⟨a.val, by have := a.isLt; omega⟩ := Fin.ext rfl
    rw [hi]
    change E (logicalSiteEquivFin d D N
      (joiningPacketLogicalSites d D N c ⟨a.val, by have := a.isLt; omega⟩)) = _
    rw [joiningPacketLogicalSites_left]
    dsimp only [E]
    rw [intervalJointOutputEmbedding_left_support _ _ _ hjm hmk em ej ek _ _ _
      (cutBondSiteEmbedding_mem_right j (internalCutEmbedding N c) a)]
    have hh := congrFun (intervalBoundaryConfig_right j (internalCutEmbedding N c) em ej
      (p.1.1, (x, p.2.2))) a
    rw [compatibleBondDilationCfg_left]
    change _ = em x a
    exact hh
  by_cases hR : i.val < 2 * q
  · let a : Fin q := ⟨i.val - q, by omega⟩
    have hi : i = ⟨q + a.val, by have := a.isLt; omega⟩ := Fin.ext (by dsimp [a]; omega)
    rw [hi]
    change E (logicalSiteEquivFin d D N
      (joiningPacketLogicalSites d D N c ⟨q + a.val, by have := a.isLt; omega⟩)) = _
    rw [joiningPacketLogicalSites_right]
    dsimp only [E]
    rw [intervalJointOutputEmbedding_right_support _ _ _ hjm hmk em ej ek _ _ _
      (cutBondSiteEmbedding_mem_left (internalCutEmbedding N c) k a)]
    have hh := congrFun (intervalBoundaryConfig_left (internalCutEmbedding N c) k ek em
      (p.1.2, (p.2.1, y))) a
    dsimp only [q]
    rw [compatibleBondDilationCfg_right]
    change _ = em y a
    exact hh
  · let a : Fin 2 := ⟨i.val - 2 * q, by have := i.isLt; omega⟩
    have hi : i = ⟨2 * q + a.val, by have := a.isLt; omega⟩ :=
      Fin.ext (by dsimp [a]; omega)
    rw [hi]
    change E (logicalSiteEquivFin d D N
      (joiningPacketLogicalSites d D N c ⟨2 * q + a.val, by have := a.isLt; omega⟩)) = _
    rw [joiningPacketLogicalSites_flag]
    dsimp only [E]
    rw [intervalJointOutputEmbedding_joiningFlag_zero _ _ _ hjm hmk em ej ek _
      (amplificationFlagEmbedding d D N (c, a))
      (by change (internalCutEmbedding N c).val = (internalCutEmbedding N c).val; rfl)]
    have ha : a = 0 ∨ a = 1 := by omega
    rcases ha with ha | ha
    · have hi0 : (⟨2 * q + a.val, by have := a.isLt; omega⟩ : Fin (2 * q + 2)) =
          ⟨2 * q, by omega⟩ := Fin.ext (by simp only [ha, Fin.val_zero, Nat.add_zero])
      rw [hi0]
      dsimp only [q]
      rw [compatibleBondDilationCfg_dilation]
      rfl
    · have hi1 : (⟨2 * q + a.val, by have := a.isLt; omega⟩ : Fin (2 * q + 2)) =
          ⟨2 * q + 1, by omega⟩ := Fin.ext (by simp only [ha, Fin.val_one])
      rw [hi1]
      dsimp only [q]
      rw [compatibleBondDilationCfg_attenuation]

end MPUCircuit
