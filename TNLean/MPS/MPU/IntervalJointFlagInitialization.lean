/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.IntervalJointOutputEncoding

/-!
# Initialization of the actual joining flags

The joining flags lie outside both child supports. Their initialized inclusion
sets precisely those two coordinates to zero while retaining every remaining
outside coordinate. The joint child output therefore carries zero joining flags.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5.
-/

open Matrix MPSTensor MPSPreparation

namespace MPUCircuit

/-- The joining flags viewed in the complement of the two child supports.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
noncomputable def intervalJointOutsideFlagSet {d D N : ℕ}
    (j m k : Fin (N + 1)) (hjm : j.val < m.val) (hmk : m.val < k.val) :
    Set {s : Fin (logicalSiteCount d D N) // s ∉ Set.range (Fin.Embedding.append
      (intervalPacketSites_disjoint (d := d) (D := D) (N := N) hjm hmk))} :=
  fun s ↦ (logicalSiteEquivFin d D N).symm s.val ∈ joiningFlagSupport d D N m.val

/-- The outside inclusion which initializes exactly the joining flags.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
noncomputable def intervalJointInitializedOutsideEmbedding {d D N : ℕ} [NeZero d]
    (j m k : Fin (N + 1)) (hjm : j.val < m.val) (hmk : m.val < k.val) :=
  initializedComplementEmbedding (d := d)
    (intervalJointOutsideFlagSet (d := d) (D := D) j m k hjm hmk)

/-- Each joining flag lies outside both child packets.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem joiningFlag_outside_childPackets {d D N : ℕ}
    (j m k : Fin (N + 1)) (hjm : j.val < m.val) (hmk : m.val < k.val)
    (s : LogicalSite d D N) (hs : s ∈ joiningFlagSupport d D N m.val) :
    logicalSiteEquivFin d D N s ∉ Set.range (Fin.Embedding.append
      (intervalPacketSites_disjoint (d := d) (D := D) (N := N) hjm hmk)) := by
  rintro ⟨i, hi⟩
  induction i using Fin.addCases with
  | left q =>
    have hq : logicalSiteEquivFin d D N s ∈
        Set.range (intervalPacketSites d D N j.val m.val) :=
      ⟨q, by simpa only [Fin.Embedding.coe_append, Fin.append_left] using hi⟩
    rw [intervalPacketSites_range] at hq
    obtain ⟨s', hs', heq⟩ := hq
    have hh : s' = s := (logicalSiteEquivFin d D N).injective heq
    exact Set.disjoint_left.mp joiningFlagSupport_disjoint_left hs (hh ▸ hs')
  | right q =>
    have hq : logicalSiteEquivFin d D N s ∈
        Set.range (intervalPacketSites d D N m.val k.val) :=
      ⟨q, by simpa only [Fin.Embedding.coe_append, Fin.append_right] using hi⟩
    rw [intervalPacketSites_range] at hq
    obtain ⟨s', hs', heq⟩ := hq
    have hh : s' = s := (logicalSiteEquivFin d D N).injective heq
    exact Set.disjoint_left.mp joiningFlagSupport_disjoint_right hs (hh ▸ hs')

/-- The initialized joint child output has zero joining flags.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem intervalJointOutputEmbedding_joiningFlag_zero
    {d D N : ℕ} [NeZero d] {r l n : Type*}
    (j m k : Fin (N + 1)) (hjm : j.val < m.val) (hmk : m.val < k.val)
    (em : r ↪ Cfg d (cutBondRegisterWidth d D N m))
    (ej : l ↪ Cfg d (cutBondRegisterWidth d D N j))
    (ek : n ↪ Cfg d (cutBondRegisterWidth d D N k))
    (p : ((CutIntervalConfig d N j.val m.val × (r × l)) ×
      (CutIntervalConfig d N m.val k.val × (n × r))) ×
        ({s // s ∉ intervalJointOutsideFlagSet (d := d) (D := D) j m k hjm hmk} → Fin d))
    (s : LogicalSite d D N) (hs : s ∈ joiningFlagSupport d D N m.val) :
    intervalJointOutputEmbedding j m k hjm hmk em ej ek
      (intervalJointInitializedOutsideEmbedding (d := d) (D := D) j m k hjm hmk) p
        (logicalSiteEquivFin d D N s) = 0 := by
  classical
  let s' : {s : Fin (logicalSiteCount d D N) // s ∉ Set.range (Fin.Embedding.append
      (intervalPacketSites_disjoint (d := d) (D := D) (N := N) hjm hmk))} :=
    ⟨logicalSiteEquivFin d D N s, joiningFlag_outside_childPackets j m k hjm hmk s hs⟩
  have hh := congrFun (jointPlacedBasisEmbedding_outside
    (intervalPacketSites d D N j.val m.val) (intervalPacketSites d D N m.val k.val)
    (intervalPacketSites_disjoint (d := d) (D := D) (N := N) hjm hmk)
    (intervalOutputEmbedding j m em ej) (intervalOutputEmbedding m k ek em)
    (intervalJointInitializedOutsideEmbedding (d := d) (D := D) j m k hjm hmk) p) s'
  change intervalJointOutputEmbedding j m k hjm hmk em ej ek
      (intervalJointInitializedOutsideEmbedding (d := d) (D := D) j m k hjm hmk) p
        (logicalSiteEquivFin d D N s) = _ at hh
  refine hh.trans (initializedComplementEmbedding_zero
    (intervalJointOutsideFlagSet (d := d) (D := D) j m k hjm hmk) p.2 s' ?_)
  change (logicalSiteEquivFin d D N).symm (logicalSiteEquivFin d D N s) ∈
    joiningFlagSupport d D N m.val
  simpa only [Equiv.symm_apply_apply] using hs

end MPUCircuit
