/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.IntervalInputRegrouping

/-!
# Parent output encoding after resetting the joining registers

The two child outputs retain separate copies of the joining bond label. When
both copies are encoded by the all-zero configuration, their restrictions to
the parent support coincide with the parent boundary configuration: the
physical outputs concatenate, the two outer bond labels are retained, and
all interior auxiliaries are zero.

The two joining flags are initialized by their concrete complement inclusion.
Every remaining outside configuration is retained through the site
equivalence between the child complement with those flags removed and the
parent complement. This gives equality of the full output encodings, without
an additional output-reset or outside-preservation hypothesis.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5.
-/

open Matrix MPSTensor MPSPreparation

namespace MPUCircuit

/-- Both joining bond registers lie strictly inside the parent interval.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem cutBondSiteEmbedding_mem_intervalInterior {d D N : ℕ}
    (j m k : Fin (N + 1)) (hjm : j.val < m.val) (hmk : m.val < k.val)
    (side : Fin 2) (q : Fin (cutBondRegisterWidth d D N m)) :
    cutBondSiteEmbedding d D N m side q ∈
      intervalInteriorAuxiliarySupport d D N j.val k.val := by
  change j.val < m.val - 1 + 1 ∧ m.val - 1 + 1 < k.val
  have hq := cutBondRegisterWidth_internal q
  constructor <;> omega

private theorem intervalBoundaryConfig_eq_physicalZero_of_not_boundaries
    {d D N : ℕ} [NeZero d] {ρ σ : Type*} (j k : Fin (N + 1))
    (eρ : ρ ↪ Cfg d (cutBondRegisterWidth d D N k))
    (eσ : σ ↪ Cfg d (cutBondRegisterWidth d D N j))
    (p : CutIntervalConfig d N j.val k.val × (ρ × σ)) (s : LogicalSite d D N)
    (hR : s ∉ Set.range (cutBondSiteEmbedding d D N k 0))
    (hL : s ∉ Set.range (cutBondSiteEmbedding d D N j 1)) :
    intervalBoundaryConfig j k eρ eσ p s = intervalPhysicalZeroConfig j.val k.val p.1 s := by
  unfold intervalBoundaryConfig
  rw [Function.extend_apply' _ _ _ hR, Function.extend_apply' _ _ _ hL]

/-- Resetting the left child's right boundary bond gives the parent boundary configuration on
the entire left child support. The parent's left bond label is retained.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem intervalBoundaryConfig_join_zero_left {d D N : ℕ} [NeZero d] {r l n : Type*}
    (j m k : Fin (N + 1)) (hjm : j.val < m.val) (hmk : m.val < k.val)
    (em : r ↪ Cfg d (cutBondRegisterWidth d D N m))
    (ej : l ↪ Cfg d (cutBondRegisterWidth d D N j))
    (ek : n ↪ Cfg d (cutBondRegisterWidth d D N k)) (q0 : r) (hem : em q0 = 0)
    (x : CutIntervalConfig d N j.val m.val) (y : CutIntervalConfig d N m.val k.val)
    (β : n) (α : l) (s : LogicalSite d D N)
    (hs : s ∈ intervalLogicalSupport d D N j.val m.val) :
    intervalBoundaryConfig j m em ej (x, (q0, α)) s =
      intervalBoundaryConfig j k ek ej (joinCutInterval j.val m.val k.val x y, (β, α)) s := by
  classical
  have hPk : s ∉ Set.range (cutBondSiteEmbedding d D N k 0) := by
    rintro ⟨q, rfl⟩
    exact Set.disjoint_left.mp (intervalLogicalSupport_disjoint hjm hmk) hs
      (cutBondSiteEmbedding_mem_right m k q)
  by_cases hL : s ∈ Set.range (cutBondSiteEmbedding d D N j 1)
  · obtain ⟨q, rfl⟩ := hL
    exact (congrFun (intervalBoundaryConfig_left j m em ej (x, (q0, α))) q).trans
      (congrFun (intervalBoundaryConfig_left j k ek ej
        (joinCutInterval j.val m.val k.val x y, (β, α))) q).symm
  by_cases hM : s ∈ Set.range (cutBondSiteEmbedding d D N m 0)
  · obtain ⟨q, rfl⟩ := hM
    calc
      intervalBoundaryConfig j m em ej (x, (q0, α)) _ = em q0 q :=
        congrFun (intervalBoundaryConfig_right j m em ej (x, (q0, α))) q
      _ = 0 := congrFun hem q
      _ = intervalBoundaryConfig j k ek ej
          (joinCutInterval j.val m.val k.val x y, (β, α)) _ :=
        (intervalBoundaryConfig_interior j k ek ej _ _
          (cutBondSiteEmbedding_mem_intervalInterior j m k hjm hmk 0 q)).symm
  rw [intervalBoundaryConfig_eq_physicalZero_of_not_boundaries j m em ej _ s hM hL,
    intervalBoundaryConfig_eq_physicalZero_of_not_boundaries j k ek ej _ s hPk hL]
  exact (intervalPhysicalZeroConfig_join_left (Nat.le_of_lt hmk) x y s hs).symm

/-- Resetting the right child's left boundary bond gives the parent boundary configuration on
the entire right child support. The parent's right bond label is retained.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem intervalBoundaryConfig_join_zero_right {d D N : ℕ} [NeZero d] {r l n : Type*}
    (j m k : Fin (N + 1)) (hjm : j.val < m.val) (hmk : m.val < k.val)
    (em : r ↪ Cfg d (cutBondRegisterWidth d D N m))
    (ej : l ↪ Cfg d (cutBondRegisterWidth d D N j))
    (ek : n ↪ Cfg d (cutBondRegisterWidth d D N k)) (q0 : r) (hem : em q0 = 0)
    (x : CutIntervalConfig d N j.val m.val) (y : CutIntervalConfig d N m.val k.val)
    (β : n) (α : l) (s : LogicalSite d D N)
    (hs : s ∈ intervalLogicalSupport d D N m.val k.val) :
    intervalBoundaryConfig m k ek em (y, (β, q0)) s =
      intervalBoundaryConfig j k ek ej (joinCutInterval j.val m.val k.val x y, (β, α)) s := by
  classical
  have hPj : s ∉ Set.range (cutBondSiteEmbedding d D N j 1) := by
    rintro ⟨q, rfl⟩
    exact Set.disjoint_left.mp (intervalLogicalSupport_disjoint hjm hmk)
      (cutBondSiteEmbedding_mem_left j m q) hs
  by_cases hR : s ∈ Set.range (cutBondSiteEmbedding d D N k 0)
  · obtain ⟨q, rfl⟩ := hR
    exact (congrFun (intervalBoundaryConfig_right m k ek em (y, (β, q0))) q).trans
      (congrFun (intervalBoundaryConfig_right j k ek ej
        (joinCutInterval j.val m.val k.val x y, (β, α))) q).symm
  by_cases hM : s ∈ Set.range (cutBondSiteEmbedding d D N m 1)
  · obtain ⟨q, rfl⟩ := hM
    calc
      intervalBoundaryConfig m k ek em (y, (β, q0)) _ = em q0 q :=
        congrFun (intervalBoundaryConfig_left m k ek em (y, (β, q0))) q
      _ = 0 := congrFun hem q
      _ = intervalBoundaryConfig j k ek ej
          (joinCutInterval j.val m.val k.val x y, (β, α)) _ :=
        (intervalBoundaryConfig_interior j k ek ej _ _
          (cutBondSiteEmbedding_mem_intervalInterior j m k hjm hmk 1 q)).symm
  rw [intervalBoundaryConfig_eq_physicalZero_of_not_boundaries m k ek em _ s hR hM,
    intervalBoundaryConfig_eq_physicalZero_of_not_boundaries j k ek ej _ s hR hPj]
  exact (intervalPhysicalZeroConfig_join_right (Nat.le_of_lt hjm) x y s hs).symm

private theorem joiningFlagSupport_subset_intervalInterior {d D N j m k : ℕ}
    (hjm : j < m) (hmk : m < k) :
    joiningFlagSupport d D N m ⊆ intervalInteriorAuxiliarySupport d D N j k := by
  intro s hs
  rcases s with s | (bond | ⟨c, flag⟩)
  · exact hs.elim
  · exact hs.elim
  · change (internalCutEmbedding N c).val = m at hs
    change j < (internalCutEmbedding N c).val ∧ (internalCutEmbedding N c).val < k
    omega

/-- The concrete jointly encoded child output, with both joining bonds reset and the joining
flags initialized, agrees with the parent boundary configuration on every parent-support site.
The flag initialization follows from the explicit complement inclusion.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem intervalJointOutputEmbedding_zero_eq_parent_support
    {d D N : ℕ} [NeZero d] {r l n : Type*}
    (j m k : Fin (N + 1)) (hjm : j.val < m.val) (hmk : m.val < k.val)
    (em : r ↪ Cfg d (cutBondRegisterWidth d D N m))
    (ej : l ↪ Cfg d (cutBondRegisterWidth d D N j))
    (ek : n ↪ Cfg d (cutBondRegisterWidth d D N k)) (q0 : r) (hem : em q0 = 0)
    (p : (CutIntervalConfig d N j.val m.val × CutIntervalConfig d N m.val k.val) × (n × l))
    (z : {s // s ∉ intervalJointOutsideFlagSet (d := d) (D := D) j m k hjm hmk} → Fin d)
    (s : LogicalSite d D N) (hs : s ∈ intervalLogicalSupport d D N j.val k.val) :
    intervalJointOutputEmbedding j m k hjm hmk em ej ek
      (intervalJointInitializedOutsideEmbedding (d := d) (D := D) j m k hjm hmk)
      (((p.1.1, (q0, p.2.2)), (p.1.2, (p.2.1, q0))), z) (logicalSiteEquivFin d D N s) =
        intervalBoundaryConfig j k ek ej
          (joinCutInterval j.val m.val k.val p.1.1 p.1.2, p.2) s := by
  rw [intervalLogicalSupport_split hjm hmk] at hs
  rcases hs with (hL | hR) | hF
  · rw [intervalJointOutputEmbedding_left_support j m k hjm hmk em ej ek _ _ s hL]
    exact intervalBoundaryConfig_join_zero_left j m k hjm hmk em ej ek q0 hem
      p.1.1 p.1.2 p.2.1 p.2.2 s hL
  · rw [intervalJointOutputEmbedding_right_support j m k hjm hmk em ej ek _ _ s hR]
    exact intervalBoundaryConfig_join_zero_right j m k hjm hmk em ej ek q0 hem
      p.1.1 p.1.2 p.2.1 p.2.2 s hR
  · rw [intervalJointOutputEmbedding_joiningFlag_zero j m k hjm hmk em ej ek _ s hF]
    exact (intervalBoundaryConfig_interior j k ek ej _ s
      (joiningFlagSupport_subset_intervalInterior hjm hmk hF)).symm

/-- The reset child output encoding is exactly the parent output encoding, retaining every
arbitrary outside configuration through the underlying site equivalence. The equality is
derived from the actual encodings and zero-preserving joining bond encoder.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem intervalJointOutputEmbedding_zero_eq_parent
    {d D N : ℕ} [NeZero d] {r l n : Type*}
    (j m k : Fin (N + 1)) (hjm : j.val < m.val) (hmk : m.val < k.val)
    (em : r ↪ Cfg d (cutBondRegisterWidth d D N m))
    (ej : l ↪ Cfg d (cutBondRegisterWidth d D N j))
    (ek : n ↪ Cfg d (cutBondRegisterWidth d D N k)) (q0 : r) (hem : em q0 = 0)
    (p : (CutIntervalConfig d N j.val m.val × CutIntervalConfig d N m.val k.val) × (n × l))
    (z : {s // s ∉ intervalJointOutsideFlagSet (d := d) (D := D) j m k hjm hmk} → Fin d) :
    intervalJointOutputEmbedding j m k hjm hmk em ej ek
        (intervalJointInitializedOutsideEmbedding (d := d) (D := D) j m k hjm hmk)
        (((p.1.1, (q0, p.2.2)), (p.1.2, (p.2.1, q0))), z) =
      placedBasisEmbedding (intervalPacketSites d D N j.val k.val)
        (intervalOutputEmbedding j k ek ej) (Function.Embedding.refl _)
        ((joinCutInterval j.val m.val k.val p.1.1 p.1.2, p.2),
          Equiv.arrowCongr (intervalJointRemainingSiteEquiv j m k hjm hmk)
            (Equiv.refl (Fin d)) z) := by
  apply (placedConfigEquiv d (intervalPacketSites d D N j.val k.val)).injective
  change (placedConfigEquiv d (intervalPacketSites d D N j.val k.val))
      (intervalJointOutputEmbedding j m k hjm hmk em ej ek _
        (((p.1.1, (q0, p.2.2)), (p.1.2, (p.2.1, q0))), z)) =
    (placedConfigEquiv d (intervalPacketSites d D N j.val k.val))
      ((placedConfigEquiv d (intervalPacketSites d D N j.val k.val)).symm
        ((intervalOutputEmbedding j k ek ej)
          (joinCutInterval j.val m.val k.val p.1.1 p.1.2, p.2),
          Equiv.arrowCongr (intervalJointRemainingSiteEquiv j m k hjm hmk)
            (Equiv.refl (Fin d)) z))
  rw [Equiv.apply_symm_apply]
  apply Prod.ext
  · rw [placedConfigEquiv_fst]
    funext i
    change intervalJointOutputEmbedding j m k hjm hmk em ej ek _
        (((p.1.1, (q0, p.2.2)), (p.1.2, (p.2.1, q0))), z)
        (logicalSiteEquivFin d D N (intervalPacketLogicalSite d D N j.val k.val i)) =
      intervalBoundaryConfig j k ek ej
        (joinCutInterval j.val m.val k.val p.1.1 p.1.2, p.2)
        (intervalPacketLogicalSite d D N j.val k.val i)
    exact intervalJointOutputEmbedding_zero_eq_parent_support j m k hjm hmk em ej ek q0 hem
      p z (intervalPacketLogicalSite d D N j.val k.val i)
      (intervalPacketLogicalSite_mem d D N j.val k.val i)
  · rw [placedConfigEquiv_snd]
    funext s
    have hh := congrFun (jointPlacedBasisEmbedding_outside
      (intervalPacketSites d D N j.val m.val) (intervalPacketSites d D N m.val k.val)
      (intervalPacketSites_disjoint (d := d) (D := D) (N := N) hjm hmk)
      (intervalOutputEmbedding j m em ej) (intervalOutputEmbedding m k ek em)
      (intervalJointInitializedOutsideEmbedding (d := d) (D := D) j m k hjm hmk)
      (((p.1.1, (q0, p.2.2)), (p.1.2, (p.2.1, q0))), z))
      ⟨s.val, ((not_mem_parentPacket_iff j m k hjm hmk s.val).mp s.property).1⟩
    exact hh.trans (intervalJointInitializedOutsideEmbedding_parentOutside j m k hjm hmk z s)

end MPUCircuit
