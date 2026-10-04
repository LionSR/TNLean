/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.EndpointBondEncoding
import TNLean.MPS.MPU.MinimalCutIntervals
import TNLean.Circuit.CleanUnitaryImplementation
import Mathlib.Logic.Equiv.Fintype

/-!
# Physical inputs and bond-label outputs of an interval

The input encoding sets every interval auxiliary to zero. The output encoding
retains the physical output and the two boundary bond labels, and sets every
strictly interior auxiliary to zero. The same definition applies to leaves and
to larger intervals, including endpoint cuts whose bond registers have width
zero.

The encodings are defined on the actual logical support of the interval. Their
injectivity follows by restriction to the physical sites and to the two
separate boundary bond registers.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5.
-/

open Matrix MPSTensor MPSPreparation

namespace MPUCircuit

/-- The number of logical sites belonging to the interval.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
noncomputable def intervalPacketCard (d D N j k : ℕ) : ℕ := by
  classical
  exact Fintype.card {s : LogicalSite d D N // s ∈ intervalLogicalSupport d D N j k}

/-- Consecutive enumeration of the actual interval support in the full logical register.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
noncomputable def intervalPacketSites (d D N j k : ℕ) :
    Fin (intervalPacketCard d D N j k) ↪ Fin (logicalSiteCount d D N) := by
  classical
  exact (Fintype.equivFin
    {s : LogicalSite d D N // s ∈ intervalLogicalSupport d D N j k}).symm.toEmbedding.trans
    ((Function.Embedding.subtype _).trans (logicalSiteEquivFin d D N).toEmbedding)

/-- The packet enumeration contains exactly the interval support.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem intervalPacketSites_range (d D N j k : ℕ) :
    Set.range (intervalPacketSites d D N j k) = intervalConsecutiveSupport d D N j k := by
  classical
  ext s
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨_, ((Fintype.equivFin _).symm a).2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    refine ⟨(Fintype.equivFin _) ⟨a, ha⟩, ?_⟩
    change (logicalSiteEquivFin d D N)
      ((Fintype.equivFin {s : LogicalSite d D N //
        s ∈ intervalLogicalSupport d D N j k}).symm
          ((Fintype.equivFin {s : LogicalSite d D N //
            s ∈ intervalLogicalSupport d D N j k}) ⟨a, ha⟩)).val = _
    rw [Equiv.symm_apply_apply]

/-- Adjacent nonempty child interval packets occupy disjoint logical sites.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem intervalPacketSites_disjoint {d D N j m k : ℕ} (hjm : j < m) (hmk : m < k) :
    Disjoint (Set.range (intervalPacketSites d D N j m))
      (Set.range (intervalPacketSites d D N m k)) := by
  rw [intervalPacketSites_range, intervalPacketSites_range]
  exact intervalConsecutiveSupport_disjoint hjm hmk

/-- The typed logical site corresponding to a consecutively indexed interval coordinate.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
noncomputable def intervalPacketLogicalSite (d D N j k : ℕ)
    (i : Fin (intervalPacketCard d D N j k)) : LogicalSite d D N := by
  classical
  exact ((Fintype.equivFin
    {s : LogicalSite d D N // s ∈ intervalLogicalSupport d D N j k}).symm i).val

/-- Every interval coordinate belongs to its logical support.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem intervalPacketLogicalSite_mem (d D N j k : ℕ)
    (i : Fin (intervalPacketCard d D N j k)) :
    intervalPacketLogicalSite d D N j k i ∈ intervalLogicalSupport d D N j k := by
  classical
  exact ((Fintype.equivFin _).symm i).2

/-- Every site of the logical support occurs in the interval enumeration.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem intervalPacketLogicalSite_surjective {d D N j k : ℕ}
    (s : LogicalSite d D N) (hs : s ∈ intervalLogicalSupport d D N j k) :
    ∃ i, intervalPacketLogicalSite d D N j k i = s := by
  classical
  exact ⟨(Fintype.equivFin _) ⟨s, hs⟩, by simp [intervalPacketLogicalSite]⟩

/-- The physical input extended by zero to all interval auxiliary registers and to the other
physical sites.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
noncomputable def intervalPhysicalZeroConfig {d D N : ℕ} [NeZero d] (j k : ℕ)
    (x : CutIntervalConfig d N j k) : LogicalSite d D N → Fin d
  | Sum.inl s => if h : j ≤ s.val ∧ s.val < k then x ⟨s, h⟩ else 0
  | Sum.inr _ => 0

/-- Restriction of the initialized configuration to an interval physical site gives the physical
input.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem intervalPhysicalZeroConfig_physical {d D N : ℕ} [NeZero d] (j k : ℕ)
    (x : CutIntervalConfig d N j k) (s : Fin N) (hs : j ≤ s.val ∧ s.val < k) :
    intervalPhysicalZeroConfig (D := D) j k x (Sum.inl s) = x ⟨s, hs⟩ := by
  simp only [intervalPhysicalZeroConfig, dite_eq_left hs]

/-- Encoding of the physical input with every interval auxiliary initialized to zero.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
noncomputable def intervalInputEmbedding {d D N : ℕ} [NeZero d] (j k : ℕ) :
    CutIntervalConfig d N j k ↪ Cfg d (intervalPacketCard d D N j k) where
  toFun x := intervalPhysicalZeroConfig (D := D) j k x ∘ intervalPacketLogicalSite d D N j k
  inj' x y h := by
    classical
    funext s
    obtain ⟨i, hi⟩ := intervalPacketLogicalSite_surjective (D := D) (Sum.inl s.val) s.2
    have hh := congrFun h i
    change intervalPhysicalZeroConfig j k x (intervalPacketLogicalSite d D N j k i) =
      intervalPhysicalZeroConfig j k y (intervalPacketLogicalSite d D N j k i) at hh
    simpa only [hi, intervalPhysicalZeroConfig_physical j k _ _ s.2] using hh

/-- The physical output and the separate right and left boundary bond encodings, with every
remaining auxiliary zero.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
noncomputable def intervalBoundaryConfig {d D N : ℕ} [NeZero d] {ρ σ : Type*}
    (j k : Fin (N + 1))
    (eρ : ρ ↪ Cfg d (cutBondRegisterWidth d D N k))
    (eσ : σ ↪ Cfg d (cutBondRegisterWidth d D N j))
    (x : CutIntervalConfig d N j.val k.val × (ρ × σ)) : LogicalSite d D N → Fin d :=
  Function.extend (cutBondSiteEmbedding d D N k 0) (eρ x.2.1)
    (Function.extend (cutBondSiteEmbedding d D N j 1) (eσ x.2.2)
      (intervalPhysicalZeroConfig j.val k.val x.1))

/-- Restriction to the right boundary recovers its bond encoding.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem intervalBoundaryConfig_right {d D N : ℕ} [NeZero d] {ρ σ : Type*}
    (j k : Fin (N + 1))
    (eρ : ρ ↪ Cfg d (cutBondRegisterWidth d D N k))
    (eσ : σ ↪ Cfg d (cutBondRegisterWidth d D N j))
    (x : CutIntervalConfig d N j.val k.val × (ρ × σ)) :
    intervalBoundaryConfig j k eρ eσ x ∘ cutBondSiteEmbedding d D N k 0 = eρ x.2.1 :=
  Function.extend_comp (cutBondSiteEmbedding d D N k 0).injective _ _

/-- Restriction to the left boundary recovers its bond encoding.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem intervalBoundaryConfig_left {d D N : ℕ} [NeZero d] {ρ σ : Type*}
    (j k : Fin (N + 1))
    (eρ : ρ ↪ Cfg d (cutBondRegisterWidth d D N k))
    (eσ : σ ↪ Cfg d (cutBondRegisterWidth d D N j))
    (x : CutIntervalConfig d N j.val k.val × (ρ × σ)) :
    intervalBoundaryConfig j k eρ eσ x ∘ cutBondSiteEmbedding d D N j 1 = eσ x.2.2 := by
  funext q
  change Function.extend _ _ _ (cutBondSiteEmbedding d D N j 1 q) = _
  rw [Function.extend_apply' _ _ _ (by
    rintro ⟨r, hr⟩
    exact Set.disjoint_left.mp (cutBondSiteEmbedding_disjoint k j
      (by decide : (0 : Fin 2) ≠ 1)) ⟨r, hr⟩ ⟨q, rfl⟩)]
  exact congrFun (Function.extend_comp (cutBondSiteEmbedding d D N j 1).injective _ _) q

/-- Restriction to an interval physical site recovers its physical output.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem intervalBoundaryConfig_physical {d D N : ℕ} [NeZero d] {ρ σ : Type*}
    (j k : Fin (N + 1))
    (eρ : ρ ↪ Cfg d (cutBondRegisterWidth d D N k))
    (eσ : σ ↪ Cfg d (cutBondRegisterWidth d D N j))
    (x : CutIntervalConfig d N j.val k.val × (ρ × σ))
    (s : Fin N) (hs : j.val ≤ s.val ∧ s.val < k.val) :
    intervalBoundaryConfig j k eρ eσ x (Sum.inl s) = x.1 ⟨s, hs⟩ := by
  unfold intervalBoundaryConfig
  rw [Function.extend_apply' _ _ _ (by rintro ⟨q, hq⟩; cases hq),
    Function.extend_apply' _ _ _ (by rintro ⟨q, hq⟩; cases hq)]
  exact intervalPhysicalZeroConfig_physical j.val k.val _ _ hs

/-- Injective encoding of the physical output and the two boundary labels in the actual interval
packet.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
noncomputable def intervalOutputEmbedding {d D N : ℕ} [NeZero d] {ρ σ : Type*}
    (j k : Fin (N + 1))
    (eρ : ρ ↪ Cfg d (cutBondRegisterWidth d D N k))
    (eσ : σ ↪ Cfg d (cutBondRegisterWidth d D N j)) :
    (CutIntervalConfig d N j.val k.val × (ρ × σ)) ↪
      Cfg d (intervalPacketCard d D N j.val k.val) where
  toFun x := intervalBoundaryConfig j k eρ eσ x ∘ intervalPacketLogicalSite d D N j.val k.val
  inj' x y h := by
    classical
    have heq : ∀ s ∈ intervalLogicalSupport d D N j.val k.val,
        intervalBoundaryConfig j k eρ eσ x s = intervalBoundaryConfig j k eρ eσ y s := by
      intro s hs
      obtain ⟨i, hi⟩ := intervalPacketLogicalSite_surjective s hs
      exact hi ▸ congrFun h i
    apply Prod.ext
    · funext s
      simpa only [intervalBoundaryConfig_physical j k _ _ _ _ s.2] using
        heq (Sum.inl s.val) s.2
    · apply Prod.ext
      · apply eρ.injective
        funext q
        exact congrFun (intervalBoundaryConfig_right j k eρ eσ x) q |>.symm.trans
          ((heq _ (cutBondSiteEmbedding_mem_right j k q)).trans
            (congrFun (intervalBoundaryConfig_right j k eρ eσ y) q))
      · apply eσ.injective
        funext q
        exact congrFun (intervalBoundaryConfig_left j k eρ eσ x) q |>.symm.trans
          ((heq _ (cutBondSiteEmbedding_mem_left j k q)).trans
            (congrFun (intervalBoundaryConfig_left j k eρ eσ y) q))


/-- Every strictly interior auxiliary is exactly zero in the interval output encoding.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem intervalBoundaryConfig_interior {d D N : ℕ} [NeZero d] {ρ σ : Type*}
    (j k : Fin (N + 1))
    (eρ : ρ ↪ Cfg d (cutBondRegisterWidth d D N k))
    (eσ : σ ↪ Cfg d (cutBondRegisterWidth d D N j))
    (x : CutIntervalConfig d N j.val k.val × (ρ × σ)) :
    IsIntervalInteriorInitialized j.val k.val (intervalBoundaryConfig j k eρ eσ x) 0 := by
  intro s hs
  have hR : ¬∃ q, cutBondSiteEmbedding d D N k 0 q = s := by
    rintro ⟨q, rfl⟩
    change j.val < k.val - 1 + 1 ∧ k.val - 1 + 1 < k.val at hs
    have hk := cutBondRegisterWidth_internal q
    omega
  have hL : ¬∃ q, cutBondSiteEmbedding d D N j 1 q = s := by
    rintro ⟨q, rfl⟩
    change j.val < j.val - 1 + 1 ∧ j.val - 1 + 1 < k.val at hs
    have hj := cutBondRegisterWidth_internal q
    omega
  unfold intervalBoundaryConfig
  rw [Function.extend_apply' _ _ _ hR, Function.extend_apply' _ _ _ hL]
  rcases s with s | s
  · exact hs.elim
  · rfl

end MPUCircuit
