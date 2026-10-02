/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.IntervalJointFlagInitialization
import TNLean.MPS.MPU.MinimalIntervalColumns
import TNLean.MPS.MPU.MinimalCutJoiningParent
import TNLean.MPS.MPU.IntervalInitializationBounds
import TNLean.MPS.Preparation.InitializedRegisterProjection

/-!
# The actual initialized input of an interval merge

Two adjacent child supports occupy the parent support except for the two
joining flags. Removing those flags from the joint complement gives exactly
the parent complement, with every remaining site unchanged. Joining the
physical inputs therefore identifies the actual jointly initialized child
input with the parent initialized input, including unrestricted outside
configurations.

The parent input range is characterized by zero values on its boundary and
interior auxiliaries. This proves equality with the range of the constructed
zero-flag inclusion used by the input reflection. The individual supported
child column identities also yield the actual joint columns with the joining
flags initialized and every remaining outside configuration retained.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5.
-/


open Matrix MPSTensor MPSPreparation
open scoped Matrix Kronecker ComplexOrder MatrixOrder

namespace MPUCircuit

/-- The range of two concatenated placements is the union of their ranges.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem mem_range_finEmbeddingAppend_iff {α : Type*} {a b : ℕ}
    (e : Fin a ↪ α) (f : Fin b ↪ α)
    (h : Disjoint (Set.range e) (Set.range f)) (s : α) :
    s ∈ Set.range (Fin.Embedding.append h) ↔ s ∈ Set.range e ∨ s ∈ Set.range f := by
  constructor
  · rintro ⟨i, hi⟩
    induction i using Fin.addCases with
    | left q =>
      exact Or.inl ⟨q, by simpa only [Fin.Embedding.coe_append, Fin.append_left] using hi⟩
    | right q =>
      exact Or.inr ⟨q, by simpa only [Fin.Embedding.coe_append, Fin.append_right] using hi⟩
  · rintro (⟨q, rfl⟩ | ⟨q, rfl⟩)
    · exact ⟨Fin.castAdd b q, by simp only [Fin.Embedding.coe_append, Fin.append_left]⟩
    · exact ⟨Fin.natAdd a q, by simp only [Fin.Embedding.coe_append, Fin.append_right]⟩

/-- Membership of a numbered interval site is membership of its typed logical site.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem mem_range_intervalPacketSites_iff (d D N j k : ℕ)
    (s : Fin (logicalSiteCount d D N)) :
    s ∈ Set.range (intervalPacketSites d D N j k) ↔
      (logicalSiteEquivFin d D N).symm s ∈ intervalLogicalSupport d D N j k := by
  rw [intervalPacketSites_range]
  constructor
  · rintro ⟨t, ht, rfl⟩
    simpa only [Equiv.symm_apply_apply] using ht
  · intro hs
    exact ⟨_, hs, Equiv.apply_symm_apply _ _⟩

/-- Outside the parent packet means outside the child packets and outside the joining flags.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem not_mem_parentPacket_iff {d D N : ℕ}
    (j m k : Fin (N + 1)) (hjm : j.val < m.val) (hmk : m.val < k.val)
    (s : Fin (logicalSiteCount d D N)) :
    s ∉ Set.range (intervalPacketSites d D N j.val k.val) ↔
      s ∉ Set.range (Fin.Embedding.append
        (intervalPacketSites_disjoint (d := d) (D := D) (N := N) hjm hmk)) ∧
      (logicalSiteEquivFin d D N).symm s ∉ joiningFlagSupport d D N m.val := by
  rw [mem_range_finEmbeddingAppend_iff]
  simp only [mem_range_intervalPacketSites_iff,
    intervalLogicalSupport_split hjm hmk, Set.mem_union, not_or]

/-- Removing the joining flags from the joint outside sites leaves exactly the parent outside
sites, with the underlying numbered site unchanged.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
noncomputable def intervalJointRemainingSiteEquiv {d D N : ℕ}
    (j m k : Fin (N + 1)) (hjm : j.val < m.val) (hmk : m.val < k.val) :
    {s : {s : Fin (logicalSiteCount d D N) // s ∉ Set.range (Fin.Embedding.append
      (intervalPacketSites_disjoint (d := d) (D := D) (N := N) hjm hmk))} //
      s ∉ intervalJointOutsideFlagSet (d := d) (D := D) j m k hjm hmk} ≃
    {s : Fin (logicalSiteCount d D N) //
      s ∉ Set.range (intervalPacketSites d D N j.val k.val)} where
  toFun s := ⟨s.val.val, (not_mem_parentPacket_iff j m k hjm hmk s.val.val).mpr
    ⟨s.val.property, s.property⟩⟩
  invFun s := ⟨⟨s.val, ((not_mem_parentPacket_iff j m k hjm hmk s.val).mp s.property).1⟩,
    ((not_mem_parentPacket_iff j m k hjm hmk s.val).mp s.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Two adjacent physical inputs and the remaining sites give exactly a parent physical input
and its unrestricted outside configuration.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
noncomputable def intervalJointInputConfigEquiv {d D N : ℕ}
    (j m k : Fin (N + 1)) (hjm : j.val < m.val) (hmk : m.val < k.val) :
    ((CutIntervalConfig d N j.val m.val × CutIntervalConfig d N m.val k.val) ×
      ({s : {s : Fin (logicalSiteCount d D N) // s ∉ Set.range (Fin.Embedding.append
        (intervalPacketSites_disjoint (d := d) (D := D) (N := N) hjm hmk))} //
        s ∉ intervalJointOutsideFlagSet (d := d) (D := D) j m k hjm hmk} → Fin d)) ≃
    (CutIntervalConfig d N j.val k.val ×
      OutsidePlacedConfig d (intervalPacketSites d D N j.val k.val)) :=
  Equiv.prodCongr (cutIntervalSplitEquiv d N j.val m.val k.val
    (Nat.le_of_lt hjm) (Nat.le_of_lt hmk)).symm
    (Equiv.arrowCongr (intervalJointRemainingSiteEquiv j m k hjm hmk) (Equiv.refl (Fin d)))

/-- The joined initialized physical configuration restricts to the left initialized input.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem intervalPhysicalZeroConfig_join_left {d D N j m k : ℕ} [NeZero d]
    (hmk : m ≤ k) (x : CutIntervalConfig d N j m) (y : CutIntervalConfig d N m k)
    (s : LogicalSite d D N) (hs : s ∈ intervalLogicalSupport d D N j m) :
    intervalPhysicalZeroConfig (D := D) j k (joinCutInterval j m k x y) s =
      intervalPhysicalZeroConfig (D := D) j m x s := by
  rcases s with s | s
  · change j ≤ s.val ∧ s.val < m at hs
    simp [intervalPhysicalZeroConfig, joinCutInterval, hs, hs.2.trans_le hmk]
  · rfl

/-- The joined initialized physical configuration restricts to the right initialized input.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem intervalPhysicalZeroConfig_join_right {d D N j m k : ℕ} [NeZero d]
    (hjm : j ≤ m) (x : CutIntervalConfig d N j m) (y : CutIntervalConfig d N m k)
    (s : LogicalSite d D N) (hs : s ∈ intervalLogicalSupport d D N m k) :
    intervalPhysicalZeroConfig (D := D) j k (joinCutInterval j m k x y) s =
      intervalPhysicalZeroConfig (D := D) m k y s := by
  rcases s with s | s
  · change m ≤ s.val ∧ s.val < k at hs
    simp [intervalPhysicalZeroConfig, joinCutInterval, hs, hjm.trans hs.1,
      Nat.not_lt_of_ge hs.1]
  · rfl

/-- An initialized physical configuration is zero on every joining flag.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem intervalPhysicalZeroConfig_joiningFlag_zero {d D N j k m : ℕ} [NeZero d]
    (x : CutIntervalConfig d N j k) (s : LogicalSite d D N)
    (hs : s ∈ joiningFlagSupport d D N m) :
    intervalPhysicalZeroConfig (D := D) j k x s = 0 := by
  rcases s with s | (s | s)
  · exact hs.elim
  · exact hs.elim
  · rfl

/-- The two initialized child inputs with both joining flags initialized, retaining every
remaining outside coordinate.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
noncomputable def intervalJointInputEmbedding {d D N : ℕ} [NeZero d]
    (j m k : Fin (N + 1)) (hjm : j.val < m.val) (hmk : m.val < k.val) :
    ((CutIntervalConfig d N j.val m.val × CutIntervalConfig d N m.val k.val) ×
      ({s : {s : Fin (logicalSiteCount d D N) // s ∉ Set.range (Fin.Embedding.append
        (intervalPacketSites_disjoint (d := d) (D := D) (N := N) hjm hmk))} //
        s ∉ intervalJointOutsideFlagSet (d := d) (D := D) j m k hjm hmk} → Fin d)) ↪
    Cfg d (logicalSiteCount d D N) :=
  jointPlacedBasisEmbedding (intervalPacketSites d D N j.val m.val)
    (intervalPacketSites d D N m.val k.val)
    (intervalPacketSites_disjoint (d := d) (D := D) (N := N) hjm hmk)
    (intervalInputEmbedding j.val m.val) (intervalInputEmbedding m.val k.val)
    (intervalJointInitializedOutsideEmbedding (d := d) (D := D) j m k hjm hmk)

/-- Restriction to the interval packet determines the value at every site of its support.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem intervalPacket_restriction_apply {d D N j k : ℕ}
    (x : Cfg d (logicalSiteCount d D N)) (y : LogicalSite d D N → Fin d)
    (h : x ∘ intervalPacketSites d D N j k = y ∘ intervalPacketLogicalSite d D N j k)
    (s : LogicalSite d D N) (hs : s ∈ intervalLogicalSupport d D N j k) :
    x (logicalSiteEquivFin d D N s) = y s := by
  obtain ⟨i, hi⟩ := intervalPacketLogicalSite_surjective s hs
  have hh := congrFun h i
  change x (logicalSiteEquivFin d D N (intervalPacketLogicalSite d D N j k i)) =
    y (intervalPacketLogicalSite d D N j k i) at hh
  simpa only [hi] using hh

/-- On each parent outside site, initializing the joining flags retains the corresponding
remaining configuration coordinate.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem intervalJointInitializedOutsideEmbedding_parentOutside {d D N : ℕ} [NeZero d]
    (j m k : Fin (N + 1)) (hjm : j.val < m.val) (hmk : m.val < k.val)
    (p : {s : {s : Fin (logicalSiteCount d D N) // s ∉ Set.range (Fin.Embedding.append
      (intervalPacketSites_disjoint (d := d) (D := D) (N := N) hjm hmk))} //
      s ∉ intervalJointOutsideFlagSet (d := d) (D := D) j m k hjm hmk} → Fin d)
    (s : {s : Fin (logicalSiteCount d D N) //
      s ∉ Set.range (intervalPacketSites d D N j.val k.val)}) :
    intervalJointInitializedOutsideEmbedding (d := d) (D := D) j m k hjm hmk p
      ⟨s.val, ((not_mem_parentPacket_iff j m k hjm hmk s.val).mp s.property).1⟩ =
    Equiv.arrowCongr (intervalJointRemainingSiteEquiv j m k hjm hmk) (Equiv.refl (Fin d)) p s := by
  classical
  change (if h : _ then p ⟨_, h⟩ else 0) = _
  have hs : (⟨s.val, ((not_mem_parentPacket_iff j m k hjm hmk s.val).mp s.property).1⟩ :
      {s : Fin (logicalSiteCount d D N) // s ∉ Set.range (Fin.Embedding.append
        (intervalPacketSites_disjoint (d := d) (D := D) (N := N) hjm hmk))}) ∉
      intervalJointOutsideFlagSet (d := d) (D := D) j m k hjm hmk :=
    ((not_mem_parentPacket_iff j m k hjm hmk s.val).mp s.property).2
  rw [dite_eq_left hs]
  rfl

/-- The actual jointly initialized child input is the parent initialized input in the joined
physical and outside coordinates.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem intervalJointInputEmbedding_eq_parent_input {d D N : ℕ} [NeZero d]
    (j m k : Fin (N + 1)) (hjm : j.val < m.val) (hmk : m.val < k.val)
    (p : ((CutIntervalConfig d N j.val m.val × CutIntervalConfig d N m.val k.val) ×
      ({s : {s : Fin (logicalSiteCount d D N) // s ∉ Set.range (Fin.Embedding.append
        (intervalPacketSites_disjoint (d := d) (D := D) (N := N) hjm hmk))} //
        s ∉ intervalJointOutsideFlagSet (d := d) (D := D) j m k hjm hmk} → Fin d))) :
    intervalJointInputEmbedding (d := d) (D := D) j m k hjm hmk p =
      minimalIntervalInputEmbedding (D := D) j.val k.val
        (intervalJointInputConfigEquiv j m k hjm hmk p) := by
  apply (placedConfigEquiv d (intervalPacketSites d D N j.val k.val)).injective
  change (placedConfigEquiv d (intervalPacketSites d D N j.val k.val))
      (intervalJointInputEmbedding j m k hjm hmk p) =
    (placedConfigEquiv d (intervalPacketSites d D N j.val k.val))
      ((placedConfigEquiv d (intervalPacketSites d D N j.val k.val)).symm
        (intervalInputEmbedding j.val k.val (joinCutInterval j.val m.val k.val p.1.1 p.1.2),
          Equiv.arrowCongr (intervalJointRemainingSiteEquiv j m k hjm hmk)
            (Equiv.refl (Fin d)) p.2))
  rw [Equiv.apply_symm_apply]
  apply Prod.ext
  · rw [placedConfigEquiv_fst]
    funext i
    let s := intervalPacketLogicalSite d D N j.val k.val i
    change intervalJointInputEmbedding j m k hjm hmk p (logicalSiteEquivFin d D N s) =
      intervalPhysicalZeroConfig j.val k.val (joinCutInterval j.val m.val k.val p.1.1 p.1.2) s
    have hs := intervalPacketLogicalSite_mem d D N j.val k.val i
    rw [intervalLogicalSupport_split hjm hmk] at hs
    rcases hs with (hl | hr) | hf
    · have hh := intervalPacket_restriction_apply
        (intervalJointInputEmbedding j m k hjm hmk p)
        (intervalPhysicalZeroConfig (D := D) j.val m.val p.1.1)
        (jointPlacedBasisEmbedding_left
          (intervalPacketSites d D N j.val m.val) (intervalPacketSites d D N m.val k.val)
          (intervalPacketSites_disjoint (d := d) (D := D) (N := N) hjm hmk)
          (intervalInputEmbedding j.val m.val) (intervalInputEmbedding m.val k.val)
          (intervalJointInitializedOutsideEmbedding (d := d) (D := D) j m k hjm hmk) p) s hl
      exact hh.trans (intervalPhysicalZeroConfig_join_left (Nat.le_of_lt hmk)
        p.1.1 p.1.2 s hl).symm
    · have hh := intervalPacket_restriction_apply
        (intervalJointInputEmbedding j m k hjm hmk p)
        (intervalPhysicalZeroConfig (D := D) m.val k.val p.1.2)
        (jointPlacedBasisEmbedding_right
          (intervalPacketSites d D N j.val m.val) (intervalPacketSites d D N m.val k.val)
          (intervalPacketSites_disjoint (d := d) (D := D) (N := N) hjm hmk)
          (intervalInputEmbedding j.val m.val) (intervalInputEmbedding m.val k.val)
          (intervalJointInitializedOutsideEmbedding (d := d) (D := D) j m k hjm hmk) p) s hr
      exact hh.trans (intervalPhysicalZeroConfig_join_right (Nat.le_of_lt hjm)
        p.1.1 p.1.2 s hr).symm
    · let t : {t : Fin (logicalSiteCount d D N) // t ∉ Set.range (Fin.Embedding.append
          (intervalPacketSites_disjoint (d := d) (D := D) (N := N) hjm hmk))} :=
        ⟨logicalSiteEquivFin d D N s, joiningFlag_outside_childPackets j m k hjm hmk s hf⟩
      have hh := congrFun (jointPlacedBasisEmbedding_outside
        (intervalPacketSites d D N j.val m.val) (intervalPacketSites d D N m.val k.val)
        (intervalPacketSites_disjoint (d := d) (D := D) (N := N) hjm hmk)
        (intervalInputEmbedding j.val m.val) (intervalInputEmbedding m.val k.val)
        (intervalJointInitializedOutsideEmbedding (d := d) (D := D) j m k hjm hmk) p) t
      have ht : t ∈ intervalJointOutsideFlagSet (d := d) (D := D) j m k hjm hmk := by
        change (logicalSiteEquivFin d D N).symm (logicalSiteEquivFin d D N s) ∈
          joiningFlagSupport d D N m.val
        simpa only [Equiv.symm_apply_apply] using hf
      exact (hh.trans (initializedComplementEmbedding_zero
        (intervalJointOutsideFlagSet (d := d) (D := D) j m k hjm hmk) p.2 t ht)).trans
          (intervalPhysicalZeroConfig_joiningFlag_zero
            (joinCutInterval j.val m.val k.val p.1.1 p.1.2) s hf).symm
  · rw [placedConfigEquiv_snd]
    funext s
    have hh := congrFun (jointPlacedBasisEmbedding_outside
      (intervalPacketSites d D N j.val m.val) (intervalPacketSites d D N m.val k.val)
      (intervalPacketSites_disjoint (d := d) (D := D) (N := N) hjm hmk)
      (intervalInputEmbedding j.val m.val) (intervalInputEmbedding m.val k.val)
      (intervalJointInitializedOutsideEmbedding (d := d) (D := D) j m k hjm hmk) p)
      ⟨s.val, ((not_mem_parentPacket_iff j m k hjm hmk s.val).mp s.property).1⟩
    exact hh.trans (intervalJointInitializedOutsideEmbedding_parentOutside j m k hjm hmk p.2 s)

/-- A placed basis inclusion restricts to its prescribed placed configuration.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem placedBasisEmbedding_restriction {d a n : ℕ} {α τ : Type*}
    (e : Fin a ↪ Fin n) (g : α ↪ Cfg d a) (t : τ ↪ OutsidePlacedConfig d e)
    (p : α × τ) : placedBasisEmbedding e g t p ∘ e = g p.1 := by
  rw [← placedConfigEquiv_fst d e]
  change ((placedConfigEquiv d e)
    ((placedConfigEquiv d e).symm (g p.1, t p.2))).1 = _
  rw [Equiv.apply_symm_apply]

/-- Every auxiliary of an interval input, including both available boundary bonds, is zero.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem minimalIntervalInputEmbedding_zero_auxiliary {d D N j k : ℕ} [NeZero d]
    (p : CutIntervalConfig d N j k ×
      OutsidePlacedConfig d (intervalPacketSites d D N j k))
    (s : LogicalSite d D N) (hs : s ∈ intervalAuxiliaryInitializationSupport d D N j k) :
    minimalIntervalInputEmbedding (D := D) j k p (logicalSiteEquivFin d D N s) = 0 := by
  obtain ⟨hs, a, rfl⟩ := hs
  exact intervalPacket_restriction_apply (minimalIntervalInputEmbedding (D := D) j k p)
    (intervalPhysicalZeroConfig (D := D) j k p.1)
    (placedBasisEmbedding_restriction (intervalPacketSites d D N j k)
      (intervalInputEmbedding j k) (Function.Embedding.refl _) p)
    (auxiliarySiteEmbedding d D N a) hs

/-- The interval input range consists exactly of configurations whose interval auxiliaries are
zero. Every other logical site is unrestricted.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem mem_range_minimalIntervalInputEmbedding_iff {d D N : ℕ} [NeZero d]
    (j k : ℕ) (x : Cfg d (logicalSiteCount d D N)) :
    x ∈ Set.range (minimalIntervalInputEmbedding (d := d) (D := D) (N := N) j k) ↔
      ∀ s ∈ intervalAuxiliaryInitializationSupport d D N j k,
        x (logicalSiteEquivFin d D N s) = 0 := by
  constructor
  · rintro ⟨p, rfl⟩ s hs
    exact minimalIntervalInputEmbedding_zero_auxiliary p s hs
  · intro hx
    let w : CutIntervalConfig d N j k := fun s ↦
      x (logicalSiteEquivFin d D N (Sum.inl s.val))
    let z : OutsidePlacedConfig d (intervalPacketSites d D N j k) := fun s ↦ x s.val
    refine ⟨(w, z), ?_⟩
    apply (placedConfigEquiv d (intervalPacketSites d D N j k)).injective
    change (placedConfigEquiv d (intervalPacketSites d D N j k))
        ((placedConfigEquiv d (intervalPacketSites d D N j k)).symm
          (intervalInputEmbedding j k w, z)) = _
    rw [Equiv.apply_symm_apply]
    apply Prod.ext
    · rw [placedConfigEquiv_fst]
      funext i
      let s := intervalPacketLogicalSite d D N j k i
      have hs : s ∈ intervalLogicalSupport d D N j k := intervalPacketLogicalSite_mem d D N j k i
      change intervalPhysicalZeroConfig j k w s = x (logicalSiteEquivFin d D N s)
      rcases s with t | a
      · change j ≤ t.val ∧ t.val < k at hs
        change (if h : j ≤ t.val ∧ t.val < k then
          x (logicalSiteEquivFin d D N (Sum.inl t)) else 0) = _
        exact dite_eq_left hs
      · exact (hx (Sum.inr a) ⟨hs, ⟨a, rfl⟩⟩).symm
    · rw [placedConfigEquiv_snd]

/-- The canonical initialized interval input and the concrete zero-flag inclusion have the same
range. This identifies the actual selected input subspace.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem range_minimalIntervalInputEmbedding_eq_zeroFlagEmbedding {d D N : ℕ} [NeZero d]
    (j k : ℕ) :
    Set.range (minimalIntervalInputEmbedding (d := d) (D := D) (N := N) j k) =
      Set.range (zeroFlagEmbedding (d := d)
        (logicalSupportSites (intervalAuxiliaryInitializationSupport d D N j k))) := by
  ext x
  rw [mem_range_minimalIntervalInputEmbedding_iff, mem_range_zeroFlagEmbedding_iff,
    logicalSupportSites_initialized_iff]

/-- The joint child input covers precisely the parent initialized input range.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem range_intervalJointInputEmbedding_eq_parent {d D N : ℕ} [NeZero d]
    (j m k : Fin (N + 1)) (hjm : j.val < m.val) (hmk : m.val < k.val) :
    Set.range (intervalJointInputEmbedding (d := d) (D := D) j m k hjm hmk) =
      Set.range (minimalIntervalInputEmbedding (d := d) (D := D) (N := N) j.val k.val) := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨intervalJointInputConfigEquiv j m k hjm hmk p,
      (intervalJointInputEmbedding_eq_parent_input j m k hjm hmk p).symm⟩
  · rintro ⟨p, rfl⟩
    refine ⟨(intervalJointInputConfigEquiv j m k hjm hmk).symm p, ?_⟩
    simpa only [Equiv.apply_symm_apply] using intervalJointInputEmbedding_eq_parent_input
      j m k hjm hmk ((intervalJointInputConfigEquiv j m k hjm hmk).symm p)

/-- The actual joint input is exactly the subspace tested by the derived zero-flag reflection.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem range_intervalJointInputEmbedding_eq_zeroFlagEmbedding {d D N : ℕ} [NeZero d]
    (j m k : Fin (N + 1)) (hjm : j.val < m.val) (hmk : m.val < k.val) :
    Set.range (intervalJointInputEmbedding (d := d) (D := D) j m k hjm hmk) =
      Set.range (zeroFlagEmbedding (d := d)
        (logicalSupportSites (intervalAuxiliaryInitializationSupport d D N j.val k.val))) := by
  rw [range_intervalJointInputEmbedding_eq_parent,
    range_minimalIntervalInputEmbedding_eq_zeroFlagEmbedding]

open scoped Classical in
/-- The two supported child identities determine their actual joint columns with both joining
flags initialized and every remaining outside configuration retained.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem minimalIntervalJointInitializedChildColumns_of_supported_individual {d D N : ℕ} [NeZero d]
    (hd : 2 ≤ d) (U : Matrix (Cfg d N) (Cfg d N) ℂ)
    (hU : U ∈ unitaryGroup (Cfg d N) ℂ)
    (hbound : ∀ j : Fin (N + 1), cutRank (operatorCoefficientTensor U) j.val ≤ D)
    (B : ∀ k, Module.Basis (Fin (cutRank (operatorCoefficientTensor U) k))
      ℂ (cutColumnSpace (operatorCoefficientTensor U) k))
    (P : ∀ j : Fin (N + 1), Matrix (Fin (cutRank (operatorCoefficientTensor U) j.val))
      (Fin (cutRank (operatorCoefficientTensor U) j.val)) ℂ)
    (j m k : Fin (N + 1)) (hjm : j.val < m.val) (hmk : m.val < k.val)
    (X Y : Matrix (Cfg d (logicalSiteCount d D N)) (Cfg d (logicalSiteCount d D N)) ℂ)
    (hSX : X ∈ supportedOperators d (intervalConsecutiveSupport d D N j.val m.val))
    (hSY : Y ∈ supportedOperators d (intervalConsecutiveSupport d D N m.val k.val))
    (hX : IsMinimalIntervalColumnImplementation hd U hU hbound B P j m (Nat.le_of_lt hjm) X)
    (hY : IsMinimalIntervalColumnImplementation hd U hU hbound B P m k (Nat.le_of_lt hmk) Y) :
    (X * Y) * initializedBasisMatrix
      (jointPlacedBasisEmbedding (intervalPacketSites d D N j.val m.val)
        (intervalPacketSites d D N m.val k.val)
          (intervalPacketSites_disjoint (d := d) (D := D) (N := N) hjm hmk)
        (intervalInputEmbedding j.val m.val) (intervalInputEmbedding m.val k.val)
        (intervalJointInitializedOutsideEmbedding (d := d) (D := D) j m k hjm hmk)) =
      initializedBasisMatrix
        (jointPlacedBasisEmbedding (intervalPacketSites d D N j.val m.val)
          (intervalPacketSites d D N m.val k.val)
          (intervalPacketSites_disjoint (d := d) (D := D) (N := N) hjm hmk)
          (intervalOutputEmbedding j m (minimalCutBondRegisterEncoding hd U hU hbound m)
            (minimalCutBondRegisterEncoding hd U hU hbound j))
          (intervalOutputEmbedding m k (minimalCutBondRegisterEncoding hd U hU hbound k)
            (minimalCutBondRegisterEncoding hd U hU hbound m))
          (intervalJointInitializedOutsideEmbedding (d := d) (D := D) j m k hjm hmk)) *
        ((vectorizedWeightedInterval (minimalOperatorInterval U B (Nat.le_of_lt hjm))
          (CFC.sqrt (P j)) (CFC.sqrt (dualGramMetric (P m))) ⊗ₖ
          vectorizedWeightedInterval (minimalOperatorInterval U B (Nat.le_of_lt hmk))
            (CFC.sqrt (P m)) (CFC.sqrt (dualGramMetric (P k)))) ⊗ₖ 1) := by
  unfold IsMinimalIntervalColumnImplementation minimalIntervalInputEmbedding
    minimalIntervalOutputEmbedding at hX hY
  convert jointPlacedColumns_of_supported_individual
    (α := CutIntervalConfig d N j.val m.val)
    (β := CutIntervalConfig d N m.val k.val)
    (γ := CutIntervalConfig d N j.val m.val ×
      (Fin (cutRank (operatorCoefficientTensor U) m.val) ×
        Fin (cutRank (operatorCoefficientTensor U) j.val)))
    (δ := CutIntervalConfig d N m.val k.val ×
      (Fin (cutRank (operatorCoefficientTensor U) k.val) ×
        Fin (cutRank (operatorCoefficientTensor U) m.val)))
    (τ := {s : {s : Fin (logicalSiteCount d D N) // s ∉ Set.range (Fin.Embedding.append
      (intervalPacketSites_disjoint (d := d) (D := D) (N := N) hjm hmk))} //
      s ∉ intervalJointOutsideFlagSet (d := d) (D := D) j m k hjm hmk} → Fin d)
    (intervalPacketSites d D N j.val m.val) (intervalPacketSites d D N m.val k.val)
    (intervalPacketSites_disjoint (d := d) (D := D) (N := N) hjm hmk)
    (intervalInputEmbedding j.val m.val) (intervalInputEmbedding m.val k.val)
    (intervalOutputEmbedding j m (minimalCutBondRegisterEncoding hd U hU hbound m)
      (minimalCutBondRegisterEncoding hd U hU hbound j))
    (intervalOutputEmbedding m k (minimalCutBondRegisterEncoding hd U hU hbound k)
      (minimalCutBondRegisterEncoding hd U hU hbound m))
    (intervalJointInitializedOutsideEmbedding (d := d) (D := D) j m k hjm hmk) X Y
    (vectorizedWeightedInterval (minimalOperatorInterval U B (Nat.le_of_lt hjm))
      (CFC.sqrt (P j)) (CFC.sqrt (dualGramMetric (P m))))
    (vectorizedWeightedInterval (minimalOperatorInterval U B (Nat.le_of_lt hmk))
      (CFC.sqrt (P m)) (CFC.sqrt (dualGramMetric (P k))))
    (by rwa [intervalPacketSites_range]) (by rwa [intervalPacketSites_range]) hX hY using 1
  all_goals congr!


end MPUCircuit
