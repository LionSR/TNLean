/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.RegisterLayout
import Mathlib.Tactic.FinCases
import TNLean.MPS.Preparation.SiteEmbedding

/-!
# Logical supports of the recursive interval construction

The two child intervals use disjoint physical and bond registers. The joining
flags complete their union to the parent support. Endpoint bond registers
have width zero, so the actual leaf placement uses one physical site and
only its available boundary bonds.

The interior-initialization predicate records the exact auxiliary condition
needed by the merger: initialized child interiors and initialized joining
auxiliaries give an initialized parent interior.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5.
-/

namespace MPUCircuit

/-- The logical sites of an interval: its physical sites, all strictly interior auxiliaries, the
left boundary bond on side one, and the right boundary bond on side zero.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
def intervalLogicalSupport (d D N j k : ℕ) : Set (LogicalSite d D N)
  | Sum.inl s => j ≤ s.val ∧ s.val < k
  | Sum.inr (Sum.inl (c, side, _)) =>
      (j < (internalCutEmbedding N c).val ∧ (internalCutEmbedding N c).val < k) ∨
        ((internalCutEmbedding N c).val = j ∧ side = 1) ∨
        ((internalCutEmbedding N c).val = k ∧ side = 0)
  | Sum.inr (Sum.inr (c, _)) =>
      j < (internalCutEmbedding N c).val ∧ (internalCutEmbedding N c).val < k

/-- The two amplification flags at the joining cut.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
def joiningFlagSupport (d D N m : ℕ) : Set (LogicalSite d D N)
  | Sum.inr (Sum.inr (c, _)) => (internalCutEmbedding N c).val = m
  | _ => False

/-- The logical supports of two adjacent nonempty child intervals are disjoint.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem intervalLogicalSupport_disjoint {d D N j m k : ℕ} (hjm : j < m) (hmk : m < k) :
    Disjoint (intervalLogicalSupport d D N j m) (intervalLogicalSupport d D N m k) := by
  rw [Set.disjoint_left]
  intro s hs ht
  rcases s with s | (⟨c, side, q⟩ | ⟨c, flag⟩)
  · change j ≤ s.val ∧ s.val < m at hs
    change m ≤ s.val ∧ s.val < k at ht
    omega
  · change (_ ∧ _) ∨ (_ ∧ side = 1) ∨ (_ ∧ side = 0) at hs ht
    fin_cases side <;> norm_num at hs ht <;> omega
  · change j < (internalCutEmbedding N c).val ∧ (internalCutEmbedding N c).val < m at hs
    change m < (internalCutEmbedding N c).val ∧ (internalCutEmbedding N c).val < k at ht
    omega

/-- The joining flags are disjoint from the left child support.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem joiningFlagSupport_disjoint_left {d D N j m : ℕ} :
    Disjoint (joiningFlagSupport d D N m) (intervalLogicalSupport d D N j m) := by
  rw [Set.disjoint_left]
  intro s hs ht
  rcases s with s | (bond | ⟨c, flag⟩)
  · exact hs
  · exact hs
  · change (internalCutEmbedding N c).val = m at hs
    change j < (internalCutEmbedding N c).val ∧ (internalCutEmbedding N c).val < m at ht
    omega

/-- The joining flags are disjoint from the right child support.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem joiningFlagSupport_disjoint_right {d D N m k : ℕ} :
    Disjoint (joiningFlagSupport d D N m) (intervalLogicalSupport d D N m k) := by
  rw [Set.disjoint_left]
  intro s hs ht
  rcases s with s | (bond | ⟨c, flag⟩)
  · exact hs
  · exact hs
  · change (internalCutEmbedding N c).val = m at hs
    change m < (internalCutEmbedding N c).val ∧ (internalCutEmbedding N c).val < k at ht
    omega

/-- The parent support is the union of the two child supports and the joining flags.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem intervalLogicalSupport_split {d D N j m k : ℕ} (hjm : j < m) (hmk : m < k) :
    intervalLogicalSupport d D N j k =
      intervalLogicalSupport d D N j m ∪ intervalLogicalSupport d D N m k ∪
        joiningFlagSupport d D N m := by
  ext s
  rcases s with s | (⟨c, side, q⟩ | ⟨c, flag⟩)
  · change (j ≤ s.val ∧ s.val < k) ↔
      ((j ≤ s.val ∧ s.val < m) ∨ (m ≤ s.val ∧ s.val < k)) ∨ False
    constructor
    · intro hs
      by_cases hsm : s.val < m
      · exact Or.inl (Or.inl ⟨hs.1, hsm⟩)
      · exact Or.inl (Or.inr ⟨by omega, hs.2⟩)
    · rintro (hs | hs)
      · rcases hs with hs | hs <;> constructor <;> omega
      · exact hs.elim
  · change ((_ ∧ _) ∨ (_ ∧ side = 1) ∨ (_ ∧ side = 0)) ↔
      (((_ ∧ _) ∨ (_ ∧ side = 1) ∨ (_ ∧ side = 0)) ∨
      ((_ ∧ _) ∨ (_ ∧ side = 1) ∨ (_ ∧ side = 0))) ∨ False
    fin_cases side <;> norm_num <;> omega
  · change (j < (internalCutEmbedding N c).val ∧ (internalCutEmbedding N c).val < k) ↔
      ((j < (internalCutEmbedding N c).val ∧ (internalCutEmbedding N c).val < m) ∨
      (m < (internalCutEmbedding N c).val ∧ (internalCutEmbedding N c).val < k)) ∨
      (internalCutEmbedding N c).val = m
    omega


/-- The bond register width at a cut. Endpoint cuts have width zero; internal cuts have the common
bond register width.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
def cutBondRegisterWidth (d D N : ℕ) (j : Fin (N + 1)) : ℕ :=
  if j.val = 0 ∨ j.val = N then 0 else bondRegisterWidth d D

/-- Every boundary bond width is at most the common bond register width.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem cutBondRegisterWidth_le (d D N : ℕ) (j : Fin (N + 1)) :
    cutBondRegisterWidth d D N j ≤ bondRegisterWidth d D := by
  simp only [cutBondRegisterWidth]
  split_ifs <;> omega

/-- A coordinate of a nonempty cut bond register necessarily belongs to an internal cut.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem cutBondRegisterWidth_internal {d D N : ℕ} {j : Fin (N + 1)}
    (q : Fin (cutBondRegisterWidth d D N j)) : 0 < j.val ∧ j.val < N := by
  have hq := q.isLt
  unfold cutBondRegisterWidth at hq
  split_ifs at hq <;> omega

/-- Placement of a boundary bond register in the logical register. Its two sides retain distinct
physical sites.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
def cutBondSiteEmbedding (d D N : ℕ) (j : Fin (N + 1)) (side : Fin 2) :
    Fin (cutBondRegisterWidth d D N j) ↪ LogicalSite d D N where
  toFun q := bondSiteEmbedding d D N
    (⟨j.val - 1, by have := cutBondRegisterWidth_internal q; omega⟩, side,
      Fin.castLE (cutBondRegisterWidth_le d D N j) q)
  inj' q r h := by
    have hh := (bondSiteEmbedding d D N).injective h
    exact Fin.ext (congrArg (fun z : BondRegisterSite d D N ↦ z.2.2.val) hh)

/-- Boundary bond registers on distinct sides are disjoint, even at the same cut.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem cutBondSiteEmbedding_disjoint {d D N : ℕ} (j k : Fin (N + 1))
    {side side' : Fin 2} (hside : side ≠ side') :
    Disjoint (Set.range (cutBondSiteEmbedding d D N j side))
      (Set.range (cutBondSiteEmbedding d D N k side')) := by
  rw [Set.disjoint_left]
  rintro s ⟨q, rfl⟩ ⟨r, h⟩
  apply hside
  have hh := (bondSiteEmbedding d D N).injective h
  exact (congrArg (fun z : BondRegisterSite d D N ↦ z.2.1) hh).symm

/-- The side-one register at the left boundary belongs to the interval support.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem cutBondSiteEmbedding_mem_left {d D N : ℕ} (j k : Fin (N + 1))
    (q : Fin (cutBondRegisterWidth d D N j)) :
    cutBondSiteEmbedding d D N j 1 q ∈ intervalLogicalSupport d D N j.val k.val := by
  change (_ ∧ _) ∨ ((j.val - 1 + 1 = j.val) ∧ (1 : Fin 2) = 1) ∨ (_ ∧ _)
  have hj := cutBondRegisterWidth_internal q
  exact Or.inr (Or.inl ⟨by omega, rfl⟩)

/-- The side-zero register at the right boundary belongs to the interval support.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem cutBondSiteEmbedding_mem_right {d D N : ℕ} (j k : Fin (N + 1))
    (q : Fin (cutBondRegisterWidth d D N k)) :
    cutBondSiteEmbedding d D N k 0 q ∈ intervalLogicalSupport d D N j.val k.val := by
  change (_ ∧ _) ∨ (_ ∧ _) ∨ ((k.val - 1 + 1 = k.val) ∧ (0 : Fin 2) = 0)
  have hk := cutBondRegisterWidth_internal q
  exact Or.inr (Or.inr ⟨by omega, rfl⟩)


/-- The leaf sites consist of one physical site, its right boundary bond, and its left boundary
bond.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
abbrev LeafLogicalSite (d D N : ℕ) (i : Fin N) :=
  Fin 1 ⊕ (Fin (cutBondRegisterWidth d D N i.succ) ⊕
    Fin (cutBondRegisterWidth d D N i.castSucc))

/-- Placement of the leaf physical site and its two available boundary bond registers. No register
outside the interval is used.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
def leafLogicalSiteEmbedding (d D N : ℕ) (i : Fin N) :
    LeafLogicalSite d D N i ↪ LogicalSite d D N where
  toFun s := match s with
    | Sum.inl _ => physicalSiteEmbedding d D N i
    | Sum.inr (Sum.inl q) => cutBondSiteEmbedding d D N i.succ 0 q
    | Sum.inr (Sum.inr q) => cutBondSiteEmbedding d D N i.castSucc 1 q
  inj' := by
    rintro (a | (a | a)) (b | (b | b)) h
    · exact congrArg Sum.inl (Subsingleton.elim a b)
    · cases h
    · cases h
    · cases h
    · exact congrArg (fun x ↦ Sum.inr (Sum.inl x))
        ((cutBondSiteEmbedding d D N i.succ 0).injective h)
    · exfalso
      exact Set.disjoint_left.mp (cutBondSiteEmbedding_disjoint i.succ i.castSucc
        (by decide : (0 : Fin 2) ≠ 1)) ⟨a, h⟩ ⟨b, rfl⟩
    · cases h
    · exfalso
      exact Set.disjoint_left.mp (cutBondSiteEmbedding_disjoint i.succ i.castSucc
        (by decide : (0 : Fin 2) ≠ 1)) ⟨b, rfl⟩ ⟨a, h⟩
    · exact congrArg (fun x ↦ Sum.inr (Sum.inr x))
        ((cutBondSiteEmbedding d D N i.castSucc 1).injective h)

/-- Consecutive indexing of the actual leaf sites, with separate right and left bond widths.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
def leafPacketSites (d D N : ℕ) (i : Fin N) :
    Fin (1 + (cutBondRegisterWidth d D N i.succ + cutBondRegisterWidth d D N i.castSucc)) ↪
      LogicalSite d D N :=
  ((Equiv.sumCongr (Equiv.refl (Fin 1)) finSumFinEquiv).trans finSumFinEquiv).symm.toEmbedding.trans
    (leafLogicalSiteEmbedding d D N i)

/-- Every leaf site belongs to the logical support of that one-site interval.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem leafLogicalSiteEmbedding_mem {d D N : ℕ} (i : Fin N) (s : LeafLogicalSite d D N i) :
    leafLogicalSiteEmbedding d D N i s ∈ intervalLogicalSupport d D N i.val (i.val + 1) := by
  rcases s with a | (q | q)
  · change i.val ≤ i.val ∧ i.val < i.val + 1
    omega
  · exact cutBondSiteEmbedding_mem_right i.castSucc i.succ q
  · exact cutBondSiteEmbedding_mem_left i.castSucc i.succ q

/-- Every consecutively indexed leaf site belongs to the leaf interval support.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem leafPacketSites_mem {d D N : ℕ} (i : Fin N)
    (s : Fin (1 + (cutBondRegisterWidth d D N i.succ + cutBondRegisterWidth d D N i.castSucc))) :
    leafPacketSites d D N i s ∈ intervalLogicalSupport d D N i.val (i.val + 1) :=
  leafLogicalSiteEmbedding_mem i _

/-- The interval support in the consecutive numbering of the logical register.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
noncomputable def intervalConsecutiveSupport (d D N j k : ℕ) :
    Set (Fin (logicalSiteCount d D N)) :=
  logicalSiteEquivFin d D N '' intervalLogicalSupport d D N j k

/-- Adjacent nonempty intervals have disjoint supports in the consecutive logical numbering.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem intervalConsecutiveSupport_disjoint {d D N j m k : ℕ}
    (hjm : j < m) (hmk : m < k) :
    Disjoint (intervalConsecutiveSupport d D N j m) (intervalConsecutiveSupport d D N m k) :=
  Set.disjoint_image_of_injective (logicalSiteEquivFin d D N).injective
    (intervalLogicalSupport_disjoint hjm hmk)

/-- Operators supported on the two child intervals commute.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem interval_supportedOperators_commute {d D N j m k : ℕ}
    (hjm : j < m) (hmk : m < k)
    {X Y : Matrix (MPSTensor.Cfg d (logicalSiteCount d D N))
      (MPSTensor.Cfg d (logicalSiteCount d D N)) ℂ}
    (hX : X ∈ MPSPreparation.supportedOperators d (intervalConsecutiveSupport d D N j m))
    (hY : Y ∈ MPSPreparation.supportedOperators d (intervalConsecutiveSupport d D N m k)) :
    Commute X Y :=
  MPSPreparation.commute_of_mem_supportedOperators
    (intervalConsecutiveSupport_disjoint hjm hmk) hX hY


/-- A bond site is in a boundary register exactly when its cut and side have the prescribed
values.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem cutBondSiteEmbedding_range_iff {d D N : ℕ} (j : Fin (N + 1)) (side : Fin 2)
    (c : Fin (N - 1)) (side' : Fin 2) (q : Fin (bondRegisterWidth d D)) :
    bondSiteEmbedding d D N (c, side', q) ∈ Set.range (cutBondSiteEmbedding d D N j side) ↔
      (internalCutEmbedding N c).val = j.val ∧ side' = side := by
  constructor
  · rintro ⟨a, ha⟩
    have h := (bondSiteEmbedding d D N).injective ha
    have hc := congrArg (fun z : BondRegisterSite d D N ↦ z.1.val) h
    have hs := congrArg (fun z : BondRegisterSite d D N ↦ z.2.1) h
    have hj := cutBondRegisterWidth_internal a
    constructor
    · change c.val + 1 = j.val
      change j.val - 1 = c.val at hc
      omega
    · exact hs.symm
  · rintro ⟨hc, rfl⟩
    have hj := internalCutEmbedding_bounds N c
    rw [hc] at hj
    have hne : ¬(j.val = 0 ∨ j.val = N) := by omega
    let a : Fin (cutBondRegisterWidth d D N j) :=
      ⟨q.val, by simpa only [cutBondRegisterWidth, ite_eq_right hne] using q.isLt⟩
    refine ⟨a, ?_⟩
    apply congrArg (bondSiteEmbedding d D N)
    apply Prod.ext
    · apply Fin.ext
      change j.val - 1 = c.val
      change c.val + 1 = j.val at hc
      omega
    · rfl

/-- The placed leaf sites are precisely the sites of its interval support.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem leafLogicalSiteEmbedding_range {d D N : ℕ} (i : Fin N) :
    Set.range (leafLogicalSiteEmbedding d D N i) =
      intervalLogicalSupport d D N i.val (i.val + 1) := by
  ext s
  constructor
  · rintro ⟨a, rfl⟩
    exact leafLogicalSiteEmbedding_mem i a
  · intro hs
    rcases s with s | (⟨c, side, q⟩ | ⟨c, flag⟩)
    · change i.val ≤ s.val ∧ s.val < i.val + 1 at hs
      have hsi : s = i := Fin.ext (by omega)
      subst s
      exact ⟨Sum.inl 0, rfl⟩
    · change (_ ∧ _) ∨ (_ ∧ side = 1) ∨ (_ ∧ side = 0) at hs
      rcases hs with hs | hs | hs
      · omega
      · obtain ⟨a, ha⟩ := (cutBondSiteEmbedding_range_iff i.castSucc 1 c side q).mpr hs
        exact ⟨Sum.inr (Sum.inr a), ha⟩
      · obtain ⟨a, ha⟩ := (cutBondSiteEmbedding_range_iff i.succ 0 c side q).mpr hs
        exact ⟨Sum.inr (Sum.inl a), ha⟩
    · change i.val < (internalCutEmbedding N c).val ∧
        (internalCutEmbedding N c).val < i.val + 1 at hs
      omega

/-- The consecutively indexed leaf sites have precisely the leaf interval support.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem leafPacketSites_range {d D N : ℕ} (i : Fin N) :
    Set.range (leafPacketSites d D N i) = intervalLogicalSupport d D N i.val (i.val + 1) := by
  change Set.range ((leafLogicalSiteEmbedding d D N i) ∘
    ((Equiv.sumCongr (Equiv.refl (Fin 1)) finSumFinEquiv).trans finSumFinEquiv).symm) = _
  rw [Set.range_comp, Equiv.range_eq_univ, Set.image_univ, leafLogicalSiteEmbedding_range]

/-- The initial endpoint has no bond register sites.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
@[simp] theorem cutBondRegisterWidth_zero (d D N : ℕ) :
    cutBondRegisterWidth d D N 0 = 0 := by
  simp [cutBondRegisterWidth]

/-- The final endpoint has no bond register sites.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
@[simp] theorem cutBondRegisterWidth_last (d D N : ℕ) :
    cutBondRegisterWidth d D N (Fin.last N) = 0 := by
  simp [cutBondRegisterWidth]


/-- All bond and flag sites strictly inside the interval. These sites are initialized again after
the interval construction.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
def intervalInteriorAuxiliarySupport (d D N j k : ℕ) : Set (LogicalSite d D N)
  | Sum.inl _ => False
  | Sum.inr (Sum.inl (c, _, _)) =>
      j < (internalCutEmbedding N c).val ∧ (internalCutEmbedding N c).val < k
  | Sum.inr (Sum.inr (c, _)) =>
      j < (internalCutEmbedding N c).val ∧ (internalCutEmbedding N c).val < k

/-- All bond and flag sites at the joining cut.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
def joiningAuxiliarySupport (d D N m : ℕ) : Set (LogicalSite d D N)
  | Sum.inl _ => False
  | Sum.inr (Sum.inl (c, _, _)) => (internalCutEmbedding N c).val = m
  | Sum.inr (Sum.inr (c, _)) => (internalCutEmbedding N c).val = m

/-- The parent interior auxiliaries are the child interior auxiliaries together with all
auxiliaries at the joining cut.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem intervalInteriorAuxiliarySupport_split {d D N j m k : ℕ}
    (hjm : j < m) (hmk : m < k) :
    intervalInteriorAuxiliarySupport d D N j k =
      intervalInteriorAuxiliarySupport d D N j m ∪
        intervalInteriorAuxiliarySupport d D N m k ∪ joiningAuxiliarySupport d D N m := by
  ext s
  rcases s with s | (⟨c, side, q⟩ | ⟨c, flag⟩)
  · change False ↔ (False ∨ False) ∨ False
    simp only [or_false]
  all_goals
    change (j < (internalCutEmbedding N c).val ∧ (internalCutEmbedding N c).val < k) ↔
      ((j < (internalCutEmbedding N c).val ∧ (internalCutEmbedding N c).val < m) ∨
      (m < (internalCutEmbedding N c).val ∧ (internalCutEmbedding N c).val < k)) ∨
      (internalCutEmbedding N c).val = m
    omega

/-- A one-site interval has no strictly interior auxiliary sites.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem intervalInteriorAuxiliarySupport_leaf {d D N : ℕ} (i : Fin N) :
    intervalInteriorAuxiliarySupport d D N i.val (i.val + 1) = ∅ := by
  ext s
  rcases s with s | (⟨c, side, q⟩ | ⟨c, flag⟩)
  · rfl
  all_goals
    change (i.val < (internalCutEmbedding N c).val ∧
      (internalCutEmbedding N c).val < i.val + 1) ↔ False
    constructor
    · intro hs
      omega
    · intro hs
      exact hs.elim

/-- A computational configuration whose strictly interior auxiliary sites all have the prescribed
initial label.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
def IsIntervalInteriorInitialized {d D N : ℕ} (j k : ℕ)
    (x : LogicalSite d D N → Fin d) (z : Fin d) : Prop :=
  ∀ s ∈ intervalInteriorAuxiliarySupport d D N j k, x s = z

/-- Interior initialization for the parent is equivalent to interior initialization for both
children and initialization of all joining auxiliaries.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem isIntervalInteriorInitialized_split {d D N j m k : ℕ}
    (hjm : j < m) (hmk : m < k) (x : LogicalSite d D N → Fin d) (z : Fin d) :
    IsIntervalInteriorInitialized j k x z ↔
      IsIntervalInteriorInitialized j m x z ∧ IsIntervalInteriorInitialized m k x z ∧
        ∀ s ∈ joiningAuxiliarySupport d D N m, x s = z := by
  simp only [IsIntervalInteriorInitialized, intervalInteriorAuxiliarySupport_split hjm hmk,
    Set.mem_union, or_imp, forall_and, and_assoc]


/-- The full physical interval uses all logical sites.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem intervalLogicalSupport_full (d D N : ℕ) :
    intervalLogicalSupport d D N 0 N = Set.univ := by
  ext s
  constructor
  · intro _
    exact Set.mem_univ _
  · intro _
    rcases s with s | (⟨c, side, q⟩ | ⟨c, flag⟩)
    · exact ⟨Nat.zero_le _, s.isLt⟩
    · exact Or.inl (internalCutEmbedding_bounds N c)
    · exact internalCutEmbedding_bounds N c

/-- Every leaf configuration has initialized interior auxiliaries, since a leaf has no interior
cuts.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem isIntervalInteriorInitialized_leaf {d D N : ℕ} (i : Fin N)
    (x : LogicalSite d D N → Fin d) (z : Fin d) :
    IsIntervalInteriorInitialized i.val (i.val + 1) x z := by
  simp only [IsIntervalInteriorInitialized, intervalInteriorAuxiliarySupport_leaf,
    Set.mem_empty_iff_false, false_implies, implies_true]

/-- Placement of the actual leaf sites in the consecutive numbering of the logical register.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
noncomputable def leafConsecutiveSites (d D N : ℕ) (i : Fin N) :
    Fin (1 + (cutBondRegisterWidth d D N i.succ + cutBondRegisterWidth d D N i.castSucc)) ↪
      Fin (logicalSiteCount d D N) :=
  (leafPacketSites d D N i).trans (logicalSiteEquivFin d D N).toEmbedding

/-- The range of the leaf placement is precisely its numbered interval support.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem leafConsecutiveSites_range {d D N : ℕ} (i : Fin N) :
    Set.range (leafConsecutiveSites d D N i) =
      intervalConsecutiveSupport d D N i.val (i.val + 1) := by
  rw [leafConsecutiveSites, Function.Embedding.coe_trans, Set.range_comp, leafPacketSites_range]
  rfl

/-- Every operator placed on the actual leaf sites is supported on that leaf interval, for
arbitrary logical states.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem leaf_embedOp_mem_supportedOperators {d D N : ℕ} (i : Fin N)
    (X : Matrix
      (MPSTensor.Cfg d
        (1 + (cutBondRegisterWidth d D N i.succ + cutBondRegisterWidth d D N i.castSucc)))
      (MPSTensor.Cfg d
        (1 + (cutBondRegisterWidth d D N i.succ + cutBondRegisterWidth d D N i.castSucc))) ℂ) :
    MPSPreparation.embedOp (leafConsecutiveSites d D N i) X ∈
      MPSPreparation.supportedOperators d (intervalConsecutiveSupport d D N i.val (i.val + 1)) := by
  have h := MPSPreparation.embedOp_mem_supportedOperators
    (leafConsecutiveSites d D N i).injective X
  rw [leafConsecutiveSites_range] at h
  exact h

end MPUCircuit
