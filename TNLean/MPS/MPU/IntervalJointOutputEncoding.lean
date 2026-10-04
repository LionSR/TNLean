/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.IntervalChildComposition
import TNLean.MPS.MPU.IntervalColumnEncoding

/-!
# Coordinates of the actual joint child output

The output columns of disjoint child intervals retain both joining bond
labels. Their restrictions to either child support are the prescribed boundary
configurations. Changing those labels changes only the two joining bond
registers. Initialization on a complement is an explicit injective inclusion.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5.
-/

open Matrix MPSTensor MPSPreparation

namespace MPUCircuit

/-- Restriction of a joint basis encoding to the left placed register.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem jointPlacedBasisEmbedding_left {d a b n : ℕ} {α β τ : Type*}
    (e : Fin a ↪ Fin n) (f : Fin b ↪ Fin n)
    (h : Disjoint (Set.range e) (Set.range f))
    (g : α ↪ Cfg d a) (k : β ↪ Cfg d b)
    (t : τ ↪ OutsidePlacedConfig d (Fin.Embedding.append h)) (p : (α × β) × τ) :
    jointPlacedBasisEmbedding e f h g k t p ∘ e = g p.1.1 := by
  rw [← jointPlacedConfigEquiv_left d e f h]
  change ((jointPlacedConfigEquiv d e f h)
    ((jointPlacedConfigEquiv d e f h).symm ((g p.1.1, k p.1.2), t p.2))).1.1 = _
  rw [Equiv.apply_symm_apply]

/-- Restriction of a joint basis encoding to the right placed register.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem jointPlacedBasisEmbedding_right {d a b n : ℕ} {α β τ : Type*}
    (e : Fin a ↪ Fin n) (f : Fin b ↪ Fin n)
    (h : Disjoint (Set.range e) (Set.range f))
    (g : α ↪ Cfg d a) (k : β ↪ Cfg d b)
    (t : τ ↪ OutsidePlacedConfig d (Fin.Embedding.append h)) (p : (α × β) × τ) :
    jointPlacedBasisEmbedding e f h g k t p ∘ f = k p.1.2 := by
  rw [← jointPlacedConfigEquiv_right d e f h]
  change ((jointPlacedConfigEquiv d e f h)
    ((jointPlacedConfigEquiv d e f h).symm ((g p.1.1, k p.1.2), t p.2))).1.2 = _
  rw [Equiv.apply_symm_apply]

/-- The outside configuration is retained by the joint basis encoding.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem jointPlacedBasisEmbedding_outside {d a b n : ℕ} {α β τ : Type*}
    (e : Fin a ↪ Fin n) (f : Fin b ↪ Fin n)
    (h : Disjoint (Set.range e) (Set.range f))
    (g : α ↪ Cfg d a) (k : β ↪ Cfg d b)
    (t : τ ↪ OutsidePlacedConfig d (Fin.Embedding.append h)) (p : (α × β) × τ) :
    (fun s : {s : Fin n // s ∉ Set.range (Fin.Embedding.append h)} ↦
      jointPlacedBasisEmbedding e f h g k t p s.val) = t p.2 := by
  rw [← jointPlacedConfigEquiv_snd d e f h]
  change ((jointPlacedConfigEquiv d e f h)
    ((jointPlacedConfigEquiv d e f h).symm ((g p.1.1, k p.1.2), t p.2))).2 = _
  rw [Equiv.apply_symm_apply]

/-- Inclusion obtained by setting the selected coordinates to zero.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
noncomputable def initializedComplementEmbedding {d : ℕ} [NeZero d] {ι : Type*} (S : Set ι) :
    ({i : ι // i ∉ S} → Fin d) ↪ (ι → Fin d) := by
  classical
  exact ⟨fun x i ↦ if h : i ∉ S then x ⟨i, h⟩ else 0, by
    intro x y h
    funext i
    have hh := congrFun h i.val
    simpa only [dite_eq_left i.2] using hh⟩

/-- The selected coordinates of the initialized inclusion are zero.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem initializedComplementEmbedding_zero {d : ℕ} [NeZero d] {ι : Type*} (S : Set ι)
    (x : {i : ι // i ∉ S} → Fin d) (i : ι) (hi : i ∈ S) :
    initializedComplementEmbedding S x i = 0 := by
  classical
  change (if h : i ∉ S then x ⟨i, h⟩ else 0) = 0
  exact dite_eq_right (not_not.mpr hi)

/-- The prescribed output basis inclusion of two adjacent child intervals.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
noncomputable def intervalJointOutputEmbedding {d D N : ℕ} [NeZero d] {r l n τ : Type*}
    (j m k : Fin (N + 1)) (hjm : j.val < m.val) (hmk : m.val < k.val)
    (em : r ↪ Cfg d (cutBondRegisterWidth d D N m))
    (ej : l ↪ Cfg d (cutBondRegisterWidth d D N j))
    (ek : n ↪ Cfg d (cutBondRegisterWidth d D N k))
    (t : τ ↪ OutsidePlacedConfig d (Fin.Embedding.append
      (intervalPacketSites_disjoint (d := d) (D := D) (N := N) hjm hmk))) :
    (((CutIntervalConfig d N j.val m.val × (r × l)) ×
      (CutIntervalConfig d N m.val k.val × (n × r))) × τ) ↪
        Cfg d (logicalSiteCount d D N) :=
  jointPlacedBasisEmbedding (intervalPacketSites d D N j.val m.val)
    (intervalPacketSites d D N m.val k.val)
    (intervalPacketSites_disjoint (d := d) (D := D) (N := N) hjm hmk)
    (intervalOutputEmbedding j m em ej) (intervalOutputEmbedding m k ek em) t

/-- The joint output agrees with the left boundary configuration on the left support.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem intervalJointOutputEmbedding_left_support {d D N : ℕ} [NeZero d] {r l n τ : Type*}
    (j m k : Fin (N + 1)) (hjm : j.val < m.val) (hmk : m.val < k.val)
    (em : r ↪ Cfg d (cutBondRegisterWidth d D N m))
    (ej : l ↪ Cfg d (cutBondRegisterWidth d D N j))
    (ek : n ↪ Cfg d (cutBondRegisterWidth d D N k))
    (t : τ ↪ OutsidePlacedConfig d (Fin.Embedding.append
      (intervalPacketSites_disjoint (d := d) (D := D) (N := N) hjm hmk)))
    (p : ((CutIntervalConfig d N j.val m.val × (r × l)) ×
      (CutIntervalConfig d N m.val k.val × (n × r))) × τ)
    (s : LogicalSite d D N) (hs : s ∈ intervalLogicalSupport d D N j.val m.val) :
    intervalJointOutputEmbedding j m k hjm hmk em ej ek t p (logicalSiteEquivFin d D N s) =
      intervalBoundaryConfig j m em ej p.1.1 s := by
  obtain ⟨i, hi⟩ := intervalPacketLogicalSite_surjective s hs
  have hh := congrFun (jointPlacedBasisEmbedding_left
    (intervalPacketSites d D N j.val m.val) (intervalPacketSites d D N m.val k.val)
    (intervalPacketSites_disjoint (d := d) (D := D) (N := N) hjm hmk)
    (intervalOutputEmbedding j m em ej) (intervalOutputEmbedding m k ek em) t p) i
  change intervalJointOutputEmbedding j m k hjm hmk em ej ek t p
      (logicalSiteEquivFin d D N (intervalPacketLogicalSite d D N j.val m.val i)) =
    intervalBoundaryConfig j m em ej p.1.1 (intervalPacketLogicalSite d D N j.val m.val i) at hh
  simpa only [hi] using hh

/-- The joint output agrees with the right boundary configuration on the right support.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem intervalJointOutputEmbedding_right_support {d D N : ℕ} [NeZero d] {r l n τ : Type*}
    (j m k : Fin (N + 1)) (hjm : j.val < m.val) (hmk : m.val < k.val)
    (em : r ↪ Cfg d (cutBondRegisterWidth d D N m))
    (ej : l ↪ Cfg d (cutBondRegisterWidth d D N j))
    (ek : n ↪ Cfg d (cutBondRegisterWidth d D N k))
    (t : τ ↪ OutsidePlacedConfig d (Fin.Embedding.append
      (intervalPacketSites_disjoint (d := d) (D := D) (N := N) hjm hmk)))
    (p : ((CutIntervalConfig d N j.val m.val × (r × l)) ×
      (CutIntervalConfig d N m.val k.val × (n × r))) × τ)
    (s : LogicalSite d D N) (hs : s ∈ intervalLogicalSupport d D N m.val k.val) :
    intervalJointOutputEmbedding j m k hjm hmk em ej ek t p (logicalSiteEquivFin d D N s) =
      intervalBoundaryConfig m k ek em p.1.2 s := by
  obtain ⟨i, hi⟩ := intervalPacketLogicalSite_surjective s hs
  have hh := congrFun (jointPlacedBasisEmbedding_right
    (intervalPacketSites d D N j.val m.val) (intervalPacketSites d D N m.val k.val)
    (intervalPacketSites_disjoint (d := d) (D := D) (N := N) hjm hmk)
    (intervalOutputEmbedding j m em ej) (intervalOutputEmbedding m k ek em) t p) i
  change intervalJointOutputEmbedding j m k hjm hmk em ej ek t p
      (logicalSiteEquivFin d D N (intervalPacketLogicalSite d D N m.val k.val i)) =
    intervalBoundaryConfig m k ek em p.1.2 (intervalPacketLogicalSite d D N m.val k.val i) at hh
  simpa only [hi] using hh


/-- Changing the right bond label leaves all other coordinates unchanged.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem intervalBoundaryConfig_right_eq_away {d D N : ℕ} [NeZero d] {ρ σ : Type*}
    (j k : Fin (N + 1))
    (eρ : ρ ↪ Cfg d (cutBondRegisterWidth d D N k))
    (eσ : σ ↪ Cfg d (cutBondRegisterWidth d D N j))
    (x : CutIntervalConfig d N j.val k.val) (β β' : ρ) (α : σ)
    (s : LogicalSite d D N) (hs : s ∉ Set.range (cutBondSiteEmbedding d D N k 0)) :
    intervalBoundaryConfig j k eρ eσ (x, (β, α)) s =
      intervalBoundaryConfig j k eρ eσ (x, (β', α)) s := by
  unfold intervalBoundaryConfig
  rw [Function.extend_apply' _ _ _ hs, Function.extend_apply' _ _ _ hs]

/-- Changing the left bond label leaves all other coordinates unchanged.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem intervalBoundaryConfig_left_eq_away {d D N : ℕ} [NeZero d] {ρ σ : Type*}
    (j k : Fin (N + 1))
    (eρ : ρ ↪ Cfg d (cutBondRegisterWidth d D N k))
    (eσ : σ ↪ Cfg d (cutBondRegisterWidth d D N j))
    (x : CutIntervalConfig d N j.val k.val) (β : ρ) (α α' : σ)
    (s : LogicalSite d D N) (hs : s ∉ Set.range (cutBondSiteEmbedding d D N j 1)) :
    intervalBoundaryConfig j k eρ eσ (x, (β, α)) s =
      intervalBoundaryConfig j k eρ eσ (x, (β, α')) s := by
  classical
  by_cases hR : s ∈ Set.range (cutBondSiteEmbedding d D N k 0)
  · obtain ⟨q, rfl⟩ := hR
    exact (congrFun (intervalBoundaryConfig_right j k eρ eσ (x, (β, α))) q).trans
      (congrFun (intervalBoundaryConfig_right j k eρ eσ (x, (β, α'))) q).symm
  · unfold intervalBoundaryConfig
    rw [Function.extend_apply' _ _ _ hR, Function.extend_apply' _ _ _ hR,
      Function.extend_apply' _ _ _ hs, Function.extend_apply' _ _ _ hs]

/-- Changing the joining labels leaves every coordinate outside the joining bonds unchanged.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem intervalJointOutputEmbedding_eq_away_joining_bonds
    {d D N : ℕ} [NeZero d] {r l n τ : Type*}
    (j m k : Fin (N + 1)) (hjm : j.val < m.val) (hmk : m.val < k.val)
    (em : r ↪ Cfg d (cutBondRegisterWidth d D N m))
    (ej : l ↪ Cfg d (cutBondRegisterWidth d D N j))
    (ek : n ↪ Cfg d (cutBondRegisterWidth d D N k))
    (t : τ ↪ OutsidePlacedConfig d (Fin.Embedding.append
      (intervalPacketSites_disjoint (d := d) (D := D) (N := N) hjm hmk)))
    (p : (CutIntervalConfig d N j.val m.val × CutIntervalConfig d N m.val k.val) × (n × l))
    (z : τ) (x y x' y' : r) (s : LogicalSite d D N)
    (h0 : s ∉ Set.range (cutBondSiteEmbedding d D N m 0))
    (h1 : s ∉ Set.range (cutBondSiteEmbedding d D N m 1)) :
    intervalJointOutputEmbedding j m k hjm hmk em ej ek t
        (((p.1.1, (x, p.2.2)), (p.1.2, (p.2.1, y))), z) (logicalSiteEquivFin d D N s) =
      intervalJointOutputEmbedding j m k hjm hmk em ej ek t
        (((p.1.1, (x', p.2.2)), (p.1.2, (p.2.1, y'))), z) (logicalSiteEquivFin d D N s) := by
  classical
  by_cases hL : s ∈ intervalLogicalSupport d D N j.val m.val
  · rw [intervalJointOutputEmbedding_left_support j m k hjm hmk em ej ek t _ s hL,
      intervalJointOutputEmbedding_left_support j m k hjm hmk em ej ek t _ s hL]
    exact intervalBoundaryConfig_right_eq_away j m em ej _ _ _ _ s h0
  by_cases hR : s ∈ intervalLogicalSupport d D N m.val k.val
  · rw [intervalJointOutputEmbedding_right_support j m k hjm hmk em ej ek t _ s hR,
      intervalJointOutputEmbedding_right_support j m k hjm hmk em ej ek t _ s hR]
    exact intervalBoundaryConfig_left_eq_away m k ek em _ _ _ _ s h1
  have hLs : logicalSiteEquivFin d D N s ∉ Set.range (intervalPacketSites d D N j.val m.val) := by
    rw [intervalPacketSites_range]
    rintro ⟨s', hs', hh⟩
    exact hL ((logicalSiteEquivFin d D N).injective hh ▸ hs')
  have hRs : logicalSiteEquivFin d D N s ∉ Set.range (intervalPacketSites d D N m.val k.val) := by
    rw [intervalPacketSites_range]
    rintro ⟨s', hs', hh⟩
    exact hR ((logicalSiteEquivFin d D N).injective hh ▸ hs')
  have hout : logicalSiteEquivFin d D N s ∉ Set.range (Fin.Embedding.append
      (intervalPacketSites_disjoint (d := d) (D := D) (N := N) hjm hmk)) := by
    rintro ⟨i, hi⟩
    induction i using Fin.addCases with
    | left q =>
      apply hLs
      exact ⟨q, by simpa only [Fin.Embedding.coe_append, Fin.append_left] using hi⟩
    | right q =>
      apply hRs
      exact ⟨q, by simpa only [Fin.Embedding.coe_append, Fin.append_right] using hi⟩
  have hfirst := congrFun (jointPlacedBasisEmbedding_outside
    (intervalPacketSites d D N j.val m.val) (intervalPacketSites d D N m.val k.val)
    (intervalPacketSites_disjoint (d := d) (D := D) (N := N) hjm hmk)
    (intervalOutputEmbedding j m em ej) (intervalOutputEmbedding m k ek em) t
      (((p.1.1, (x, p.2.2)), (p.1.2, (p.2.1, y))), z))
    ⟨logicalSiteEquivFin d D N s, hout⟩
  have hsecond := congrFun (jointPlacedBasisEmbedding_outside
    (intervalPacketSites d D N j.val m.val) (intervalPacketSites d D N m.val k.val)
    (intervalPacketSites_disjoint (d := d) (D := D) (N := N) hjm hmk)
    (intervalOutputEmbedding j m em ej) (intervalOutputEmbedding m k ek em) t
      (((p.1.1, (x', p.2.2)), (p.1.2, (p.2.1, y'))), z))
    ⟨logicalSiteEquivFin d D N s, hout⟩
  exact hfirst.trans hsecond.symm

end MPUCircuit
