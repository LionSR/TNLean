/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.IntervalJoiningPacketEncoding
import TNLean.MPS.MPU.ProductBasisFactorization
import TNLean.MPS.MPU.BalancedIntervalDilation

/-!
# Product coordinates for the actual joint child output

The prescribed joining packet can be placed last by a permutation of logical
sites. After this change of coordinates the actual joint output inclusion
factors as the product of an injective prefix inclusion and the compatible
joining bond inclusion. The prefix inclusion and permutation are derived;
they are not supplied as hypotheses. The outside configuration is unrestricted
except for the explicitly initialized joining flags.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5.
-/

open Matrix MPSTensor MPSPreparation

namespace MPUCircuit

/-- Regrouping which places the spectator before the joining pair.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
def outerSpectatorJoiningRegrouping (ρ κ τ : Type*) : ((ρ × τ) × κ) ≃ ((ρ × κ) × τ) :=
  (Equiv.prodAssoc ρ τ κ).trans
    ((Equiv.prodCongr (Equiv.refl ρ) (Equiv.prodComm τ κ)).trans
      (Equiv.prodAssoc ρ κ τ).symm)

/-- Transport of a basis inclusion along a bijection of physical sites.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
def pullbackBasisEmbedding {d a b : ℕ} {α : Type*}
    (E : α ↪ Cfg d b) (e : Fin a ≃ Fin b) : α ↪ Cfg d a :=
  E.trans (Equiv.arrowCongr e.symm (Equiv.refl (Fin d))).toEmbedding

/-- The transported inclusion is precomposition by the site bijection.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem pullbackBasisEmbedding_apply {d a b : ℕ} {α : Type*}
    (E : α ↪ Cfg d b) (e : Fin a ≃ Fin b) (p : α) :
    pullbackBasisEmbedding E e p = E p ∘ e := rfl

/-- Prefix coordinates lie outside the prescribed suffix packet.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem suffixCoordinates_prefix_not_mem {a b n : ℕ}
    (hn : a + b = n) (τ : Equiv.Perm (Fin n)) (e : Fin b ↪ Fin n)
    (he : ∀ i, τ (Fin.cast hn (Fin.natAdd a i)) = e i) (i : Fin a) :
    τ (Fin.cast hn (Fin.castAdd b i)) ∉ Set.range e := by
  rintro ⟨j, hj⟩
  rw [← he j] at hj
  have hh := congrArg Fin.val (τ.injective hj)
  simp only [Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd] at hh
  have := i.isLt
  omega

/-- The left joining bond register belongs to the joining packet.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem joiningPacketLogicalSites_range_left {d D N : ℕ} (c : Fin (N - 1)) :
    Set.range (cutBondSiteEmbedding d D N (internalCutEmbedding N c) 0) ⊆
      Set.range (joiningPacketLogicalSites d D N c) := by
  rintro s ⟨i, rfl⟩
  exact ⟨⟨i.val, by have := i.isLt; omega⟩, joiningPacketLogicalSites_left d D N c i⟩

/-- The right joining bond register belongs to the joining packet.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem joiningPacketLogicalSites_range_right {d D N : ℕ} (c : Fin (N - 1)) :
    Set.range (cutBondSiteEmbedding d D N (internalCutEmbedding N c) 1) ⊆
      Set.range (joiningPacketLogicalSites d D N c) := by
  rintro s ⟨i, rfl⟩
  exact ⟨⟨cutBondRegisterWidth d D N (internalCutEmbedding N c) + i.val,
    by have := i.isLt; omega⟩, joiningPacketLogicalSites_right d D N c i⟩

/-- The actual joint output inclusion with the joining pair last.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
noncomputable def regroupedIntervalJointOutputEmbedding
    {d D N r l n : ℕ} [NeZero d]
    (c : Fin (N - 1)) (j k : Fin (N + 1))
    (hjm : j.val < (internalCutEmbedding N c).val)
    (hmk : (internalCutEmbedding N c).val < k.val)
    (em : Fin r ↪ Cfg d (cutBondRegisterWidth d D N (internalCutEmbedding N c)))
    (ej : Fin l ↪ Cfg d (cutBondRegisterWidth d D N j))
    (ek : Fin n ↪ Cfg d (cutBondRegisterWidth d D N k)) :
    ((((CutIntervalConfig d N j.val (internalCutEmbedding N c).val ×
      CutIntervalConfig d N (internalCutEmbedding N c).val k.val) × (Fin n × Fin l)) ×
      ({s // s ∉ intervalJointOutsideFlagSet (d := d) (D := D) j
        (internalCutEmbedding N c) k hjm hmk} → Fin d)) × (Fin r × Fin r)) ↪
      Cfg d (logicalSiteCount d D N) :=
  ((outerSpectatorJoiningRegrouping _ _ _).trans
    (Equiv.prodCongr intervalChildrenRegrouping.symm (Equiv.refl _))).toEmbedding.trans
      (intervalJointOutputEmbedding j (internalCutEmbedding N c) k hjm hmk em ej ek
        (intervalJointInitializedOutsideEmbedding (d := d) (D := D) j
          (internalCutEmbedding N c) k hjm hmk))

/-- The regrouped output has the two original child boundary labels.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem regroupedIntervalJointOutputEmbedding_apply
    {d D N r l n : ℕ} [NeZero d]
    (c : Fin (N - 1)) (j k : Fin (N + 1))
    (hjm : j.val < (internalCutEmbedding N c).val)
    (hmk : (internalCutEmbedding N c).val < k.val)
    (em : Fin r ↪ Cfg d (cutBondRegisterWidth d D N (internalCutEmbedding N c)))
    (ej : Fin l ↪ Cfg d (cutBondRegisterWidth d D N j))
    (ek : Fin n ↪ Cfg d (cutBondRegisterWidth d D N k))
    (p : (((CutIntervalConfig d N j.val (internalCutEmbedding N c).val ×
      CutIntervalConfig d N (internalCutEmbedding N c).val k.val) × (Fin n × Fin l)) ×
      ({s // s ∉ intervalJointOutsideFlagSet (d := d) (D := D) j
        (internalCutEmbedding N c) k hjm hmk} → Fin d)) × (Fin r × Fin r)) :
    regroupedIntervalJointOutputEmbedding c j k hjm hmk em ej ek p =
      intervalJointOutputEmbedding j (internalCutEmbedding N c) k hjm hmk em ej ek
        (intervalJointInitializedOutsideEmbedding (d := d) (D := D) j
          (internalCutEmbedding N c) k hjm hmk)
        (((p.1.1.1.1, (p.2.2, p.1.1.2.2)),
          (p.1.1.1.2, (p.1.1.2.1, p.2.1))), p.1.2) := rfl


/-- The actual regrouped joint output admits the prescribed product coordinates.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem exists_regroupedIntervalJointOutput_product_coordinates
    {d D N r l n : ℕ} [NeZero d] (hd : 2 ≤ d) (hr : 0 < r)
    (c : Fin (N - 1)) (j k : Fin (N + 1))
    (hjm : j.val < (internalCutEmbedding N c).val)
    (hmk : (internalCutEmbedding N c).val < k.val)
    (em : Fin r ↪ Cfg d (cutBondRegisterWidth d D N (internalCutEmbedding N c)))
    (ej : Fin l ↪ Cfg d (cutBondRegisterWidth d D N j))
    (ek : Fin n ↪ Cfg d (cutBondRegisterWidth d D N k)) :
    ∃ (a : ℕ) (hn : a +
        (2 * cutBondRegisterWidth d D N (internalCutEmbedding N c) + 2) =
          logicalSiteCount d D N)
      (τ : Equiv.Perm (Fin (logicalSiteCount d D N)))
      (f : (((CutIntervalConfig d N j.val (internalCutEmbedding N c).val ×
        CutIntervalConfig d N (internalCutEmbedding N c).val k.val) × (Fin n × Fin l)) ×
        ({s // s ∉ intervalJointOutsideFlagSet (d := d) (D := D) j
          (internalCutEmbedding N c) k hjm hmk} → Fin d)) ↪ Cfg d a),
      (∀ i, τ (Fin.cast hn (Fin.natAdd a i)) = joiningPacketSites d D N c i) ∧
      pullbackBasisEmbedding (regroupedIntervalJointOutputEmbedding c j k hjm hmk em ej ek)
          ((finCongr hn).trans τ) =
        appendBasisEmbedding f
          ((joiningChildBasisEmbedding (r := r) hd).trans
            (compatibleBondDilationEmbedding hd em)) := by
  classical
  obtain ⟨a, hn, τ, hτ⟩ := exists_joiningPacket_suffix_coordinates d D N c
  let q := cutBondRegisterWidth d D N (internalCutEmbedding N c)
  let E := regroupedIntervalJointOutputEmbedding c j k hjm hmk em ej ek
  let E' := pullbackBasisEmbedding E ((finCongr hn).trans τ)
  let e := (joiningChildBasisEmbedding (r := r) hd).trans
    (compatibleBondDilationEmbedding hd em)
  let z : Fin r × Fin r := (⟨0, hr⟩, ⟨0, hr⟩)
  have hsuffix : ∀ p, E' p ∘ Fin.natAdd a = e p.2 := by
    intro p
    funext i
    change E p (τ (Fin.cast hn (Fin.natAdd a i))) = e p.2 i
    rw [hτ i]
    have hh := congrFun (intervalJointOutputEmbedding_joiningPacket_active hd c j k
      hjm hmk em ej ek p.1.1 p.2.2 p.2.1 p.1.2) i
    exact hh
  have hprefix : ∀ p, E' p ∘ Fin.castAdd (2 * q + 2) =
      E' (p.1, z) ∘ Fin.castAdd (2 * q + 2) := by
    intro p
    funext i
    let s := (logicalSiteEquivFin d D N).symm (τ (Fin.cast hn (Fin.castAdd (2 * q + 2) i)))
    have hs : s ∉ Set.range (joiningPacketLogicalSites d D N c) := by
      rintro ⟨b, hb⟩
      apply suffixCoordinates_prefix_not_mem hn τ (joiningPacketSites d D N c) hτ i
      refine ⟨b, ?_⟩
      change logicalSiteEquivFin d D N (joiningPacketLogicalSites d D N c b) = _
      rw [hb]
      exact (logicalSiteEquivFin d D N).apply_symm_apply _
    have h0 : s ∉ Set.range (cutBondSiteEmbedding d D N (internalCutEmbedding N c) 0) :=
      fun h ↦ hs (joiningPacketLogicalSites_range_left c h)
    have h1 : s ∉ Set.range (cutBondSiteEmbedding d D N (internalCutEmbedding N c) 1) :=
      fun h ↦ hs (joiningPacketLogicalSites_range_right c h)
    have hh := intervalJointOutputEmbedding_eq_away_joining_bonds j
      (internalCutEmbedding N c) k hjm hmk em ej ek
      (intervalJointInitializedOutsideEmbedding (d := d) (D := D) j
        (internalCutEmbedding N c) k hjm hmk)
      p.1.1 p.1.2 p.2.2 p.2.1 z.2 z.1 s h0 h1
    dsimp only [Function.comp_apply, E', pullbackBasisEmbedding_apply]
    change E p (τ (Fin.cast hn (Fin.castAdd (2 * q + 2) i))) =
      E (p.1, z) (τ (Fin.cast hn (Fin.castAdd (2 * q + 2) i)))
    dsimp only [E]
    rw [regroupedIntervalJointOutputEmbedding_apply,
      regroupedIntervalJointOutputEmbedding_apply]
    simpa only [s, Equiv.apply_symm_apply] using hh
  let f := prefixBasisEmbedding E' e z hsuffix
  refine ⟨a, hn, τ, f, hτ, ?_⟩
  exact (appendBasisEmbedding_prefixBasisEmbedding E' e z hsuffix hprefix).symm

end MPUCircuit
