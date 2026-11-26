/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Circuit.Registers.IntervalJointFlagInitialization
import TNLean.MPS.MPU.Circuit.Registers.JoiningRegisterCoordinates
import TNLean.MPS.MPU.Circuit.Merging.CompatibleBondDilationCircuit
import TNLean.MPS.MPU.Circuit.Merging.BalancedIntervalDilation
import QICLean.Circuit.Protocol.ZeroRegister.Projection
import TNLean.MPS.MPU.Circuit.Merging.EncodedUniformMergingCircuit

/-!
# The actual joining packet encoding

The joining packet of the two child output columns carries the two given
bond labels and two zero flags, in the exact order of the compatible dilation.
This identity is derived from the prescribed child boundary configurations
and initialization of the joining flags.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5.

## Product coordinates for the actual joint child output

The prescribed joining packet can be placed last by a permutation of logical
sites. After this change of coordinates the actual joint output inclusion
factors as the product of an injective prefix inclusion and the compatible
joining bond inclusion. The prefix inclusion and permutation are derived;
they are not supplied as hypotheses. The outside configuration is unrestricted
except for the explicitly initialized joining flags.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5.

## Initialized basis coordinates under a site bijection

A site bijection transports both an initialized basis inclusion and its
selected zero-coordinate set. Equality of the initialized ranges is derived
from their concrete zero-coordinate predicates. No independent initialization
or cleanup identity is assumed.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5.

It also contains the following results.

* `MPUCircuit.prefixBasisEmbedding`, `MPUCircuit.appendBasisEmbedding_prefixBasisEmbedding`:
  factorization of product-compatible computational basis encodings.
-/

section ProductBasisFactorization

/-!
## Factorization of product-compatible computational basis encodings

Suppose that the final register depends only on its prescribed bond label,
and that the remaining registers are independent of that label. The full
injective encoding then factors as a product encoding. Injectivity of the
remaining-register encoding follows from injectivity of the full encoding;
it is not supplied separately.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5.
-/

open MPSTensor
namespace MPUCircuit

/-- The remaining-register encoding obtained by fixing one label of the final register. Its
injectivity follows from injectivity of the full encoding and the fixed final-register encoding.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
def prefixBasisEmbedding {d a b : ℕ} {ρ κ : Type*}
    (E : (ρ × κ) ↪ Cfg d (a + b)) (e : κ ↪ Cfg d b) (z : κ)
    (hsuffix : ∀ p, E p ∘ Fin.natAdd a = e p.2) : ρ ↪ Cfg d a where
  toFun p := E (p, z) ∘ Fin.castAdd b
  inj' p q h := by
    have heq : E (p, z) = E (q, z) := by
      funext i
      induction i using Fin.addCases with
      | left j => exact congrFun h j
      | right j =>
        exact (congrFun (hsuffix (p, z)) j).trans (congrFun (hsuffix (q, z)) j).symm
    exact congrArg Prod.fst (E.injective heq)

/-- Independence of the final-register label in the prefix and the prescribed suffix encoding
imply an exact factorization of the full basis embedding.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem appendBasisEmbedding_prefixBasisEmbedding {d a b : ℕ} {ρ κ : Type*}
    (E : (ρ × κ) ↪ Cfg d (a + b)) (e : κ ↪ Cfg d b) (z : κ)
    (hsuffix : ∀ p, E p ∘ Fin.natAdd a = e p.2)
    (hprefix : ∀ p, E p ∘ Fin.castAdd b = E (p.1, z) ∘ Fin.castAdd b) :
    appendBasisEmbedding (prefixBasisEmbedding E e z hsuffix) e = E := by
  apply Function.Embedding.ext
  intro p
  funext i
  induction i using Fin.addCases with
  | left j =>
    change Fin.append _ _ (Fin.castAdd b j) = E p (Fin.castAdd b j)
    rw [Fin.append_left]
    exact (congrFun (hprefix p) j).symm
  | right j =>
    change Fin.append _ _ (Fin.natAdd a j) = E p (Fin.natAdd a j)
    rw [Fin.append_right]
    exact (congrFun (hsuffix p) j).symm

end MPUCircuit

end ProductBasisFactorization

section IntervalJointSuffixFactorization

section

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

end

section

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

end

section

open Matrix MPSPreparation MPSTensor QuantumCircuit

namespace MPUCircuit

/-- Range membership under a site bijection is range membership of the inverse configuration.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem mem_range_pullbackBasisEmbedding_iff {d a n : ℕ} {α : Type*}
    (E : α ↪ Cfg d n) (e : Fin a ≃ Fin n) (x : Cfg d a) :
    x ∈ Set.range (pullbackBasisEmbedding E e) ↔ x ∘ e.symm ∈ Set.range E := by
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p, ?_⟩
    funext i
    have hh := congrFun hp (e.symm i)
    simpa only [pullbackBasisEmbedding_apply, Function.comp_apply,
      Equiv.apply_symm_apply] using hh
  · rintro ⟨p, hp⟩
    refine ⟨p, ?_⟩
    funext i
    have hh := congrFun hp (e i)
    simpa only [pullbackBasisEmbedding_apply, Function.comp_apply,
      Equiv.symm_apply_apply] using hh

/-- Transport of the selected sites identifies the pulled-back initialized range.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem range_pullbackBasisEmbedding_eq_zeroFlagEmbedding
    {d a n b : ℕ} [NeZero d] {α : Type*}
    (E : α ↪ Cfg d n) (e : Fin a ≃ Fin n) (s : Fin b ↪ Fin a)
    (S : Set (Fin n))
    (hS : Set.range (s.trans e.toEmbedding) = S)
    (hE : ∀ x, x ∈ Set.range E ↔ ∀ i ∈ S, x i = 0) :
    Set.range (pullbackBasisEmbedding E e) = Set.range (zeroFlagEmbedding (d := d) s) := by
  ext x
  rw [mem_range_pullbackBasisEmbedding_iff, mem_range_zeroFlagEmbedding_iff, hE]
  constructor
  · intro hx j
    have hs : e (s j) ∈ S := by
      rw [← hS]
      exact ⟨j, rfl⟩
    simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hx (e (s j)) hs
  · intro hx i hi
    rw [← hS] at hi
    obtain ⟨j, rfl⟩ := hi
    simpa only [Function.comp_apply, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
      Equiv.symm_apply_apply] using hx j

end MPUCircuit

end

end IntervalJointSuffixFactorization
