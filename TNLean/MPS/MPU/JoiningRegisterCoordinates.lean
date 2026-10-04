/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.IntervalRegisterLayout
import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Logic.Equiv.Fintype

/-!
# Coordinates of the actual joining registers

The joining packet consists of the left child's right bond register, the
right child's left bond register, and the two amplification flags. Its order
agrees with the compatible bond dilation. A permutation of the full logical
register placing this actual packet at the end is derived from the two
injective site enumerations; no permutation is supplied as a hypothesis.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5.
-/

namespace MPUCircuit

/-- The two amplification flags at the given internal cut.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
def joiningFlagPacketSites (d D N : ℕ) (c : Fin (N - 1)) : Fin 2 ↪ LogicalSite d D N where
  toFun i := amplificationFlagEmbedding d D N (c, i)
  inj' _ _ h := congrArg (fun s : AmplificationFlagSite N ↦ s.2)
    ((amplificationFlagEmbedding d D N).injective h)

/-- The two joining bond registers, with the left child register first.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
def joiningBondPacketSites (d D N : ℕ) (c : Fin (N - 1)) :
    Fin (cutBondRegisterWidth d D N (internalCutEmbedding N c) +
      cutBondRegisterWidth d D N (internalCutEmbedding N c)) ↪ LogicalSite d D N :=
  Fin.Embedding.append (cutBondSiteEmbedding_disjoint
    (internalCutEmbedding N c) (internalCutEmbedding N c) (by decide : (0 : Fin 2) ≠ 1))

/-- Joining bond registers and amplification flags occupy distinct logical sites.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem joiningBondPacketSites_disjoint_flags (d D N : ℕ) (c : Fin (N - 1)) :
    Disjoint (Set.range (joiningBondPacketSites d D N c))
      (Set.range (joiningFlagPacketSites d D N c)) := by
  rw [Set.disjoint_left]
  rintro s ⟨i, rfl⟩ ⟨f, hf⟩
  induction i using Fin.addCases with
  | left q =>
    simp only [joiningFlagPacketSites, joiningBondPacketSites, Fin.Embedding.coe_append,
      Fin.append_left] at hf
    cases hf
  | right q =>
    simp only [joiningFlagPacketSites, joiningBondPacketSites, Fin.Embedding.coe_append,
      Fin.append_right] at hf
    cases hf

/-- The actual two bond registers followed by the dilation and attenuation flags.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
def joiningPacketLogicalSites (d D N : ℕ) (c : Fin (N - 1)) :
    Fin (2 * cutBondRegisterWidth d D N (internalCutEmbedding N c) + 2) ↪
      LogicalSite d D N :=
  (finCongr (by omega :
    2 * cutBondRegisterWidth d D N (internalCutEmbedding N c) + 2 =
      (cutBondRegisterWidth d D N (internalCutEmbedding N c) +
        cutBondRegisterWidth d D N (internalCutEmbedding N c)) + 2)).toEmbedding.trans
    (Fin.Embedding.append (joiningBondPacketSites_disjoint_flags d D N c))

/-- Placement of the ordered joining packet in the consecutively indexed logical register.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
noncomputable def joiningPacketSites (d D N : ℕ) (c : Fin (N - 1)) :
    Fin (2 * cutBondRegisterWidth d D N (internalCutEmbedding N c) + 2) ↪
      Fin (logicalSiteCount d D N) :=
  (joiningPacketLogicalSites d D N c).trans (logicalSiteEquivFin d D N).toEmbedding

/-- The first packet block is the left child right boundary bond register.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem joiningPacketLogicalSites_left (d D N : ℕ) (c : Fin (N - 1))
    (i : Fin (cutBondRegisterWidth d D N (internalCutEmbedding N c))) :
    joiningPacketLogicalSites d D N c ⟨i.val, by have := i.isLt; omega⟩ =
      cutBondSiteEmbedding d D N (internalCutEmbedding N c) 0 i := by
  change Fin.append (joiningBondPacketSites d D N c) (joiningFlagPacketSites d D N c)
    (Fin.castAdd 2 (Fin.castAdd _ i)) = _
  rw [Fin.append_left]
  simp only [joiningBondPacketSites, Fin.Embedding.coe_append, Fin.append_left]

/-- The second packet block is the right child left boundary bond register.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem joiningPacketLogicalSites_right (d D N : ℕ) (c : Fin (N - 1))
    (i : Fin (cutBondRegisterWidth d D N (internalCutEmbedding N c))) :
    joiningPacketLogicalSites d D N c
      ⟨cutBondRegisterWidth d D N (internalCutEmbedding N c) + i.val,
        by have := i.isLt; omega⟩ =
      cutBondSiteEmbedding d D N (internalCutEmbedding N c) 1 i := by
  change Fin.append (joiningBondPacketSites d D N c) (joiningFlagPacketSites d D N c)
    (Fin.castAdd 2 (Fin.natAdd _ i)) = _
  rw [Fin.append_left]
  simp only [joiningBondPacketSites, Fin.Embedding.coe_append, Fin.append_right]

/-- The last two packet sites are the amplification flags in their prescribed order.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem joiningPacketLogicalSites_flag (d D N : ℕ) (c : Fin (N - 1)) (i : Fin 2) :
    joiningPacketLogicalSites d D N c
      ⟨2 * cutBondRegisterWidth d D N (internalCutEmbedding N c) + i.val,
        by have := i.isLt; omega⟩ = amplificationFlagEmbedding d D N (c, i) := by
  change Fin.append (joiningBondPacketSites d D N c) (joiningFlagPacketSites d D N c)
    ⟨2 * cutBondRegisterWidth d D N (internalCutEmbedding N c) + i.val,
      by have := i.isLt; omega⟩ = _
  have hi : (⟨2 * cutBondRegisterWidth d D N (internalCutEmbedding N c) + i.val,
      by have := i.isLt; omega⟩ :
        Fin ((cutBondRegisterWidth d D N (internalCutEmbedding N c) +
          cutBondRegisterWidth d D N (internalCutEmbedding N c)) + 2)) =
        Fin.natAdd (cutBondRegisterWidth d D N (internalCutEmbedding N c) +
          cutBondRegisterWidth d D N (internalCutEmbedding N c)) i :=
      Fin.ext (by simp only [Fin.val_natAdd]; omega)
  rw [hi, Fin.append_right]
  rfl


/-- There is a permutation sending the final packet of logical coordinates to the actual joining
registers, with their exact order preserved.

See `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, §5. -/
theorem exists_joiningPacket_suffix_coordinates (d D N : ℕ) (c : Fin (N - 1)) :
    ∃ (a : ℕ) (hn : a +
        (2 * cutBondRegisterWidth d D N (internalCutEmbedding N c) + 2) =
          logicalSiteCount d D N)
      (τ : Equiv.Perm (Fin (logicalSiteCount d D N))),
      ∀ i : Fin (2 * cutBondRegisterWidth d D N (internalCutEmbedding N c) + 2),
        τ (Fin.cast hn (Fin.natAdd a i)) = joiningPacketSites d D N c i := by
  have hcap : 2 * cutBondRegisterWidth d D N (internalCutEmbedding N c) + 2 ≤
      logicalSiteCount d D N := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective (joiningPacketSites d D N c)
        (joiningPacketSites d D N c).injective
  let a := logicalSiteCount d D N -
    (2 * cutBondRegisterWidth d D N (internalCutEmbedding N c) + 2)
  have hn : a + (2 * cutBondRegisterWidth d D N (internalCutEmbedding N c) + 2) =
      logicalSiteCount d D N := by dsimp [a]; omega
  let e : Fin (2 * cutBondRegisterWidth d D N (internalCutEmbedding N c) + 2) ↪
      Fin (logicalSiteCount d D N) :=
    ⟨fun i ↦ Fin.cast hn (Fin.natAdd a i), by
      intro i j h
      apply Fin.ext
      have hv := congrArg Fin.val h
      simp only [Fin.val_cast, Fin.val_natAdd] at hv
      omega⟩
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_extending_pair e (joiningPacketSites d D N c)
    e.injective (joiningPacketSites d D N c).injective
  exact ⟨a, hn, τ, hτ⟩

end MPUCircuit
