/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Index
import TNLean.MPS.MPU.ReducedCanonicalRepresentative
import TNLean.MPS.MPU.VirtualUnitaryGauge
import TNLean.MPS.MPU.VirtualSandwich

/-!
# The index across matrix product unitary representatives

Equality of periodic operator families determines the source ranks of
full-support canonical-form-II representatives, even when their bond
dimensions are initially different. A common positive simple blocking
then determines one index for all such representatives.

For an arbitrary positive-dimensional matrix product unitary, the index
below is defined through a reduced canonical-form-II representative.
Choice independence is proved from equality of the positive-length
periodic operators. No equality of raw source ranks under rectangular
reduction is assumed.

**Scope restriction (representative index):** This definition agrees with
the canonical-form-II index of every reduced representative. Its equality
with a logarithmic formula using the unreduced tensor's own source cuts
is not asserted. See `docs/paper-gaps/mpu_canonical_form_full_support.tex`.

## References

* CPSV17, arXiv:1703.09188, Definition `def:index` and Proposition
  `index-well-defined` (lines 681–704), and the canonical-form discussion
  (lines 257–294, 319–356).
-/
open scoped Matrix

namespace MPOTensor

/-- Canonical-form-II tensors with equal periodic operators at every length
greater than one have equal right and left source-cut ranks, even when their
bond dimensions differ. The comparison uses the literal unitary virtual gauge.
CPSV17, lines 257–294 and 681–704. -/
theorem IsMPUCanonicalFormII.sourceRanks_eq_of_mpo_eq
    {d D₁ D₂ : ℕ} {U : MPOTensor d D₁} {V : MPOTensor d D₂}
    (hU : IsMPUCanonicalFormII U) (hV : IsMPUCanonicalFormII V)
    (hEq : ∀ N : ℕ, 1 < N → mpo U N = mpo V N) :
    r[V] = r[U] ∧ ℓ[V] = ℓ[U] := by
  obtain ⟨rfl, z, hG⟩ := hU.exists_unitary_virtual_gauge_of_mpo_eq hV hEq
  have hVeq : V = virtualSandwich (z : Matrix (Fin D₁) (Fin D₁) ℂ) U
      (z : Matrix (Fin D₁) (Fin D₁) ℂ)ᴴ :=
    funext fun i => funext fun j => hG i j
  rw [hVeq]
  exact ⟨rightRank_virtualSandwich _ U _ Unitary.isUnit_coe Unitary.isUnit_coe.star,
    leftRank_virtualSandwich _ U _ Unitary.isUnit_coe Unitary.isUnit_coe.star⟩

/-- The canonical-form-II source index depends only on the periodic operator
family, also across different bond dimensions. CPSV17, Definition IV.1 and
Proposition IV.2, lines 681–704. -/
theorem IsMPUCanonicalFormII.index_eq_of_mpo_eq
    {d D₁ D₂ : ℕ} {U : MPOTensor d D₁} {V : MPOTensor d D₂}
    (hU : IsMPUCanonicalFormII U) (hV : IsMPUCanonicalFormII V)
    (hEq : ∀ N : ℕ, 1 < N → mpo U N = mpo V N) :
    hU.index = hV.index := by
  let : NeZero d := hU.neZero_phys
  let : NeZero D₁ := hU.neZero_bond
  let : NeZero D₂ := hV.neZero_bond
  obtain ⟨k, hk, hSU', hSV'⟩ :=
    hU.isMPU.exists_common_blockTensor_isMPUSimple hV.isMPU
  have hEqBlock : ∀ N : ℕ, 1 < N →
      mpo (MPOTensor.blockTensor U k) N =
        mpo (MPOTensor.blockTensor V k) N := by
    intro N hN
    rw [mpo_blockTensor_eq_reindex, mpo_blockTensor_eq_reindex,
      hEq (N * k) (hN.trans_le (Nat.le_mul_of_pos_right N hk))]
  have hRanks := (hU.blockTensor k hk).sourceRanks_eq_of_mpo_eq
    (hV.blockTensor k hk) hEqBlock
  rw [hU.index_eq_logb_of_isMPUSimple_blockTensor hk hSU',
    hV.index_eq_logb_of_isMPUSimple_blockTensor hk hSV']
  rw [hRanks.1, hRanks.2]

/-- A positive-dimensional MPU has a reduced canonical-form-II representative
and hence an index value. CPSV17, canonical-form discussion, lines 319–356. -/
private theorem IsMPU.exists_canonical_index_value
    {d D : ℕ} [NeZero d] [NeZero D]
    {U : MPOTensor d D} (hU : IsMPU U) :
    ∃ i : ℝ, ∃ Dred : ℕ, 0 < Dred ∧
      ∃ Ured : MPOTensor d Dred,
        ∃ hred : IsMPUCanonicalFormII Ured,
          (∀ N : ℕ, 0 < N → mpo Ured N = mpo U N) ∧ i = hred.index := by
  obtain ⟨Dred, hDred, Ured, hred, _, hMpo⟩ :=
    hU.exists_reduced_cfii_representative
  exact ⟨hred.index, Dred, hDred, Ured, hred, hMpo, rfl⟩

/-- The index of a positive-dimensional matrix product unitary is the index
of a reduced canonical-form-II representative. This does not identify the
source-cut ranks of an unreduced presentation. CPSV17, Definition IV.1,
lines 681–688; see `docs/paper-gaps/mpu_canonical_form_full_support.tex`. -/
noncomputable def IsMPU.index
    {d D : ℕ} [NeZero d] [NeZero D]
    {U : MPOTensor d D} (hU : IsMPU U) : ℝ :=
  Classical.choose hU.exists_canonical_index_value

/-- Every reduced canonical-form-II representative with the same
positive-length periodic operators gives the chosen index. CPSV17,
Definition IV.1 and Proposition IV.2, lines 681–704. -/
theorem IsMPU.index_eq_canonical_representative
    {d D Dred : ℕ} [NeZero d] [NeZero D]
    {U : MPOTensor d D} (hU : IsMPU U)
    {Ured : MPOTensor d Dred} (hred : IsMPUCanonicalFormII Ured)
    (hMpo : ∀ N : ℕ, 0 < N → mpo Ured N = mpo U N) :
    hU.index = hred.index := by
  obtain ⟨Dchosen, _, Uch, hch, hMpoCh, hi⟩ :=
    Classical.choose_spec hU.exists_canonical_index_value
  change Classical.choose hU.exists_canonical_index_value = hred.index
  rw [hi]
  apply hch.index_eq_of_mpo_eq hred
  intro N hN
  rw [hMpoCh N (by omega), hMpo N (by omega)]

/-- Two positive-dimensional MPUs with equal periodic operators at every
length greater than one have the same representative-defined index,
independently of their bond dimensions. CPSV17, Definition IV.1 and
Proposition IV.2, lines 681–704. -/
theorem IsMPU.index_eq_of_mpo_eq
    {d D₁ D₂ : ℕ} [NeZero d] [NeZero D₁] [NeZero D₂]
    {U : MPOTensor d D₁} {V : MPOTensor d D₂}
    (hU : IsMPU U) (hV : IsMPU V)
    (hEq : ∀ N : ℕ, 1 < N → mpo U N = mpo V N) :
    hU.index = hV.index := by
  obtain ⟨DredU, _, Ured, hredU, hMpoU, hiU⟩ :=
    Classical.choose_spec hU.exists_canonical_index_value
  obtain ⟨DredV, _, Vred, hredV, hMpoV, hiV⟩ :=
    Classical.choose_spec hV.exists_canonical_index_value
  change Classical.choose hU.exists_canonical_index_value =
    Classical.choose hV.exists_canonical_index_value
  rw [hiU, hiV]
  apply hredU.index_eq_of_mpo_eq hredV
  intro N hN
  rw [hMpoU N (by omega), hEq N hN, ← hMpoV N (by omega)]

end MPOTensor
