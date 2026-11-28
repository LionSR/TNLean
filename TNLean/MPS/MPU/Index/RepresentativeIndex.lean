/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Index.Index
import TNLean.MPS.MPU.CanonicalForm.ReducedCanonicalRepresentative
import TNLean.MPS.MPU.CanonicalForm.VirtualUnitaryGauge
import TNLean.MPS.MPU.CanonicalForm.VirtualSandwich
import TNLean.MPS.MPU.Simple.SimpleSupportCompression

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

It also contains the following results.

* `MPOTensor.IsMPU.rightRank_mul_leftRank_of_isInjective_of_isMPUSimple`,
  `MPOTensor.IsMPU.index_eq_logb_of_isInjective_of_isMPUSimple`: source-cut ranks and the index of
  simple injective tensors.

## References

* CPSV17, arXiv:1703.09188, Definition `def:index` and Proposition
  `index-well-defined` (lines 681–704), and the canonical-form discussion
  (lines 257–294, 319–356).
* CPSV17, Theorem `FundamentalMPU` (Fundamental Theorem of MPU, lines
  624–652), for the unitary virtual gauge between canonical-form-II
  representatives with equal periodic operators.
* CPSV17, Proposition IV.5 (lines 786–812), for invariance of the source-cut
  ranks under an invertible virtual sandwich.

## Blocking and adjunction of the representative MPU index

The index of an arbitrary positive-dimensional matrix product unitary is
defined through a reduced canonical-form-II representative. Positive physical
blocking preserves this index, and physical adjunction reverses its sign.
Both statements descend from the corresponding canonical-form-II identities
through equality of the positive-length periodic operator families.

**Scope restriction (representative index):** No equality of the unreduced
tensor's own source-cut ranks with those of its reduced representative is
asserted. See `docs/paper-gaps/mpu_canonical_form_full_support.tex`.

### References

* CPSV17, arXiv:1703.09188, Proposition `index-well-defined`, lines 690–704.
* CPSV17, arXiv:1703.09188, physical-adjoint index discussion, lines 1196–1207.
-/

section RepresentativeIndex

section

open scoped Matrix

namespace MPOTensor

/-- Canonical-form-II tensors with equal periodic operators at every length
greater than one have equal right and left source-cut ranks, even when their
bond dimensions differ. The comparison uses the literal unitary virtual
gauge of CPSV17, Theorem `FundamentalMPU` (lines 624–652), and the
source-rank invariance under a virtual sandwich of CPSV17, Proposition IV.5
(lines 786–812). The notation `r`, `ℓ` is CPSV17, Definition `defnrl`
(line 475). -/
theorem IsMPUCanonicalFormII.sourceRanks_eq_of_mpo_eq
    {d D₁ D₂ : ℕ} {U : MPOTensor d D₁} {V : MPOTensor d D₂}
    (hU : IsMPUCanonicalFormII U) (hV : IsMPUCanonicalFormII V)
    (hEq : ∀ N : ℕ, 1 < N → mpo U N = mpo V N) :
    r[V] = r[U] ∧ ℓ[V] = ℓ[U] := by
  obtain ⟨rfl, z, hG⟩ := hU.exists_unitary_virtual_gauge_of_mpo_eq hV hEq
  have hVeq : V = virtualSandwich (z : Matrix (Fin D₁) (Fin D₁) ℂ) U
      (z : Matrix (Fin D₁) (Fin D₁) ℂ)ᴴ :=
    funext fun p => hG p.1 p.2
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
source-cut ranks of an unreduced presentation; for a tensor in canonical form,
`IsMPU.index_eq_logb_of_isMPUCanonicalForm` (IndexOfCanonicalForm.lean) computes the
index from the ranks of its own simple blockings. CPSV17, Definition IV.1,
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

end

section

namespace MPOTensor

/-- Positive physical blocking preserves the representative-defined index of
every positive-dimensional MPU. CPSV17, Proposition IV.2, lines 690–704. -/
theorem IsMPU.index_blockTensor
    {d D : ℕ} [NeZero d] [NeZero D] {U : MPOTensor d D}
    (hU : IsMPU U) (p : ℕ) (hp : 0 < p) :
    (hU.blockTensor p hp).index = hU.index := by
  let : NeZero (Kraus.blockPhysDim d p) := ⟨by
    rw [Kraus.blockPhysDim_eq_pow]
    exact pow_ne_zero p (NeZero.ne d)⟩
  obtain ⟨Dred, _, Ured, hred, _, hMpo⟩ :=
    hU.exists_reduced_cfii_representative
  calc
    (hU.blockTensor p hp).index = (hred.blockTensor p hp).index := by
      apply (hU.blockTensor p hp).index_eq_canonical_representative
      intro N hN
      rw [mpo_blockTensor_eq_reindex, mpo_blockTensor_eq_reindex]
      rw [hMpo (N * p) (Nat.mul_pos hN hp)]
    _ = hred.index := hred.index_blockTensor p hp
    _ = hU.index := (hU.index_eq_canonical_representative hred hMpo).symm

/-- Physical adjunction reverses the representative-defined index of every
positive-dimensional MPU. CPSV17, lines 1196–1207. -/
theorem IsMPU.index_physicalAdjointTensor
    {d D : ℕ} [NeZero d] [NeZero D] {U : MPOTensor d D}
    (hU : IsMPU U) :
    hU.physicalAdjointTensor.index = -hU.index := by
  obtain ⟨Dred, _, Ured, hred, _, hMpo⟩ :=
    hU.exists_reduced_cfii_representative
  calc
    hU.physicalAdjointTensor.index = hred.physicalAdjointTensor.index := by
      apply hU.physicalAdjointTensor.index_eq_canonical_representative
      intro N hN
      ext σ τ
      rw [mpo_physicalAdjointTensor, mpo_physicalAdjointTensor]
      rw [hMpo N hN]
    _ = -hred.index := hred.index_physicalAdjointTensor
    _ = -hU.index := congrArg Neg.neg (hU.index_eq_canonical_representative hred hMpo).symm

end MPOTensor

end

end RepresentativeIndex

section InjectiveSourceIndex

/-!
## Source-cut ranks and the index of simple injective tensors

For a simple injective matrix product unitary of physical dimension \(d\), the
two source-cut ranks satisfy \(r\ell=d^2\), and the index is
\(\frac12(\log_2 r-\log_2\ell)\). No canonical form is assumed for the original
tensor: injectivity forces its reduced canonical representative to have the
same bond dimension, and the resulting invertible bond similarity preserves
both source ranks and simplicity.

Source: arXiv:1703.09188, Theorem `ThmFund1` and Definition `def:index`,
lines 520--573 and 681--704; arXiv:2502.20257, lines 1403--1407 and 1547.
-/

namespace MPOTensor

variable {d D : ℕ}

private theorem canonical_index_eq_logb_of_isMPUSimple {U : MPOTensor d D}
    (hU : IsMPUCanonicalFormII U) (hS : IsMPUSimple U) :
    hU.index = (1 / 2 : ℝ) * (Real.logb 2 r[U] - Real.logb 2 ℓ[U]) := by
  have hS₁ : IsMPUSimple (blockTensor U 1) := by
    rw [blockTensor_one_eq_reindexPhysical]
    exact hS.reindexPhysical (Kraus.singleBlockEquiv d)
  rw [hU.index_eq_logb_of_isMPUSimple_blockTensor (by omega) hS₁,
    blockTensor_one_eq_reindexPhysical, rightRank_reindexPhysical,
    leftRank_reindexPhysical]

private theorem exists_cfii_simple_same_sourceRanks [NeZero d]
    {U : MPOTensor d D} (hU : IsMPU U)
    (hI : Kraus.IsInjective U) (hS : IsMPUSimple U) :
    ∃ V : MPOTensor d D, ∃ _hV : IsMPUCanonicalFormII V,
      IsMPUSimple V ∧ r[V] = r[U] ∧ ℓ[V] = ℓ[U] ∧
        ∀ N : ℕ, 0 < N → mpo V N = mpo U N := by
  obtain ⟨V, hV, X, hX, hMpo⟩ := hU.exists_cfii_representative_of_isInjective hI
  have hVeq : V = virtualSandwich (X : Matrix (Fin D) (Fin D) ℂ) U
      ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) :=
    funext fun p => hX p.1 p.2
  have hS' : IsMPUSimple V := by
    rw [hVeq]
    exact hS.rectangularSandwich _ _ (by simp)
  have hR : r[V] = r[U] := by
    rw [hVeq]
    exact rightRank_virtualSandwich _ U _ ⟨X, rfl⟩ ⟨X⁻¹, rfl⟩
  have hL : ℓ[V] = ℓ[U] := by
    rw [hVeq]
    exact leftRank_virtualSandwich _ U _ ⟨X, rfl⟩ ⟨X⁻¹, rfl⟩
  exact ⟨V, hV, hS', hR, hL, hMpo⟩

/-- The two source ranks of a simple injective matrix product unitary have
product equal to the square of the physical dimension. Canonical form is
obtained by an invertible bond similarity, rather than assumed for the given
tensor. Source: CPSV17, Theorem `ThmFund1`, lines 562--573; FBC25,
arXiv:2502.20257, lines 1403--1407 and 1547. -/
theorem IsMPU.rightRank_mul_leftRank_of_isInjective_of_isMPUSimple [NeZero d]
    {U : MPOTensor d D} (hU : IsMPU U)
    (hI : Kraus.IsInjective U) (hS : IsMPUSimple U) :
    r[U] * ℓ[U] = d ^ 2 := by
  obtain ⟨V, hV, hS', hR, hL, _⟩ := exists_cfii_simple_same_sourceRanks hU hI hS
  have hprod := (hV.isMPUSimple_tfae.out 1 2).mp hS'
  simpa only [hR, hL, pow_two] using hprod

/-- For a simple injective tensor, the representative-defined index is the
half-difference of the logarithms of its original source-cut ranks. No
canonical-form presentation of the original tensor is supplied. Source:
CPSV17, Definition `def:index` and Proposition `index-well-defined`,
lines 681--704; FBC25, arXiv:2502.20257, line 1547. -/
theorem IsMPU.index_eq_logb_of_isInjective_of_isMPUSimple [NeZero d] [NeZero D]
    {U : MPOTensor d D} (hU : IsMPU U)
    (hI : Kraus.IsInjective U) (hS : IsMPUSimple U) :
    hU.index = (1 / 2 : ℝ) * (Real.logb 2 r[U] - Real.logb 2 ℓ[U]) := by
  obtain ⟨V, hV, hS', hR, hL, hMpo⟩ := exists_cfii_simple_same_sourceRanks hU hI hS
  rw [hU.index_eq_canonical_representative hV hMpo,
    canonical_index_eq_logb_of_isMPUSimple hV hS', hR, hL]

end MPOTensor

end InjectiveSourceIndex
