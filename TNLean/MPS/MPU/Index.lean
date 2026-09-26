/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.AdjointSimpleContraction
import TNLean.MPS.MPU.CanonicalFormBlocking
import TNLean.MPS.MPU.SimpleTensorEquivalence
import TNLean.MPS.MPU.SourceIndexValue

/-!
# The index of a canonical-form-II matrix product unitary

For a positive simple blocking, the two source ranks satisfy
$r_k\ell_k=d^{2k}$. The source rank-growth bounds therefore imply that
$\frac12(\log_2 r_k-\log_2\ell_k)$ is independent of the blocking length.
The resulting index is also independent of the recorded canonical-form-II
presentation of the same tensor.

**Scope restriction (canonical representatives):** the tensor is already in
canonical form II. No equality of indices across a change of the ambient bond
dimension is asserted. The distinction from an arbitrary unreduced tensor is
recorded in `docs/paper-gaps/mpu_canonical_form_full_support.tex`.

**Local fix (rank-product exponent):** the source prints $d^k$ in the
rank-product calculation; the physical dimension after blocking is $d^k$, so
the product is $d^{2k}$. See
`docs/paper-gaps/mpu_blocking_rank_product_exponent.tex`.

## Main definitions

* `MPOTensor.IsMPUCanonicalFormII.index`: the base-two logarithmic MPU index.

## Main statements

* `MPOTensor.IsMPUCanonicalFormII.sourceIndexValue_eq_index`: every positive
  simple block computes the index.
* `MPOTensor.IsMPUCanonicalFormII.index_eq`: the recorded canonical-form-II
  presentation does not affect the value.
* `MPOTensor.IsMPUCanonicalFormII.index_blockTensor`: positive blocking
  preserves the index.
* `MPOTensor.IsMPUCanonicalFormII.index_physicalAdjointTensor`: physical
  adjunction reverses its sign.

## References

Cirac--Pérez-García--Schuch--Verstraete, arXiv:1703.09188,
Definition `def:index` and Proposition `index-well-defined`, lines 681--704.
-/

namespace MPOTensor

variable {d D : ℕ} {U : MPOTensor d D}

/-- The source-rank product of a positive simple block is the square of its
physical dimension. Source: arXiv:1703.09188, `ThmFund1` and the proof of
`index-well-defined`, lines 697--704. -/
theorem IsMPUCanonicalFormII.rightRank_mul_leftRank_blockTensor
    (hU : IsMPUCanonicalFormII U) {k : ℕ} (hk : 0 < k)
    (hS : IsMPUSimple (MPOTensor.blockTensor U k)) :
    r[MPOTensor.blockTensor U k] * ℓ[MPOTensor.blockTensor U k] = d ^ (2 * k) := by
  have hprod : r[MPOTensor.blockTensor U k] * ℓ[MPOTensor.blockTensor U k] =
      MPSTensor.blockPhysDim d k * MPSTensor.blockPhysDim d k :=
    ((hU.blockTensor k hk).isMPUSimple_tfae.out 0 1).mp hS
  simpa [MPSTensor.blockPhysDim, Kraus.blockPhysDim, pow_mul, pow_two, Nat.mul_comm] using hprod

private theorem sourceIndexValue_blockTensor_eq_of_le
    (hU : IsMPUCanonicalFormII U) {k₀ k : ℕ}
    (hk₀ : 0 < k₀) (hk : 0 < k) (hle : k₀ ≤ k)
    (hS₀ : IsMPUSimple (blockTensor U k₀)) (hS : IsMPUSimple (blockTensor U k))
    (hr₀ : 0 < r[blockTensor U k₀]) (hℓ₀ : 0 < ℓ[blockTensor U k₀])
    (hr : 0 < r[blockTensor U k]) (hℓ : 0 < ℓ[blockTensor U k]) :
    sourceIndexValue (blockTensor U k) hr hℓ =
      sourceIndexValue (blockTensor U k₀) hr₀ hℓ₀ := by
  exact sourceIndexValue_blockTensor_eq_of_products U hle
    (Nat.pos_of_ne_zero hU.neZero_phys.out)
    (hU.rightRank_mul_leftRank_blockTensor hk₀ hS₀)
    (hU.rightRank_mul_leftRank_blockTensor hk hS)

/-- Any two positive simple blocks give the same logarithmic source-index
value. No rank-product equality is supplied as a hypothesis.
Source: arXiv:1703.09188, Proposition `index-well-defined`, lines 690--704. -/
theorem IsMPUCanonicalFormII.sourceIndexValue_blockTensor_eq
    (hU : IsMPUCanonicalFormII U) {k₀ k : ℕ}
    (hk₀ : 0 < k₀) (hk : 0 < k)
    (hS₀ : IsMPUSimple (MPOTensor.blockTensor U k₀))
    (hS : IsMPUSimple (MPOTensor.blockTensor U k))
    (hr₀ : 0 < r[MPOTensor.blockTensor U k₀]) (hℓ₀ : 0 < ℓ[MPOTensor.blockTensor U k₀])
    (hr : 0 < r[MPOTensor.blockTensor U k]) (hℓ : 0 < ℓ[MPOTensor.blockTensor U k]) :
    sourceIndexValue (MPOTensor.blockTensor U k) hr hℓ =
      sourceIndexValue (MPOTensor.blockTensor U k₀) hr₀ hℓ₀ := by
  exact (le_total k₀ k).elim
    (fun hle => sourceIndexValue_blockTensor_eq_of_le hU hk₀ hk hle hS₀ hS hr₀ hℓ₀ hr hℓ)
    (fun hle => (sourceIndexValue_blockTensor_eq_of_le hU hk hk₀ hle hS hS₀ hr hℓ hr₀ hℓ₀).symm)

/-- Both source ranks of a positive simple block are positive.
Source: arXiv:1703.09188, `ThmFund1` and `def:index`, lines 681--688. -/
theorem IsMPUCanonicalFormII.sourceRanks_blockTensor_pos
    (hU : IsMPUCanonicalFormII U) {k : ℕ} (hk : 0 < k)
    (hS : IsMPUSimple (MPOTensor.blockTensor U k)) :
    0 < r[MPOTensor.blockTensor U k] ∧ 0 < ℓ[MPOTensor.blockTensor U k] := by
  exact ⟨Nat.pos_of_mul_pos_right ((hU.rightRank_mul_leftRank_blockTensor hk hS).symm ▸
    Nat.pow_pos (Nat.pos_of_ne_zero hU.neZero_phys.out)),
    Nat.pos_of_mul_pos_left ((hU.rightRank_mul_leftRank_blockTensor hk hS).symm ▸
    Nat.pow_pos (Nat.pos_of_ne_zero hU.neZero_phys.out))⟩

/-- The MPU index is computed from any positive simple block as
$\frac12(\log_2 r-\log_2\ell)$.
Source: arXiv:1703.09188, Definition `def:index`, lines 681--688. -/
noncomputable def IsMPUCanonicalFormII.index (hU : IsMPUCanonicalFormII U) : ℝ :=
  let p := hU.exists_sourceV_blockTensor_isIsometry.choose
  let hp := hU.exists_sourceV_blockTensor_isIsometry.choose_spec
  sourceIndexValue (MPOTensor.blockTensor U p)
    (hU.sourceRanks_blockTensor_pos hp.1 hp.2.2.1).1
    (hU.sourceRanks_blockTensor_pos hp.1 hp.2.2.1).2

/-- Every positive simple block computes the index, independently of its
length. Source: arXiv:1703.09188, Proposition `index-well-defined`, lines 690--704. -/
theorem IsMPUCanonicalFormII.sourceIndexValue_eq_index (hU : IsMPUCanonicalFormII U)
    {k : ℕ} (hk : 0 < k) (hS : IsMPUSimple (MPOTensor.blockTensor U k))
    (hr : 0 < r[MPOTensor.blockTensor U k]) (hℓ : 0 < ℓ[MPOTensor.blockTensor U k]) :
    sourceIndexValue (MPOTensor.blockTensor U k) hr hℓ = hU.index := by
  exact let hp := hU.exists_sourceV_blockTensor_isIsometry.choose_spec
    hU.sourceIndexValue_blockTensor_eq hp.1 hk hp.2.2.1 hS
      (hU.sourceRanks_blockTensor_pos hp.1 hp.2.2.1).1
      (hU.sourceRanks_blockTensor_pos hp.1 hp.2.2.1).2 hr hℓ

/-- The index is the half-difference of the base-two logarithms of the two
source ranks of any positive simple block. Rank positivity follows from the
canonical form and simplicity, and is not an additional hypothesis.
Source: arXiv:1703.09188, `def:index` and `index-well-defined`, lines 681--704. -/
theorem IsMPUCanonicalFormII.index_eq_logb_of_isMPUSimple_blockTensor
    (hU : IsMPUCanonicalFormII U) {k : ℕ} (hk : 0 < k)
    (hS : IsMPUSimple (MPOTensor.blockTensor U k)) :
    hU.index = (1 / 2 : ℝ) * (Real.logb 2 r[MPOTensor.blockTensor U k] -
      Real.logb 2 ℓ[MPOTensor.blockTensor U k]) := by
  exact (hU.sourceIndexValue_eq_index hk hS
    (hU.sourceRanks_blockTensor_pos hk hS).1
    (hU.sourceRanks_blockTensor_pos hk hS).2).symm

/-- Two canonical-form-II presentations of the same tensor give the same
index. This follows by computing both values at one simple block.
Source: arXiv:1703.09188, `def:index` and `index-well-defined`, lines 681--704. -/
theorem IsMPUCanonicalFormII.index_eq (hU hV : IsMPUCanonicalFormII U) :
    hU.index = hV.index := by
  exact let hp := hU.exists_sourceV_blockTensor_isIsometry.choose_spec
    let hr := hU.sourceRanks_blockTensor_pos hp.1 hp.2.2.1
    (hU.sourceIndexValue_eq_index hp.1 hp.2.2.1 hr.1 hr.2).symm.trans
      (hV.sourceIndexValue_eq_index hp.1 hp.2.2.1 hr.1 hr.2)

/-- Positive physical blocking preserves the index.
Source: arXiv:1703.09188, Proposition `index-well-defined`, lines 690--704. -/
theorem IsMPUCanonicalFormII.index_blockTensor (hU : IsMPUCanonicalFormII U)
    (p : ℕ) (hp : 0 < p) : (hU.blockTensor p hp).index = hU.index := by
  obtain ⟨k, hk, _, hS, _⟩ :=
    (hU.blockTensor p hp).exists_sourceV_blockTensor_isIsometry
  have hS' : IsMPUSimple (MPOTensor.blockTensor U (p * k)) := by
    simpa only [reindexPhysical_blockTensor_blockTensor] using
      hS.reindexPhysical (MPSTensor.directIteratedBlockEquiv d p k)
  rw [(hU.blockTensor p hp).index_eq_logb_of_isMPUSimple_blockTensor hk hS,
    hU.index_eq_logb_of_isMPUSimple_blockTensor (Nat.mul_pos hp hk) hS',
    ← reindexPhysical_blockTensor_blockTensor U p k,
    rightRank_reindexPhysical, leftRank_reindexPhysical]

/-- The right-rank expression for the index at any positive simple block.
Source: arXiv:1703.09188, the formulas following `def:index`, lines 686--688. -/
theorem IsMPUCanonicalFormII.index_eq_logb_rightRank_div
    (hU : IsMPUCanonicalFormII U) {k : ℕ} (hk : 0 < k)
    (hS : IsMPUSimple (MPOTensor.blockTensor U k)) :
    hU.index = Real.logb 2 ((r[MPOTensor.blockTensor U k] : ℝ) / (d ^ k : ℕ)) := by
  exact let hpos := hU.sourceRanks_blockTensor_pos hk hS
    (hU.sourceIndexValue_eq_index hk hS hpos.1 hpos.2).symm.trans
      (by
        simpa only [MPSTensor.blockPhysDim_eq_pow] using
          (sourceIndexValue_eq_logb_rightRank_div _ hpos.1 hpos.2
            (by simpa only [MPSTensor.blockPhysDim_eq_pow] using
              Nat.pow_pos (n := k) (Nat.pos_of_ne_zero hU.neZero_phys.out))
            (by simpa only [pow_two] using
              ((hU.blockTensor k hk).isMPUSimple_tfae.out 0 1).mp hS)))

/-- The left-rank expression for the index at any positive simple block.
Source: arXiv:1703.09188, the formulas following `def:index`, lines 686--688. -/
theorem IsMPUCanonicalFormII.index_eq_neg_logb_leftRank_div
    (hU : IsMPUCanonicalFormII U) {k : ℕ} (hk : 0 < k)
    (hS : IsMPUSimple (MPOTensor.blockTensor U k)) :
    hU.index = -Real.logb 2 ((ℓ[MPOTensor.blockTensor U k] : ℝ) / (d ^ k : ℕ)) := by
  exact let hpos := hU.sourceRanks_blockTensor_pos hk hS
    (hU.sourceIndexValue_eq_index hk hS hpos.1 hpos.2).symm.trans
      (by
        simpa only [MPSTensor.blockPhysDim_eq_pow] using
          (sourceIndexValue_eq_neg_logb_leftRank_div _ hpos.1 hpos.2
            (by simpa only [MPSTensor.blockPhysDim_eq_pow] using
              Nat.pow_pos (n := k) (Nat.pos_of_ne_zero hU.neZero_phys.out))
            (by simpa only [pow_two] using
              ((hU.blockTensor k hk).isMPUSimple_tfae.out 0 1).mp hS)))

/-- Physical adjunction reverses the sign of the index.
Source: arXiv:1703.09188, `def:index` and the time-reversal discussion,
lines 1196--1207. -/
theorem IsMPUCanonicalFormII.index_physicalAdjointTensor
    (hU : IsMPUCanonicalFormII U) : hU.physicalAdjointTensor.index = -hU.index := by
  obtain ⟨k, hk, _, hS, _⟩ := hU.exists_sourceV_blockTensor_isIsometry
  have hprod : r[MPOTensor.blockTensor U k] * ℓ[MPOTensor.blockTensor U k] =
      MPSTensor.blockPhysDim d k * MPSTensor.blockPhysDim d k :=
    ((hU.blockTensor k hk).isMPUSimple_tfae.out 0 1).mp hS
  have hSad : IsMPUSimple (MPOTensor.physicalAdjointTensor (MPOTensor.blockTensor U k)) :=
    (((hU.blockTensor k hk).physicalAdjointTensor).isMPUSimple_tfae.out 0 1).mpr
      (by simpa only [rightRank_physicalAdjointTensor, leftRank_physicalAdjointTensor,
        mul_comm] using hprod)
  rw [hU.index_eq_neg_logb_leftRank_div hk hS, neg_neg,
    hU.physicalAdjointTensor.index_eq_logb_rightRank_div hk
      (by simpa only [physicalAdjointTensor_blockTensor] using hSad),
    ← physicalAdjointTensor_blockTensor, rightRank_physicalAdjointTensor]

end MPOTensor
