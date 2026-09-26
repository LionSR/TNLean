/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.ScaledNormality
import TNLean.MPS.Core.ReductionExistence
import TNLean.MPS.CanonicalForm.NormalTensorGauge
import TNLean.MPS.FundamentalTheorem.Reduction.MPOProduct
import TNLean.MPS.MPU.CompositionRanks
import TNLean.MPS.MPU.RectangularSourceRanks
import TNLean.MPS.MPU.RepresentativeIndex

/-!
# Additivity of the matrix product unitary index under composition

After a common positive blocking, let the two input tensors be simple and
write their source ranks as $r,\ell$ and $r',\ell'$. The four-site composition
bounds give $r''\le d^2rr'$ and $\ell''\le d^2\ell\ell'$ for a reduced canonical
representative. Its rank product is $r''\ell''=d^8$, equal to the product of
the bounds. Both bounds are therefore equalities, and their common factor
cancels in the logarithmic index.

Rectangular reduction is used only to decrease source ranks. No equality
between the raw source ranks and the ranks of a reduced tensor is assumed.

## References

* CPSV17, arXiv:1703.09188, Theorem `IndexTh` (ii), lines 824–845.
-/

namespace MPOTensor

/-- The four-site composition rank bounds are equalities after reduction to a
simple canonical representative. CPSV17, arXiv:1703.09188, Theorem
`IndexTh` (ii), lines 830–845. -/
theorem IsMPUCanonicalFormII.compositionRanks_of_isReduction
    {d D₁ D₂ E : ℕ} {U : MPOTensor d D₁} {V : MPOTensor d D₂}
    {R : MPOTensor d E}
    (hU : IsMPUCanonicalFormII U) (hV : IsMPUCanonicalFormII V)
    (hR : IsMPUCanonicalFormII R)
    (hSU : IsMPUSimple U) (hSV : IsMPUSimple V)
    (hSR : IsMPUSimple (MPOTensor.blockTensor R 4))
    {A : Matrix (Fin E) (Fin (D₁ * D₂)) ℂ}
    {B : Matrix (Fin (D₁ * D₂)) (Fin E) ℂ}
    (hred : MPSTensor.IsReduction (mulTensor U V).toMPSTensor R.toMPSTensor A B) :
    r[MPOTensor.blockTensor R 4] = d ^ 2 * r[U] * r[V] ∧
      ℓ[MPOTensor.blockTensor R 4] = d ^ 2 * ℓ[U] * ℓ[V] := by
  apply eq_and_eq_of_pos_of_le_of_mul_le_mul
    (hR.sourceRanks_blockTensor_pos (by decide) hSR).1
    (hR.sourceRanks_blockTensor_pos (by decide) hSR).2
    ((rightRank_blockTensor_le_of_isReduction hred 4).trans
      (rightRank_blockTensor_mulTensor_four_le U V))
    ((leftRank_blockTensor_le_of_isReduction hred 4).trans
      (leftRank_blockTensor_mulTensor_four_le U V))
  rw [hR.rightRank_mul_leftRank_blockTensor (by decide) hSR]
  have hprod : d ^ 2 * r[U] * r[V] * (d ^ 2 * ℓ[U] * ℓ[V]) =
      d ^ 4 * (r[U] * ℓ[U]) * (r[V] * ℓ[V]) := by ring
  have hprodU : r[U] * ℓ[U] = d * d := (hU.isMPUSimple_tfae.out 1 2).mp hSU
  have hprodV : r[V] * ℓ[V] = d * d := (hV.isMPUSimple_tfae.out 1 2).mp hSV
  rw [hprod, hprodU, hprodV]
  exact le_of_eq (by ring)

/-- Equality of all positive-length periodic operators gives a rectangular
reduction to a canonical-form-II tensor. The target is normal after removing
the normalization scalar; apply the normal-target reduction theorem.
CPSV17, canonical-form discussion, lines 319–356. -/
theorem exists_isReduction_of_mpo_eq_cfii
    {d D E : ℕ} {U : MPOTensor d D} {V : MPOTensor d E}
    (hV : IsMPUCanonicalFormII V)
    (hEq : ∀ N : ℕ, 0 < N → mpo U N = mpo V N) :
    ∃ (A : Matrix (Fin E) (Fin D) ℂ)
      (B : Matrix (Fin D) (Fin E) ℂ),
      MPSTensor.IsReduction U.toMPSTensor V.toMPSTensor A B := by
  let _ : NeZero d := hV.neZero_phys
  let _ : NeZero E := hV.neZero_bond
  have hsqrt : (Real.sqrt d : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr (by exact_mod_cast NeZero.pos d)
  have hζ : ((Real.sqrt d : ℂ)⁻¹) ≠ 0 := inv_ne_zero hsqrt
  have hNormalNorm : Kraus.IsNormal V.normalizedFlattening :=
    hV.isNormalTensor_normalizedFlattening.isNormal
  have hNormalRaw : Kraus.IsNormal V.toMPSTensor := by
    apply (MPSTensor.isNormal_smul_iff hζ V.toMPSTensor).mp
    exact hNormalNorm
  have hSame : MPSTensor.SameMPV₂Pos U.toMPSTensor V.toMPSTensor := by
    intro N hN σ
    rw [mpv_toMPSTensor, mpv_toMPSTensor, hEq N hN]
  exact MPSTensor.exists_isReduction_of_isNormal_of_sameMPV₂Pos
    V.toMPSTensor U.toMPSTensor hNormalRaw hSame

/-- A canonical representative of a composition has the sum of the indices
of its canonical factors. CPSV17, arXiv:1703.09188, Theorem `IndexTh` (ii),
lines 830–845. -/
theorem IsMPUCanonicalFormII.index_eq_add_of_mpo_eq_mulTensor
    {d D₁ D₂ E : ℕ} {U : MPOTensor d D₁} {V : MPOTensor d D₂}
    {R : MPOTensor d E}
    (hU : IsMPUCanonicalFormII U) (hV : IsMPUCanonicalFormII V)
    (hR : IsMPUCanonicalFormII R)
    (hMpo : ∀ N : ℕ, 0 < N → mpo R N = mpo (mulTensor U V) N) :
    hR.index = hU.index + hV.index := by
  obtain ⟨A, B, hred⟩ := exists_isReduction_of_mpo_eq_cfii hR
    (fun N hN => (hMpo N hN).symm)
  obtain ⟨k, hcommon⟩ :=
    letI := hU.neZero_phys
    letI := hU.neZero_bond
    letI := hV.neZero_bond
    letI := hR.neZero_bond
    hU.isMPU.exists_common_blockTensor_isMPUSimple_three hV.isMPU hR.isMPU
  have hredK : MPSTensor.IsReduction
      (mulTensor (MPOTensor.blockTensor U k)
        (MPOTensor.blockTensor V k)).toMPSTensor
      (MPOTensor.blockTensor R k).toMPSTensor A B := by
    rw [← blockTensor_mulTensor]
    simpa only [toMPSTensor_blockTensor] using
      (hred.blockTensor k).reindexPhysical
        (blockedDoubledIndexEquiv d k)
  have hRanks := (hU.blockTensor k hcommon.1).compositionRanks_of_isReduction
    (hV.blockTensor k hcommon.1)
    (hR.blockTensor k hcommon.1)
    hcommon.2.1 hcommon.2.2.1
    (hcommon.2.2.2.blockTensor 4 (by decide)) hredK
  have hValue :=
    let hu := hU.sourceRanks_blockTensor_pos hcommon.1 hcommon.2.1
    let hv := hV.sourceRanks_blockTensor_pos hcommon.1 hcommon.2.2.1
    let hr := (hR.blockTensor k hcommon.1).sourceRanks_blockTensor_pos
      (by decide) (hcommon.2.2.2.blockTensor 4 (by decide))
    letI := (hU.blockTensor k hcommon.1).neZero_phys
    sourceIndexValue_eq_add_of_common_rank_product
      (MPOTensor.blockTensor U k)
      (MPOTensor.blockTensor V k)
      (MPOTensor.blockTensor (MPOTensor.blockTensor R k) 4)
      (MPSTensor.blockPhysDim d k ^ 2)
      (pow_pos (NeZero.pos _) _) hu.1 hu.2 hv.1 hv.2 hr.1 hr.2 hRanks.1 hRanks.2
  simpa only [
    (hR.blockTensor k hcommon.1).sourceIndexValue_eq_index
      (by decide) (hcommon.2.2.2.blockTensor 4 (by decide)),
    hR.index_blockTensor k hcommon.1,
    hU.sourceIndexValue_eq_index hcommon.1 hcommon.2.1,
    hV.sourceIndexValue_eq_index hcommon.1 hcommon.2.2.1] using hValue

/-- The index is additive under composition of positive-dimensional MPUs.
No choice of blocking length or canonical representative occurs in the
statement. CPSV17, arXiv:1703.09188, Theorem `IndexTh` (ii), lines 824–845. -/
theorem IsMPU.index_mulTensor
    {d D₁ D₂ : ℕ} [NeZero d] [NeZero D₁] [NeZero D₂]
    {U : MPOTensor d D₁} {V : MPOTensor d D₂}
    (hU : IsMPU U) (hV : IsMPU V) :
    (hU.mulTensor hV).index = hU.index + hV.index := by
  obtain ⟨E, hE, R, hR, _, hMpo⟩ :=
    (hU.mulTensor hV).exists_reduced_cfii_representative
  obtain ⟨⟨EU, _, Ured, hUred, _, hMpoU⟩, ⟨EV, _, Vred, hVred, _, hMpoV⟩⟩ :=
    And.intro hU.exists_reduced_cfii_representative hV.exists_reduced_cfii_representative
  rw [(hU.mulTensor hV).index_eq_canonical_representative hR hMpo,
    hU.index_eq_canonical_representative hUred hMpoU,
    hV.index_eq_canonical_representative hVred hMpoV]
  apply hUred.index_eq_add_of_mpo_eq_mulTensor hVred hR
  intro N hN
  rw [hMpo N hN, mpo_mulTensor, mpo_mulTensor, hMpoU N hN, hMpoV N hN]

end MPOTensor
