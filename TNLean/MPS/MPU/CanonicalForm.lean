/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.Peripheral.TransferMatrix
import TNLean.MPS.CanonicalForm.CPSVBlocking
import TNLean.MPS.CanonicalForm.CPSVPhysicalReindex
import TNLean.MPS.CanonicalForm.Reduction
import TNLean.MPS.MPDO.PhysicalBlocking
import TNLean.MPS.MPU.TransferMultiplicity
import TNLean.MPS.MPU.TransferMatrix

/-!
# Full-support CPSV canonical forms

This file isolates the minimal-support condition needed when a CPSV canonical-form
representative is used as an ambient tensor.

**Scope restriction (full-support irreducibility):** This module treats the
intended reduced canonical representative in the argument for arXiv:1703.09188,
Proposition `prop:normal-tensor`. The formalization does not construct the reduced
representative obtained by omitting the ambient zero complement. Consequently the
MPU normality capstone below assumes full support and does not claim bare
`IsMPU` implies ambient normality. See
`docs/paper-gaps/mpu_canonical_form_full_support.tex`.
-/

open scoped Matrix BigOperators Matrix.Norms.Operator Kraus

namespace MPSTensor

variable {d D : ℕ} {A : MPSTensor d D}

namespace CPSVCanonicalFormData

/-- The CPSV blocks occupy the entire ambient bond space.

**Local fix (full support):** This condition excludes an ambient zero complement. It
describes the intended reduced representative used in arXiv:1703.09188, Proposition
`prop:normal-tensor`, lines 319--326 and 344--354, rather than every tensor satisfying
the paper's literal canonical-form definition. See
`docs/paper-gaps/mpu_canonical_form_full_support.tex`. -/
def HasFullSupport (data : CPSVCanonicalFormData A) : Prop :=
  ∑ k, data.dim k = D

/-- Full support is preserved by blocking a positive number of sites.

Source: arXiv:1703.09188, Section II, lines 297--305, and Section III, line 356. -/
theorem hasFullSupport_blockTensor (data : CPSVCanonicalFormData A)
    (hfull : data.HasFullSupport) (p : ℕ) (hp : 0 < p) :
    (data.blockTensor p hp).HasFullSupport := by
  change ∑ k, data.dim k = D
  exact hfull

/-- Full support is unchanged by a bijective relabeling of the physical alphabet. -/
theorem hasFullSupport_reindexPhysical {d' : ℕ} (data : CPSVCanonicalFormData A)
    (hfull : data.HasFullSupport) (e : Fin d' ≃ Fin d) :
    (data.reindexPhysical e).HasFullSupport := by
  change ∑ k, data.dim k = D
  exact hfull

/-- Tensor irreducibility is invariant under simultaneous bond-index reindexing. -/
private theorem isIrreducibleTensor_reindexBond
    {n m : ℕ} (e : Fin n ≃ Fin m) (B : MPSTensor d n)
    (hB : Kraus.IsIrreducibleFamily B) :
    Kraus.IsIrreducibleFamily (fun i => Matrix.reindex e e (B i)) := by
  classical
  intro hHas
  apply hB
  rcases hHas with ⟨P, hP, hP0, hP1, hInv⟩
  let Q := Matrix.reindex e.symm e.symm P
  refine ⟨Q, ?_, ?_, ?_, ?_⟩
  · constructor
    · change (Matrix.reindex e.symm e.symm P)ᴴ = Matrix.reindex e.symm e.symm P
      rw [Matrix.conjTranspose_reindex]
      exact congrArg (Matrix.reindex e.symm e.symm) hP.1
    · change Matrix.reindex e.symm e.symm P * Matrix.reindex e.symm e.symm P =
        Matrix.reindex e.symm e.symm P
      change Matrix.reindexLinearEquiv ℂ ℂ e.symm e.symm P *
        Matrix.reindexLinearEquiv ℂ ℂ e.symm e.symm P =
        Matrix.reindexLinearEquiv ℂ ℂ e.symm e.symm P
      rw [Matrix.reindexLinearEquiv_mul]
      exact congrArg (Matrix.reindex e.symm e.symm) hP.2
  · intro hQ
    apply hP0
    simpa [Q] using congrArg (Matrix.reindex e e) hQ
  · intro hQ
    apply hP1
    simpa [Q] using congrArg (Matrix.reindex e e) hQ
  · intro i
    have h := congrArg (Matrix.reindex e.symm e.symm) (hInv i)
    change Matrix.reindexLinearEquiv ℂ ℂ e.symm e.symm
      ((1 - P) * Matrix.reindexLinearEquiv ℂ ℂ e e (B i) * P) = 0 at h
    change (Matrix.reindexRingEquiv ℂ e.symm)
      ((1 - P) * (Matrix.reindexRingEquiv ℂ e) (B i) * P) = 0 at h
    rw [map_mul, map_mul] at h
    have hone : (1 - P).submatrix e e = 1 - P.submatrix e e := by
      ext x y
      simp [Matrix.one_apply]
    have hone' : (Matrix.reindexRingEquiv ℂ e.symm) (1 - P) =
        1 - (Matrix.reindexRingEquiv ℂ e.symm) P := hone
    rw [hone'] at h
    simpa [Q] using h

/-- A canonical-form block of ambient bond dimension makes the ambient tensor
irreducible.

**Scope restriction (full ambient block):** Proposition `prop:normal-tensor` of
arXiv:1703.09188, lines 344--354, is used for the intended reduced representative
after lines 319--326. This theorem assumes the resulting ambient-dimensional
block directly. See
`docs/paper-gaps/mpu_canonical_form_full_support.tex`. -/
theorem isIrreducibleTensor_of_dim_eq
    (data : CPSVCanonicalFormData A) (k : Fin data.r) (hDim : data.dim k = D) :
    Kraus.IsIrreducibleFamily A := by
  classical
  have hsum : ∑ j : Fin data.r, data.dim j = D := by
    apply Nat.le_antisymm data.total_dim_le
    calc
      D = data.dim k := hDim.symm
      _ ≤ ∑ j : Fin data.r, data.dim j :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  have huniq : ∀ j : Fin data.r, j = k := by
    intro j
    by_contra hj
    have hle : data.dim k + data.dim j ≤ ∑ q : Fin data.r, data.dim q := by
      exact Finset.add_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
        (Finset.mem_univ j) (Ne.symm hj)
    have hjpos := data.dim_pos j
    omega
  have hkval : k.val = 0 := by
    let z : Fin data.r := ⟨0, Nat.zero_lt_of_lt k.isLt⟩
    exact congrArg Fin.val (huniq z).symm
  let : IsEmpty (Fin k) := ⟨fun x =>
    (Nat.not_lt_zero x.val (by simpa [hkval] using x.isLt)).elim⟩
  let eTotal : Fin (∑ j : Fin data.r, data.dim j) ≃ Fin D := finCongr hsum
  let eBlock : Fin (data.dim k) ≃ Fin D := finCongr hDim
  let U : Matrix (Fin D) (Fin D) ℂ :=
    data.ambient_coisometry.submatrix eTotal.symm (Equiv.refl _)
  let B : MPSTensor d D := fun i => Matrix.reindex eBlock eBlock (data.blocks k i)
  have hUcois : U * Uᴴ = 1 := by
    unfold U
    rw [Matrix.conjTranspose_submatrix]
    rw [Matrix.submatrix_mul_equiv data.ambient_coisometry
      data.ambient_coisometryᴴ eTotal.symm (Equiv.refl _) eTotal.symm]
    rw [data.coisometric]
    ext x y
    simp [Matrix.one_apply]
  have hUunit : IsUnit U := by
    have hUiso : Uᴴ * U = 1 := mul_eq_one_comm.mpr hUcois
    exact ⟨⟨U, Uᴴ, hUcois, hUiso⟩, rfl⟩
  have hB : Kraus.IsIrreducibleFamily B := by
    exact isIrreducibleTensor_reindexBond eBlock (data.blocks k)
      (data.blocks_normal k).no_invariant_proj
  have hassembled : ∀ i,
      Matrix.reindex eTotal eTotal
          (toTensorFromBlocks (d := d) data.weights data.blocks i) =
        data.weights k • B i := by
    intro i
    ext x y
    change Matrix.blockDiagonal' (fun q => data.weights q • data.blocks q i)
      (finSigmaFinEquiv.symm (eTotal.symm x))
      (finSigmaFinEquiv.symm (eTotal.symm y)) = _
    generalize hsxdef : finSigmaFinEquiv.symm (eTotal.symm x) = sx
    generalize hsydef : finSigmaFinEquiv.symm (eTotal.symm y) = sy
    rcases sx with ⟨sxj, sxi⟩
    rcases sy with ⟨syj, syi⟩
    have hsxj : sxj = k := huniq sxj
    have hsyj : syj = k := huniq syj
    subst sxj
    subst syj
    change Matrix.blockDiagonal' (fun q => data.weights q • data.blocks q i)
      ⟨k, sxi⟩ ⟨k, syi⟩ = _
    rw [Matrix.blockDiagonal'_apply_eq]
    simp only [Matrix.smul_apply, B, Matrix.reindex_apply]
    congr 2
    · apply Fin.ext
      have hxpair := finSigmaFinEquiv_apply (⟨k, sxi⟩ :
        (q : Fin data.r) × Fin (data.dim q))
      have hxinv := congrArg Fin.val (finSigmaFinEquiv.apply_symm_apply (eTotal.symm x))
      have hxcoord : sxi.val = (eTotal.symm x).val := by
        have hpair : (finSigmaFinEquiv (⟨k, sxi⟩ :
            (q : Fin data.r) × Fin (data.dim q))).val = (eTotal.symm x).val := by
          rw [← hsxdef]
          exact hxinv
        simpa [hkval] using hxpair.symm.trans hpair
      have hxTotal := congrArg Fin.val (eTotal.apply_symm_apply x)
      have hxBlock := congrArg Fin.val (eBlock.apply_symm_apply x)
      exact hxcoord.trans (hxTotal.trans hxBlock.symm)
    · apply Fin.ext
      have hypair := finSigmaFinEquiv_apply (⟨k, syi⟩ :
        (q : Fin data.r) × Fin (data.dim q))
      have hyinv := congrArg Fin.val (finSigmaFinEquiv.apply_symm_apply (eTotal.symm y))
      have hycoord : syi.val = (eTotal.symm y).val := by
        have hpair : (finSigmaFinEquiv (⟨k, syi⟩ :
            (q : Fin data.r) × Fin (data.dim q))).val = (eTotal.symm y).val := by
          rw [← hsydef]
          exact hyinv
        simpa [hkval] using hypair.symm.trans hpair
      have hyTotal := congrArg Fin.val (eTotal.apply_symm_apply y)
      have hyBlock := congrArg Fin.val (eBlock.apply_symm_apply y)
      exact hycoord.trans (hyTotal.trans hyBlock.symm)
  have hrec : ∀ i, A i = Uᴴ * (data.weights k • B i) * U := by
    intro i
    rw [data.reconstruct i, ← hassembled i]
    symm
    unfold U eTotal
    rw [Matrix.conjTranspose_submatrix]
    change data.ambient_coisometryᴴ.submatrix (Equiv.refl _) (finCongr hsum).symm *
      (toTensorFromBlocks data.weights data.blocks i).submatrix
        (finCongr hsum).symm (finCongr hsum).symm *
      data.ambient_coisometry.submatrix (finCongr hsum).symm (Equiv.refl _) = _
    rw [Matrix.submatrix_mul_equiv data.ambient_coisometryᴴ
      (toTensorFromBlocks data.weights data.blocks i) (Equiv.refl _) (finCongr hsum).symm
      (finCongr hsum).symm]
    rw [Matrix.submatrix_mul_equiv
      (data.ambient_coisometryᴴ * toTensorFromBlocks data.weights data.blocks i)
      data.ambient_coisometry (Equiv.refl _) (finCongr hsum).symm (Equiv.refl _)]
    simp
  have hirr := isIrreducibleTensor_smul_conj B hB hUunit (data.weights_ne_zero k)
  have hinv : U⁻¹ = Uᴴ := Matrix.inv_eq_left_inv (mul_eq_one_comm.mpr hUcois)
  convert hirr using 1
  funext i
  rw [hrec i, hinv, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]

/-- With a single block, every index equals the given one. -/
private theorem eq_of_r_eq_one (data : CPSVCanonicalFormData A) (hr : data.r = 1)
    (j k : Fin data.r) : j = k := by
  apply Fin.ext
  have := j.isLt
  have := k.isLt
  omega

/-- Under full support, the unique block has the ambient bond dimension. -/
theorem dim_eq_of_r_eq_one_of_fullSupport
    (data : CPSVCanonicalFormData A) (hr : data.r = 1)
    (hfull : data.HasFullSupport) (k : Fin data.r) :
    data.dim k = D := by
  have hsum : (∑ j, data.dim j) = data.dim k := by
    rw [Finset.sum_eq_single k]
    · intro j _ hj
      exact absurd (data.eq_of_r_eq_one hr j k) hj
    · intro h
      exact absurd (Finset.mem_univ k) h
  exact hsum.symm.trans hfull

/-- Under full support, the unique block inclusion is onto as well as isometric. -/
theorem ambientBlockInclusion_mul_conjTranspose_eq_one
    (data : CPSVCanonicalFormData A) (hr : data.r = 1)
    (hfull : data.HasFullSupport) (k : Fin data.r) :
    data.ambientBlockInclusion k * (data.ambientBlockInclusion k)ᴴ = 1 := by
  have hdim := data.dim_eq_of_r_eq_one_of_fullSupport hr hfull k
  have hcarddim : Fintype.card (Fin D) = Fintype.card (Fin (data.dim k)) := by
    simp [hdim]
  exact (Matrix.mul_eq_one_comm_of_card_eq
      (Fin D) (Fin (data.dim k)) ℂ
      (A := data.ambientBlockInclusion k)
      (B := (data.ambientBlockInclusion k)ᴴ) hcarddim).mpr
    (data.ambientBlockInclusion_conjTranspose_mul_self k)

/-- Full support and a unique block force ambient tensor irreducibility.

**Scope restriction (unique full-support block):** This is the algebraic
irreducibility conclusion for the intended reduced representative in
arXiv:1703.09188, Proposition `prop:normal-tensor`, lines 344--354. The reduction
that omits the ambient zero complement is not formalized here; see
`docs/paper-gaps/mpu_canonical_form_full_support.tex`. -/
theorem isIrreducibleTensor_of_r_eq_one_of_fullSupport
    (data : CPSVCanonicalFormData A) (hr : data.r = 1)
    (hfull : data.HasFullSupport) : Kraus.IsIrreducibleFamily A := by
  let k : Fin data.r := ⟨0, by omega⟩
  exact data.isIrreducibleTensor_of_dim_eq k
    (data.dim_eq_of_r_eq_one_of_fullSupport hr hfull k)

/-- Combine the full-support one-block conclusion with supplied transfer-radius and
primitivity fields.

**Scope restriction (supplied spectral data):** The radius and primitivity fields
are the spectral conclusions of arXiv:1703.09188, Proposition
`prop:normal-tensor`, lines 349--354. The full-support premise describes the
intended reduced representative after lines 319--326; the reduction that omits
the ambient zero complement is not formalized here. See
`docs/paper-gaps/mpu_canonical_form_full_support.tex`. -/
theorem isNormalTensor_of_r_eq_one_of_fullSupport
    (data : CPSVCanonicalFormData A) (hr : data.r = 1)
    (hfull : data.HasFullSupport)
    (hrad : spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
        (Kraus.transferMap A)) = 1)
    (hprim : IsPrimitive (Kraus.transferMap A)) : IsNormalTensor A where
  no_invariant_proj :=
    data.isIrreducibleTensor_of_r_eq_one_of_fullSupport hr hfull
  spectral_radius_one := hrad
  primitive_transfer := hprim

end CPSVCanonicalFormData

end MPSTensor

namespace MPOTensor

variable {d D : ℕ}

private theorem sqrt_blockPhysDim (d p : ℕ) :
    Real.sqrt (MPSTensor.blockPhysDim d p) = Real.sqrt d ^ p := by
  suffices Real.sqrt ((d ^ p : ℕ) : ℝ) = Real.sqrt d ^ p by
    simpa [MPSTensor.blockPhysDim] using this
  induction p with
  | zero => simp
  | succ p ih =>
      rw [pow_succ, Nat.cast_mul, Real.sqrt_mul (by positivity), ih]
      simp [pow_succ]

/-- Normalized MPO flattening commutes with physical blocking, up to the canonical equivalence
between a doubled blocked index and a block of doubled indices.

The identity holds for every blocking length; positivity is required only when it is used to
preserve the full support and normal blocks.

Source: arXiv:1703.09188, definition `blocking`, equation `MPUblock`, equation
`eq:transfer-op`, and line 356. -/
theorem normalizedFlattening_blockTensor (U : MPOTensor d D) (p : ℕ) :
    (MPOTensor.blockTensor U p).normalizedFlattening =
      Kraus.reindexPhysical (blockedDoubledIndexEquiv d p)
        (MPSTensor.blockTensor U.normalizedFlattening p) := by
  funext ij
  rw [normalizedFlattening, toMPSTensor_blockTensor]
  simp only [Kraus.reindexPhysical]
  simp only [MPSTensor.blockTensor]
  change _ = Kraus.evalWord
    (fun i => ((Real.sqrt d : ℂ)⁻¹) • U.toMPSTensor i) _
  rw [Kraus.evalWord_smul, MPSTensor.length_wordOfBlock]
  have hsqrtC : (Real.sqrt (MPSTensor.blockPhysDim d p) : ℂ) =
      (Real.sqrt d : ℂ) ^ p := by
    rw [sqrt_blockPhysDim]
    exact Complex.ofReal_pow _ _
  rw [hsqrtC, inv_pow]

/-- Construct canonical-form-II data for a positively blocked MPO normalized flattening.

The blocked MPS data are relabeled by `blockedDoubledIndexEquiv`, matching the index orientation in
`normalizedFlattening_blockTensor`.

Source: arXiv:1703.09188, Section II, lines 297--305, and Section III, line 356. -/
noncomputable def blockTensorCFIIData (U : MPOTensor d D)
    (data : MPSTensor.CPSVCanonicalFormIIData U.normalizedFlattening)
    (p : ℕ) (hp : 0 < p) :
    MPSTensor.CPSVCanonicalFormIIData (MPOTensor.blockTensor U p).normalizedFlattening := by
  rw [normalizedFlattening_blockTensor]
  exact (data.blockTensor p hp).reindexPhysical (blockedDoubledIndexEquiv d p)

/-- The normalized flattening of an MPU is normal when the chosen CPSV canonical-form
representative has full support.

**Scope restriction (full support):** Bare `IsMPU` does not imply normality for a
nonminimal ambient representative: adjoining a zero virtual direct summand preserves all
periodic operators but introduces a nontrivial invariant projection. This theorem treats
the intended reduced representative in arXiv:1703.09188, Proposition
`prop:normal-tensor`, lines 319--326 and 344--354, by requiring full support.
See `docs/paper-gaps/mpu_canonical_form_full_support.tex`. -/
theorem IsMPU.isNormalTensor_normalizedFlattening_of_cpsv
    [NeZero d] [NeZero D] {U : MPOTensor d D}
    (hU : U.IsMPU)
    (data : MPSTensor.CPSVCanonicalFormData U.normalizedFlattening)
    (hfull : data.HasFullSupport) :
    MPSTensor.IsNormalTensor U.normalizedFlattening := by
  have htrace : ∀ N : ℕ, 1 < N →
      Matrix.trace
        (transferMatrix (Kraus.transferMap U.normalizedFlattening) ^ N) = 1 :=
    fun _ hN => hU.trace_transferMatrix_normalizedFlattening_pow_eq_one hN
  have hr : data.r = 1 :=
    data.r_eq_one_of_shifted_transfer_trace htrace
  obtain ⟨hrad, hprim⟩ :=
    spectralRadius_eq_one_and_isPrimitive_of_transferMatrix_shifted_trace
      (Kraus.transferMap U.normalizedFlattening) htrace
  exact data.isNormalTensor_of_r_eq_one_of_fullSupport
    hr hfull hrad hprim

end MPOTensor
