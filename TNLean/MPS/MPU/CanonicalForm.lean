/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.Definitions
import TNLean.MPS.MPU.ActiveTransferMultiplicity
import TNLean.MPS.CanonicalForm.Reduction

/-!
# Full-support CPSV canonical forms

This file isolates the minimal-support condition needed when a CPSV canonical-form
representative is used as an ambient tensor.

**Scope restriction (full-support irreducibility):** This module treats the
intended reduced canonical representative in the argument for arXiv:1703.09188,
Proposition `prop:normal-tensor`. The paper's canonical-form definition itself
permits displayed zero-weight blocks, and the formalization does not construct
the reduced representative obtained by omitting them. This module also does not
formalize the proposition's spectral derivation from `IsMPU`. See
`docs/paper-gaps/mpu_canonical_form_full_support.tex`.
-/

open scoped Matrix BigOperators Matrix.Norms.Operator

namespace MPSTensor

variable {d D : ℕ} {A : MPSTensor d D}

namespace CPSVCanonicalFormData

/-- The active CPSV blocks occupy the entire ambient bond space.

**Local fix (full active support):** This condition excludes both an ambient
zero complement and displayed inactive blocks. It describes the intended reduced
representative used in arXiv:1703.09188, Proposition `prop:normal-tensor`, lines
319--326 and 344--354, rather than every tensor satisfying the paper's literal
canonical-form definition. See
`docs/paper-gaps/mpu_canonical_form_full_support.tex`. -/
def HasFullActiveSupport (data : CPSVCanonicalFormData A) : Prop :=
  ∑ k : data.Active, data.dim k.1 = D

/-- Tensor irreducibility is invariant under simultaneous bond-index reindexing. -/
private theorem isIrreducibleTensor_reindexBond
    {n m : ℕ} (e : Fin n ≃ Fin m) (B : MPSTensor d n)
    (hB : IsIrreducibleTensor B) :
    IsIrreducibleTensor (fun i => Matrix.reindex e e (B i)) := by
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

/-- An active canonical-form block of ambient bond dimension makes the ambient tensor
irreducible.

**Scope restriction (full ambient block):** Proposition `prop:normal-tensor` of
arXiv:1703.09188, lines 344--354, is used for the intended reduced representative
after lines 319--326. The paper's canonical-form definition still permits
zero-weight displayed blocks; this theorem assumes the resulting ambient-dimensional
active block directly. See
`docs/paper-gaps/mpu_canonical_form_full_support.tex`. -/
theorem isIrreducibleTensor_of_active_dim_eq
    (data : CPSVCanonicalFormData A) (k : Fin data.r)
    (hk : data.weights k ≠ 0) (hDim : data.dim k = D) :
    IsIrreducibleTensor A := by
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
  letI : IsEmpty (Fin k) := ⟨fun x =>
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
  have hB : IsIrreducibleTensor B := by
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
  have hirr := isIrreducibleTensor_smul_conj B hB hUunit hk
  have hinv : U⁻¹ = Uᴴ := Matrix.inv_eq_left_inv (mul_eq_one_comm.mpr hUcois)
  convert hirr using 1
  funext i
  rw [hrec i, hinv, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]

/-- Full active support and a unique active block force ambient tensor irreducibility.

**Scope restriction (unique full-support active block):** This is the algebraic
irreducibility conclusion for the intended reduced representative in
arXiv:1703.09188, Proposition `prop:normal-tensor`, lines 344--354. The reduction
that omits displayed zero-weight blocks is not formalized here; see
`docs/paper-gaps/mpu_canonical_form_full_support.tex`. -/
theorem isIrreducibleTensor_of_card_active_eq_one_of_fullActiveSupport
    (data : CPSVCanonicalFormData A) (hcard : Fintype.card data.Active = 1)
    (hfull : data.HasFullActiveSupport) : IsIrreducibleTensor A := by
  classical
  letI : Unique data.Active :=
    Classical.choice (Fintype.card_eq_one_iff_nonempty_unique.mp hcard)
  let k : data.Active := default
  apply data.isIrreducibleTensor_of_active_dim_eq k.1 k.2
  have hsum : (∑ j : data.Active, data.dim j.1) = data.dim k.1 :=
    Fintype.sum_unique (fun j : data.Active => data.dim j.1)
  exact hsum.symm.trans hfull

/-- Combine the full-support one-active-block conclusion with supplied transfer-radius and
primitivity fields.

**Scope restriction (supplied spectral data):** The radius and primitivity fields
are the spectral conclusions of arXiv:1703.09188, Proposition
`prop:normal-tensor`, lines 349--354. The full-support premise describes the
intended reduced representative after lines 319--326; the reduction that omits
zero-weight displayed blocks is not formalized here. See
`docs/paper-gaps/mpu_canonical_form_full_support.tex`. -/
theorem isNormalTensor_of_card_active_eq_one_of_fullActiveSupport
    (data : CPSVCanonicalFormData A) (hcard : Fintype.card data.Active = 1)
    (hfull : data.HasFullActiveSupport)
    (hrad : spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
        (transferMap A)) = 1)
    (hprim : IsPrimitive (transferMap A)) : IsNormalTensor A where
  no_invariant_proj :=
    data.isIrreducibleTensor_of_card_active_eq_one_of_fullActiveSupport hcard hfull
  spectral_radius_one := hrad
  primitive_transfer := hprim

end CPSVCanonicalFormData

end MPSTensor
