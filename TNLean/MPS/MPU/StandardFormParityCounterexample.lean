/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.IdentityTensor
import TNLean.MPS.MPDO.SimpleScaling
import TNLean.MPS.MPU.Simple
import TNLean.MPS.MPU.SourceUV
import TNLean.MPS.MPU.TransferStabilizationConverse

/-!
# A parity obstruction for two-site standard forms

The bond-one identity tensor and its negative are both simple matrix product
unitaries. Their two-site blocks agree, but their periodic operators differ at
odd lengths. This is the formal parity witness for the unblocked all-length
reading of the converse in arXiv:1703.09188, Theorem `FundamentalMPU`, lines
619--648. The explicit source factors and local standard-form gauges are
calculated separately in `docs/paper-gaps/mpu_standard_form_parity_gap.tex`;
the theorem below does not assert those local relations from block equality
alone.

The second part of the module computes source factors of both tensors and
their gates (the chapter's Example 6.4). Both source cuts of the identity
tensor are the `2 × 2` identity up to the order of the product index, and those
of its negative are the negative identity, so all four source ranks are two.
With the factors $X_1=X_2=Y_1=Y_2=Z_1=Z_2=I$ for the identity tensor, and
$X_1=X_2=I$, $Y_1=Y_2=Z_1=Z_2=-I$ for its negative, both gates
$u=Y_2\mathbin{-}Y_1$ and $v=X_1\mathbin{-}X_2$ are the identity in their
displayed index orders. The paper-gap note puts the two minus signs on
$X_1,X_2$ instead; the gates are the identity for either choice.

## Main results

* `MPOTensor.exists_simple_blockTwo_eq_mpo_three_ne`: the parity witness, assembled from
  `isMPUSimple_parityIdentityTensor`, `isMPUSimple_parityNegativeIdentityTensor`,
  `blockTensor_parityNegativeIdentityTensor_two` and
  `mpo_parityNegativeIdentityTensor_three_ne`.
* `MPOTensor.parityIdentityTensor_exists_canonicalFormII`,
  `MPOTensor.parityNegativeIdentityTensor_exists_canonicalFormII`: both tensors are in
  canonical form II with fixed matrix `ρ = 1`.
* `MPOTensor.rightRank_parityIdentityTensor`, `MPOTensor.leftRank_parityIdentityTensor`,
  `MPOTensor.rightRank_parityNegativeIdentityTensor`,
  `MPOTensor.leftRank_parityNegativeIdentityTensor`: all four source ranks are two.
* `MPOTensor.parityIdentitySourceFactors`, `MPOTensor.parityNegativeSourceFactors`: the
  displayed source factors for the weight `ρ = 1`.
* `MPOTensor.sourceU_parityIdentity_apply`, `MPOTensor.sourceU_parityNegative_apply`,
  `MPOTensor.sourceV_parityIdentity_apply`, `MPOTensor.sourceV_parityNegative_apply`: both
  gates are the identity.
* `MPOTensor.sourceU_parity_eq`, `MPOTensor.sourceV_parity_eq`: the gates of the two tensors
  coincide entry by entry.
-/

open scoped Matrix ComplexOrder

namespace MPOTensor

/-- The bond-one identity tensor on `ℂ²`, the tensor `U = 1` of the chapter's Example 6.4 and
of `docs/paper-gaps/mpu_standard_form_parity_gap.tex`. -/
noncomputable def parityIdentityTensor : MPOTensor 2 1 := idTensor 2

/-- The negative `U' = -1` of the bond-one identity tensor on `ℂ²` (the chapter's Example 6.4
and `docs/paper-gaps/mpu_standard_form_parity_gap.tex`). -/
noncomputable def parityNegativeIdentityTensor : MPOTensor 2 1 :=
  (-1 : ℂ) • parityIdentityTensor

/-- The two-site blocks of the identity tensor and of its negative agree, since the sign
squares to one (the chapter's Example 6.4). -/
theorem blockTensor_parityNegativeIdentityTensor_two :
    blockTensor parityNegativeIdentityTensor 2 =
      blockTensor parityIdentityTensor 2 := by
  rw [parityNegativeIdentityTensor, blockTensor_smul]
  norm_num

private theorem parity_mpo_identity_three : mpo parityIdentityTensor 3 = 1 :=
  mpo_idTensor 2 3

private theorem parity_mpo_negative_three : mpo parityNegativeIdentityTensor 3 = -1 := by
  rw [parityNegativeIdentityTensor, mpo_smul, parity_mpo_identity_three]
  norm_num

/-- On three sites the periodic operators of the identity tensor and of its negative differ:
they are `1` and `-1` (the chapter's Example 6.4). -/
theorem mpo_parityNegativeIdentityTensor_three_ne :
    mpo parityNegativeIdentityTensor 3 ≠ mpo parityIdentityTensor 3 := by
  rw [parity_mpo_negative_three, parity_mpo_identity_three]
  intro h
  have h00 := congrArg
    (fun M : Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ =>
      M (fun _ => 0) (fun _ => 0)) h
  norm_num at h00

/-- The bond-one identity tensor is a simple matrix product unitary. -/
theorem isMPUSimple_parityIdentityTensor : IsMPUSimple parityIdentityTensor :=
  isMPUSimple_idTensor 2

private theorem parity_double_negative_eq_identity :
    doubleLayerTensor parityNegativeIdentityTensor =
      doubleLayerTensor parityIdentityTensor := by
  exact doubleLayerTensor_smul_of_star_mul_self (-1) parityIdentityTensor (by norm_num)

/-- The negative of the bond-one identity tensor is a simple matrix product unitary: its
double-layer tensor is that of the identity tensor. -/
theorem isMPUSimple_parityNegativeIdentityTensor :
    IsMPUSimple parityNegativeIdentityTensor := by
  obtain ⟨a, b, h₁, h₂⟩ := isMPUSimple_parityIdentityTensor
  refine ⟨a, b, ?_, ?_⟩
  · simpa only [parity_double_negative_eq_identity] using h₁
  · simpa only [parity_double_negative_eq_identity] using h₂

/-- Two simple MPUs of physical dimension two have identical two-site blocks
but different periodic operators at length three.

This is a parity witness for the unblocked all-length converse printed in
arXiv:1703.09188, Theorem `FundamentalMPU`, lines 624--648. Definition `SF`
at lines 619--622 instead defines the standard form of the two-site block.
The local source-factor relation for this example is calculated in
`docs/paper-gaps/mpu_standard_form_parity_gap.tex`; block equality alone is
not claimed to imply that relation. -/
theorem exists_simple_blockTwo_eq_mpo_three_ne :
    ∃ (A B : MPOTensor 2 1), IsMPUSimple A ∧ IsMPUSimple B ∧
      blockTensor A 2 = blockTensor B 2 ∧ mpo A 3 ≠ mpo B 3 := by
  refine ⟨parityIdentityTensor, parityNegativeIdentityTensor,
    isMPUSimple_parityIdentityTensor, isMPUSimple_parityNegativeIdentityTensor,
    blockTensor_parityNegativeIdentityTensor_two.symm, ?_⟩
  exact Ne.symm mpo_parityNegativeIdentityTensor_three_ne

/-! ### Source cuts, ranks, factors and gates -/

/-- The entries of the bond-one identity tensor. -/
theorem parityIdentityTensor_apply (i j : Fin 2) (α β : Fin 1) :
    parityIdentityTensor i j α β = if i = j then 1 else 0 := by
  obtain rfl := Subsingleton.elim α β
  by_cases h : i = j <;> simp [parityIdentityTensor, idTensor, h]

/-- The entries of the negative bond-one identity tensor. -/
theorem parityNegativeIdentityTensor_apply (i j : Fin 2) (α β : Fin 1) :
    parityNegativeIdentityTensor i j α β = -(if i = j then 1 else 0) := by
  by_cases h : i = j <;> simp [parityNegativeIdentityTensor, parityIdentityTensor_apply, h]

/-- The first source cut of the identity tensor is the identity, up to the order of the
column index (arXiv:1703.09188, lines 450--477). -/
theorem sourceCutM₁_parityIdentityTensor :
    sourceCutM₁ parityIdentityTensor =
      Matrix.reindex (Equiv.refl _) (Equiv.prodComm _ _) 1 := by
  ext ⟨i, β⟩ ⟨α, j⟩
  obtain rfl := Subsingleton.elim α β
  simp [parityIdentityTensor_apply, Matrix.one_apply]

/-- The second source cut of the identity tensor is the identity, up to the order of the
row index (arXiv:1703.09188, lines 450--477). -/
theorem sourceCutM₂_parityIdentityTensor :
    sourceCutM₂ parityIdentityTensor =
      Matrix.reindex (Equiv.prodComm _ _) (Equiv.refl _) 1 := by
  ext ⟨α, i⟩ ⟨j, β⟩
  obtain rfl := Subsingleton.elim α β
  simp [parityIdentityTensor_apply, Matrix.one_apply]

/-- The first source cut of the negative identity tensor is the negative identity, up to the
order of the column index (arXiv:1703.09188, lines 450--477). -/
theorem sourceCutM₁_parityNegativeIdentityTensor :
    sourceCutM₁ parityNegativeIdentityTensor =
      Matrix.reindex (Equiv.refl _) (Equiv.prodComm _ _) (-1) := by
  ext ⟨i, β⟩ ⟨α, j⟩
  obtain rfl := Subsingleton.elim α β
  simp [parityNegativeIdentityTensor_apply, Matrix.one_apply]

/-- The second source cut of the negative identity tensor is the negative identity, up to the
order of the row index (arXiv:1703.09188, lines 450--477). -/
theorem sourceCutM₂_parityNegativeIdentityTensor :
    sourceCutM₂ parityNegativeIdentityTensor =
      Matrix.reindex (Equiv.prodComm _ _) (Equiv.refl _) (-1) := by
  ext ⟨α, i⟩ ⟨j, β⟩
  obtain rfl := Subsingleton.elim α β
  simp [parityNegativeIdentityTensor_apply, Matrix.one_apply]

/-- The right source rank of the identity tensor is two (arXiv:1703.09188, definition
`defnrl`, lines 450--477; the chapter's Example 6.4). -/
theorem rightRank_parityIdentityTensor : r[parityIdentityTensor] = 2 := by
  rw [rightRank, sourceCutM₁_parityIdentityTensor, Matrix.rank_reindex, Matrix.rank_one]
  simp

/-- The left source rank of the identity tensor is two (arXiv:1703.09188, definition
`defnrl`, lines 450--477; the chapter's Example 6.4). -/
theorem leftRank_parityIdentityTensor : ℓ[parityIdentityTensor] = 2 := by
  rw [leftRank, sourceCutM₂_parityIdentityTensor, Matrix.rank_reindex, Matrix.rank_one]
  simp

/-- The right source rank of the negative identity tensor is two (arXiv:1703.09188, definition
`defnrl`, lines 450--477; the chapter's Example 6.4). -/
theorem rightRank_parityNegativeIdentityTensor : r[parityNegativeIdentityTensor] = 2 := by
  rw [rightRank, sourceCutM₁_parityNegativeIdentityTensor, Matrix.rank_reindex,
    Matrix.rank_of_isUnit (-1 : Matrix (Fin 2 × Fin 1) (Fin 2 × Fin 1) ℂ) isUnit_one.neg]
  simp

/-- The left source rank of the negative identity tensor is two (arXiv:1703.09188, definition
`defnrl`, lines 450--477; the chapter's Example 6.4). -/
theorem leftRank_parityNegativeIdentityTensor : ℓ[parityNegativeIdentityTensor] = 2 := by
  rw [leftRank, sourceCutM₂_parityNegativeIdentityTensor, Matrix.rank_reindex,
    Matrix.rank_of_isUnit (-1 : Matrix (Fin 2 × Fin 1) (Fin 2 × Fin 1) ℂ) isUnit_one.neg]
  simp

/-- The factor `δ_{q,i}` from the `(physical, virtual)` product index to a rank index, read
through the value of the rank index. -/
private def parityLegPV (n : ℕ) : Matrix (Fin 2 × Fin 1) (Fin n) ℂ :=
  fun p q ↦ if (q : ℕ) = (p.1 : ℕ) then 1 else 0

/-- The factor `δ_{q,i}` from the `(virtual, physical)` product index to a rank index, read
through the value of the rank index. -/
private def parityLegVP (n : ℕ) : Matrix (Fin 1 × Fin 2) (Fin n) ℂ :=
  fun p q ↦ if (q : ℕ) = (p.2 : ℕ) then 1 else 0

private theorem parityLegPV_mul_transpose {n : ℕ} (hn : n = 2) :
    parityLegPV n * (parityLegVP n)ᵀ =
      Matrix.reindex (Equiv.refl _) (Equiv.prodComm _ _) 1 := by
  subst hn
  ext ⟨i, β⟩ ⟨α, j⟩
  obtain rfl := Subsingleton.elim α β
  fin_cases i <;> fin_cases j <;>
    simp [parityLegPV, parityLegVP, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

private theorem parityLegVP_mul_transpose {n : ℕ} (hn : n = 2) :
    parityLegVP n * (parityLegPV n)ᵀ =
      Matrix.reindex (Equiv.prodComm _ _) (Equiv.refl _) 1 := by
  subst hn
  ext ⟨α, i⟩ ⟨j, β⟩
  obtain rfl := Subsingleton.elim α β
  fin_cases i <;> fin_cases j <;>
    simp [parityLegPV, parityLegVP, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

private theorem parityLegPV_conjTranspose_mul {n : ℕ} (hn : n = 2) :
    (parityLegPV n)ᴴ * parityLegPV n = 1 := by
  subst hn
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [parityLegPV, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

private theorem parityLegVP_conjTranspose_mul {n : ℕ} (hn : n = 2) :
    (parityLegVP n)ᴴ * parityLegVP n = 1 := by
  subst hn
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [parityLegVP, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

private theorem parityLegPV_transpose_mul {n : ℕ} (hn : n = 2) :
    (parityLegPV n)ᵀ * parityLegPV n = 1 := by
  subst hn
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [parityLegPV, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

private theorem parityLegVP_transpose_mul {n : ℕ} (hn : n = 2) :
    (parityLegVP n)ᵀ * parityLegVP n = 1 := by
  subst hn
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [parityLegVP, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

private theorem parity_sourceWeight_one :
    sourceWeight (d := 2) (1 : Matrix (Fin 1) (Fin 1) ℂ) = 1 :=
  Matrix.one_kronecker_one

/-- The displayed source factors of the identity tensor for the weight `ρ = 1`: all six factors
are the identity, $X_1=X_2=Y_1=Y_2=Z_1=Z_2=I$, with entries `δ_{q,i}` read through the value of
the rank index (arXiv:1703.09188, `eq:sf-svd`--`YZ=1`, lines 479--506; the chapter's
Example 6.4; `docs/paper-gaps/mpu_standard_form_parity_gap.tex`). -/
noncomputable def parityIdentitySourceFactors :
    SourceFactors parityIdentityTensor (1 : Matrix (Fin 1) (Fin 1) ℂ) where
  X₁ := parityLegPV _
  Y₁ := (parityLegVP _)ᵀ
  Z₁ := parityLegVP _
  X₂ := parityLegVP _
  Y₂ := (parityLegPV _)ᵀ
  Z₂ := parityLegPV _
  sourceCutM₁_eq := by
    rw [sourceCutM₁_parityIdentityTensor,
      parityLegPV_mul_transpose rightRank_parityIdentityTensor]
  sourceCutM₂_eq := by
    rw [sourceCutM₂_parityIdentityTensor,
      parityLegVP_mul_transpose leftRank_parityIdentityTensor]
  X₁_weighted_isometry := by
    rw [parity_sourceWeight_one, Matrix.mul_one,
      parityLegPV_conjTranspose_mul rightRank_parityIdentityTensor]
  X₂_isometry := parityLegVP_conjTranspose_mul leftRank_parityIdentityTensor
  Y₁_mul_Z₁ := parityLegVP_transpose_mul rightRank_parityIdentityTensor
  Y₂_mul_Z₂ := parityLegPV_transpose_mul leftRank_parityIdentityTensor

/-- The displayed source factors of the negative identity tensor for the weight `ρ = 1`:
$X_1=X_2=I$ and $Y_1=Y_2=Z_1=Z_2=-I$, with entries read through the value of the rank index
(arXiv:1703.09188, `eq:sf-svd`--`YZ=1`, lines 479--506; the chapter's Example 6.4). The
paper-gap note `docs/paper-gaps/mpu_standard_form_parity_gap.tex` places the two minus signs on
$X_1,X_2$ instead; both choices satisfy the six identities. -/
noncomputable def parityNegativeSourceFactors :
    SourceFactors parityNegativeIdentityTensor (1 : Matrix (Fin 1) (Fin 1) ℂ) where
  X₁ := parityLegPV _
  Y₁ := -(parityLegVP _)ᵀ
  Z₁ := -parityLegVP _
  X₂ := parityLegVP _
  Y₂ := -(parityLegPV _)ᵀ
  Z₂ := -parityLegPV _
  sourceCutM₁_eq := by
    rw [sourceCutM₁_parityNegativeIdentityTensor, Matrix.mul_neg,
      parityLegPV_mul_transpose rightRank_parityNegativeIdentityTensor]
    rfl
  sourceCutM₂_eq := by
    rw [sourceCutM₂_parityNegativeIdentityTensor, Matrix.mul_neg,
      parityLegVP_mul_transpose leftRank_parityNegativeIdentityTensor]
    rfl
  X₁_weighted_isometry := by
    rw [parity_sourceWeight_one, Matrix.mul_one,
      parityLegPV_conjTranspose_mul rightRank_parityNegativeIdentityTensor]
  X₂_isometry := parityLegVP_conjTranspose_mul leftRank_parityNegativeIdentityTensor
  Y₁_mul_Z₁ := by
    rw [Matrix.neg_mul, Matrix.mul_neg, neg_neg,
      parityLegVP_transpose_mul rightRank_parityNegativeIdentityTensor]
  Y₂_mul_Z₂ := by
    rw [Matrix.neg_mul, Matrix.mul_neg, neg_neg,
      parityLegPV_transpose_mul leftRank_parityNegativeIdentityTensor]

/-- The gate $u=Y_2\mathbin{-}Y_1$ of the identity tensor is the identity,
$u_{(l,r),(i_1,i_2)}=\delta_{li_1}\delta_{ri_2}$ (arXiv:1703.09188, equations `uuvv` and
`uu`, lines 532--543; the chapter's Example 6.4). -/
theorem sourceU_parityIdentity_apply (l : Fin ℓ[parityIdentityTensor])
    (r : Fin r[parityIdentityTensor]) (i₁ i₂ : Fin 2) :
    SourceFactors.sourceU parityIdentityTensor parityIdentitySourceFactors (l, r) (i₁, i₂) =
      if (l : ℕ) = (i₁ : ℕ) ∧ (r : ℕ) = (i₂ : ℕ) then 1 else 0 := by
  rw [SourceFactors.sourceU_apply, Fin.sum_univ_one]
  simp only [parityIdentitySourceFactors, parityLegPV, parityLegVP, Matrix.transpose_apply,
    ite_zero_mul_ite_zero, mul_one]

/-- The gate $u=Y_2\mathbin{-}Y_1$ of the negative identity tensor is the identity: the minus
signs of $Y_1$ and $Y_2$ cancel (arXiv:1703.09188, equations `uuvv` and `uu`, lines 532--543;
the chapter's Example 6.4). -/
theorem sourceU_parityNegative_apply (l : Fin ℓ[parityNegativeIdentityTensor])
    (r : Fin r[parityNegativeIdentityTensor]) (i₁ i₂ : Fin 2) :
    SourceFactors.sourceU parityNegativeIdentityTensor parityNegativeSourceFactors
        (l, r) (i₁, i₂) =
      if (l : ℕ) = (i₁ : ℕ) ∧ (r : ℕ) = (i₂ : ℕ) then 1 else 0 := by
  rw [SourceFactors.sourceU_apply, Fin.sum_univ_one]
  simp only [parityNegativeSourceFactors, parityLegPV, parityLegVP, Matrix.neg_apply,
    Matrix.transpose_apply, neg_mul_neg, ite_zero_mul_ite_zero, mul_one]

/-- The gate $v=X_1\mathbin{-}X_2$ of the identity tensor is the identity,
$v_{(j_1,j_2),(r,l)}=\delta_{j_1r}\delta_{j_2l}$ (arXiv:1703.09188, equations `uuvv` and
`vdagger`, lines 532--543; the chapter's Example 6.4). -/
theorem sourceV_parityIdentity_apply (j₁ j₂ : Fin 2) (r : Fin r[parityIdentityTensor])
    (l : Fin ℓ[parityIdentityTensor]) :
    SourceFactors.sourceV parityIdentityTensor parityIdentitySourceFactors (j₁, j₂) (r, l) =
      if (j₁ : ℕ) = (r : ℕ) ∧ (j₂ : ℕ) = (l : ℕ) then 1 else 0 := by
  rw [SourceFactors.sourceV_apply, Fin.sum_univ_one]
  simp only [parityIdentitySourceFactors, parityLegPV, parityLegVP, ite_zero_mul_ite_zero,
    mul_one]
  exact if_congr (and_congr eq_comm eq_comm) rfl rfl

/-- The gate $v=X_1\mathbin{-}X_2$ of the negative identity tensor is the identity
(arXiv:1703.09188, equations `uuvv` and `vdagger`, lines 532--543; the chapter's
Example 6.4). -/
theorem sourceV_parityNegative_apply (j₁ j₂ : Fin 2) (r : Fin r[parityNegativeIdentityTensor])
    (l : Fin ℓ[parityNegativeIdentityTensor]) :
    SourceFactors.sourceV parityNegativeIdentityTensor parityNegativeSourceFactors
        (j₁, j₂) (r, l) =
      if (j₁ : ℕ) = (r : ℕ) ∧ (j₂ : ℕ) = (l : ℕ) then 1 else 0 := by
  rw [SourceFactors.sourceV_apply, Fin.sum_univ_one]
  simp only [parityNegativeSourceFactors, parityLegPV, parityLegVP, ite_zero_mul_ite_zero,
    mul_one]
  exact if_congr (and_congr eq_comm eq_comm) rfl rfl

/-- **The gates `u` of the two parity tensors coincide** (the chapter's Example 6.4; the
coinciding-gates proposition of the M-C plan): at rank indices with equal values, the gates
$u=Y_2\mathbin{-}Y_1$ of the identity tensor and of its negative have equal entries. The rank
index types of the two tensors are distinct terms, so the comparison is made through the
values of the indices. -/
theorem sourceU_parity_eq (l : Fin ℓ[parityIdentityTensor]) (r : Fin r[parityIdentityTensor])
    (l' : Fin ℓ[parityNegativeIdentityTensor]) (r' : Fin r[parityNegativeIdentityTensor])
    (hl : (l : ℕ) = l') (hr : (r : ℕ) = r') (i₁ i₂ : Fin 2) :
    SourceFactors.sourceU parityIdentityTensor parityIdentitySourceFactors (l, r) (i₁, i₂) =
      SourceFactors.sourceU parityNegativeIdentityTensor parityNegativeSourceFactors
        (l', r') (i₁, i₂) := by
  rw [sourceU_parityIdentity_apply, sourceU_parityNegative_apply, hl, hr]

/-- **The gates `v` of the two parity tensors coincide** (the chapter's Example 6.4; the
coinciding-gates proposition of the M-C plan): at rank indices with equal values, the gates
$v=X_1\mathbin{-}X_2$ of the identity tensor and of its negative have equal entries. -/
theorem sourceV_parity_eq (j₁ j₂ : Fin 2) (r : Fin r[parityIdentityTensor])
    (l : Fin ℓ[parityIdentityTensor]) (r' : Fin r[parityNegativeIdentityTensor])
    (l' : Fin ℓ[parityNegativeIdentityTensor]) (hr : (r : ℕ) = r') (hl : (l : ℕ) = l') :
    SourceFactors.sourceV parityIdentityTensor parityIdentitySourceFactors (j₁, j₂) (r, l) =
      SourceFactors.sourceV parityNegativeIdentityTensor parityNegativeSourceFactors
        (j₁, j₂) (r', l') := by
  rw [sourceV_parityIdentity_apply, sourceV_parityNegative_apply, hl, hr]

/-! ### Canonical form II with `ρ = 1` -/

/-- At bond dimension one, the normalized transfer matrix of a matrix product unitary is the
rank-one matrix `|ρ)(1|` with `ρ = 1`. -/
private theorem transferMatrix_pow_one_eq_of_fin_one {U : MPOTensor 2 1} (hU : IsMPU U) :
    transferMatrix (Kraus.transferMap U.normalizedFlattening) ^ 1 =
      Matrix.vecMulVec (1 : Matrix (Fin 1) (Fin 1) ℂ).vec
        (1 : Matrix (Fin 1) (Fin 1) ℂ).vec := by
  rw [pow_one, hU.normalized_transfer_matrix_eq_one_fin_one]
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i
  fin_cases j
  fin_cases k
  fin_cases l
  simp [Matrix.vecMulVec_apply]

/-- The bond-one identity tensor is in canonical form II with fixed matrix `ρ = 1`
(arXiv:1703.09188, canonical form II, lines 269--281 and Proposition `prop:normal-tensor`,
lines 344--355; the chapter's Example 6.4). -/
theorem parityIdentityTensor_exists_canonicalFormII :
    ∃ h : IsMPUCanonicalFormII parityIdentityTensor, h.ρ = 1 := by
  have hU := isMPUSimple_parityIdentityTensor.isMPU
  exact hU.exists_canonicalFormII_of_supplied_transfer_power 1 Matrix.PosDef.one (by simp) 1
    (transferMatrix_pow_one_eq_of_fin_one hU)

/-- The negative of the bond-one identity tensor is in canonical form II with fixed matrix
`ρ = 1`: at bond dimension one the normalized transfer map is the identity, and does not see
the sign (arXiv:1703.09188, canonical form II, lines 269--281 and Proposition
`prop:normal-tensor`, lines 344--355; the chapter's Example 6.4). -/
theorem parityNegativeIdentityTensor_exists_canonicalFormII :
    ∃ h : IsMPUCanonicalFormII parityNegativeIdentityTensor, h.ρ = 1 := by
  have hU := isMPUSimple_parityNegativeIdentityTensor.isMPU
  exact hU.exists_canonicalFormII_of_supplied_transfer_power 1 Matrix.PosDef.one (by simp) 1
    (transferMatrix_pow_one_eq_of_fin_one hU)

end MPOTensor
