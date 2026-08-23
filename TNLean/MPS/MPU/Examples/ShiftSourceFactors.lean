/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ComplexSqrt
import TNLean.MPS.MPU.Examples.ShiftSourceRanks
import TNLean.MPS.MPU.SourceUV

/-!
# Supplied source factors for the cyclic-shift examples

This module chooses the source factorizations used for the three shift families
in arXiv:1703.09188, equations `eq:SF_u1_u3`, `eq:uv2_U2`, and `eq:uv2_U3`
(lines 2009--2034).  The choices are explicit; none of the statements below
identifies these factors with the factors chosen by compact singular-value
decomposition.
-/

open scoped Matrix Kronecker BigOperators

namespace MPOTensor

private noncomputable def sourceSqrt (d : ℕ) : ℂ :=
  Real.sqrt d

private theorem sourceSqrt_ne_zero (d : ℕ) [NeZero d] : sourceSqrt d ≠ 0 := by
  unfold sourceSqrt
  exact Complex.ofReal_ne_zero.mpr <|
    Real.sqrt_ne_zero'.2 (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d))

private theorem sourceSqrt_sq (d : ℕ) : sourceSqrt d ^ 2 = (d : ℂ) := by
  exact Complex.ofReal_sqrt_sq d (by positivity)

private theorem sourceSqrt_inv_mul_nat_mul_inv (d : ℕ) [NeZero d] :
    (sourceSqrt d)⁻¹ * (d : ℂ) * (sourceSqrt d)⁻¹ = 1 := by
  rw [← sourceSqrt_sq]
  field_simp [sourceSqrt_ne_zero d]

private theorem nat_mul_sourceSqrt_inv_mul_inv (d : ℕ) [NeZero d] :
    (d : ℂ) * ((sourceSqrt d)⁻¹ * (sourceSqrt d)⁻¹) = 1 := by
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    sourceSqrt_inv_mul_nat_mul_inv d

private noncomputable def normalizedIdentityVec (d : ℕ) : Fin d × Fin d → ℂ :=
  (sourceSqrt d)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ).vec

private noncomputable def normalizedIdentityColumn (d : ℕ) :
    Matrix (Fin d × Fin d) (Fin 1) ℂ :=
  Matrix.replicateCol (Fin 1) (normalizedIdentityVec d)

private theorem identityVec_star_dotProduct_identityVec (d : ℕ) :
    star (1 : Matrix (Fin d) (Fin d) ℂ).vec ⬝ᵥ
        (1 : Matrix (Fin d) (Fin d) ℂ).vec = d := by
  rw [Matrix.star_vec_dotProduct_vec]
  simp

private theorem normalizedIdentityVec_star_dotProduct_normalizedIdentityVec
    (d : ℕ) [NeZero d] :
    star (normalizedIdentityVec d) ⬝ᵥ normalizedIdentityVec d = 1 := by
  rw [normalizedIdentityVec, star_smul, smul_dotProduct, dotProduct_smul,
    identityVec_star_dotProduct_identityVec]
  simp only [smul_eq_mul, star_inv₀]
  rw [show star (sourceSqrt d) = sourceSqrt d by simp [sourceSqrt]]
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    sourceSqrt_inv_mul_nat_mul_inv d

private theorem normalizedIdentityColumn_isIsometry (d : ℕ) [NeZero d] :
    (normalizedIdentityColumn d).IsIsometry := by
  rw [Matrix.IsIsometry, normalizedIdentityColumn,
    Matrix.conjTranspose_replicateCol]
  ext a b
  simp [normalizedIdentityVec_star_dotProduct_normalizedIdentityVec d,
    Matrix.one_apply, Subsingleton.elim a b]

private theorem normalizedIdentityColumn_mul_scaled_conjTranspose (d : ℕ)
    [NeZero d] :
    normalizedIdentityColumn d *
        ((d : ℂ) • (normalizedIdentityColumn d)ᴴ) =
      Matrix.vecMulVec (1 : Matrix (Fin d) (Fin d) ℂ).vec
        (1 : Matrix (Fin d) (Fin d) ℂ).vec := by
  ext ⟨a, b⟩ ⟨c, e⟩
  have hsstar : star (sourceSqrt d) = sourceSqrt d := by simp [sourceSqrt]
  by_cases hab : b = a <;> by_cases hce : e = c <;>
    simp [Matrix.mul_apply, normalizedIdentityColumn,
      normalizedIdentityVec, Matrix.vecMulVec_apply, Matrix.vec,
      hab, hce, hsstar, nat_mul_sourceSqrt_inv_mul_inv,
      mul_comm, mul_left_comm]

private theorem scaled_conjTranspose_mul_inverse_scaled_column (d : ℕ)
    [NeZero d] :
    ((d : ℂ) • (normalizedIdentityColumn d)ᴴ) *
        ((d : ℂ)⁻¹ • normalizedIdentityColumn d) = 1 := by
  calc
    ((d : ℂ) • (normalizedIdentityColumn d)ᴴ) *
        ((d : ℂ)⁻¹ • normalizedIdentityColumn d) =
        ((d : ℂ) * (d : ℂ)⁻¹) •
          ((normalizedIdentityColumn d)ᴴ * normalizedIdentityColumn d) := by
            simp [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    _ = 1 := by
      rw [mul_inv_cancel₀ (by exact_mod_cast NeZero.ne d)]
      simpa only [one_smul, Matrix.IsIsometry] using
        normalizedIdentityColumn_isIsometry d

/-- The product coordinates are the right source coordinates of the right shift.

Source: arXiv:1703.09188, lines 2009--2034. -/
noncomputable def rightShiftRightRankEquiv (d : ℕ) :
    Fin d × Fin d ≃ Fin r[rightShiftTensor d] :=
  finProdFinEquiv.trans (finCongr (rightRank_rightShiftTensor d).symm)

/-- The unique coordinate is the left source coordinate of the right shift.

Source: arXiv:1703.09188, lines 2009--2034. -/
noncomputable def rightShiftLeftRankEquiv (d : ℕ) [NeZero d] :
    Fin 1 ≃ Fin ℓ[rightShiftTensor d] :=
  finCongr (leftRank_rightShiftTensor d).symm

/-- The unique coordinate is the right source coordinate of the left shift.

Source: arXiv:1703.09188, lines 2009--2034. -/
noncomputable def leftShiftRightRankEquiv (d : ℕ) [NeZero d] :
    Fin 1 ≃ Fin r[leftShiftTensor d] :=
  finCongr (rightRank_leftShiftTensor d).symm

/-- The product coordinates are the left source coordinates of the left shift.

Source: arXiv:1703.09188, lines 2009--2034. -/
noncomputable def leftShiftLeftRankEquiv (d : ℕ) :
    Fin d × Fin d ≃ Fin ℓ[leftShiftTensor d] :=
  finProdFinEquiv.trans (finCongr (leftRank_leftShiftTensor d).symm)

/-- Remove the unique virtual coordinate from a source-cut row of the
bond-one identity tensor.

Source: arXiv:1703.09188, equation `eq:SF_u1_u3` (lines 2009--2016). -/
def identitySourceRowEquiv (d : ℕ) : Fin 1 × Fin d ≃ Fin d where
  toFun x := x.2
  invFun i := (0, i)
  left_inv x := by ext <;> simp
  right_inv _ := rfl

/-- Remove the unique virtual coordinate from a source-cut column of the
bond-one identity tensor.

Source: arXiv:1703.09188, equation `eq:SF_u1_u3` (lines 2009--2016). -/
def identitySourceColumnEquiv (d : ℕ) : Fin d × Fin 1 ≃ Fin d where
  toFun x := x.1
  invFun i := (i, 0)
  left_inv x := by ext <;> simp
  right_inv _ := rfl

@[simp] theorem identitySourceRowEquiv_apply (d : ℕ) (x : Fin 1 × Fin d) :
    identitySourceRowEquiv d x = x.2 := rfl

@[simp] theorem identitySourceRowEquiv_symm_apply (d : ℕ) (i : Fin d) :
    (identitySourceRowEquiv d).symm i = (0, i) := rfl

@[simp] theorem identitySourceColumnEquiv_apply (d : ℕ) (x : Fin d × Fin 1) :
    identitySourceColumnEquiv d x = x.1 := rfl

@[simp] theorem identitySourceColumnEquiv_symm_apply (d : ℕ) (i : Fin d) :
    (identitySourceColumnEquiv d).symm i = (i, 0) := rfl

/-- Both source cuts of the bond-one identity tensor are the identity after
removing their unique virtual coordinates.

Source: arXiv:1703.09188, equation `eq:SF_u1_u3` (lines 2009--2016). -/
theorem sourceCutM₁_identityMPUTensor (d : ℕ) :
    sourceCutM₁ (identityMPUTensor d) =
      Matrix.reindex (identitySourceRowEquiv d).symm
        (identitySourceColumnEquiv d).symm
        (1 : Matrix (Fin d) (Fin d) ℂ) := by
  ext ⟨α, j⟩ ⟨i, β⟩
  have hαβ : α = β := Subsingleton.elim _ _
  by_cases hij : i = j
  · simp [sourceCutM₁, identityMPUTensor, idTensor, Matrix.reindex_apply,
      Matrix.one_apply, hij, hαβ]
  · have hji : j ≠ i := Ne.symm hij
    simp [sourceCutM₁, identityMPUTensor, idTensor, Matrix.reindex_apply,
      Matrix.one_apply, hij, hji, hαβ]

/-- The second source cut of the bond-one identity tensor is the same
reindexed identity as its first source cut.

Source: arXiv:1703.09188, equation `eq:SF_u1_u3` (lines 2009--2016). -/
theorem sourceCutM₂_identityMPUTensor (d : ℕ) :
    sourceCutM₂ (identityMPUTensor d) =
      Matrix.reindex (identitySourceRowEquiv d).symm
        (identitySourceColumnEquiv d).symm
        (1 : Matrix (Fin d) (Fin d) ℂ) := by
  ext ⟨α, i⟩ ⟨j, β⟩
  have hαβ : α = β := Subsingleton.elim _ _
  by_cases hij : i = j <;>
    simp [sourceCutM₂, identityMPUTensor, idTensor, Matrix.reindex_apply,
      Matrix.one_apply, hij, hαβ]

/-- The right source rank of the bond-one identity tensor is its physical
dimension.

Source: arXiv:1703.09188, equation `eq:SF_u1_u3` (lines 2009--2016). -/
theorem rightRank_identityMPUTensor (d : ℕ) :
    r[identityMPUTensor d] = d := by
  rw [rightRank, sourceCutM₁_identityMPUTensor, Matrix.rank_reindex,
    Matrix.rank_one]
  simp

/-- The left source rank of the bond-one identity tensor is its physical
dimension.

Source: arXiv:1703.09188, equation `eq:SF_u1_u3` (lines 2009--2016). -/
theorem leftRank_identityMPUTensor (d : ℕ) :
    ℓ[identityMPUTensor d] = d := by
  rw [leftRank, sourceCutM₂_identityMPUTensor, Matrix.rank_reindex,
    Matrix.rank_one]
  simp

/-- Physical coordinates are the right source coordinates of the bond-one
identity tensor.

Source: arXiv:1703.09188, equation `eq:SF_u1_u3` (lines 2009--2016). -/
noncomputable def identityRightRankEquiv (d : ℕ) :
    Fin d ≃ Fin r[identityMPUTensor d] :=
  finCongr (rightRank_identityMPUTensor d).symm

/-- Physical coordinates are the left source coordinates of the bond-one
identity tensor.

Source: arXiv:1703.09188, equation `eq:SF_u1_u3` (lines 2009--2016). -/
noncomputable def identityLeftRankEquiv (d : ℕ) :
    Fin d ≃ Fin ℓ[identityMPUTensor d] :=
  finCongr (leftRank_identityMPUTensor d).symm

/-- Explicit supplied source factors for the bond-one identity tensor.

Both cuts are transported identity matrices.  This is the building block for
$u_1=v_1=\Id\otimes\Id$ in arXiv:1703.09188, equation
`eq:SF_u1_u3` (lines 2009--2016). -/
noncomputable def identitySourceFactors (d : ℕ) :
    SourceFactors (identityMPUTensor d) (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  let eRow := identitySourceRowEquiv d
  let eCol := identitySourceColumnEquiv d
  let eR := identityRightRankEquiv d
  let eL := identityLeftRankEquiv d
  let X₁ : Matrix (Fin 1 × Fin d) (Fin r[identityMPUTensor d]) ℂ :=
    Matrix.reindex eRow.symm eR (1 : Matrix (Fin d) (Fin d) ℂ)
  let Y₁ : Matrix (Fin r[identityMPUTensor d]) (Fin d × Fin 1) ℂ :=
    Matrix.reindex eR eCol.symm (1 : Matrix (Fin d) (Fin d) ℂ)
  let Z₁ : Matrix (Fin d × Fin 1) (Fin r[identityMPUTensor d]) ℂ :=
    Matrix.reindex eCol.symm eR (1 : Matrix (Fin d) (Fin d) ℂ)
  let X₂ : Matrix (Fin 1 × Fin d) (Fin ℓ[identityMPUTensor d]) ℂ :=
    Matrix.reindex eRow.symm eL (1 : Matrix (Fin d) (Fin d) ℂ)
  let Y₂ : Matrix (Fin ℓ[identityMPUTensor d]) (Fin d × Fin 1) ℂ :=
    Matrix.reindex eL eCol.symm (1 : Matrix (Fin d) (Fin d) ℂ)
  let Z₂ : Matrix (Fin d × Fin 1) (Fin ℓ[identityMPUTensor d]) ℂ :=
    Matrix.reindex eCol.symm eL (1 : Matrix (Fin d) (Fin d) ℂ)
  have hone : (1 : Matrix (Fin d) (Fin d) ℂ).IsUnitaryBetween :=
    ⟨by simp [Matrix.IsIsometry], by simp [Matrix.IsCoisometry]⟩
  have hX₁ : X₁.IsUnitaryBetween :=
    Matrix.IsUnitaryBetween.reindex _ hone eRow.symm eR
  have hX₂ : X₂.IsUnitaryBetween :=
    Matrix.IsUnitaryBetween.reindex _ hone eRow.symm eL
  have hcut₁ : sourceCutM₁ (identityMPUTensor d) = X₁ * Y₁ := by
    rw [sourceCutM₁_identityMPUTensor]
    change Matrix.reindexLinearEquiv ℂ ℂ eRow.symm eCol.symm 1 =
      Matrix.reindexLinearEquiv ℂ ℂ eRow.symm eR 1 *
        Matrix.reindexLinearEquiv ℂ ℂ eR eCol.symm 1
    rw [Matrix.reindexLinearEquiv_mul ℂ ℂ eRow.symm eR eCol.symm,
      Matrix.one_mul]
  have hcut₂ : sourceCutM₂ (identityMPUTensor d) = X₂ * Y₂ := by
    rw [sourceCutM₂_identityMPUTensor]
    change Matrix.reindexLinearEquiv ℂ ℂ eRow.symm eCol.symm 1 =
      Matrix.reindexLinearEquiv ℂ ℂ eRow.symm eL 1 *
        Matrix.reindexLinearEquiv ℂ ℂ eL eCol.symm 1
    rw [Matrix.reindexLinearEquiv_mul ℂ ℂ eRow.symm eL eCol.symm,
      Matrix.one_mul]
  have hweighted : X₁ᴴ * sourceWeight (d := d)
      (1 : Matrix (Fin 1) (Fin 1) ℂ) * X₁ = 1 := by
    rw [show sourceWeight (d := d) (1 : Matrix (Fin 1) (Fin 1) ℂ) = 1 by
      simp [sourceWeight]]
    simpa [Matrix.IsIsometry] using hX₁.1
  have hY₁Z₁ : Y₁ * Z₁ = 1 := by
    change Matrix.reindexLinearEquiv ℂ ℂ eR eCol.symm 1 *
        Matrix.reindexLinearEquiv ℂ ℂ eCol.symm eR 1 = 1
    rw [Matrix.reindexLinearEquiv_mul ℂ ℂ eR eCol.symm eR,
      Matrix.one_mul, Matrix.reindexLinearEquiv_one]
  have hY₂Z₂ : Y₂ * Z₂ = 1 := by
    change Matrix.reindexLinearEquiv ℂ ℂ eL eCol.symm 1 *
        Matrix.reindexLinearEquiv ℂ ℂ eCol.symm eL 1 = 1
    rw [Matrix.reindexLinearEquiv_mul ℂ ℂ eL eCol.symm eL,
      Matrix.one_mul, Matrix.reindexLinearEquiv_one]
  exact ⟨X₁, Y₁, Z₁, X₂, Y₂, Z₂, hcut₁, hcut₂,
    hweighted, hX₂.1, hY₁Z₁, hY₂Z₂⟩

/-- Explicit supplied source factors for the right-shift tensor.

The first cut is the identity in the coordinates `rightShiftRightRankEquiv`.
The second cut uses the normalized vectorization of the identity matrix.  This
is the elementary right-shift factorization used in arXiv:1703.09188,
equations `eq:SF_u1_u3`, `eq:uv2_U2`, and `eq:uv2_U3` (lines 2009--2034). -/
noncomputable def rightShiftSourceFactors (d : ℕ) [NeZero d] :
    SourceFactors (rightShiftTensor d) (1 : Matrix (Fin d) (Fin d) ℂ) := by
  let eR := rightShiftRightRankEquiv d
  let eL := rightShiftLeftRankEquiv d
  let P : Matrix (Fin d × Fin d) (Fin r[rightShiftTensor d]) ℂ :=
    Matrix.reindex (Equiv.refl _) eR (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
  let C : Matrix (Fin d × Fin d) (Fin ℓ[rightShiftTensor d]) ℂ :=
    Matrix.reindex (Equiv.refl _) eL (normalizedIdentityColumn d)
  let R : Matrix (Fin ℓ[rightShiftTensor d]) (Fin d × Fin d) ℂ :=
    Matrix.reindex eL (Equiv.refl _)
      ((d : ℂ) • (normalizedIdentityColumn d)ᴴ)
  let Z : Matrix (Fin d × Fin d) (Fin ℓ[rightShiftTensor d]) ℂ :=
    Matrix.reindex (Equiv.refl _) eL
      ((d : ℂ)⁻¹ • normalizedIdentityColumn d)
  have hP : P.IsUnitaryBetween := by
    apply Matrix.IsUnitaryBetween.reindex
    exact ⟨by simp [Matrix.IsIsometry], by simp [Matrix.IsCoisometry]⟩
  have hC : C.IsIsometry := by
    exact Matrix.IsIsometry.reindex _ (normalizedIdentityColumn_isIsometry d)
      (Equiv.refl _) eL
  have hcut₁ : sourceCutM₁ (rightShiftTensor d) = P * Pᴴ := by
    rw [sourceCutM₁_rightShiftTensor]
    exact hP.2.symm
  have hcut₂ : sourceCutM₂ (rightShiftTensor d) = C * R := by
    rw [sourceCutM₂_rightShiftTensor]
    change _ =
      Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) eL (normalizedIdentityColumn d) *
        Matrix.reindexLinearEquiv ℂ ℂ eL (Equiv.refl _)
          ((d : ℂ) • (normalizedIdentityColumn d)ᴴ)
    rw [Matrix.reindexLinearEquiv_mul ℂ ℂ (Equiv.refl _) eL (Equiv.refl _),
      normalizedIdentityColumn_mul_scaled_conjTranspose d]
    rfl
  have hweighted : Pᴴ * sourceWeight (d := d)
      (1 : Matrix (Fin d) (Fin d) ℂ) * P = 1 := by
    rw [show sourceWeight (d := d) (1 : Matrix (Fin d) (Fin d) ℂ) = 1 by
      simp [sourceWeight]]
    simpa [Matrix.IsIsometry] using hP.1
  have hRZ : R * Z = 1 := by
    change
      Matrix.reindexLinearEquiv ℂ ℂ eL (Equiv.refl _)
          ((d : ℂ) • (normalizedIdentityColumn d)ᴴ) *
        Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) eL
          ((d : ℂ)⁻¹ • normalizedIdentityColumn d) = 1
    rw [Matrix.reindexLinearEquiv_mul ℂ ℂ eL (Equiv.refl _) eL,
      scaled_conjTranspose_mul_inverse_scaled_column d,
      Matrix.reindexLinearEquiv_one]
  exact ⟨P, Pᴴ, P, C, R, Z, hcut₁, hcut₂, hweighted, hC,
    hP.1, hRZ⟩

/-- Explicit supplied source factors for the left-shift tensor.

The first cut uses the normalized vectorization of the identity matrix.  The
second cut is the identity in the coordinates `leftShiftLeftRankEquiv`.  This
is the elementary left-shift factorization used in arXiv:1703.09188,
equations `eq:SF_u1_u3`, `eq:uv2_U2`, and `eq:uv2_U3` (lines 2009--2034). -/
noncomputable def leftShiftSourceFactors (d : ℕ) [NeZero d] :
    SourceFactors (leftShiftTensor d) (1 : Matrix (Fin d) (Fin d) ℂ) := by
  let eR := leftShiftRightRankEquiv d
  let eL := leftShiftLeftRankEquiv d
  let C : Matrix (Fin d × Fin d) (Fin r[leftShiftTensor d]) ℂ :=
    Matrix.reindex (Equiv.refl _) eR (normalizedIdentityColumn d)
  let R : Matrix (Fin r[leftShiftTensor d]) (Fin d × Fin d) ℂ :=
    Matrix.reindex eR (Equiv.refl _)
      ((d : ℂ) • (normalizedIdentityColumn d)ᴴ)
  let Z : Matrix (Fin d × Fin d) (Fin r[leftShiftTensor d]) ℂ :=
    Matrix.reindex (Equiv.refl _) eR
      ((d : ℂ)⁻¹ • normalizedIdentityColumn d)
  let P : Matrix (Fin d × Fin d) (Fin ℓ[leftShiftTensor d]) ℂ :=
    Matrix.reindex (Equiv.refl _) eL
      (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
  have hC : C.IsIsometry := by
    exact Matrix.IsIsometry.reindex _ (normalizedIdentityColumn_isIsometry d)
      (Equiv.refl _) eR
  have hP : P.IsUnitaryBetween := by
    apply Matrix.IsUnitaryBetween.reindex
    exact ⟨by simp [Matrix.IsIsometry], by simp [Matrix.IsCoisometry]⟩
  have hcut₁ : sourceCutM₁ (leftShiftTensor d) = C * R := by
    rw [sourceCutM₁_leftShiftTensor]
    change _ =
      Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) eR (normalizedIdentityColumn d) *
        Matrix.reindexLinearEquiv ℂ ℂ eR (Equiv.refl _)
          ((d : ℂ) • (normalizedIdentityColumn d)ᴴ)
    rw [Matrix.reindexLinearEquiv_mul ℂ ℂ (Equiv.refl _) eR (Equiv.refl _),
      normalizedIdentityColumn_mul_scaled_conjTranspose d]
    rfl
  have hcut₂ : sourceCutM₂ (leftShiftTensor d) = P * Pᴴ := by
    rw [sourceCutM₂_leftShiftTensor]
    exact hP.2.symm
  have hweighted : Cᴴ * sourceWeight (d := d)
      (1 : Matrix (Fin d) (Fin d) ℂ) * C = 1 := by
    rw [show sourceWeight (d := d) (1 : Matrix (Fin d) (Fin d) ℂ) = 1 by
      simp [sourceWeight]]
    simpa [Matrix.IsIsometry] using hC
  have hRZ : R * Z = 1 := by
    change
      Matrix.reindexLinearEquiv ℂ ℂ eR (Equiv.refl _)
          ((d : ℂ) • (normalizedIdentityColumn d)ᴴ) *
        Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) eR
          ((d : ℂ)⁻¹ • normalizedIdentityColumn d) = 1
    rw [Matrix.reindexLinearEquiv_mul ℂ ℂ eR (Equiv.refl _) eR,
      scaled_conjTranspose_mul_inverse_scaled_column d,
      Matrix.reindexLinearEquiv_one]
  exact ⟨C, R, Z, P, Pᴴ, P, hcut₁, hcut₂, hweighted, hP.1,
    hRZ, hP.1⟩

/-- Product source coordinates, followed by the multiplicative right-rank
identification for an independent tensor product.

Source: arXiv:1703.09188, proof of Theorem `IndexTh` (ii), lines 824--847. -/
noncomputable def tensorProductRightRankEquiv
    {d D e E : ℕ} (U : MPOTensor d D) (V : MPOTensor e E) :
    Fin r[U] × Fin r[V] ≃ Fin r[tensorProduct U V] :=
  finProdFinEquiv.trans (finCongr (rightRank_tensorProduct U V).symm)

/-- Product source coordinates, followed by the multiplicative left-rank
identification for an independent tensor product.

Source: arXiv:1703.09188, proof of Theorem `IndexTh` (ii), lines 824--847. -/
noncomputable def tensorProductLeftRankEquiv
    {d D e E : ℕ} (U : MPOTensor d D) (V : MPOTensor e E) :
    Fin ℓ[U] × Fin ℓ[V] ≃ Fin ℓ[tensorProduct U V] :=
  finProdFinEquiv.trans (finCongr (leftRank_tensorProduct U V).symm)

private theorem tensorProductCutShuffle_symm_apply
    (a b c f : ℕ) (x : Fin a × Fin b) (y : Fin c × Fin f) :
    (tensorProductCutShuffle a b c f).symm
        (finProdFinEquiv (x.1, y.1), finProdFinEquiv (x.2, y.2)) = (x, y) :=
  (tensorProductCutShuffle a b c f).symm_apply_apply (x, y)

private noncomputable def SourceFactors.independentTensorProduct
    {d D e E : ℕ} {U : MPOTensor d D} {V : MPOTensor e E}
    (S : SourceFactors U (1 : Matrix (Fin D) (Fin D) ℂ))
    (T : SourceFactors V (1 : Matrix (Fin E) (Fin E) ℂ)) :
    SourceFactors (tensorProduct U V)
      (1 : Matrix (Fin (D * E)) (Fin (D * E)) ℂ) := by
  let eRow := tensorProductCutShuffle D d E e
  let eCol := tensorProductCutShuffle d D e E
  let eR := tensorProductRightRankEquiv U V
  let eL := tensorProductLeftRankEquiv U V
  let X₁ := Matrix.reindex eRow eR (S.X₁ ⊗ₖ T.X₁)
  let Y₁ := Matrix.reindex eR eCol (S.Y₁ ⊗ₖ T.Y₁)
  let Z₁ := Matrix.reindex eCol eR (S.Z₁ ⊗ₖ T.Z₁)
  let X₂ := Matrix.reindex eRow eL (S.X₂ ⊗ₖ T.X₂)
  let Y₂ := Matrix.reindex eL eCol (S.Y₂ ⊗ₖ T.Y₂)
  let Z₂ := Matrix.reindex eCol eL (S.Z₂ ⊗ₖ T.Z₂)
  have hSX₁ : S.X₁.IsIsometry := by
    have h := S.X₁_weighted_isometry
    rw [show sourceWeight (d := d) (1 : Matrix (Fin D) (Fin D) ℂ) = 1 by
      simp [sourceWeight]] at h
    simpa [Matrix.IsIsometry] using h
  have hTX₁ : T.X₁.IsIsometry := by
    have h := T.X₁_weighted_isometry
    rw [show sourceWeight (d := e) (1 : Matrix (Fin E) (Fin E) ℂ) = 1 by
      simp [sourceWeight]] at h
    simpa [Matrix.IsIsometry] using h
  have hKX₁ : (S.X₁ ⊗ₖ T.X₁).IsIsometry := by
    rw [Matrix.IsIsometry, Matrix.conjTranspose_kronecker,
      ← Matrix.mul_kronecker_mul]
    change (S.X₁ᴴ * S.X₁) ⊗ₖ (T.X₁ᴴ * T.X₁) = 1
    rw [show S.X₁ᴴ * S.X₁ = 1 by exact hSX₁,
      show T.X₁ᴴ * T.X₁ = 1 by exact hTX₁]
    simp
  have hKX₂ : (S.X₂ ⊗ₖ T.X₂).IsIsometry := by
    rw [Matrix.IsIsometry, Matrix.conjTranspose_kronecker,
      ← Matrix.mul_kronecker_mul]
    change (S.X₂ᴴ * S.X₂) ⊗ₖ (T.X₂ᴴ * T.X₂) = 1
    rw [show S.X₂ᴴ * S.X₂ = 1 by exact S.X₂_isometry,
      show T.X₂ᴴ * T.X₂ = 1 by exact T.X₂_isometry]
    simp
  have hX₁ : X₁.IsIsometry :=
    Matrix.IsIsometry.reindex _ hKX₁ eRow eR
  have hX₂ : X₂.IsIsometry :=
    Matrix.IsIsometry.reindex _ hKX₂ eRow eL
  have hcut₁ : sourceCutM₁ (tensorProduct U V) = X₁ * Y₁ := by
    rw [sourceCutM₁_tensorProduct, S.sourceCutM₁_eq, T.sourceCutM₁_eq]
    change Matrix.reindexLinearEquiv ℂ ℂ eRow eCol
        ((S.X₁ * S.Y₁) ⊗ₖ (T.X₁ * T.Y₁)) =
      Matrix.reindexLinearEquiv ℂ ℂ eRow eR (S.X₁ ⊗ₖ T.X₁) *
        Matrix.reindexLinearEquiv ℂ ℂ eR eCol (S.Y₁ ⊗ₖ T.Y₁)
    rw [Matrix.reindexLinearEquiv_mul ℂ ℂ eRow eR eCol,
      Matrix.mul_kronecker_mul]
  have hcut₂ : sourceCutM₂ (tensorProduct U V) = X₂ * Y₂ := by
    rw [sourceCutM₂_tensorProduct, S.sourceCutM₂_eq, T.sourceCutM₂_eq]
    change Matrix.reindexLinearEquiv ℂ ℂ eRow eCol
        ((S.X₂ * S.Y₂) ⊗ₖ (T.X₂ * T.Y₂)) =
      Matrix.reindexLinearEquiv ℂ ℂ eRow eL (S.X₂ ⊗ₖ T.X₂) *
        Matrix.reindexLinearEquiv ℂ ℂ eL eCol (S.Y₂ ⊗ₖ T.Y₂)
    rw [Matrix.reindexLinearEquiv_mul ℂ ℂ eRow eL eCol,
      Matrix.mul_kronecker_mul]
  have hweighted : X₁ᴴ * sourceWeight (d := d * e)
      (1 : Matrix (Fin (D * E)) (Fin (D * E)) ℂ) * X₁ = 1 := by
    rw [show sourceWeight (d := d * e)
        (1 : Matrix (Fin (D * E)) (Fin (D * E)) ℂ) = 1 by
      simp [sourceWeight]]
    simpa [Matrix.IsIsometry] using hX₁
  have hY₁Z₁ : Y₁ * Z₁ = 1 := by
    change Matrix.reindexLinearEquiv ℂ ℂ eR eCol (S.Y₁ ⊗ₖ T.Y₁) *
      Matrix.reindexLinearEquiv ℂ ℂ eCol eR (S.Z₁ ⊗ₖ T.Z₁) = 1
    rw [Matrix.reindexLinearEquiv_mul ℂ ℂ eR eCol eR,
      ← Matrix.mul_kronecker_mul, S.Y₁_mul_Z₁, T.Y₁_mul_Z₁]
    simp
  have hY₂Z₂ : Y₂ * Z₂ = 1 := by
    change Matrix.reindexLinearEquiv ℂ ℂ eL eCol (S.Y₂ ⊗ₖ T.Y₂) *
      Matrix.reindexLinearEquiv ℂ ℂ eCol eL (S.Z₂ ⊗ₖ T.Z₂) = 1
    rw [Matrix.reindexLinearEquiv_mul ℂ ℂ eL eCol eL,
      ← Matrix.mul_kronecker_mul, S.Y₂_mul_Z₂, T.Y₂_mul_Z₂]
    simp
  exact ⟨X₁, Y₁, Z₁, X₂, Y₂, Z₂, hcut₁, hcut₂,
    hweighted, hX₂, hY₁Z₁, hY₂Z₂⟩

private theorem SourceFactors.sourceU_independentTensorProduct_apply
    {d D e E : ℕ} {U : MPOTensor d D} {V : MPOTensor e E}
    (S : SourceFactors U (1 : Matrix (Fin D) (Fin D) ℂ))
    (T : SourceFactors V (1 : Matrix (Fin E) (Fin E) ℂ))
    (lᵤ : Fin ℓ[U]) (lᵥ : Fin ℓ[V]) (rᵤ : Fin r[U]) (rᵥ : Fin r[V])
    (i₁ i₂ : Fin d) (j₁ j₂ : Fin e) :
    SourceFactors.sourceU (tensorProduct U V)
        (SourceFactors.independentTensorProduct S T)
        (tensorProductLeftRankEquiv U V (lᵤ, lᵥ),
          tensorProductRightRankEquiv U V (rᵤ, rᵥ))
        (finProdFinEquiv (i₁, j₁), finProdFinEquiv (i₂, j₂)) =
      SourceFactors.sourceU U S (lᵤ, rᵤ) (i₁, i₂) *
        SourceFactors.sourceU V T (lᵥ, rᵥ) (j₁, j₂) := by
  simp only [SourceFactors.sourceU, SourceFactors.independentTensorProduct]
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, Equiv.symm_apply_apply]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro β _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro γ _
  rw [tensorProductCutShuffle_symm_apply d D e E (i₁, β) (j₁, γ),
    tensorProductCutShuffle_symm_apply D d E e (β, i₂) (γ, j₂)]
  ring

private theorem SourceFactors.sourceV_independentTensorProduct_apply
    {d D e E : ℕ} {U : MPOTensor d D} {V : MPOTensor e E}
    (S : SourceFactors U (1 : Matrix (Fin D) (Fin D) ℂ))
    (T : SourceFactors V (1 : Matrix (Fin E) (Fin E) ℂ))
    (j₁ j₂ : Fin d) (k₁ k₂ : Fin e)
    (rᵤ : Fin r[U]) (rᵥ : Fin r[V]) (lᵤ : Fin ℓ[U]) (lᵥ : Fin ℓ[V]) :
    SourceFactors.sourceV (tensorProduct U V)
        (SourceFactors.independentTensorProduct S T)
        (finProdFinEquiv (j₁, k₁), finProdFinEquiv (j₂, k₂))
        (tensorProductRightRankEquiv U V (rᵤ, rᵥ),
          tensorProductLeftRankEquiv U V (lᵤ, lᵥ)) =
      SourceFactors.sourceV U S (j₁, j₂) (rᵤ, lᵤ) *
        SourceFactors.sourceV V T (k₁, k₂) (rᵥ, lᵥ) := by
  simp only [SourceFactors.sourceV, SourceFactors.independentTensorProduct]
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, Equiv.symm_apply_apply]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro α _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro γ _
  rw [tensorProductCutShuffle_symm_apply D d E e (α, j₁) (γ, k₁),
    tensorProductCutShuffle_symm_apply d D e E (j₂, α) (k₂, γ)]
  ring

/-- Explicit supplied source factors for the paper's identity family $U_1$.

Source: arXiv:1703.09188, equation `eq:SF_u1_u3` (lines 2009--2016). -/
noncomputable def shiftExampleU₁SourceFactors (d : ℕ) :
    SourceFactors (shiftExampleU₁ d) (1 : Matrix (Fin 1) (Fin 1) ℂ) :=
  SourceFactors.independentTensorProduct (identitySourceFactors d)
    (identitySourceFactors d)

/-- Explicit supplied source factors for the paper's counter-shift family $U_2$.

Source: arXiv:1703.09188, equation `eq:uv2_U2` (lines 2018--2027). -/
noncomputable def shiftExampleU₂SourceFactors (d : ℕ) [NeZero d] :
    SourceFactors (shiftExampleU₂ d)
      (1 : Matrix (Fin (d * d)) (Fin (d * d)) ℂ) :=
  SourceFactors.independentTensorProduct (leftShiftSourceFactors d)
    (rightShiftSourceFactors d)

/-- Explicit supplied source factors for the paper's reversed counter-shift
family $U_3$.

Source: arXiv:1703.09188, equations `eq:SF_u1_u3` and `eq:uv2_U3`
(lines 2009--2016 and 2028--2034). -/
noncomputable def shiftExampleU₃SourceFactors (d : ℕ) [NeZero d] :
    SourceFactors (shiftExampleU₃ d)
      (1 : Matrix (Fin (d * d)) (Fin (d * d)) ℂ) :=
  SourceFactors.independentTensorProduct (rightShiftSourceFactors d)
    (leftShiftSourceFactors d)

/-- Entry formula for the source $u$ supplied by the bond-one identity
factors.  The source row is written in the paper order (left, right).

Source: arXiv:1703.09188, equation `eq:SF_u1_u3` (lines 2009--2016). -/
theorem sourceU_identitySourceFactors_apply (d : ℕ) (l r i₁ i₂ : Fin d) :
    SourceFactors.sourceU (identityMPUTensor d) (identitySourceFactors d)
        (identityLeftRankEquiv d l, identityRightRankEquiv d r) (i₁, i₂) =
      if r = i₁ ∧ l = i₂ then 1 else 0 := by
  by_cases hr : r = i₁ <;> by_cases hl : l = i₂ <;>
    simp [SourceFactors.sourceU_apply, identitySourceFactors,
      Matrix.reindex_apply, Matrix.one_apply, hr, hl, ne_comm]

/-- Entry formula for the source $v$ supplied by the bond-one identity
factors.  Its source column has the paper order (right, left).

Source: arXiv:1703.09188, equation `eq:SF_u1_u3` (lines 2009--2016). -/
theorem sourceV_identitySourceFactors_apply (d : ℕ) (j₁ j₂ r l : Fin d) :
    SourceFactors.sourceV (identityMPUTensor d) (identitySourceFactors d)
        (j₁, j₂) (identityRightRankEquiv d r, identityLeftRankEquiv d l) =
      if r = j₁ ∧ l = j₂ then 1 else 0 := by
  by_cases hr : r = j₁ <;> by_cases hl : l = j₂ <;>
    simp [SourceFactors.sourceV_apply, identitySourceFactors,
      Matrix.reindex_apply, Matrix.one_apply, hr, hl]
  all_goals grind

/-- Entry formula for the source $u$ supplied by the right-shift factors.

Source: arXiv:1703.09188, equations `eq:SF_u1_u3`, `eq:uv2_U2`, and
`eq:uv2_U3` (lines 2009--2034). -/
theorem sourceU_rightShiftSourceFactors_apply (d : ℕ) [NeZero d]
    (a b i₁ i₂ : Fin d) :
    SourceFactors.sourceU (rightShiftTensor d) (rightShiftSourceFactors d)
        (rightShiftLeftRankEquiv d 0, rightShiftRightRankEquiv d (a, b)) (i₁, i₂) =
      if a = i₁ ∧ b = i₂ then (Real.sqrt d : ℂ)⁻¹ else 0 := by
  by_cases ha : a = i₁ <;> by_cases hb : b = i₂ <;>
    simp [SourceFactors.sourceU_apply, rightShiftSourceFactors,
      normalizedIdentityColumn, normalizedIdentityVec, Matrix.reindex_apply,
      Matrix.one_apply, sourceSqrt, ha, hb]

/-- Entry formula for the source $v$ supplied by the right-shift factors.

Source: arXiv:1703.09188, equations `eq:SF_u1_u3`, `eq:uv2_U2`, and
`eq:uv2_U3` (lines 2009--2034). -/
theorem sourceV_rightShiftSourceFactors_apply (d : ℕ) [NeZero d]
    (j₁ j₂ a b : Fin d) :
    SourceFactors.sourceV (rightShiftTensor d) (rightShiftSourceFactors d)
        (j₁, j₂) (rightShiftRightRankEquiv d (a, b), rightShiftLeftRankEquiv d 0) =
      if a = j₂ ∧ b = j₁ then (d : ℂ) * (Real.sqrt d : ℂ)⁻¹ else 0 := by
  by_cases ha : a = j₂ <;> by_cases hb : b = j₁ <;>
    simp [SourceFactors.sourceV_apply, rightShiftSourceFactors,
      normalizedIdentityColumn, normalizedIdentityVec, Matrix.reindex_apply,
      Matrix.one_apply, sourceSqrt, ha, hb, NeZero.ne d,
      mul_comm, mul_left_comm]
  all_goals grind

/-- Entry formula for the source $u$ supplied by the left-shift factors.

Source: arXiv:1703.09188, equations `eq:SF_u1_u3`, `eq:uv2_U2`, and
`eq:uv2_U3` (lines 2009--2034). -/
theorem sourceU_leftShiftSourceFactors_apply (d : ℕ) [NeZero d]
    (a b i₁ i₂ : Fin d) :
    SourceFactors.sourceU (leftShiftTensor d) (leftShiftSourceFactors d)
        (leftShiftLeftRankEquiv d (a, b), leftShiftRightRankEquiv d 0) (i₁, i₂) =
      if a = i₁ ∧ b = i₂ then (d : ℂ) * (Real.sqrt d : ℂ)⁻¹ else 0 := by
  by_cases ha : a = i₁ <;> by_cases hb : b = i₂ <;>
    simp [SourceFactors.sourceU_apply, leftShiftSourceFactors,
      normalizedIdentityColumn, normalizedIdentityVec, Matrix.reindex_apply,
      Matrix.one_apply, sourceSqrt, ha, hb, NeZero.ne d, ne_comm,
      mul_comm, mul_left_comm]

/-- Entry formula for the source $v$ supplied by the left-shift factors.

Source: arXiv:1703.09188, equations `eq:SF_u1_u3`, `eq:uv2_U2`, and
`eq:uv2_U3` (lines 2009--2034). -/
theorem sourceV_leftShiftSourceFactors_apply (d : ℕ) [NeZero d]
    (j₁ j₂ a b : Fin d) :
    SourceFactors.sourceV (leftShiftTensor d) (leftShiftSourceFactors d)
        (j₁, j₂) (leftShiftRightRankEquiv d 0, leftShiftLeftRankEquiv d (a, b)) =
      if a = j₂ ∧ b = j₁ then (Real.sqrt d : ℂ)⁻¹ else 0 := by
  by_cases ha : a = j₂ <;> by_cases hb : b = j₁ <;>
    simp [SourceFactors.sourceV_apply, leftShiftSourceFactors,
      normalizedIdentityColumn, normalizedIdentityVec, Matrix.reindex_apply,
      Matrix.one_apply, sourceSqrt, ha, hb, NeZero.ne d]
  all_goals grind

end MPOTensor
