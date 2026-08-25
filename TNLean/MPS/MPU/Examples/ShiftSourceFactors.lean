/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ComplexSqrt
import QICLean.Algebra.MatrixReindex
import TNLean.MPS.MPU.Examples.ShiftSourceRanks
import TNLean.MPS.MPU.SourceUV

/-!
# Supplied source factors for the cyclic-shift examples

This module constructs explicit formalization witnesses realizing the source
matrices printed for the three shift families in arXiv:1703.09188, equations
`eq:SF_u1_u3`, `eq:uv2_U2`, and `eq:uv2_U3` (lines 2009--2034).  The paper does
not print these normalized factors or their intermediate coordinate
identities.  None of the statements below identifies the supplied witnesses
with factors chosen by compact singular-value decomposition.
-/

open scoped Matrix BigOperators

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

/-- The normalization cancellation used when a left-shift source entry is
multiplied by a right-shift source entry.

Formalization identity used to derive arXiv:1703.09188, equations
`eq:SF_u1_u3`, `eq:uv2_U2`, and `eq:uv2_U3` (lines 2009--2034); the paper
prints the resulting permutation matrices, not this scalar calculation. -/
theorem shiftSourceScale_cancel (d : ℕ) [NeZero d] :
    ((d : ℂ) * (Real.sqrt d : ℂ)⁻¹) * (Real.sqrt d : ℂ)⁻¹ = 1 := by
  simpa [sourceSqrt, mul_assoc] using nat_mul_sourceSqrt_inv_mul_inv d

/-- The reflected normalization cancellation used when a right-shift source
entry is multiplied by a left-shift source entry.

Formalization identity used to derive arXiv:1703.09188, equations
`eq:SF_u1_u3`, `eq:uv2_U2`, and `eq:uv2_U3` (lines 2009--2034); the paper
prints the resulting permutation matrices, not this scalar calculation. -/
theorem shiftSourceScale_cancel_rev (d : ℕ) [NeZero d] :
    (Real.sqrt d : ℂ)⁻¹ * ((d : ℂ) * (Real.sqrt d : ℂ)⁻¹) = 1 := by
  simpa [sourceSqrt, mul_assoc] using sourceSqrt_inv_mul_nat_mul_inv d

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

Formalization coordinate for the printed source formulas in arXiv:1703.09188,
lines 2009--2034; the paper does not state this intermediate equivalence. -/
noncomputable def rightShiftRightRankEquiv (d : ℕ) :
    Fin d × Fin d ≃ Fin r[rightShiftTensor d] :=
  finProdFinEquiv.trans (finCongr (rightRank_rightShiftTensor d).symm)

/-- The unique coordinate is the left source coordinate of the right shift.

Formalization coordinate for the printed source formulas in arXiv:1703.09188,
lines 2009--2034; the paper does not state this intermediate equivalence. -/
noncomputable def rightShiftLeftRankEquiv (d : ℕ) [NeZero d] :
    Fin 1 ≃ Fin ℓ[rightShiftTensor d] :=
  finCongr (leftRank_rightShiftTensor d).symm

/-- The unique coordinate is the right source coordinate of the left shift.

Formalization coordinate for the printed source formulas in arXiv:1703.09188,
lines 2009--2034; the paper does not state this intermediate equivalence. -/
noncomputable def leftShiftRightRankEquiv (d : ℕ) [NeZero d] :
    Fin 1 ≃ Fin r[leftShiftTensor d] :=
  finCongr (rightRank_leftShiftTensor d).symm

/-- The product coordinates are the left source coordinates of the left shift.

Formalization coordinate for the printed source formulas in arXiv:1703.09188,
lines 2009--2034; the paper does not state this intermediate equivalence. -/
noncomputable def leftShiftLeftRankEquiv (d : ℕ) :
    Fin d × Fin d ≃ Fin ℓ[leftShiftTensor d] :=
  finProdFinEquiv.trans (finCongr (leftRank_leftShiftTensor d).symm)

/-- Both source cuts of the bond-one identity tensor are the identity after
removing their unique virtual coordinates.

Formalization identity used to realize equation `eq:SF_u1_u3` in
arXiv:1703.09188, lines 2009--2016; the paper does not state this intermediate
source-cut formula. -/
theorem sourceCutM₁_identityMPUTensor (d : ℕ) :
    sourceCutM₁ (identityMPUTensor d) =
      Matrix.reindex (Equiv.uniqueProd (Fin d) (Fin 1)).symm
        (Equiv.prodUnique (Fin d) (Fin 1)).symm
        (1 : Matrix (Fin d) (Fin d) ℂ) := by
  ext ⟨α, j⟩ ⟨i, β⟩
  have hαβ : α = β := Subsingleton.elim _ _
  by_cases hij : i = j
  · simp [sourceCutM₁, identityMPUTensor, idTensor, Matrix.reindex_apply,
      Matrix.one_apply, hij, hαβ]
  · have hji : j ≠ i := Ne.symm hij
    simp [sourceCutM₁, identityMPUTensor, idTensor, Matrix.reindex_apply,
      hij, hji, hαβ]

/-- The second source cut of the bond-one identity tensor is the same
reindexed identity as its first source cut.

Formalization identity used to realize equation `eq:SF_u1_u3` in
arXiv:1703.09188, lines 2009--2016; the paper does not state this intermediate
source-cut formula. -/
theorem sourceCutM₂_identityMPUTensor (d : ℕ) :
    sourceCutM₂ (identityMPUTensor d) =
      Matrix.reindex (Equiv.uniqueProd (Fin d) (Fin 1)).symm
        (Equiv.prodUnique (Fin d) (Fin 1)).symm
        (1 : Matrix (Fin d) (Fin d) ℂ) := by
  ext ⟨α, i⟩ ⟨j, β⟩
  have hαβ : α = β := Subsingleton.elim _ _
  by_cases hij : i = j <;>
    simp [sourceCutM₂, identityMPUTensor, idTensor, Matrix.reindex_apply,
      Matrix.one_apply, hij, hαβ]

/-- The right source rank of the bond-one identity tensor is its physical
dimension.

Formalization rank identity used to realize equation `eq:SF_u1_u3` in
arXiv:1703.09188, lines 2009--2016; the paper does not state this intermediate
identity. -/
theorem rightRank_identityMPUTensor (d : ℕ) :
    r[identityMPUTensor d] = d := by
  rw [rightRank, sourceCutM₁_identityMPUTensor, Matrix.rank_reindex,
    Matrix.rank_one]
  simp

/-- The left source rank of the bond-one identity tensor is its physical
dimension.

Formalization rank identity used to realize equation `eq:SF_u1_u3` in
arXiv:1703.09188, lines 2009--2016; the paper does not state this intermediate
identity. -/
theorem leftRank_identityMPUTensor (d : ℕ) :
    ℓ[identityMPUTensor d] = d := by
  rw [leftRank, sourceCutM₂_identityMPUTensor, Matrix.rank_reindex,
    Matrix.rank_one]
  simp

/-- Physical coordinates are the right source coordinates of the bond-one
identity tensor.

Formalization coordinate for equation `eq:SF_u1_u3` in arXiv:1703.09188,
lines 2009--2016; the paper does not state this intermediate equivalence. -/
noncomputable def identityRightRankEquiv (d : ℕ) :
    Fin d ≃ Fin r[identityMPUTensor d] :=
  finCongr (rightRank_identityMPUTensor d).symm

/-- Physical coordinates are the left source coordinates of the bond-one
identity tensor.

Formalization coordinate for equation `eq:SF_u1_u3` in arXiv:1703.09188,
lines 2009--2016; the paper does not state this intermediate equivalence. -/
noncomputable def identityLeftRankEquiv (d : ℕ) :
    Fin d ≃ Fin ℓ[identityMPUTensor d] :=
  finCongr (leftRank_identityMPUTensor d).symm

/-- Explicit supplied source factors for the bond-one identity tensor.

Both cuts are transported identity matrices.  This explicit formalization
witness realizes $u_1=v_1=\Id\otimes\Id$ in arXiv:1703.09188, equation
`eq:SF_u1_u3` (lines 2009--2016); the paper does not print the normalized
factor witness itself. -/
noncomputable def identitySourceFactors (d : ℕ) :
    SourceFactors (identityMPUTensor d) (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  let eRow := Equiv.uniqueProd (Fin d) (Fin 1)
  let eCol := Equiv.prodUnique (Fin d) (Fin 1)
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
    change Matrix.reindex eRow.symm eCol.symm 1 =
      Matrix.reindex eRow.symm eR 1 *
        Matrix.reindex eR eCol.symm 1
    rw [Matrix.reindex_mul_reindex, Matrix.one_mul]
  have hcut₂ : sourceCutM₂ (identityMPUTensor d) = X₂ * Y₂ := by
    rw [sourceCutM₂_identityMPUTensor]
    change Matrix.reindex eRow.symm eCol.symm 1 =
      Matrix.reindex eRow.symm eL 1 *
        Matrix.reindex eL eCol.symm 1
    rw [Matrix.reindex_mul_reindex, Matrix.one_mul]
  have hweighted : X₁ᴴ * sourceWeight (d := d)
      (1 : Matrix (Fin 1) (Fin 1) ℂ) * X₁ = 1 := by
    rw [show sourceWeight (d := d) (1 : Matrix (Fin 1) (Fin 1) ℂ) = 1 by
      simp [sourceWeight]]
    simpa [Matrix.IsIsometry] using hX₁.1
  have hY₁Z₁ : Y₁ * Z₁ = 1 := by
    change Matrix.reindex eR eCol.symm 1 *
        Matrix.reindex eCol.symm eR 1 = 1
    rw [Matrix.reindex_mul_reindex, Matrix.one_mul]
    simp [Matrix.reindex_apply]
  have hY₂Z₂ : Y₂ * Z₂ = 1 := by
    change Matrix.reindex eL eCol.symm 1 *
        Matrix.reindex eCol.symm eL 1 = 1
    rw [Matrix.reindex_mul_reindex, Matrix.one_mul]
    simp [Matrix.reindex_apply]
  exact ⟨X₁, Y₁, Z₁, X₂, Y₂, Z₂, hcut₁, hcut₂,
    hweighted, hX₂.1, hY₁Z₁, hY₂Z₂⟩

/-- Explicit supplied source factors for the right-shift tensor.

The first cut is the identity in the coordinates `rightShiftRightRankEquiv`.
The second cut uses the normalized vectorization of the identity matrix.  This
explicit formalization witness realizes the right-shift contribution to the
printed formulas `eq:SF_u1_u3`, `eq:uv2_U2`, and `eq:uv2_U3` in
arXiv:1703.09188, lines 2009--2034; the paper does not print the normalized
factor witness itself. -/
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
  have hC : C.IsIsometry :=
    Matrix.IsIsometry.reindex _ (normalizedIdentityColumn_isIsometry d)
      (Equiv.refl _) eL
  have hcut₁ : sourceCutM₁ (rightShiftTensor d) = P * Pᴴ := by
    rw [sourceCutM₁_rightShiftTensor]
    exact hP.2.symm
  have hcut₂ : sourceCutM₂ (rightShiftTensor d) = C * R := by
    rw [sourceCutM₂_rightShiftTensor]
    change _ =
      Matrix.reindex (Equiv.refl _) eL (normalizedIdentityColumn d) *
        Matrix.reindex eL (Equiv.refl _)
          ((d : ℂ) • (normalizedIdentityColumn d)ᴴ)
    rw [Matrix.reindex_mul_reindex,
      normalizedIdentityColumn_mul_scaled_conjTranspose d]
    rfl
  have hweighted : Pᴴ * sourceWeight (d := d)
      (1 : Matrix (Fin d) (Fin d) ℂ) * P = 1 := by
    rw [show sourceWeight (d := d) (1 : Matrix (Fin d) (Fin d) ℂ) = 1 by
      simp [sourceWeight]]
    simpa [Matrix.IsIsometry] using hP.1
  have hRZ : R * Z = 1 := by
    change
      Matrix.reindex eL (Equiv.refl _)
          ((d : ℂ) • (normalizedIdentityColumn d)ᴴ) *
        Matrix.reindex (Equiv.refl _) eL
          ((d : ℂ)⁻¹ • normalizedIdentityColumn d) = 1
    rw [Matrix.reindex_mul_reindex,
      scaled_conjTranspose_mul_inverse_scaled_column d]
    simp [Matrix.reindex_apply]
  exact ⟨P, Pᴴ, P, C, R, Z, hcut₁, hcut₂, hweighted, hC,
    hP.1, hRZ⟩

/-- Explicit supplied source factors for the left-shift tensor.

The first cut uses the normalized vectorization of the identity matrix.  The
second cut is the identity in the coordinates `leftShiftLeftRankEquiv`.  This
explicit formalization witness realizes the left-shift contribution to the
printed formulas `eq:SF_u1_u3`, `eq:uv2_U2`, and `eq:uv2_U3` in
arXiv:1703.09188, lines 2009--2034; the paper does not print the normalized
factor witness itself. -/
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
  have hC : C.IsIsometry :=
    Matrix.IsIsometry.reindex _ (normalizedIdentityColumn_isIsometry d)
      (Equiv.refl _) eR
  have hP : P.IsUnitaryBetween := by
    apply Matrix.IsUnitaryBetween.reindex
    exact ⟨by simp [Matrix.IsIsometry], by simp [Matrix.IsCoisometry]⟩
  have hcut₁ : sourceCutM₁ (leftShiftTensor d) = C * R := by
    rw [sourceCutM₁_leftShiftTensor]
    change _ =
      Matrix.reindex (Equiv.refl _) eR (normalizedIdentityColumn d) *
        Matrix.reindex eR (Equiv.refl _)
          ((d : ℂ) • (normalizedIdentityColumn d)ᴴ)
    rw [Matrix.reindex_mul_reindex,
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
      Matrix.reindex eR (Equiv.refl _)
          ((d : ℂ) • (normalizedIdentityColumn d)ᴴ) *
        Matrix.reindex (Equiv.refl _) eR
          ((d : ℂ)⁻¹ • normalizedIdentityColumn d) = 1
    rw [Matrix.reindex_mul_reindex,
      scaled_conjTranspose_mul_inverse_scaled_column d]
    simp [Matrix.reindex_apply]
  exact ⟨C, R, Z, P, Pᴴ, P, hcut₁, hcut₂, hweighted, hP.1,
    hRZ, hP.1⟩

/-- Entry formula for the source $u$ supplied by the bond-one identity
factors.  The source row is written in the paper order (left, right).

Formalization coordinate identity used to derive equation `eq:SF_u1_u3` in
arXiv:1703.09188, lines 2009--2016; the paper does not state this intermediate
entry formula. -/
theorem sourceU_identitySourceFactors_apply (d : ℕ) (l r i₁ i₂ : Fin d) :
    SourceFactors.sourceU (identityMPUTensor d) (identitySourceFactors d)
        (identityLeftRankEquiv d l, identityRightRankEquiv d r) (i₁, i₂) =
      if r = i₁ ∧ l = i₂ then 1 else 0 := by
  by_cases hr : r = i₁ <;> by_cases hl : l = i₂ <;>
    simp [SourceFactors.sourceU_apply, identitySourceFactors,
      Matrix.reindex_apply, Matrix.one_apply, hr, hl, ne_comm]

/-- Entry formula for the source $v$ supplied by the bond-one identity
factors.  Its source column has the paper order (right, left).

Formalization coordinate identity used to derive equation `eq:SF_u1_u3` in
arXiv:1703.09188, lines 2009--2016; the paper does not state this intermediate
entry formula. -/
theorem sourceV_identitySourceFactors_apply (d : ℕ) (j₁ j₂ r l : Fin d) :
    SourceFactors.sourceV (identityMPUTensor d) (identitySourceFactors d)
        (j₁, j₂) (identityRightRankEquiv d r, identityLeftRankEquiv d l) =
      if r = j₁ ∧ l = j₂ then 1 else 0 := by
  by_cases hr : r = j₁ <;> by_cases hl : l = j₂ <;>
    simp [SourceFactors.sourceV_apply, identitySourceFactors,
      Matrix.reindex_apply, Matrix.one_apply, hr, hl]
  all_goals grind

/-- Entry formula for the source $u$ supplied by the right-shift factors.

Formalization coordinate identity used to derive equations `eq:SF_u1_u3`,
`eq:uv2_U2`, and `eq:uv2_U3` in arXiv:1703.09188, lines 2009--2034; the paper
does not state this intermediate entry formula. -/
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

Formalization coordinate identity used to derive equations `eq:SF_u1_u3`,
`eq:uv2_U2`, and `eq:uv2_U3` in arXiv:1703.09188, lines 2009--2034; the paper
does not state this intermediate entry formula. -/
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

Formalization coordinate identity used to derive equations `eq:SF_u1_u3`,
`eq:uv2_U2`, and `eq:uv2_U3` in arXiv:1703.09188, lines 2009--2034; the paper
does not state this intermediate entry formula. -/
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

Formalization coordinate identity used to derive equations `eq:SF_u1_u3`,
`eq:uv2_U2`, and `eq:uv2_U3` in arXiv:1703.09188, lines 2009--2034; the paper
does not state this intermediate entry formula. -/
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
