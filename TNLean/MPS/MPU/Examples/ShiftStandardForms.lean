/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.SwapMatrix
import TNLean.MPS.MPU.Examples.ShiftSwapMatrices
import TNLean.MPS.MPU.Examples.ShiftNormalizedSourceFactors
import TNLean.MPS.MPU.Examples.ShiftTilde
import TNLean.MPS.MPU.TwoSiteStandardForm

/-!
# Explicit standard forms of the shift families

The supplied gates and half factors realize CPSV17, equations `eq:SF_u1_u3`,
`eq:uv2_U2`, and `eq:uv2_U3` (lines 2009–2034). The first two swap-transformed
families realize the gates in `SFu1u3` (lines 2090–2099).

The two blocked families use trace-normalized supplied source factors. The
unblocked third family uses reciprocal square-root scalings of its delta half
factors. Both normalization identities are proved below for these witnesses.
-/

open scoped Matrix

namespace MPOTensor

/-- The identity family has identity gates (CPSV17, `eq:SF_u1_u3`). -/
noncomputable def shiftExampleU₁StandardForm (d : ℕ) [NeZero d] :
    TwoSiteStandardFormData (shiftExampleU₁ d)
      (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) 1 := by
  classical
  refine {
    phys_pos := NeZero.pos d
    bond_pos := by decide
    left_pos := NeZero.pos d
    right_pos := NeZero.pos d
    X₁ := fun i r => if i.1 = r then 1 else 0
    X₂ := fun i l => if i.2 = l then 1 else 0
    u_unitary := ⟨by simp [Matrix.IsIsometry], by simp [Matrix.IsCoisometry]⟩
    v_unitary := ⟨by simp [Matrix.IsIsometry], by simp [Matrix.IsCoisometry]⟩
    v_apply := ?_
    W_apply := ?_
  }
  · intro i₁ i₂ s t
    by_cases h₁ : i₁ = s <;> by_cases h₂ : i₂ = t <;> simp [Matrix.one_apply, h₁, h₂]
  · intro i j α γ
    have hαγ : α = γ := Subsingleton.elim _ _
    simp [shiftExampleU₁, identityMPUTensor, tensorProduct, idTensor,
      Matrix.reindex_apply, Matrix.one_apply,
      Prod.mk.injEq, ite_and, apply_ite]
    split_ifs <;> simp_all

/-- The identity family has isometric half factors, with its scalar bond weight one.
Source: CPSV17, `Y1Y1X1X1` and `eq:SF_u1_u3`. -/
theorem shiftExampleU₁StandardForm_normalized (d : ℕ) [NeZero d] :
    (shiftExampleU₁StandardForm d).X₁.IsIsometry ∧
      (shiftExampleU₁StandardForm d).X₂.IsIsometry := by
  simp only [Matrix.IsIsometry]
  constructor <;> ext r t <;>
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type] <;>
    simp [shiftExampleU₁StandardForm, Matrix.one_apply, eq_comm] <;> split_ifs <;> simp

/-- The counterpropagating family has swap gates (CPSV17, `eq:SF_u1_u3`). -/
noncomputable def shiftExampleU₃StandardForm (d : ℕ) [NeZero d] :
    TwoSiteStandardFormData (shiftExampleU₃ d) (Matrix.swapMatrix d)
      (Matrix.swapMatrix d) := by
  classical
  let c : ℂ := Real.sqrt d
  have hc : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast (Real.sqrt_pos.2 (Nat.cast_pos.mpr (NeZero.pos d))).ne'
  refine {
    phys_pos := NeZero.pos d
    bond_pos := Nat.mul_pos (NeZero.pos d) (NeZero.pos d)
    left_pos := NeZero.pos d
    right_pos := NeZero.pos d
    X₁ := fun i r => if i.2.divNat = r ∧ i.2.modNat = i.1 then c else 0
    X₂ := fun i l => if i.1.divNat = i.2 ∧ i.1.modNat = l then c⁻¹ else 0
    u_unitary := Matrix.swapMatrix_isUnitaryBetween d
    v_unitary := Matrix.swapMatrix_isUnitaryBetween d
    v_apply := ?_
    W_apply := ?_
  }
  · intro i₁ i₂ s t
    rw [← Equiv.sum_comp finProdFinEquiv]
    simp [Matrix.swapMatrix, Fintype.sum_prod_type, ite_and, eq_comm]
    split_ifs <;> simp_all
  · intro i j α γ
    simp [shiftExampleU₃, tensorProduct, rightShiftTensor, leftShiftTensor,
      physicalAdjointTensor, Matrix.reindex_apply, Matrix.kroneckerMap_apply,
      Matrix.single, Matrix.swapMatrix, ite_and, eq_comm]
    split_ifs <;> simp_all


/-- The unblocked third family has normalized half factors with trace-one bond weight.
Source: CPSV17, `Y1Y1X1X1` and `eq:SF_u1_u3`. -/
theorem shiftExampleU₃StandardForm_normalized (d : ℕ) [NeZero d] :
    let T := shiftExampleU₃StandardForm d
    T.X₁ᴴ * sourceWeight (d := d) (shiftPaperWeightSquared d) * T.X₁ = 1 ∧
      T.X₂.IsIsometry := by
  have hw : sourceWeight (d := d) (shiftPaperWeightSquared d) =
      ((d : ℂ)⁻¹ * (d : ℂ)⁻¹) • (1 : Matrix (Fin d × Fin (d * d)) _ ℂ) := by
    simp [sourceWeight, shiftPaperWeightSquared, shiftPaperWeight, Matrix.kronecker_smul]
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hs : (Real.sqrt d : ℂ) * (Real.sqrt d : ℂ) = (d : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  constructor
  · rw [hw, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    ext r t
    simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type]
    simp_rw [← Equiv.sum_comp finProdFinEquiv]
    simp [shiftExampleU₃StandardForm, Fintype.sum_prod_type, Matrix.one_apply,
      ite_and, mul_ite, eq_comm]
    split_ifs <;> simp_all [mul_assoc]
  · change (shiftExampleU₃StandardForm d).X₂ᴴ * (shiftExampleU₃StandardForm d).X₂ = 1
    ext r t
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type]
    rw [← Equiv.sum_comp finProdFinEquiv]
    simp [shiftExampleU₃StandardForm, Fintype.sum_prod_type, Matrix.one_apply,
      ite_and, mul_ite, eq_comm]
    split_ifs <;> simp_all [Complex.ofReal_sqrt_inv_mul_self, Nat.cast_nonneg]

/-- The first counterpropagating family after two-site blocking, with the
four-spin gates of CPSV17, equation `eq:uv2_U2`, lines 2021–2026. -/
noncomputable def shiftExampleU₂BlockedStandardForm (d : ℕ) [NeZero d] :
    TwoSiteStandardFormData (blockTwo (shiftExampleU₂ d))
      (Matrix.reindex (shiftTwoSitePhysicalEquiv d) (shiftTwoSitePhysicalEquiv d)
        (identitySwapIdentityMatrix d))
      (Matrix.reindex (shiftTwoSitePhysicalEquiv d) (shiftTwoSitePhysicalEquiv d)
        (swapTensorSwapMatrix d * identitySwapIdentityMatrix d)) := by
  classical
  let S := shiftExampleU₂PaperSourceFactors d
  let eL := finProdFinEquiv.symm.trans (shiftExampleU₂LeftRankEquiv d)
  let eR := finProdFinEquiv.symm.trans (shiftExampleU₂RightRankEquiv d)
  have hdecode (x : Fin (d * d)) : finProdFinEquiv (x.divNat, x.modNat) = x :=
    finProdFinEquiv.apply_symm_apply x
  have hu (l r : Fin (d * d)) (i j : Fin (d * d)) :
      SourceFactors.sourceU (shiftExampleU₂ d) S (eL l, eR r) (i, j) =
        Matrix.reindex (shiftTwoSitePhysicalEquiv d) (shiftTwoSitePhysicalEquiv d)
          (identitySwapIdentityMatrix d) (l, r) (i, j) := by
    simpa [S, eL, eR, shiftExampleU₂SourceURowEquiv, shiftTwoSitePhysicalEquiv,
      Matrix.reindex_apply, hdecode] using
      shiftExampleU₂Paper_sourceU_fourSpin_apply d l.divNat l.modNat r.divNat r.modNat
        i.divNat i.modNat j.divNat j.modNat
  have hv (i j r l : Fin (d * d)) :
      Matrix.reindex (shiftTwoSitePhysicalEquiv d) (shiftTwoSitePhysicalEquiv d)
          ((swapTensorSwapMatrix d * identitySwapIdentityMatrix d)) (i, j) (r, l) =
        SourceFactors.sourceV (shiftExampleU₂ d) S (i, j) (eR r, eL l) := by
    simpa [S, eL, eR, shiftExampleU₂SourceVColumnEquiv, shiftTwoSitePhysicalEquiv,
      Matrix.reindex_apply, hdecode] using
      (shiftExampleU₂Paper_sourceV_fourSpin_apply d i.divNat i.modNat j.divNat j.modNat
        r.divNat r.modNat l.divNat l.modNat).symm
  refine {
    phys_pos := Nat.mul_pos (NeZero.pos d) (NeZero.pos d)
    bond_pos := Nat.mul_pos (NeZero.pos d) (NeZero.pos d)
    left_pos := Nat.mul_pos (NeZero.pos d) (NeZero.pos d)
    right_pos := Nat.mul_pos (NeZero.pos d) (NeZero.pos d)
    X₁ := fun i r => S.X₁ i (eR r)
    X₂ := fun i l => S.X₂ i (eL l)
    u_unitary := (identitySwapIdentityMatrix_isUnitaryBetween d).reindex _ _ _
    v_unitary :=
      (swapTensorSwapMatrix_mul_identitySwapIdentityMatrix_isUnitaryBetween d).reindex _ _ _
    v_apply := hv
    W_apply := ?_
  }
  intro i j α γ
  rw [SourceFactors.blockTwo_apply_eq_sum_X₂_mul_sourceU_mul_X₁ (shiftExampleU₂ d) S,
    ← Equiv.sum_comp eL]
  apply Finset.sum_congr rfl
  intro l _
  rw [← Equiv.sum_comp eR]
  simp only [hu]

/-- The reversed family after two-site blocking, with the four-spin gates
of CPSV17, equation `eq:uv2_U3`, lines 2030–2034. -/
noncomputable def shiftExampleU₃BlockedStandardForm (d : ℕ) [NeZero d] :
    TwoSiteStandardFormData (blockTwo (shiftExampleU₃ d))
      (Matrix.reindex (shiftTwoSitePhysicalEquiv d) (shiftTwoSitePhysicalEquiv d)
        (identitySwapIdentityMatrix d * swapTensorSwapMatrix d))
      (Matrix.reindex (shiftTwoSitePhysicalEquiv d) (shiftTwoSitePhysicalEquiv d)
        (identitySwapIdentityMatrix d)) := by
  classical
  let S := shiftExampleU₃PaperSourceFactors d
  let eL := finProdFinEquiv.symm.trans (shiftExampleU₃LeftRankEquiv d)
  let eR := finProdFinEquiv.symm.trans (shiftExampleU₃RightRankEquiv d)
  have hdecode (x : Fin (d * d)) : finProdFinEquiv (x.divNat, x.modNat) = x :=
    finProdFinEquiv.apply_symm_apply x
  have hu (l r : Fin (d * d)) (i j : Fin (d * d)) :
      SourceFactors.sourceU (shiftExampleU₃ d) S (eL l, eR r) (i, j) =
        Matrix.reindex (shiftTwoSitePhysicalEquiv d) (shiftTwoSitePhysicalEquiv d)
          ((identitySwapIdentityMatrix d * swapTensorSwapMatrix d)) (l, r) (i, j) := by
    simpa [S, eL, eR, shiftExampleU₃SourceURowEquiv, shiftTwoSitePhysicalEquiv,
      Matrix.reindex_apply, hdecode] using
      shiftExampleU₃Paper_sourceU_fourSpin_apply d l.divNat l.modNat r.divNat r.modNat
        i.divNat i.modNat j.divNat j.modNat
  have hv (i j r l : Fin (d * d)) :
      Matrix.reindex (shiftTwoSitePhysicalEquiv d) (shiftTwoSitePhysicalEquiv d)
          (identitySwapIdentityMatrix d) (i, j) (r, l) =
        SourceFactors.sourceV (shiftExampleU₃ d) S (i, j) (eR r, eL l) := by
    simpa [S, eL, eR, shiftExampleU₃SourceVColumnEquiv, shiftTwoSitePhysicalEquiv,
      Matrix.reindex_apply, hdecode] using
      (shiftExampleU₃Paper_sourceV_fourSpin_apply d i.divNat i.modNat j.divNat j.modNat
        r.divNat r.modNat l.divNat l.modNat).symm
  refine {
    phys_pos := Nat.mul_pos (NeZero.pos d) (NeZero.pos d)
    bond_pos := Nat.mul_pos (NeZero.pos d) (NeZero.pos d)
    left_pos := Nat.mul_pos (NeZero.pos d) (NeZero.pos d)
    right_pos := Nat.mul_pos (NeZero.pos d) (NeZero.pos d)
    X₁ := fun i r => S.X₁ i (eR r)
    X₂ := fun i l => S.X₂ i (eL l)
    u_unitary :=
      (identitySwapIdentityMatrix_mul_swapTensorSwapMatrix_isUnitaryBetween d).reindex _ _ _
    v_unitary := (identitySwapIdentityMatrix_isUnitaryBetween d).reindex _ _ _
    v_apply := hv
    W_apply := ?_
  }
  intro i j α γ
  rw [SourceFactors.blockTwo_apply_eq_sum_X₂_mul_sourceU_mul_X₁ (shiftExampleU₃ d) S,
    ← Equiv.sum_comp eL]
  apply Finset.sum_congr rfl
  intro l _
  rw [← Equiv.sum_comp eR]
  simp only [hu]


/-- The blocked standard form retains the trace-normalized source-factor identities.
Source: CPSV17, `Y1Y1X1X1` and `eq:uv2_U2`. -/
theorem shiftExampleU₂BlockedStandardForm_normalized (d : ℕ) [NeZero d] :
    let T := shiftExampleU₂BlockedStandardForm d
    T.X₁ᴴ * sourceWeight (d := d * d) (shiftPaperWeightSquared d) * T.X₁ = 1 ∧
      T.X₂.IsIsometry := by
  let S := shiftExampleU₂PaperSourceFactors d
  let eR := finProdFinEquiv.symm.trans (shiftExampleU₂RightRankEquiv d)
  let eL := finProdFinEquiv.symm.trans (shiftExampleU₂LeftRankEquiv d)
  constructor
  · let X : Matrix (Fin (d * d) × Fin (d * d)) (Fin (d * d)) ℂ :=
      fun x r => S.X₁ x (eR r)
    change Xᴴ * sourceWeight (d := d * d) (shiftPaperWeightSquared d) * X = 1
    ext r t
    change (S.X₁ᴴ * sourceWeight (d := d * d) (shiftPaperWeightSquared d) * S.X₁)
      (eR r) (eR t) = (1 : Matrix (Fin (d * d)) (Fin (d * d)) ℂ) r t
    rw [S.X₁_weighted_isometry]
    change (if eR r = eR t then (1 : ℂ) else 0) = if r = t then 1 else 0
    simp
  · exact S.X₂_isometry.reindex S.X₂ (Equiv.refl _) eL.symm

/-- The blocked standard form retains the trace-normalized source-factor identities.
Source: CPSV17, `Y1Y1X1X1` and `eq:uv2_U3`. -/
theorem shiftExampleU₃BlockedStandardForm_normalized (d : ℕ) [NeZero d] :
    let T := shiftExampleU₃BlockedStandardForm d
    T.X₁ᴴ * sourceWeight (d := d * d) (shiftPaperWeightSquared d) * T.X₁ = 1 ∧
      T.X₂.IsIsometry := by
  let S := shiftExampleU₃PaperSourceFactors d
  let eR := finProdFinEquiv.symm.trans (shiftExampleU₃RightRankEquiv d)
  let eL := finProdFinEquiv.symm.trans (shiftExampleU₃LeftRankEquiv d)
  constructor
  · let X : Matrix (Fin (d * d) × Fin (d * d)) (Fin (d * d)) ℂ :=
      fun x r => S.X₁ x (eR r)
    change Xᴴ * sourceWeight (d := d * d) (shiftPaperWeightSquared d) * X = 1
    ext r t
    change (S.X₁ᴴ * sourceWeight (d := d * d) (shiftPaperWeightSquared d) * S.X₁)
      (eR r) (eR t) = (1 : Matrix (Fin (d * d)) (Fin (d * d)) ℂ) r t
    rw [S.X₁_weighted_isometry]
    change (if eR r = eR t then (1 : ℂ) else 0) = if r = t then 1 else 0
    simp
  · exact S.X₂_isometry.reindex S.X₂ (Equiv.refl _) eL.symm

private theorem ketLeftMul_shiftPhysicalSwap_apply {d D : ℕ}
    (U : MPOTensor (d * d) D) (i j : Fin (d * d)) (α β : Fin D) :
    U.ketLeftMul (shiftPhysicalSwap d) i j α β =
      U (finProdFinEquiv (i.modNat, i.divNat)) j α β := by
  simp [ketLeftMul, shiftPhysicalSwap, Equiv.Perm.permMatrix, PEquiv.toMatrix,
    bondPairSwapEquiv, bondPairSwap, Matrix.sum_apply, Matrix.ite_apply]

/-- The swap-transformed identity family has a swap gate followed by an
identity gate (CPSV17, `SFu1u3`, lines 2090–2099). -/
noncomputable def shiftExampleTildeU₁StandardForm (d : ℕ) [NeZero d] :
    TwoSiteStandardFormData (shiftExampleTildeU₁ d) (Matrix.swapMatrix d)
      (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) := by
  classical
  let S := shiftExampleU₁StandardForm d
  refine {
    phys_pos := S.phys_pos
    bond_pos := S.bond_pos
    left_pos := S.left_pos
    right_pos := S.right_pos
    X₁ := S.X₁
    X₂ := S.X₂
    u_unitary := Matrix.swapMatrix_isUnitaryBetween d
    v_unitary := S.v_unitary
    v_apply := S.v_apply
    W_apply := ?_
  }
  intro i j α γ
  have hαγ : α = γ := Subsingleton.elim _ _
  rw [shiftExampleTildeU₁, ketLeftMul_shiftPhysicalSwap_apply]
  simp [S, shiftExampleU₁StandardForm, shiftExampleU₁, identityMPUTensor,
    tensorProduct, idTensor, Matrix.reindex_apply,
    Matrix.swapMatrix, ite_and, apply_ite]
  split_ifs <;> simp_all

/-- The swap-transformed second family has an identity gate followed by a
swap gate (CPSV17, `SFu1u3`, lines 2090–2099). -/
noncomputable def shiftExampleTildeU₂StandardForm (d : ℕ) [NeZero d] :
    TwoSiteStandardFormData (shiftExampleTildeU₂ d)
      (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (Matrix.swapMatrix d) := by
  classical
  let c : ℂ := Real.sqrt d
  have hc : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast (Real.sqrt_pos.2 (Nat.cast_pos.mpr (NeZero.pos d))).ne'
  refine {
    phys_pos := NeZero.pos d
    bond_pos := Nat.mul_pos (NeZero.pos d) (NeZero.pos d)
    left_pos := NeZero.pos d
    right_pos := NeZero.pos d
    X₁ := fun i r => if i.2.divNat = i.1 ∧ i.2.modNat = r then c else 0
    X₂ := fun i l => if i.1.divNat = l ∧ i.1.modNat = i.2 then c⁻¹ else 0
    u_unitary := ⟨by simp [Matrix.IsIsometry], by simp [Matrix.IsCoisometry]⟩
    v_unitary := Matrix.swapMatrix_isUnitaryBetween d
    v_apply := ?_
    W_apply := ?_
  }
  · intro i₁ i₂ r l
    rw [← Equiv.sum_comp finProdFinEquiv]
    simp [Matrix.swapMatrix, Fintype.sum_prod_type, ite_and, eq_comm]
    split_ifs <;> simp_all
  · intro i j α γ
    rw [shiftExampleTildeU₂, ketLeftMul_shiftPhysicalSwap_apply]
    simp [shiftExampleU₂, tensorProduct, rightShiftTensor, leftShiftTensor,
      physicalAdjointTensor, Matrix.reindex_apply, Matrix.kroneckerMap_apply,
      Matrix.single, Matrix.one_apply, Prod.mk.injEq, ite_and, eq_comm]
    split_ifs <;> simp_all

/-- The swap-transformed identity family retains the normalized half factors.
Source: CPSV17, `SFu1u3`, lines 2090–2099. -/
theorem shiftExampleTildeU₁StandardForm_normalized (d : ℕ) [NeZero d] :
    (shiftExampleTildeU₁StandardForm d).X₁.IsIsometry ∧
      (shiftExampleTildeU₁StandardForm d).X₂.IsIsometry :=
  shiftExampleU₁StandardForm_normalized d

/-- The swap-transformed second family has normalized half factors with trace-one bond weight.
Source: CPSV17, `Y1Y1X1X1` and `SFu1u3`, lines 2090–2099. -/
theorem shiftExampleTildeU₂StandardForm_normalized (d : ℕ) [NeZero d] :
    let T := shiftExampleTildeU₂StandardForm d
    T.X₁ᴴ * sourceWeight (d := d) (shiftPaperWeightSquared d) * T.X₁ = 1 ∧
      T.X₂.IsIsometry := by
  have hw : sourceWeight (d := d) (shiftPaperWeightSquared d) =
      ((d : ℂ)⁻¹ * (d : ℂ)⁻¹) • (1 : Matrix (Fin d × Fin (d * d)) _ ℂ) := by
    simp [sourceWeight, shiftPaperWeightSquared, shiftPaperWeight, Matrix.kronecker_smul]
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hs : (Real.sqrt d : ℂ) * (Real.sqrt d : ℂ) = (d : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  constructor
  · rw [hw, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    ext r t
    simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type]
    simp_rw [← Equiv.sum_comp finProdFinEquiv]
    simp [shiftExampleTildeU₂StandardForm, Fintype.sum_prod_type, Matrix.one_apply,
      ite_and, mul_ite, eq_comm]
    split_ifs <;> simp_all [mul_assoc]
  · change (shiftExampleTildeU₂StandardForm d).X₂ᴴ * (shiftExampleTildeU₂StandardForm d).X₂ = 1
    ext r t
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type]
    rw [← Equiv.sum_comp finProdFinEquiv]
    simp [shiftExampleTildeU₂StandardForm, Fintype.sum_prod_type, Matrix.one_apply,
      ite_and, mul_ite, eq_comm]
    split_ifs <;> simp_all [Complex.ofReal_sqrt_inv_mul_self, Nat.cast_nonneg]

end MPOTensor
