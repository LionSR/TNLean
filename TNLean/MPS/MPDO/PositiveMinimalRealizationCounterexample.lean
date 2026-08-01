/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.NormalCommutant
import TNLean.MPS.MPDO.BNTAlgebraTensorClausePositivity
import TNLean.MPS.MPDO.FigureEightPairwise
import TNLean.MPS.Tactic.Basic

/-!
# Closed matrix product vectors do not determine an isometric realization

This file gives two injective normal tensors with bond dimension two which
are related by the nonunitary similarity
\[
  X=\begin{pmatrix}2&0\\0&1\end{pmatrix}.
\]
They therefore have identical closed matrix product vectors.  Nevertheless,
the second tensor admits no square isometric compression onto a positive
scalar multiple of the first tensor.

Thus equality of positive-length closed matrix product vectors, even with a
positive coefficient equal to one, does not determine an isometric
realization of a prescribed normal representative.  A theorem asserting such
a realization must use a common physical tensor or equivalent marked-chain
information.

This is the obstruction recorded in the discussion of arXiv:1606.00608,
Appendix C.4, lines 2048--2057, and Proposition 4.13, lines 1898--1921.

## Main results

* `gramDressing_gauge_ne_one`: the exact invertible gauge does not preserve
  the identity Gram dressing.
* `sameMPV₂Pos_does_not_force_positive_isometric_realization`: the explicit
  nonunitary-similarity counterexample.
-/

open scoped Matrix ComplexOrder

noncomputable section

namespace MPSTensor.PositiveMinimalRealizationCounterexample

/-- Four matrices spanning \(M_2(\mathbb C)\).  The last missing matrix unit is
\(E_{11}=I-E_{00}\). -/
def tensor : MPSTensor 4 2 :=
  ![1, !![1, 0; 0, 0], !![0, 1; 0, 0], !![0, 0; 1, 0]]

/-- The nonunitary diagonal similarity used in the counterexample. -/
def gaugeMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![2, 0; 0, 1]

private lemma gaugeMatrix_det_ne_zero : gaugeMatrix.det ≠ 0 := by
  norm_num [gaugeMatrix, Matrix.det_fin_two]

/-- The invertible matrix represented by \(\operatorname{diag}(2,1)\). -/
def gauge : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero gaugeMatrix gaugeMatrix_det_ne_zero

@[simp]
lemma gauge_val : (gauge : Matrix (Fin 2) (Fin 2) ℂ) = gaugeMatrix :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

@[simp]
lemma gauge_inv_val :
    ((gauge⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![1 / 2, 0; 0, 1] := by
  have h : gauge * (Matrix.GeneralLinearGroup.mkOfDetNeZero
      (!![1 / 2, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) (by
        norm_num [Matrix.det_fin_two])) = 1 := by
    apply Units.ext
    simp only [Units.val_mul, gauge_val, gaugeMatrix, Units.val_one,
      Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  rw [show gauge⁻¹ = Matrix.GeneralLinearGroup.mkOfDetNeZero
      (!![1 / 2, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) (by
        norm_num [Matrix.det_fin_two]) from
    inv_eq_of_mul_eq_one_right h]
  exact Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

/-- The tensor obtained by conjugating every letter by
\(\operatorname{diag}(2,1)\). -/
def gaugedTensor : MPSTensor 4 2 :=
  fun i ↦
    (gauge : Matrix (Fin 2) (Fin 2) ℂ) * tensor i *
      ((gauge⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)

/-- The four displayed matrices span the full two-by-two matrix algebra. -/
lemma tensor_isInjective : tensor.IsInjective := by
  rw [IsInjective, eq_top_iff]
  intro M _
  have mem : ∀ i : Fin 4, tensor i ∈ Submodule.span ℂ (Set.range tensor) :=
    fun i ↦ Submodule.subset_span ⟨i, rfl⟩
  have hspan : ∀ p q : Fin 2, Matrix.single p q (1 : ℂ) ∈
      Submodule.span ℂ (Set.range tensor) := by
    intro p q
    fin_cases p <;> fin_cases q
    · exact (show tensor 1 = Matrix.single (0 : Fin 2) 0 (1 : ℂ) by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [tensor, Matrix.single]) ▸ mem 1
    · exact (show tensor 2 = Matrix.single (0 : Fin 2) 1 (1 : ℂ) by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [tensor, Matrix.single]) ▸ mem 2
    · exact (show tensor 3 = Matrix.single (1 : Fin 2) 0 (1 : ℂ) by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [tensor, Matrix.single]) ▸ mem 3
    · refine (show Matrix.single (1 : Fin 2) 1 (1 : ℂ) = tensor 0 - tensor 1 from ?_) ▸
        Submodule.sub_mem _ (mem 0) (mem 1)
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [tensor, Matrix.single, Matrix.sub_apply]
  have hM : M = M 0 0 • Matrix.single 0 0 1 + M 0 1 • Matrix.single 0 1 1 +
      M 1 0 • Matrix.single 1 0 1 + M 1 1 • Matrix.single 1 1 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.single]
  rw [hM]
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ _ (hspan 0 0)) (Submodule.smul_mem _ _ (hspan 0 1)))
    (Submodule.smul_mem _ _ (hspan 1 0))) (Submodule.smul_mem _ _ (hspan 1 1))

/-- The source tensor is normal already at word length one. -/
lemma tensor_isNormal : tensor.IsNormal :=
  tensor_isInjective.isNormal

/-- The two tensors are related by the displayed nonunitary similarity. -/
lemma tensor_gaugeEquiv_gaugedTensor : GaugeEquiv tensor gaugedTensor :=
  ⟨gauge, fun _ ↦ rfl⟩

/-- The conjugated tensor remains injective. -/
lemma gaugedTensor_isInjective : gaugedTensor.IsInjective :=
  isInjective_of_gaugeEquiv tensor_isInjective tensor_gaugeEquiv_gaugedTensor

/-- The conjugated tensor remains normal. -/
lemma gaugedTensor_isNormal : gaugedTensor.IsNormal :=
  isNormal_of_gaugeEquiv tensor_isNormal tensor_gaugeEquiv_gaugedTensor

/-- The two tensors have identical positive-length closed matrix product
vectors. -/
lemma tensor_sameMPV₂Pos_gaugedTensor : SameMPV₂Pos tensor gaugedTensor := by
  mpv_ext
  exact GaugeEquiv.sameMPV tensor_gaugeEquiv_gaugedTensor N σ

/-- The nonunitary similarity has a nontrivial Gram dressing on the source
tensor.

Thus equality of all positive-length closed chains and an exact invertible
gauge do not permit transport of the identity Gram dressing through a general
invertible gauge.  A common physical target or equivalent marked-chain
identity is still necessary.

Source: arXiv:1606.00608, Appendix C.4, lines 2048--2057, and Proposition
4.13, lines 1898--1921. -/
lemma gramDressing_gauge_ne_one :
    MPOTensor.gramDressing (D := 2) gauge tensor ≠
      MPOTensor.gramDressing (D := 2) (1 : GL (Fin 2) ℂ) tensor := by
  intro h
  have h2 := congrFun h 2
  simp only [MPOTensor.gramDressing] at h2
  rw [Matrix.mul_inv_rev, ← Matrix.conjTranspose_nonsing_inv] at h2
  rw [← Matrix.coe_units_inv gauge] at h2
  rw [gauge_inv_val] at h2
  have h201 := congrArg (fun M ↦ M 0 1) h2
  norm_num [gauge_val, gaugeMatrix, tensor,
    Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
    Matrix.conjTranspose_apply, map_ofNat] at h201
  simp at h201

@[simp]
private lemma tensor_zero : tensor 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tensor]

@[simp]
private lemma tensor_three : tensor 3 = !![0, 0; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tensor]

@[simp]
private lemma gaugedTensor_zero : gaugedTensor 0 = 1 := by
  rw [gaugedTensor, tensor_zero, Matrix.mul_one]
  change ((gauge * gauge⁻¹ : GL (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ) = 1
  simp

@[simp]
private lemma gaugedTensor_three : gaugedTensor 3 = !![0, 0; 1 / 2, 0] := by
  rw [gaugedTensor, tensor_three, gauge_val, gauge_inv_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gaugeMatrix, Matrix.mul_apply, Fin.sum_univ_two]

private lemma gauge_gram_not_scalar :
    ¬ ∃ z : ℂ,
      (gauge : Matrix (Fin 2) (Fin 2) ℂ)ᴴ *
        (gauge : Matrix (Fin 2) (Fin 2) ℂ) = z • 1 := by
  rintro ⟨z, hz⟩
  have h00 := congrArg (fun M ↦ M 0 0) hz
  have h11 := congrArg (fun M ↦ M 1 1) hz
  norm_num [gaugeMatrix, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.conjTranspose_apply, Matrix.smul_apply] at h00 h11
  have h := h00.trans h11.symm
  norm_num [map_ofNat] at h

/-- There is no square isometry compressing the conjugated tensor to a
positive scalar multiple of the original tensor.

The identity letter forces the scalar to equal one.  If such an isometry
existed, its product with the nonunitary gauge would commute with all four
letters.  Normality makes this product scalar, which would make
\(X^\dagger X=\operatorname{diag}(4,1)\) scalar, a contradiction. -/
lemma no_positive_isometric_realization :
    ¬ ∃ (c : ℝ) (V : Matrix (Fin 2) (Fin 2) ℂ),
      0 < c ∧ Vᴴ * V = 1 ∧
        ∀ i, Vᴴ * gaugedTensor i * V = (c : ℂ) • tensor i := by
  rintro ⟨c, V, _hc, hV, hcorner⟩
  have hc_complex : (c : ℂ) = 1 := by
    have h0 := hcorner 0
    rw [gaugedTensor_zero, tensor_zero] at h0
    simp only [Matrix.mul_one, hV] at h0
    have h00 := congrArg (fun M ↦ M 0 0) h0
    simpa [Matrix.smul_apply] using h00.symm
  have hVV : V * Vᴴ = 1 := mul_eq_one_comm.mpr hV
  let S : Matrix (Fin 2) (Fin 2) ℂ :=
    Vᴴ * (gauge : Matrix (Fin 2) (Fin 2) ℂ)
  have hcomm : ∀ i, S * tensor i = tensor i * S := by
    intro i
    have hi := hcorner i
    rw [hc_complex, one_smul] at hi
    dsimp only [S]
    calc
      (Vᴴ * (gauge : Matrix (Fin 2) (Fin 2) ℂ)) * tensor i =
          Vᴴ * (gauge : Matrix (Fin 2) (Fin 2) ℂ) * tensor i := rfl
      _ = Vᴴ * (gauge : Matrix (Fin 2) (Fin 2) ℂ) * tensor i *
          (((gauge⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
            (gauge : Matrix (Fin 2) (Fin 2) ℂ)) := by
        rw [← Units.val_mul]
        simp
      _ = Vᴴ * (gauge : Matrix (Fin 2) (Fin 2) ℂ) * tensor i *
          ((gauge⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
          (V * Vᴴ) * (gauge : Matrix (Fin 2) (Fin 2) ℂ) := by
        rw [hVV]
        simp [Matrix.mul_assoc]
      _ = (Vᴴ * gaugedTensor i * V) *
          (Vᴴ * (gauge : Matrix (Fin 2) (Fin 2) ℂ)) := by
        simp only [gaugedTensor]
        simp [Matrix.mul_assoc]
      _ = tensor i * (Vᴴ * (gauge : Matrix (Fin 2) (Fin 2) ℂ)) := by
        rw [hi]
  obtain ⟨z, hz⟩ := tensor_isNormal.eq_smul_one_of_commute hcomm
  apply gauge_gram_not_scalar
  refine ⟨star z * z, ?_⟩
  have hSgram :
      Sᴴ * S =
        (gauge : Matrix (Fin 2) (Fin 2) ℂ)ᴴ *
          (gauge : Matrix (Fin 2) (Fin 2) ℂ) := by
    dsimp only [S]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      ((gauge : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * V) *
          (Vᴴ * (gauge : Matrix (Fin 2) (Fin 2) ℂ)) =
          (gauge : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * (V * Vᴴ) *
            (gauge : Matrix (Fin 2) (Fin 2) ℂ) := by
        simp [Matrix.mul_assoc]
      _ = (gauge : Matrix (Fin 2) (Fin 2) ℂ)ᴴ *
          (gauge : Matrix (Fin 2) (Fin 2) ℂ) := by
        rw [hVV, Matrix.mul_one]
  rw [← hSgram, hz]
  simp [Matrix.conjTranspose_smul, smul_smul, mul_comm]

/-- Equality of positive-length closed matrix product vectors and positive
coefficient one do not force an isometric realization of a chosen normal
representative.

Both tensors are injective and normal, and they are related by an exact
invertible gauge.  Nevertheless, no square isometry compresses the second
tensor to a positive scalar multiple of the first. -/
theorem sameMPV₂Pos_does_not_force_positive_isometric_realization :
    tensor.IsInjective ∧ tensor.IsNormal ∧
      gaugedTensor.IsInjective ∧ gaugedTensor.IsNormal ∧
      GaugeEquiv tensor gaugedTensor ∧ SameMPV₂Pos tensor gaugedTensor ∧
      ¬ ∃ (c : ℝ) (V : Matrix (Fin 2) (Fin 2) ℂ),
        0 < c ∧ Vᴴ * V = 1 ∧
          ∀ i, Vᴴ * gaugedTensor i * V = (c : ℂ) • tensor i :=
  ⟨tensor_isInjective, tensor_isNormal,
    gaugedTensor_isInjective, gaugedTensor_isNormal,
    tensor_gaugeEquiv_gaugedTensor, tensor_sameMPV₂Pos_gaugedTensor,
    no_positive_isometric_realization⟩

/-- The terminal physical-trace transfer of the source tensor is
\(\begin{psmallmatrix}1&0\\1&1\end{psmallmatrix}\). -/
lemma physTraceTransfer_tensor :
    MPOTensor.physTraceTransfer (MPOTensor.verticalBNTMPO (D := 2) tensor) =
      !![1, 0; 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [MPOTensor.physTraceTransfer, MPOTensor.verticalBNTMPO, tensor,
      Fin.sum_univ_two, finProdFinEquiv]

/-- The source tensor in the minimal-realization counterexample has a
non-Hermitian terminal physical-trace transfer, hence it is not positive
semidefinite. -/
lemma physTraceTransfer_tensor_not_posSemidef :
    ¬ (MPOTensor.physTraceTransfer
      (MPOTensor.verticalBNTMPO (D := 2) tensor)).PosSemidef := by
  intro hPos
  have hHerm := hPos.isHermitian.apply (0 : Fin 2) (1 : Fin 2)
  rw [physTraceTransfer_tensor] at hHerm
  norm_num [Matrix.conjTranspose_apply] at hHerm

private theorem physTraceTransfer_verticalBNTMPO_cast_posSemidef {n m : ℕ}
    (h : n = m) (A : MPSTensor (2 * 2) n)
    (hPos : (MPOTensor.physTraceTransfer
      (MPOTensor.verticalBNTMPO (D := 2) A)).PosSemidef) :
    (MPOTensor.physTraceTransfer
      (MPOTensor.verticalBNTMPO
        (cast (congrArg (MPSTensor (2 * 2)) h) A))).PosSemidef := by
  cases h
  simpa using hPos

private theorem not_retained_positive_sector_of_physTraceTransfer_not_posSemidef
    (A : MPSTensor 4 2)
    (hA : ¬ (MPOTensor.physTraceTransfer
      (MPOTensor.verticalBNTMPO (D := 2) A)).PosSemidef) :
    ¬ ∃ (d : ℕ) (M : MPOTensor d 2) (H : MPOTensor.BNTAlgebraTensorClause M)
        (γ : Fin H.labelCount) (hBond : H.bondDim γ = 2),
      M.IsMPDO ∧
        cast (congrArg (MPSTensor (2 * 2)) hBond) (H.tensor γ) = A := by
  rintro ⟨d, M, H, γ, hBond, hM, hTensor⟩
  have hPos := H.physTraceTransfer_verticalBNTMPO_posSemidef hM γ
  have hPosCast :
      (MPOTensor.physTraceTransfer
        (MPOTensor.verticalBNTMPO
          (cast (congrArg (MPSTensor (2 * 2)) hBond) (H.tensor γ)))).PosSemidef := by
    exact physTraceTransfer_verticalBNTMPO_cast_posSemidef hBond (H.tensor γ) hPos
  rw [hTensor] at hPosCast
  exact hA hPosCast

/-- The source tensor of the minimal-realization counterexample cannot be a
retained sector of a tensor-attached BNT algebra clause for a positive MPO. -/
theorem tensor_not_retained_positive_sector :
    ¬ ∃ (d : ℕ) (M : MPOTensor d 2) (H : MPOTensor.BNTAlgebraTensorClause M)
        (γ : Fin H.labelCount) (hBond : H.bondDim γ = 2),
      M.IsMPDO ∧
        cast (congrArg (MPSTensor (2 * 2)) hBond) (H.tensor γ) = tensor := by
  exact not_retained_positive_sector_of_physTraceTransfer_not_posSemidef tensor
    physTraceTransfer_tensor_not_posSemidef

/-- The terminal physical-trace transfer of the gauged tensor is
\(\begin{psmallmatrix}1&0\\1/2&1\end{psmallmatrix}\). -/
lemma physTraceTransfer_gaugedTensor :
    MPOTensor.physTraceTransfer (MPOTensor.verticalBNTMPO (D := 2) gaugedTensor) =
      !![1, 0; 1 / 2, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [MPOTensor.physTraceTransfer, MPOTensor.verticalBNTMPO, Fin.sum_univ_two,
      finProdFinEquiv, Matrix.add_apply]

/-- The gauged tensor in the minimal-realization counterexample has a
non-Hermitian terminal physical-trace transfer, hence it is not positive
semidefinite. -/
lemma physTraceTransfer_gaugedTensor_not_posSemidef :
    ¬ (MPOTensor.physTraceTransfer
      (MPOTensor.verticalBNTMPO (D := 2) gaugedTensor)).PosSemidef := by
  intro hPos
  have hHerm := hPos.isHermitian.apply (0 : Fin 2) (1 : Fin 2)
  rw [physTraceTransfer_gaugedTensor] at hHerm
  norm_num [Matrix.conjTranspose_apply] at hHerm

/-- The gauged tensor of the minimal-realization counterexample cannot be a
retained sector of a tensor-attached BNT algebra clause for a positive MPO. -/
theorem gaugedTensor_not_retained_positive_sector :
    ¬ ∃ (d : ℕ) (M : MPOTensor d 2) (H : MPOTensor.BNTAlgebraTensorClause M)
        (γ : Fin H.labelCount) (hBond : H.bondDim γ = 2),
      M.IsMPDO ∧
        cast (congrArg (MPSTensor (2 * 2)) hBond) (H.tensor γ) = gaugedTensor := by
  exact not_retained_positive_sector_of_physTraceTransfer_not_posSemidef gaugedTensor
    physTraceTransfer_gaugedTensor_not_posSemidef

end MPSTensor.PositiveMinimalRealizationCounterexample
