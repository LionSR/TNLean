/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.ActiveBlocks
import TNLean.MPS.CanonicalForm.NormalTensorGauge
import TNLean.MPS.FundamentalTheorem.Multi
import TNLean.MPS.FundamentalTheorem.SectorBNT.PreparedReconstruction

/-!
# CPSV canonical forms as SectorBNT decompositions

A normalized nonzero CPSV canonical form determines a SectorBNT decomposition of its active
blocks. Each active normal block is first put into a trace-preserving gauge, after which the
prepared-block constructor groups phase-equivalent copies into BNT sectors.

Source: arXiv:2011.12127, lines 1831--1885; arXiv:1606.00608, lines 237--301 and
1135--1146.
-/
open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ} {A : MPSTensor d D}

private noncomputable def equivalenceCoisometry
    {α β : Type*} [DecidableEq β] (e : α ≃ β) : Matrix α β ℂ :=
  (1 : Matrix β β ℂ).submatrix e (Equiv.refl β)

@[simp] private theorem equivalenceCoisometry_apply
    {α β : Type*} [DecidableEq β] (e : α ≃ β) (x : α) (y : β) :
    equivalenceCoisometry e x y = if e x = y then 1 else 0 := by
  simp [equivalenceCoisometry, Matrix.one_apply]

private theorem equivalenceCoisometry_mul_conjTranspose
    {α β : Type*} [DecidableEq α] [Fintype β] [DecidableEq β] (e : α ≃ β) :
    equivalenceCoisometry e * (equivalenceCoisometry e)ᴴ = 1 := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    equivalenceCoisometry_apply]
  by_cases hxy : x = y
  · subst y
    simp
  · simp only [Matrix.one_apply, hxy, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro z _
    by_cases hxz : e x = z
    · have hyz : ¬ e y = z := by
        intro hyz
        exact hxy (e.injective (hxz.trans hyz.symm))
      simp [hxz, hyz]
    · simp [hxz]

private theorem reindex_eq_equivalenceCoisometry_conj
    {α β : Type*} [Fintype α] [Finite β] [DecidableEq β]
    (e : α ≃ β) (M : Matrix α α ℂ) :
    Matrix.reindex e e M =
      (equivalenceCoisometry e)ᴴ * M * equivalenceCoisometry e := by
  change Matrix.reindex e e M =
    ((1 : Matrix β β ℂ).submatrix e id)ᴴ * M *
      (1 : Matrix β β ℂ).submatrix e id
  classical
  let := Fintype.ofFinite β
  rw [Matrix.conjTranspose_submatrix]
  simp only [Matrix.conjTranspose_one]
  rw [Matrix.one_submatrix_mul id e M]
  rw [Matrix.mul_submatrix_one e id]
  rfl

private noncomputable def transportGL
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (Y : GL β ℂ) : GL α ℂ :=
  Units.map (Matrix.reindexAlgEquiv ℂ ℂ e.symm).toRingEquiv.toMonoidHom Y

@[simp] private theorem transportGL_val
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (Y : GL β ℂ) :
    (transportGL e Y : Matrix α α ℂ) = Matrix.reindex e.symm e.symm Y := rfl

@[simp] private theorem transportGL_inv_val
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (Y : GL β ℂ) :
    (↑((transportGL e Y)⁻¹) : Matrix α α ℂ) =
      Matrix.reindex e.symm e.symm (↑(Y⁻¹) : Matrix β β ℂ) := rfl

private theorem equivalenceCoisometry_mul_eq_transportGL_mul
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (Y : GL β ℂ) :
    equivalenceCoisometry e * (Y : Matrix β β ℂ) =
      (transportGL e Y : Matrix α α ℂ) * equivalenceCoisometry e := by
  change (1 : Matrix β β ℂ).submatrix e id * (Y : Matrix β β ℂ) =
    Matrix.reindex e.symm e.symm (Y : Matrix β β ℂ) *
      (1 : Matrix β β ℂ).submatrix e id
  calc
    (1 : Matrix β β ℂ).submatrix e id * (Y : Matrix β β ℂ) =
        Matrix.submatrix (Y : Matrix β β ℂ)
          ((Equiv.refl β).symm ∘ e) id :=
      Matrix.one_submatrix_mul e (Equiv.refl β) (Y : Matrix β β ℂ)
    _ = Matrix.reindex e.symm e.symm (Y : Matrix β β ℂ) *
        (1 : Matrix β β ℂ).submatrix e id := by
      rw [Matrix.mul_submatrix_one e id]
      ext x y
      simp [Matrix.reindex_apply, Matrix.submatrix_apply]

private theorem inv_mul_conjTranspose_equivalenceCoisometry_eq
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (Y : GL β ℂ) :
    (↑(Y⁻¹) : Matrix β β ℂ) * (equivalenceCoisometry e)ᴴ =
      (equivalenceCoisometry e)ᴴ *
        (↑((transportGL e Y)⁻¹) : Matrix α α ℂ) := by
  change (↑(Y⁻¹) : Matrix β β ℂ) *
      ((1 : Matrix β β ℂ).submatrix e id)ᴴ =
    ((1 : Matrix β β ℂ).submatrix e id)ᴴ *
      Matrix.reindex e.symm e.symm (↑(Y⁻¹) : Matrix β β ℂ)
  rw [Matrix.conjTranspose_submatrix]
  simp only [Matrix.conjTranspose_one]
  calc
    (↑(Y⁻¹) : Matrix β β ℂ) * (1 : Matrix β β ℂ).submatrix id e =
        Matrix.submatrix (↑(Y⁻¹) : Matrix β β ℂ) id
          ((Equiv.refl β).symm ∘ e) :=
      Matrix.mul_submatrix_one (Equiv.refl β) e
        (↑(Y⁻¹) : Matrix β β ℂ)
    _ = (1 : Matrix β β ℂ).submatrix id e *
        Matrix.reindex e.symm e.symm (↑(Y⁻¹) : Matrix β β ℂ) := by
      rw [Matrix.one_submatrix_mul id e]
      ext x y
      simp [Matrix.reindex_apply, Matrix.submatrix_apply]

namespace CPSVCanonicalFormData

/-- A normalized nonzero CPSV canonical form has an exact active BNT reconstruction through
a coisometry.

The sector decomposition retains exactly the nonzero-weight displayed block dimensions. The
matrix $U$ has orientation $U U^\dagger=1$, and the equality holds at every physical letter:
$$
A^i=U^\dagger X P^i X^{-1}U.
$$
Zero-weight displayed blocks and unused ambient coordinates do not contribute to the retained
bond dimension.

Source: arXiv:1606.00608, lines 214--301 and 1080--1148; arXiv:2011.12127,
lines 1831--1885. -/
theorem exists_active_isBNTCanonicalForm_exact
    (data : CPSVCanonicalFormData A)
    (hNorm : data.IsWeightNormalized)
    (hA : A ≠ 0) :
    ∃ P : SectorDecomposition d,
      IsBNTCanonicalForm P ∧
      P.totalDim = ∑ k : data.Active, data.dim k.1 ∧
      ∃ U : Matrix (Fin P.totalDim) (Fin D) ℂ, U * Uᴴ = 1 ∧
        ∃ X : GL (Fin P.totalDim) ℂ,
          ∀ i, A i = Uᴴ *
            ((X : Matrix _ _ ℂ) * P.toTensor i *
              (↑(X⁻¹) : Matrix _ _ ℂ)) * U := by
  classical
  have : ∀ k, NeZero (data.activeDim k) :=
    fun k => ⟨(data.dim_pos (data.activeEquiv k)).ne'⟩
  choose σ hσ hσfix hTP hGauge hPrim hIrr using
    fun k => (data.blocks_normal (data.activeEquiv k)).exists_tpGauge
  let prepared : (k : Fin (Fintype.card data.Active)) →
      MPSTensor d (data.activeDim k) := fun k =>
    tpGauge (data.blocks (data.activeEquiv k)) (σ k)
  have hDim : ∀ k, 0 < data.activeDim k := by
    intro k
    exact data.dim_pos (data.activeEquiv k)
  have hWeightNe : ∀ k, data.activeWeight k ≠ 0 := fun k => (data.activeEquiv k).property
  have hWeightLe : ∀ k, ‖data.activeWeight k‖ ≤ 1 := by
    intro k
    exact hNorm.weight_norm_le_one (data.activeEquiv k)
  have hWeightUnit : ∃ k, ‖data.activeWeight k‖ = 1 := by
    obtain ⟨k, hk⟩ := hNorm.weight_unit_exists hA
    have hkNe : data.weights k ≠ 0 := by
      intro hkZero
      simp [hkZero] at hk
    let ka : data.Active := ⟨k, hkNe⟩
    let l := data.activeEquiv.symm ka
    refine ⟨l, ?_⟩
    change ‖data.weights (data.activeEquiv l)‖ = 1
    rw [show data.activeEquiv l = ka by simp [l]]
    exact hk
  have hDirectGauge : GaugeEquiv
      (toTensorFromBlocks (d := d) data.activeWeight data.activeBlocks)
      (toTensorFromBlocks (d := d) data.activeWeight prepared) := by
    apply gaugeEquiv_toTensorFromBlocks_of_blockGauge
    intro k
    simpa only [prepared, activeBlocks, activeDim] using hGauge k
  obtain ⟨Y, hY⟩ := hDirectGauge
  obtain ⟨U, hU, hActive⟩ := data.exact_active_reconstruction
  obtain ⟨P, hBNT, hTotal, e, X, hExact⟩ :=
    exists_isBNTCanonicalForm_exact_of_tp_primitive_irr_blocks
      data.activeWeight prepared hDim hTP hPrim hIrr hWeightNe hWeightLe hWeightUnit
  have hTotalActive : P.totalDim = ∑ k : data.Active, data.dim k.1 := by
    rw [hTotal]
    exact data.activeEquiv.sum_comp (fun k : data.Active => data.dim k.1)
  let Q : Matrix (Fin P.totalDim) (Fin (∑ k, data.activeDim k)) ℂ :=
    equivalenceCoisometry e
  let W := transportGL e Y
  let Z : GL (Fin P.totalDim) ℂ := W⁻¹ * X
  let U' := Q * U
  have hQ : Q * Qᴴ = 1 := equivalenceCoisometry_mul_conjTranspose e
  have hU' : U' * U'ᴴ = 1 := by
    simp only [U', Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U Uᴴ, hU, Matrix.one_mul, hQ]
  have hOriginal : ∀ i,
      toTensorFromBlocks (d := d) data.activeWeight data.activeBlocks i =
        Qᴴ * ((Z : Matrix _ _ ℂ) * P.toTensor i *
          (↑(Z⁻¹) : Matrix _ _ ℂ)) * Q := by
    intro i
    have hp := hExact i
    rw [reindex_eq_equivalenceCoisometry_conj] at hp
    let Qh : Matrix (Fin (∑ k, data.activeDim k)) (Fin P.totalDim) ℂ := Qᴴ
    have hLeft := inv_mul_conjTranspose_equivalenceCoisometry_eq e Y
    have hRight := equivalenceCoisometry_mul_eq_transportGL_mul e Y
    change (↑(Y⁻¹) : Matrix _ _ ℂ) * Qh =
      Qh * (↑(W⁻¹) : Matrix _ _ ℂ) at hLeft
    change Q * (Y : Matrix _ _ ℂ) = (W : Matrix _ _ ℂ) * Q at hRight
    calc
      toTensorFromBlocks (d := d) data.activeWeight data.activeBlocks i =
          (↑(Y⁻¹) : Matrix _ _ ℂ) *
            ((Y : Matrix _ _ ℂ) *
              toTensorFromBlocks (d := d) data.activeWeight data.activeBlocks i *
              (↑(Y⁻¹) : Matrix _ _ ℂ)) * (Y : Matrix _ _ ℂ) := by
            simp only [← Matrix.mul_assoc]
            rw [Units.inv_mul, Matrix.one_mul]
            rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
      _ = (↑(Y⁻¹) : Matrix _ _ ℂ) *
            toTensorFromBlocks (d := d) data.activeWeight prepared i *
            (Y : Matrix _ _ ℂ) := by rw [hY]
      _ = (↑(Y⁻¹) : Matrix _ _ ℂ) *
            (Qh * ((X : Matrix _ _ ℂ) * P.toTensor i *
              (↑(X⁻¹) : Matrix _ _ ℂ)) * Q) *
            (Y : Matrix _ _ ℂ) := by rw [hp]
      _ = Qh * ((Z : Matrix _ _ ℂ) * P.toTensor i *
            (↑(Z⁻¹) : Matrix _ _ ℂ)) * Q := by
          let M : Matrix (Fin P.totalDim) (Fin P.totalDim) ℂ :=
            (X : Matrix _ _ ℂ) * P.toTensor i * (↑(X⁻¹) : Matrix _ _ ℂ)
          have hAssoc :
              (↑(Y⁻¹) : Matrix (Fin (∑ k, data.activeDim k))
                (Fin (∑ k, data.activeDim k)) ℂ) * (Qh * M * Q) *
                (Y : Matrix (Fin (∑ k, data.activeDim k))
                (Fin (∑ k, data.activeDim k)) ℂ) =
                ((↑(Y⁻¹) : Matrix (Fin (∑ k, data.activeDim k))
                (Fin (∑ k, data.activeDim k)) ℂ) * Qh) * M *
                  (Q * (Y : Matrix (Fin (∑ k, data.activeDim k))
                (Fin (∑ k, data.activeDim k)) ℂ)) := by
            simp only [Matrix.mul_assoc]
          have hMid :
              ((↑(Y⁻¹) : Matrix (Fin (∑ k, data.activeDim k))
                  (Fin (∑ k, data.activeDim k)) ℂ) * Qh) * M *
                  (Q * (Y : Matrix (Fin (∑ k, data.activeDim k))
                    (Fin (∑ k, data.activeDim k)) ℂ)) =
                (Qh * (↑(W⁻¹) : Matrix (Fin P.totalDim)
                  (Fin P.totalDim) ℂ)) * M *
                  ((W : Matrix (Fin P.totalDim) (Fin P.totalDim) ℂ) * Q) :=
            congrArg₂
              (fun (L : Matrix (Fin (∑ k, data.activeDim k))
                  (Fin P.totalDim) ℂ)
                (R : Matrix (Fin P.totalDim)
                  (Fin (∑ k, data.activeDim k)) ℂ) => L * M * R)
              hLeft hRight
          change (↑(Y⁻¹) : Matrix _ _ ℂ) * (Qh * M * Q) *
              (Y : Matrix _ _ ℂ) = _
          rw [hAssoc, hMid]
          change (Qh * (↑(W⁻¹) : Matrix (Fin P.totalDim)
              (Fin P.totalDim) ℂ)) * M *
              ((W : Matrix (Fin P.totalDim) (Fin P.totalDim) ℂ) * Q) =
            Qh * (((↑(W⁻¹) : Matrix (Fin P.totalDim) (Fin P.totalDim) ℂ) *
                (X : Matrix (Fin P.totalDim) (Fin P.totalDim) ℂ)) *
              P.toTensor i *
              ((↑(X⁻¹) : Matrix (Fin P.totalDim) (Fin P.totalDim) ℂ) *
                (W : Matrix (Fin P.totalDim) (Fin P.totalDim) ℂ))) * Q
          simp only [M, Matrix.mul_assoc]
  refine ⟨P, hBNT, hTotalActive, U', hU', Z, ?_⟩
  intro i
  rw [hActive i, hOriginal i]
  simp only [U', Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- A normalized nonzero CPSV canonical form has a SectorBNT decomposition whose total bond
dimension is the sum of its active block dimensions.

The conclusion concerns only the active direct sum. Zero-weight displayed blocks and unused
ambient coordinates do not contribute to this dimension.

Source: arXiv:2011.12127, lines 1831--1885; arXiv:1606.00608, lines 237--301 and
1135--1146. -/
theorem exists_active_isBNTCanonicalForm
    (data : CPSVCanonicalFormData A)
    (hNorm : data.IsWeightNormalized)
    (hA : A ≠ 0) :
    ∃ P : SectorDecomposition d,
      IsBNTCanonicalForm P ∧
      SameMPV₂Pos A P.toTensor ∧
      P.totalDim = ∑ k : data.Active, data.dim k.1 := by
  obtain ⟨P, hBNT, hTotal, U, hU, X, hReconstruct⟩ :=
    data.exists_active_isBNTCanonicalForm_exact hNorm hA
  let B : MPSTensor d P.totalDim := fun i =>
    (X : Matrix _ _ ℂ) * P.toTensor i * (↑(X⁻¹) : Matrix _ _ ℂ)
  have hCoisometry : SameMPV₂Pos A B :=
    sameMPV₂Pos_of_coisometry_reconstruction A B U hU hReconstruct
  have hGauge : GaugeEquiv P.toTensor B := ⟨X, fun _ => rfl⟩
  have hGaugeMPV : SameMPV₂Pos P.toTensor B :=
    fun N _hN w => GaugeEquiv.sameMPV hGauge N w
  exact ⟨P, hBNT, hCoisometry.trans hGaugeMPV.symm, hTotal⟩

end CPSVCanonicalFormData

end MPSTensor
