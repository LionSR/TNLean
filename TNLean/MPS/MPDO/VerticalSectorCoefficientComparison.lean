/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.VerticalSectorGeneration
import TNLean.MPS.MPDO.VerticalSectorRelabeling

/-!
# Coefficients of transported vertical sectors

The unitary relabelling of the transported vertical-sector maps determines the
coefficient relating each two-site vertical BNT representative to its paired
one-site representative.  The coefficient is the ratio of the traces of the
two positive multiplicity matrices.

The source is CPSV16, arXiv:1606.00608, Appendix C.4, lines 2001--2008.
-/

open scoped Matrix ComplexOrder

noncomputable section

namespace MPOTensor

private theorem component_eq_of_unitary_single
    {g₁ g₂ : ℕ} {dim₁ : Fin g₁ → ℕ} {dim₂ : Fin g₂ → ℕ}
    (Tbar : VerticalSectorAlgebra dim₁ →ₗ[ℂ] VerticalSectorAlgebra dim₂)
    (sigma : Fin g₁ ≃ Fin g₂) (hDim : ∀ i, dim₁ i = dim₂ (sigma i))
    (V : ∀ i, Matrix.unitaryGroup (Fin (dim₂ (sigma i))) ℂ)
    (hSingle : ∀ (i : Fin g₁)
      (X : Matrix (Fin (dim₁ i)) (Fin (dim₁ i)) ℂ),
      Tbar (Pi.single i X) = Pi.single (sigma i)
        ((V i : Matrix (Fin (dim₂ (sigma i))) (Fin (dim₂ (sigma i))) ℂ) *
          Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDim i)) X *
            (V i : Matrix (Fin (dim₂ (sigma i))) (Fin (dim₂ (sigma i))) ℂ)ᴴ))
    (Y : VerticalSectorAlgebra dim₁) (i : Fin g₁) :
    Tbar Y (sigma i) =
      (V i : Matrix (Fin (dim₂ (sigma i))) (Fin (dim₂ (sigma i))) ℂ) *
        Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDim i)) (Y i) *
          (V i : Matrix (Fin (dim₂ (sigma i))) (Fin (dim₂ (sigma i))) ℂ)ᴴ := by
  classical
  calc
    Tbar Y (sigma i) = Tbar (∑ j, Pi.single j (Y j)) (sigma i) := by
      rw [Finset.univ_sum_single]
    _ = ∑ j, Tbar (Pi.single j (Y j)) (sigma i) := by
      rw [map_sum, Finset.sum_apply]
    _ = (V i : Matrix (Fin (dim₂ (sigma i))) (Fin (dim₂ (sigma i))) ℂ) *
          Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDim i)) (Y i) *
            (V i : Matrix (Fin (dim₂ (sigma i))) (Fin (dim₂ (sigma i))) ℂ)ᴴ := by
      rw [Finset.sum_eq_single i]
      · rw [hSingle, Pi.single_eq_same]
      · intro j _ hji
        rw [hSingle, Pi.single_eq_of_ne]
        exact sigma.injective.ne hji.symm
      · simp

private theorem component_eq_trace_ratio_smul_of_unitary_single
    {g₁ g₂ : ℕ} {dim₁ : Fin g₁ → ℕ} {dim₂ : Fin g₂ → ℕ}
    {mult₁ : Fin g₁ → ℕ} {mult₂ : Fin g₂ → ℕ}
    (weight₁ : (α : Fin g₁) → Fin (mult₁ α) → ℂ)
    (weight₂ : (β : Fin g₂) → Fin (mult₂ β) → ℂ)
    (hMult₂ : ∀ β, 0 < mult₂ β)
    (hWeight₂ : ∀ β q, (0 : ℂ) < weight₂ β q)
    (Tbar : VerticalSectorAlgebra dim₁ →ₗ[ℂ] VerticalSectorAlgebra dim₂)
    (sigma : Fin g₁ ≃ Fin g₂) (hDim : ∀ i, dim₁ i = dim₂ (sigma i))
    (V : ∀ i, Matrix.unitaryGroup (Fin (dim₂ (sigma i))) ℂ)
    (hSingle : ∀ (i : Fin g₁)
      (X : Matrix (Fin (dim₁ i)) (Fin (dim₁ i)) ℂ),
      Tbar (Pi.single i X) = Pi.single (sigma i)
        ((V i : Matrix (Fin (dim₂ (sigma i))) (Fin (dim₂ (sigma i))) ℂ) *
          Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDim i)) X *
            (V i : Matrix (Fin (dim₂ (sigma i))) (Fin (dim₂ (sigma i))) ℂ)ᴴ))
    (X₁ : VerticalSectorAlgebra dim₁) (X₂ : VerticalSectorAlgebra dim₂)
    (hScaled : Tbar (fun α ↦ verticalMultiplicityTrace weight₁ α • X₁ α) =
      fun β ↦ verticalMultiplicityTrace weight₂ β • X₂ β)
    (i : Fin g₁) :
    X₂ (sigma i) =
      (verticalMultiplicityTrace weight₁ i /
        verticalMultiplicityTrace weight₂ (sigma i)) •
      ((V i : Matrix (Fin (dim₂ (sigma i))) (Fin (dim₂ (sigma i))) ℂ) *
        Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDim i)) (X₁ i) *
          (V i : Matrix (Fin (dim₂ (sigma i))) (Fin (dim₂ (sigma i))) ℂ)ᴴ) := by
  have hComponent := congrFun hScaled (sigma i)
  rw [component_eq_of_unitary_single Tbar sigma hDim V hSingle] at hComponent
  simp only [map_smul, Matrix.mul_smul, Matrix.smul_mul] at hComponent
  have hn : verticalMultiplicityTrace weight₂ (sigma i) ≠ 0 :=
    verticalMultiplicityTrace_ne_zero (sigma i) (hMult₂ (sigma i)) (hWeight₂ (sigma i))
  calc
    X₂ (sigma i) = (verticalMultiplicityTrace weight₂ (sigma i))⁻¹ •
        (verticalMultiplicityTrace weight₂ (sigma i) • X₂ (sigma i)) := by
      rw [smul_smul, inv_mul_cancel₀ hn, one_smul]
    _ = (verticalMultiplicityTrace weight₂ (sigma i))⁻¹ •
        (verticalMultiplicityTrace weight₁ i •
          ((V i : Matrix (Fin (dim₂ (sigma i))) (Fin (dim₂ (sigma i))) ℂ) *
            Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDim i)) (X₁ i) *
              (V i : Matrix (Fin (dim₂ (sigma i))) (Fin (dim₂ (sigma i))) ℂ)ᴴ)) := by
      rw [hComponent]
    _ = _ := by
      rw [smul_smul, div_eq_mul_inv, mul_comm]

/-- Paired one-site and two-site vertical BNT sectors differ by unitary
conjugation and the ratio of their multiplicity-matrix traces.  The first
conclusion is the identity for an arbitrary horizontal bond contraction; the
second is its tensor-letter specialization.

Source: CPSV16, arXiv:1606.00608, Appendix C.4, lines 2001--2008. -/
theorem transportedVerticalSector_exists_unitaryBlockEquiv_coefficient_eq
    {g₁ g₂ d D : ℕ}
    (dim₁ mult₁ : Fin g₁ → ℕ)
    (weight₁ : (α : Fin g₁) → Fin (mult₁ α) → ℂ)
    (dim₂ mult₂ : Fin g₂ → ℕ)
    (weight₂ : (β : Fin g₂) → Fin (mult₂ β) → ℂ)
    (hMult₁ : ∀ α, 0 < mult₁ α)
    (hWeight₁ : ∀ α q, (0 : ℂ) < weight₁ α q)
    (hMult₂ : ∀ β, 0 < mult₂ β)
    (hWeight₂ : ∀ β q, (0 : ℂ) < weight₂ β q)
    (M : MPOTensor d D)
    (A₁ : (α : Fin g₁) → MPSTensor (D * D) (dim₁ α))
    (A₂ : (β : Fin g₂) → MPSTensor (D * D) (dim₂ β))
    (hBNT₁ : MPSTensor.IsCPSVBasisOfNormalTensors (verticalTensor M)
      (fun α ↦ ⟨dim₁ α, A₁ α⟩))
    (hBNT₂ : MPSTensor.IsCPSVBasisOfNormalTensors (verticalTensor (blockTwo M))
      (fun β ↦ ⟨dim₂ β, A₂ β⟩))
    (U₁ : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g₁, mult₁ α), verticalCopyDim dim₁ mult₁ q))
      (Fin d) ℂ)
    (U₂ : Matrix
      (Fin (∑ q : Fin (∑ β : Fin g₂, mult₂ β), verticalCopyDim dim₂ mult₂ q))
      (Fin (d * d)) ℂ)
    (hU₁ : U₁ * U₁ᴴ = 1)
    (hU₂ : U₂ * U₂ᴴ = 1)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ)
    (hTCPTP : IsKrausCPTP T)
    (hSCPTP : IsKrausCPTP S)
    (hForward₁ : ∀ ab, U₁ * verticalTensor M ab * U₁ᴴ =
      verticalAssembledTensor dim₁ mult₁ weight₁ A₁ ab)
    (hReconstruct₁ : ∀ ab, verticalTensor M ab =
      U₁ᴴ * verticalAssembledTensor dim₁ mult₁ weight₁ A₁ ab * U₁)
    (hForward₂ : ∀ ab, U₂ * verticalTensor (blockTwo M) ab * U₂ᴴ =
      verticalAssembledTensor dim₂ mult₂ weight₂ A₂ ab)
    (hReconstruct₂ : ∀ ab, verticalTensor (blockTwo M) ab =
      U₂ᴴ * verticalAssembledTensor dim₂ mult₂ weight₂ A₂ ab * U₂)
    (hTphys : ∀ X, T (physClose1 M X) = physClose2 M X)
    (hSphys : ∀ X, S (physClose2 M X) = physClose1 M X) :
    ∃ sigma : Fin g₁ ≃ Fin g₂, ∃ hDim : ∀ i, dim₁ i = dim₂ (sigma i),
      ∃ V : ∀ i, Matrix.unitaryGroup (Fin (dim₂ (sigma i))) ℂ,
        (∀ (i : Fin g₁) (X : Matrix (Fin D) (Fin D) ℂ),
          MPSTensor.contractBondMatrix (A₂ (sigma i)) X =
            (verticalMultiplicityTrace weight₁ i /
              verticalMultiplicityTrace weight₂ (sigma i)) •
            ((V i : Matrix (Fin (dim₂ (sigma i))) (Fin (dim₂ (sigma i))) ℂ) *
              Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDim i))
                (MPSTensor.contractBondMatrix (A₁ i) X) *
              (V i : Matrix (Fin (dim₂ (sigma i))) (Fin (dim₂ (sigma i))) ℂ)ᴴ)) ∧
        ∀ (i : Fin g₁) (ab : Fin (D * D)),
          A₂ (sigma i) ab =
            (verticalMultiplicityTrace weight₁ i /
              verticalMultiplicityTrace weight₂ (sigma i)) •
            ((V i : Matrix (Fin (dim₂ (sigma i))) (Fin (dim₂ (sigma i))) ℂ) *
              Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDim i)) (A₁ i ab) *
              (V i : Matrix (Fin (dim₂ (sigma i))) (Fin (dim₂ (sigma i))) ℂ)ᴴ) := by
  classical
  obtain ⟨sigma, hDim, V, hVT, _⟩ :=
    transportedVerticalSector_exists_unitaryBlockEquiv
      dim₁ mult₁ weight₁ dim₂ mult₂ weight₂
      hMult₁ hWeight₁ hMult₂ hWeight₂ M A₁ A₂ hBNT₁ hBNT₂
      U₁ U₂ hU₁ hU₂ T S hTCPTP hSCPTP
      hForward₁ hReconstruct₁ hForward₂ hReconstruct₂ hTphys hSphys
  have hCoefficient : ∀ (i : Fin g₁) (X : Matrix (Fin D) (Fin D) ℂ),
      MPSTensor.contractBondMatrix (A₂ (sigma i)) X =
        (verticalMultiplicityTrace weight₁ i /
          verticalMultiplicityTrace weight₂ (sigma i)) •
        ((V i : Matrix (Fin (dim₂ (sigma i))) (Fin (dim₂ (sigma i))) ℂ) *
          Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDim i))
            (MPSTensor.contractBondMatrix (A₁ i) X) *
          (V i : Matrix (Fin (dim₂ (sigma i))) (Fin (dim₂ (sigma i))) ℂ)ᴴ) := by
    intro i X
    let X₁ : VerticalSectorAlgebra dim₁ :=
      fun α ↦ MPSTensor.contractBondMatrix (A₁ α) X
    let X₂ : VerticalSectorAlgebra dim₂ :=
      fun β ↦ MPSTensor.contractBondMatrix (A₂ β) X
    have hScaled :
        transportedVerticalSectorT dim₁ mult₁ weight₁ dim₂ mult₂ U₁ U₂ T
            (fun α ↦ verticalMultiplicityTrace weight₁ α • X₁ α) =
          fun β ↦ verticalMultiplicityTrace weight₂ β • X₂ β := by
      exact transportedVerticalSectorT_contractBondMatrix_trace_smul
        dim₁ mult₁ weight₁ dim₂ mult₂ weight₂ hMult₁ hWeight₁
        M A₁ A₂ U₁ U₂ T hReconstruct₁ hForward₂ X (hTphys X)
    exact component_eq_trace_ratio_smul_of_unitary_single
      weight₁ weight₂ hMult₂ hWeight₂
      (transportedVerticalSectorT dim₁ mult₁ weight₁ dim₂ mult₂ U₁ U₂ T)
      sigma hDim V hVT X₁ X₂ hScaled i
  refine ⟨sigma, hDim, V, hCoefficient, ?_⟩
  intro i ab
  simpa only [MPSTensor.contractBondMatrix_single_mod_div] using
    hCoefficient i (Matrix.single ab.modNat ab.divNat 1)

end MPOTensor
