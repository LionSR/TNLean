/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTFusionTensorClause
import TNLean.MPS.MPDO.BNTMultiplicityNormalization
import TNLean.MPS.MPDO.RFPPositiveFusionDecomposition
import TNLean.MPS.MPDO.VerticalBlockedOperatorRepresentations

/-!
# The BNT fusion clause from the renormalization fixed-point condition

This file proves the implication from the physical renormalization
fixed-point condition to the positive BNT fusion clause. The length-one
trace-scalar identity is obtained by comparing the two closed-chain
representations of the blocked vertical tensor and then applying the positive
power-sum theorem.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Theorem 4.14(i)--(iii), lines 972--993, and Appendix C.4,
  lines 1951--2042
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

noncomputable section

namespace MPOTensor

/-- The closed-chain operators of a CPSV16 basis of normal tensors are
linearly independent at every sufficiently large length.

This is the operator form of the eventual linear independence used to compare
the coefficients in CPSV16, Appendix C.4, lines 2038--2042. -/
private theorem eventually_linearIndependent_verticalBNTOperators
    {g D : ℕ} {dim : Fin g → ℕ}
    {T : MPSTensor (D * D) d}
    (A : (α : Fin g) → MPSTensor (D * D) (dim α))
    (hBNT : MPSTensor.IsCPSVBasisOfNormalTensors T
      (fun α ↦ ⟨dim α, A α⟩)) :
    ∃ L₀ : ℕ, ∀ L > L₀,
      LinearIndependent ℂ (fun α ↦ mpo (verticalBNTMPO (A α)) L) := by
  classical
  obtain ⟨L₀, hLI⟩ := hBNT.eventually_li
  refine ⟨L₀, fun L hL ↦ ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro c hc α
  apply Fintype.linearIndependent_iff.mp (hLI L hL) c
  apply PiLp.ext
  intro η
  let σ : Fin L → Fin D := fun n ↦ (finProdFinEquiv.symm (η n)).1
  let τ : Fin L → Fin D := fun n ↦ (finProdFinEquiv.symm (η n)).2
  have hη : (fun n ↦ finProdFinEquiv (σ n, τ n)) = η := by
    funext n
    exact finProdFinEquiv.apply_symm_apply (η n)
  have hEntry := congrFun (congrFun hc σ) τ
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.zero_apply,
    smul_eq_mul] at hEntry
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, MPSTensor.mpvState_apply, PiLp.zero_apply]
  rw [← hη]
  simpa only [← MPSTensor.mpv_toMPSTensor_pairConfig,
    verticalBNTMPO_toMPSTensor] using hEntry

namespace HasBNTFusionTensorClause

/-- **Implication (i) to (iii) of CPSV16, Theorem 4.14.**

A horizontally canonical matrix product density operator satisfying the
physical renormalization fixed-point condition has a positive fusion
coisometry for its vertical basis of normal tensors. The same diagonal
matrices satisfy the length-one idempotent trace-scalar identity.

The idempotent identity is derived from the two representations of the
blocked closed-chain operator, eventual linear independence of the BNT
operators, and the positive power-sum theorem.

**Local fix (Figure-11 fusion coisometry):** The fusion map is written in the
retained-row orientation, so it satisfies $UU^\dagger=1$ and its adjoint gives
exact reconstruction. Documented in
`docs/paper-gaps/cpsv16_figure11_fusion_coisometry.tex`.

Source: arXiv:1606.00608, Theorem 4.14(i)--(iii), lines 972--993, and
Appendix C.4, lines 1951--2042. -/
theorem of_isRFP (M : MPOTensor d D) (hHorizontal : IsHorizontalCF M)
    (hM : IsMPDO M) (hRFP : IsRFPViaTS M) :
    HasBNTFusionTensorClause M := by
  classical
  obtain ⟨D₁⟩ := hHorizontal.exists_cpsvVerticalDecomposition M hM
  obtain ⟨D₂⟩ := hHorizontal.blockTwo.exists_cpsvVerticalDecomposition
    (blockTwo M) hM.blockTwo
  obtain ⟨Smap, T, hSCPTP, hTCPTP, hSphys, hTphys⟩ := hRFP
  obtain ⟨sigma, hDim, V, _hContract, hLetter⟩ :=
    transportedVerticalSector_exists_unitaryBlockEquiv_coefficient_eq
      D₁.bondDim D₁.multiplicity D₁.weight
      D₂.bondDim D₂.multiplicity D₂.weight
      D₁.multiplicity_pos D₁.weight_pos
      D₂.multiplicity_pos D₂.weight_pos
      M D₁.tensor D₂.tensor D₁.isCPSVBNT D₂.isCPSVBNT
      D₁.verticalCoisometry D₂.verticalCoisometry
      D₁.coisometry D₂.coisometry T Smap hTCPTP hSCPTP
      D₁.forward D₁.reconstruction D₂.forward D₂.reconstruction
      hTphys hSphys
  obtain ⟨chi, U, hChi, hU, hFusion, hFusionReconstruction⟩ :=
    transportedVerticalSector_exists_positiveFusionDecomposition
      D₁.bondDim D₁.multiplicity D₁.weight
      D₂.bondDim D₂.multiplicity D₂.weight
      D₁.multiplicity_pos D₁.weight_pos
      D₂.multiplicity_pos D₂.weight_pos
      M D₁.tensor D₂.tensor D₁.isCPSVBNT D₂.isCPSVBNT
      D₁.verticalCoisometry D₂.verticalCoisometry
      D₁.coisometry D₂.coisometry T Smap hTCPTP hSCPTP
      D₁.forward D₁.reconstruction D₂.forward D₂.reconstruction
      hTphys hSphys hHorizontal hM
  let Fam : BNTFusionCoisometryFamily (Fin D₁.labelCount) D := {
    bondDim := D₁.bondDim
    tensor := fun γ ↦ verticalBNTMPO (D₁.tensor γ)
    chi := chi
    posEntries := hChi
    fusionCoisometry := U
    coisometry := hU
    fusion := hFusion
    reconstruction := hFusionReconstruction
  }
  have hIdempotent :
      (verticalBNTTraceScalarFamily D₁.weight).HasIdempotentCoefficientForm
        (BNTLabelCoefficientFamily.ofChi chi) := by
    let m := verticalBNTTraceScalarFamily D₁.weight
    let ratio : Fin D₁.labelCount → ℂ := fun γ ↦
      verticalMultiplicityTrace D₁.weight γ /
        verticalMultiplicityTrace D₂.weight (sigma γ)
    let twoEntry : ∀ γ : Fin D₁.labelCount,
        Fin (D₂.multiplicity (sigma γ)) → ℂ :=
      fun γ q ↦ ratio γ * D₂.weight (sigma γ) q
    have hRatioPos : ∀ γ, (0 : ℂ) < ratio γ := by
      intro γ
      exact div_pos
        (verticalMultiplicityTrace_pos D₁.multiplicity_pos D₁.weight_pos γ)
        (verticalMultiplicityTrace_pos D₂.multiplicity_pos D₂.weight_pos
          (sigma γ))
    have hTwoPos : ∀ γ q, (0 : ℂ) < twoEntry γ q := by
      intro γ q
      exact mul_pos (hRatioPos γ) (D₂.weight_pos (sigma γ) q)
    obtain ⟨L₀, hLinearIndependent⟩ :=
      eventually_linearIndependent_verticalBNTOperators D₁.tensor
        D₁.isCPSVBNT
    have hPowerSums : ∀ γ : Fin D₁.labelCount, ∀ L : ℕ, L₀ < L →
        (∑ r, twoEntry γ r ^ L) =
          ∑ x : BNTProductMultiplicityIndex chi D₁.multiplicity γ,
            (D₁.weight x.1 x.2.2.1 * D₁.weight x.2.1 x.2.2.2.1 *
              chi.entry x.1 x.2.1 γ x.2.2.2.2) ^ L := by
      intro γ L hLarge
      have hL : 0 < L := lt_of_le_of_lt (Nat.zero_le L₀) hLarge
      obtain ⟨hFirst, hSecond⟩ :=
        blockedVerticalOperatorRepresentations_of_unitaryBlockEquiv
          D₁.bondDim D₁.multiplicity D₁.weight
          D₂.bondDim D₂.multiplicity D₂.weight
          M D₁.tensor D₂.tensor D₁.verticalCoisometry
          D₂.verticalCoisometry D₁.coisometry D₂.coisometry
          D₁.reconstruction D₂.reconstruction sigma hDim V hLetter hL
      have hCommon :
          (∑ δ,
              ((ratio δ ^ L) * (∑ q, D₂.weight (sigma δ) q ^ L)) •
                mpo (verticalBNTMPO (D₁.tensor δ)) L) =
            ∑ δ,
              (∑ α, ∑ β,
                ((∑ q, D₁.weight α q ^ L) *
                    (∑ r, D₁.weight β r ^ L)) *
                  chi.tracePowerCoeff α β δ L) •
                mpo (verticalBNTMPO (D₁.tensor δ)) L := by
        calc
          _ = mpo (verticalBNTMPO (verticalTensor (blockTwo M))) L := by
            simpa only [ratio] using hFirst.symm
          _ = ∑ α, ∑ β,
              ((∑ q, D₁.weight α q ^ L) *
                (∑ r, D₁.weight β r ^ L)) •
                (mpo (verticalBNTMPO (D₁.tensor α)) L *
                  mpo (verticalBNTMPO (D₁.tensor β)) L) := hSecond
          _ = ∑ δ,
              (∑ α, ∑ β,
                ((∑ q, D₁.weight α q ^ L) *
                    (∑ r, D₁.weight β r ^ L)) *
                  chi.tracePowerCoeff α β δ L) •
                mpo (verticalBNTMPO (D₁.tensor δ)) L := by
            change (∑ α, ∑ β,
              ((∑ q, D₁.weight α q ^ L) *
                (∑ r, D₁.weight β r ^ L)) •
                (mpo (Fam.tensor α) L * mpo (Fam.tensor β) L)) = _
            simp_rw [Fam.mpo_mul_mpo_eq_sum L hL]
            simp only [Fam]
            simp only [Finset.smul_sum, Finset.sum_smul, smul_smul]
            calc
              _ = ∑ α, ∑ δ, ∑ β,
                  (((∑ q, D₁.weight α q ^ L) *
                      (∑ r, D₁.weight β r ^ L)) *
                    chi.tracePowerCoeff α β δ L) •
                    mpo (verticalBNTMPO (D₁.tensor δ)) L := by
                apply Finset.sum_congr rfl
                intro α _
                rw [Finset.sum_comm]
              _ = _ := by rw [Finset.sum_comm]
      have hCoeff :
          ratio γ ^ L * (∑ q, D₂.weight (sigma γ) q ^ L) =
            ∑ α, ∑ β,
              ((∑ q, D₁.weight α q ^ L) *
                  (∑ r, D₁.weight β r ^ L)) *
                chi.tracePowerCoeff α β γ L :=
        congrFun
          (linearIndependent_iff_injective_fintypeLinearCombination.mp
            (hLinearIndependent L hLarge) hCommon) γ
      calc
        (∑ r, twoEntry γ r ^ L) =
            ratio γ ^ L * (∑ r, D₂.weight (sigma γ) r ^ L) := by
          simp only [twoEntry, mul_pow, Finset.mul_sum]
        _ = ∑ α, ∑ β,
              ((∑ q, D₁.weight α q ^ L) *
                  (∑ r, D₁.weight β r ^ L)) *
                chi.tracePowerCoeff α β γ L := hCoeff
        _ = ∑ x : BNTProductMultiplicityIndex chi D₁.multiplicity γ,
              (D₁.weight x.1 x.2.2.1 * D₁.weight x.2.1 x.2.2.2.1 *
                chi.entry x.1 x.2.1 γ x.2.2.2.2) ^ L := by
          simp only [BNTProductMultiplicityIndex, Fintype.sum_sigma,
            Fintype.sum_prod_type, mul_pow,
            DiagonalChiFamily.tracePowerCoeff]
          apply Finset.sum_congr rfl
          intro α _
          apply Finset.sum_congr rfl
          intro β _
          symm
          calc
            (∑ i, ∑ j, ∑ k,
                (D₁.weight α i ^ L * D₁.weight β j ^ L) *
                  chi.entry α β γ k ^ L) =
                ∑ i, ∑ j,
                  (D₁.weight α i ^ L * D₁.weight β j ^ L) *
                    ∑ k, chi.entry α β γ k ^ L := by
              simp only [Finset.mul_sum, mul_assoc]
            _ = (∑ i, D₁.weight α i ^ L) *
                  ((∑ j, D₁.weight β j ^ L) *
                    ∑ k, chi.entry α β γ k ^ L) := by
              rw [Fintype.sum_mul_sum, Fintype.sum_mul_sum]
              simp only [Finset.mul_sum, mul_assoc]
            _ = ((∑ i, D₁.weight α i ^ L) *
                    (∑ j, D₁.weight β j ^ L)) *
                  ∑ k, chi.entry α β γ k ^ L := by
              ring
    let C : BNTMultiplicitySpectrumComparison chi m :=
      BNTMultiplicitySpectrumComparison.ofEventuallyEqualPowerSums
        chi m hChi D₁.multiplicity D₁.weight D₁.weight_pos
        (fun α ↦ rfl) (fun γ ↦ D₂.multiplicity (sigma γ)) twoEntry
        hTwoPos hPowerSums
    have hTwoTrace : ∀ γ, ∑ r, twoEntry γ r = m.traceScalar γ := by
      intro γ
      change (∑ r, ratio γ * D₂.weight (sigma γ) r) =
        verticalMultiplicityTrace D₁.weight γ
      rw [← Finset.mul_sum]
      change ratio γ * verticalMultiplicityTrace D₂.weight (sigma γ) = _
      simp only [ratio]
      exact div_mul_cancel₀ _
        (verticalMultiplicityTrace_ne_zero (sigma γ)
          (D₂.multiplicity_pos (sigma γ)) (D₂.weight_pos (sigma γ)))
    intro γ
    calc
      m.traceScalar γ = ∑ r, C.twoEntry γ r := by
        change m.traceScalar γ = ∑ r, twoEntry γ r
        exact (hTwoTrace γ).symm
      _ = ∑ x : BNTProductMultiplicityIndex chi C.oneDim γ,
          C.oneEntry x.1 x.2.2.1 * C.oneEntry x.2.1 x.2.2.2.1 *
            chi.entry x.1 x.2.1 γ x.2.2.2.2 :=
        C.sum_twoEntry_eq_sum_products γ
      _ = ∑ α, ∑ β,
          chi.tracePowerCoeff α β γ 1 *
            (m.traceScalar α * m.traceScalar β) :=
        C.sum_products_eq γ
  exact ⟨{
    labelCount := D₁.labelCount
    bondDim := D₁.bondDim
    multiplicity := D₁.multiplicity
    weight := D₁.weight
    tensor := D₁.tensor
    verticalCoisometry := D₁.verticalCoisometry
    multiplicity_pos := D₁.multiplicity_pos
    weight_pos := D₁.weight_pos
    coisometry := D₁.coisometry
    isBNT := D₁.isCPSVBNT.isBNT
    forward := D₁.forward
    reconstruction := D₁.reconstruction
    chi := chi
    chi_pos := hChi
    fusionCoisometry := U
    fusionCoisometry_mul_conjTranspose := hU
    fusion := hFusion
    fusionReconstruction := hFusionReconstruction
    idempotent := hIdempotent
  }⟩

end HasBNTFusionTensorClause

end MPOTensor
