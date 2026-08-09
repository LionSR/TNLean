/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinSum
import TNLean.MPS.BNT.Bridge
import TNLean.MPS.MPDO.BNTAssociativity
import TNLean.MPS.MPDO.BNTFusionTensorClause
import TNLean.MPS.MPDO.BNTMultiplicityNormalization
import TNLean.MPS.MPDO.RFPPositiveFusionDecomposition

/-!
# The BNT fusion clause from the MPDO renormalization fixed-point condition

This file gives the common construction of the BNT fusion tensor clause from
one-site and two-site vertical decompositions, and its specialization to an
MPDO in normalized BNT-refined horizontal form. The transported vertical forms
give both representations of the blocked closed-chain operator. Eventual
linear independence of the BNT operators compares their coefficients, and the
positive power-sum lemma gives the length-one trace-scalar identity.

## Main result

* `HasBNTFusionTensorClause.of_verticalDecompositions_of_unitaryBlockEquiv`
  completes positive fusion data related by a unitary sector equivalence to a
  BNT fusion tensor clause.
* `HasBNTFusionTensorClause.of_isRFPViaTS_of_horizontalCF` specializes the
  construction to normalized BNT-refined horizontal form.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Theorem 4.14 and Appendix C.4, lines 1929--2046
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

noncomputable section

namespace MPOTensor

/-- A CPSV16 basis of normal tensors gives eventual linear independence of
the corresponding closed-chain MPO operators.

Source: CPSV16, lines 271--275, used in Appendix C.4, lines 2030--2042. -/
theorem eventuallyLinearIndependent_verticalBNTOperatorFamily
    {g D d : ℕ} {dim : Fin g → ℕ}
    {M : MPOTensor d D} {A : (γ : Fin g) → MPSTensor (D * D) (dim γ)}
    (hBNT : MPSTensor.IsCPSVBasisOfNormalTensors (verticalTensor M)
      (fun γ ↦ ⟨dim γ, A γ⟩)) :
    (verticalBNTOperatorFamily A).EventuallyLinearIndependent := by
  obtain ⟨N₀, hli⟩ := hBNT.eventually_li
  refine ⟨N₀, ?_⟩
  intro L hL
  apply Fintype.linearIndependent_iff.mpr
  intro c hc γ
  have hzero : ∑ j : Fin g, c j •
      MPSTensor.mpvState (d := D * D) (A j) L = 0 := by
    apply PiLp.ext
    intro σ
    let ket : Fin L → Fin D := fun l ↦ (finProdFinEquiv.symm (σ l)).1
    let bra : Fin L → Fin D := fun l ↦ (finProdFinEquiv.symm (σ l)).2
    have hentry := congrArg (fun X ↦ X ket bra) hc
    change (∑ j, c j • mpo (verticalBNTMPO (A j)) L) ket bra =
      (0 : Matrix (Fin L → Fin D) (Fin L → Fin D) ℂ) ket bra at hentry
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.zero_apply] at hentry
    simp_rw [← MPSTensor.mpv_toMPSTensor_pairConfig] at hentry
    simp only [verticalBNTMPO_toMPSTensor] at hentry
    have hcfg : (fun n ↦ finProdFinEquiv (ket n, bra n)) = σ := by
      funext n
      exact Equiv.apply_symm_apply finProdFinEquiv (σ n)
    rw [hcfg] at hentry
    simpa [PiLp.smul_apply, PiLp.zero_apply, MPSTensor.mpvState_apply,
      smul_eq_mul, ket, bra, Equiv.apply_symm_apply] using hentry
  exact Fintype.linearIndependent_iff.mp (hli L hL) c hzero γ

/-- The simultaneous blocked-operator representations and the active-support
fusion law imply the length-one idempotent trace-scalar identity.

The proof is the coefficient comparison in CPSV16 Appendix C.4: eventual BNT
linear independence identifies all sufficiently large power sums, positivity
recovers the multiplicity multisets, and summing the resulting multiset
identity gives the idempotent law.

Source: CPSV16, Appendix C.4, lines 2030--2046, using the power-sum lemma at
lines 1155--1163. -/
theorem hasIdempotentCoefficientForm_of_blockedRepresentations
    {d D : ℕ} {M : MPOTensor d D}
    (D₁ : CPSVVerticalDecomposition M)
    (D₂ : CPSVVerticalDecomposition (blockTwo M))
    (sigma : Fin D₁.labelCount ≃ Fin D₂.labelCount)
    (chi : DiagonalChiFamily (Fin D₁.labelCount))
    (U : ∀ α β : Fin D₁.labelCount,
      Matrix ((γ : Fin D₁.labelCount) ×
        (Fin (chi.dim α β γ) × Fin (D₁.bondDim γ)))
        (Fin (D₁.bondDim α * D₁.bondDim β)) ℂ)
    (hChiPos : chi.PosEntries)
    (hCoisometry : ∀ α β, U α β * (U α β)ᴴ = 1)
    (hFusion : ∀ (α β : Fin D₁.labelCount) (i j : Fin D),
      U α β *
          (mulTensor (verticalBNTMPO (D₁.tensor α))
            (verticalBNTMPO (D₁.tensor β))) i j *
          (U α β)ᴴ =
        Matrix.blockDiagonal' fun γ ↦
          chi.matrix α β γ ⊗ₖ (verticalBNTMPO (D₁.tensor γ)) i j)
    (hReconstruction : ∀ (α β : Fin D₁.labelCount) (i j : Fin D),
      (mulTensor (verticalBNTMPO (D₁.tensor α))
        (verticalBNTMPO (D₁.tensor β))) i j =
        (U α β)ᴴ *
          (Matrix.blockDiagonal' fun γ ↦
            chi.matrix α β γ ⊗ₖ (verticalBNTMPO (D₁.tensor γ)) i j) *
          U α β)
    (hRepresentations : ∀ (L : ℕ), 0 < L →
      mpo (verticalBNTMPO (verticalTensor (blockTwo M))) L =
          ∑ γ,
            (((verticalMultiplicityTrace D₁.weight γ /
                verticalMultiplicityTrace D₂.weight (sigma γ)) ^ L) *
              (∑ r, D₂.weight (sigma γ) r ^ L)) •
              mpo (verticalBNTMPO (D₁.tensor γ)) L ∧
      mpo (verticalBNTMPO (verticalTensor (blockTwo M))) L =
        ∑ α, ∑ β,
          ((∑ q, D₁.weight α q ^ L) * (∑ r, D₁.weight β r ^ L)) •
            (mpo (verticalBNTMPO (D₁.tensor α)) L *
              mpo (verticalBNTMPO (D₁.tensor β)) L)) :
    (verticalBNTTraceScalarFamily D₁.weight).HasIdempotentCoefficientForm
      (BNTLabelCoefficientFamily.ofChi chi) := by
  classical
  let Fam : BNTFusionCoisometryFamily (Fin D₁.labelCount) D := {
    bondDim := D₁.bondDim
    tensor := fun γ ↦ verticalBNTMPO (D₁.tensor γ)
    chi := chi
    posEntries := hChiPos
    fusionCoisometry := U
    coisometry := hCoisometry
    fusion := hFusion
    reconstruction := hReconstruction
  }
  let op := verticalBNTOperatorFamily D₁.tensor
  let m := verticalBNTTraceScalarFamily D₁.weight
  have hOpLI : op.EventuallyLinearIndependent :=
    eventuallyLinearIndependent_verticalBNTOperatorFamily D₁.isCPSVBNT
  obtain ⟨N₀, hN₀⟩ := hOpLI
  have hCoeff : ∀ (L : ℕ), N₀ < L → ∀ γ,
      ((verticalMultiplicityTrace D₁.weight γ /
          verticalMultiplicityTrace D₂.weight (sigma γ)) ^ L) *
        (∑ r, D₂.weight (sigma γ) r ^ L) =
      ∑ α, ∑ β,
        ((∑ q, D₁.weight α q ^ L) *
          (∑ r, D₁.weight β r ^ L)) *
          Fam.chi.tracePowerCoeff α β γ L := by
    intro L hL γ
    have hLpos : 0 < L := lt_of_le_of_lt (Nat.zero_le N₀) hL
    obtain ⟨hFirst, hSecond⟩ := hRepresentations L hLpos
    have hProduct (α β : Fin D₁.labelCount) :
        mpo (verticalBNTMPO (D₁.tensor α)) L *
            mpo (verticalBNTMPO (D₁.tensor β)) L =
          ∑ γ, chi.tracePowerCoeff α β γ L •
            mpo (verticalBNTMPO (D₁.tensor γ)) L := by
      simpa only [Fam] using Fam.mpo_mul_mpo_eq_sum L hLpos α β
    have hExpanded :
        mpo (verticalBNTMPO (verticalTensor (blockTwo M))) L =
          ∑ γ, (∑ α, ∑ β,
            ((∑ q, D₁.weight α q ^ L) *
              (∑ r, D₁.weight β r ^ L)) *
              Fam.chi.tracePowerCoeff α β γ L) •
                mpo (verticalBNTMPO (D₁.tensor γ)) L := by
      rw [hSecond]
      simp_rw [hProduct, Finset.smul_sum, smul_smul]
      calc
        (∑ α, ∑ β, ∑ γ,
            (((∑ q, D₁.weight α q ^ L) *
              (∑ r, D₁.weight β r ^ L)) *
              chi.tracePowerCoeff α β γ L) •
                mpo (verticalBNTMPO (D₁.tensor γ)) L) =
            ∑ α, ∑ γ, ∑ β,
              (((∑ q, D₁.weight α q ^ L) *
                (∑ r, D₁.weight β r ^ L)) *
                chi.tracePowerCoeff α β γ L) •
                  mpo (verticalBNTMPO (D₁.tensor γ)) L := by
          apply Finset.sum_congr rfl
          intro α _
          rw [Finset.sum_comm]
        _ = ∑ γ, ∑ α, ∑ β,
              (((∑ q, D₁.weight α q ^ L) *
                (∑ r, D₁.weight β r ^ L)) *
                chi.tracePowerCoeff α β γ L) •
                  mpo (verticalBNTMPO (D₁.tensor γ)) L := by
          rw [Finset.sum_comm]
        _ = ∑ γ, (∑ α, ∑ β,
              ((∑ q, D₁.weight α q ^ L) *
                (∑ r, D₁.weight β r ^ L)) *
                chi.tracePowerCoeff α β γ L) •
                  mpo (verticalBNTMPO (D₁.tensor γ)) L := by
          apply Finset.sum_congr rfl
          intro γ _
          symm
          calc
            (∑ α, ∑ β,
                ((∑ q, D₁.weight α q ^ L) *
                  (∑ r, D₁.weight β r ^ L)) *
                  chi.tracePowerCoeff α β γ L) •
                mpo (verticalBNTMPO (D₁.tensor γ)) L =
              ∑ α, (∑ β,
                ((∑ q, D₁.weight α q ^ L) *
                  (∑ r, D₁.weight β r ^ L)) *
                  chi.tracePowerCoeff α β γ L) •
                mpo (verticalBNTMPO (D₁.tensor γ)) L := by
                  exact map_sum
                    ((smulAddHom ℂ
                      (Matrix (Fin L → Fin D) (Fin L → Fin D) ℂ)).flip
                        (mpo (verticalBNTMPO (D₁.tensor γ)) L))
                    (fun α ↦ ∑ β,
                      ((∑ q, D₁.weight α q ^ L) *
                        (∑ r, D₁.weight β r ^ L)) *
                        chi.tracePowerCoeff α β γ L)
                    Finset.univ
            _ = ∑ α, ∑ β,
                (((∑ q, D₁.weight α q ^ L) *
                  (∑ r, D₁.weight β r ^ L)) *
                  chi.tracePowerCoeff α β γ L) •
                mpo (verticalBNTMPO (D₁.tensor γ)) L := by
                  apply Finset.sum_congr rfl
                  intro α _
                  exact map_sum
                    ((smulAddHom ℂ
                      (Matrix (Fin L → Fin D) (Fin L → Fin D) ℂ)).flip
                        (mpo (verticalBNTMPO (D₁.tensor γ)) L))
                    (fun β ↦ ((∑ q, D₁.weight α q ^ L) *
                      (∑ r, D₁.weight β r ^ L)) *
                      chi.tracePowerCoeff α β γ L)
                    Finset.univ
    have hsum :
        ∑ γ,
            (((verticalMultiplicityTrace D₁.weight γ /
                verticalMultiplicityTrace D₂.weight (sigma γ)) ^ L) *
              (∑ r, D₂.weight (sigma γ) r ^ L)) •
              op.operator L γ =
          ∑ γ, (∑ α, ∑ β,
            ((∑ q, D₁.weight α q ^ L) *
              (∑ r, D₁.weight β r ^ L)) *
              Fam.chi.tracePowerCoeff α β γ L) •
              op.operator L γ := by
      simpa only [op, verticalBNTOperatorFamily_operator] using
        hFirst.symm.trans hExpanded
    exact congrFun
      (linearIndependent_iff_injective_fintypeLinearCombination.mp
        (hN₀ L hL) hsum) γ
  let twoEntry : ∀ γ : Fin D₁.labelCount,
      Fin (D₂.multiplicity (sigma γ)) → ℂ := fun γ r ↦
    (verticalMultiplicityTrace D₁.weight γ /
      verticalMultiplicityTrace D₂.weight (sigma γ)) *
        D₂.weight (sigma γ) r
  have hTwoPos : ∀ γ r, (0 : ℂ) < twoEntry γ r := by
    intro γ r
    exact mul_pos
      (div_pos
        (verticalMultiplicityTrace_pos D₁.multiplicity_pos D₁.weight_pos γ)
        (verticalMultiplicityTrace_pos D₂.multiplicity_pos D₂.weight_pos
          (sigma γ)))
      (D₂.weight_pos (sigma γ) r)
  let C := BNTMultiplicitySpectrumComparison.ofEventuallyEqualPowerSums
    Fam.chi m Fam.posEntries
    D₁.multiplicity D₁.weight D₁.weight_pos (fun _ ↦ rfl)
    (fun γ ↦ D₂.multiplicity (sigma γ)) twoEntry hTwoPos
    (L₀ := N₀) (by
      intro γ L hL
      rw [show (∑ r, twoEntry γ r ^ L) =
          ((verticalMultiplicityTrace D₁.weight γ /
            verticalMultiplicityTrace D₂.weight (sigma γ)) ^ L) *
              ∑ r, D₂.weight (sigma γ) r ^ L by
        simp only [twoEntry, mul_pow, Finset.mul_sum]]
      rw [hCoeff L hL γ]
      simp only [BNTProductMultiplicityIndex, Fintype.sum_sigma,
        Fintype.sum_prod_type, DiagonalChiFamily.tracePowerCoeff, mul_pow]
      apply Finset.sum_congr rfl
      intro α _
      apply Finset.sum_congr rfl
      intro β _
      rw [mul_assoc, Fintype.sum_mul_sum, Fintype.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro r _
      simpa only [mul_comm, mul_left_comm, mul_assoc] using
        (Fintype.sum_mul_mul_eq_mul_sum_mul (D₁.weight α q ^ L)
          (fun _ => D₁.weight β r ^ L)
          (fun k => Fam.chi.entry α β γ k ^ L)).symm)
  intro γ
  have hTwoTrace : ∑ r, C.twoEntry γ r = m.traceScalar γ := by
    change ∑ r, twoEntry γ r = ∑ q, D₁.weight γ q
    simp only [twoEntry]
    rw [← Finset.mul_sum]
    change (verticalMultiplicityTrace D₁.weight γ /
        verticalMultiplicityTrace D₂.weight (sigma γ)) *
        verticalMultiplicityTrace D₂.weight (sigma γ) =
      verticalMultiplicityTrace D₁.weight γ
    exact div_mul_cancel₀ _
      (verticalMultiplicityTrace_pos D₂.multiplicity_pos
        D₂.weight_pos (sigma γ)).ne'
  rw [← hTwoTrace, C.sum_twoEntry_eq_sum_products]
  simpa only [Fam, BNTLabelCoefficientFamily.ofChi_coeff] using
    C.sum_products_eq γ

namespace HasBNTFusionTensorClause

/-- Two vertical decompositions related by a unitary sector equivalence and a
positive active-sector fusion decomposition determine the BNT fusion tensor
clause.

This is the common final construction in the forward implication of CPSV16,
Theorem 4.14. The simultaneous one-site and two-site representations give the
idempotent trace-scalar identity, which completes the supplied positive fusion
data to the tensor clause.

Source: CPSV16, Theorem 4.14(i),(iii), lines 972--993, and Appendix C.4,
lines 2001--2046 of `Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem of_verticalDecompositions_of_unitaryBlockEquiv
    {d D : ℕ} {M : MPOTensor d D}
    (D₁ : CPSVVerticalDecomposition M)
    (D₂ : CPSVVerticalDecomposition (blockTwo M))
    (sigma : Fin D₁.labelCount ≃ Fin D₂.labelCount)
    (hDim : ∀ i, D₁.bondDim i = D₂.bondDim (sigma i))
    (V : ∀ i, Matrix.unitaryGroup (Fin (D₂.bondDim (sigma i))) ℂ)
    (hLetter : ∀ (i : Fin D₁.labelCount) (ab : Fin (D * D)),
      D₂.tensor (sigma i) ab =
        (verticalMultiplicityTrace D₁.weight i /
          verticalMultiplicityTrace D₂.weight (sigma i)) •
        ((V i : Matrix (Fin (D₂.bondDim (sigma i)))
            (Fin (D₂.bondDim (sigma i))) ℂ) *
          Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDim i)) (D₁.tensor i ab) *
          (V i : Matrix (Fin (D₂.bondDim (sigma i)))
            (Fin (D₂.bondDim (sigma i))) ℂ)ᴴ))
    (chi : DiagonalChiFamily (Fin D₁.labelCount))
    (U : ∀ α β : Fin D₁.labelCount,
      Matrix ((γ : Fin D₁.labelCount) ×
        (Fin (chi.dim α β γ) × Fin (D₁.bondDim γ)))
        (Fin (D₁.bondDim α * D₁.bondDim β)) ℂ)
    (hChiPos : chi.PosEntries)
    (hCoisometry : ∀ α β, U α β * (U α β)ᴴ = 1)
    (hFusion : ∀ (α β : Fin D₁.labelCount) (i j : Fin D),
      U α β *
          (mulTensor (verticalBNTMPO (D₁.tensor α))
            (verticalBNTMPO (D₁.tensor β))) i j *
          (U α β)ᴴ =
        Matrix.blockDiagonal' fun γ ↦
          chi.matrix α β γ ⊗ₖ (verticalBNTMPO (D₁.tensor γ)) i j)
    (hReconstruction : ∀ (α β : Fin D₁.labelCount) (i j : Fin D),
      (mulTensor (verticalBNTMPO (D₁.tensor α))
        (verticalBNTMPO (D₁.tensor β))) i j =
        (U α β)ᴴ *
          (Matrix.blockDiagonal' fun γ ↦
            chi.matrix α β γ ⊗ₖ (verticalBNTMPO (D₁.tensor γ)) i j) *
          U α β) :
    HasBNTFusionTensorClause M := by
  have hRepresentations : ∀ (L : ℕ), 0 < L →
      mpo (verticalBNTMPO (verticalTensor (blockTwo M))) L =
          ∑ γ,
            (((verticalMultiplicityTrace D₁.weight γ /
                verticalMultiplicityTrace D₂.weight (sigma γ)) ^ L) *
              (∑ r, D₂.weight (sigma γ) r ^ L)) •
              mpo (verticalBNTMPO (D₁.tensor γ)) L ∧
      mpo (verticalBNTMPO (verticalTensor (blockTwo M))) L =
        ∑ α, ∑ β,
          ((∑ q, D₁.weight α q ^ L) * (∑ r, D₁.weight β r ^ L)) •
            (mpo (verticalBNTMPO (D₁.tensor α)) L *
              mpo (verticalBNTMPO (D₁.tensor β)) L) := by
    intro L hL
    exact blockedVerticalOperatorRepresentations_of_unitaryBlockEquiv
      D₁.bondDim D₁.multiplicity D₁.weight
      D₂.bondDim D₂.multiplicity D₂.weight
      M D₁.tensor D₂.tensor
      D₁.verticalCoisometry D₂.verticalCoisometry
      D₁.coisometry D₂.coisometry
      D₁.reconstruction D₂.reconstruction
      sigma hDim V hLetter hL
  have hIdempotent := hasIdempotentCoefficientForm_of_blockedRepresentations
    D₁ D₂ sigma chi U hChiPos hCoisometry hFusion hReconstruction
    hRepresentations
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
    isCPSVBNT := D₁.isCPSVBNT
    forward := D₁.forward
    reconstruction := D₁.reconstruction
    chi := chi
    chi_pos := hChiPos
    fusionCoisometry := U
    fusionCoisometry_mul_conjTranspose := hCoisometry
    fusion := hFusion
    fusionReconstruction := hReconstruction
    idempotent := hIdempotent
  }⟩

/-- An MPDO in normalized BNT-refined horizontal form that satisfies the
Definition 4.1 renormalization fixed-point condition has the active-support
BNT fusion clause.

**Scope restriction (BNT-refined horizontal form):** `IsHorizontalCF` is
stronger than the literal CPSV canonical form used in Theorem 4.14 through
Proposition 4.13; see `docs/paper-gaps/cpgsv17_vertical_cf_grouping.tex`.

The one-site vertical decomposition supplies the BNT tensors, multiplicities,
and positive weights.
The transported RFP maps compare it with the two-site decomposition, produce
the positive chi matrices and fusion coisometries, and give both blocked
operator representations.  The preceding coefficient comparison supplies the
remaining length-one idempotent law.

Source: CPSV16, Appendix C.4, lines 1929--2046 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem of_isRFPViaTS_of_horizontalCF (M : MPOTensor d D)
    (hHorizontal : IsHorizontalCF M) (hM : IsMPDO M)
    (hRFP : IsRFPViaTS M) : HasBNTFusionTensorClause M := by
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
  obtain ⟨chi, U, hChiPos, hU, hFusion, hFusionReconstruction⟩ :=
    exists_positiveFusionDecomposition_of_unitaryBlockEquiv
      D₁.bondDim D₁.multiplicity D₁.weight
      D₂.bondDim D₂.multiplicity D₂.weight
      D₁.multiplicity_pos D₁.weight_pos
      D₂.multiplicity_pos D₂.weight_pos
      M D₁.tensor D₂.tensor D₂.isCPSVBNT
      D₁.verticalCoisometry D₂.verticalCoisometry
      D₁.coisometry D₂.coisometry D₁.reconstruction D₂.reconstruction
      sigma hDim V hLetter hHorizontal hM
  exact of_verticalDecompositions_of_unitaryBlockEquiv
    D₁ D₂ sigma hDim V hLetter chi U hChiPos hU hFusion
      hFusionReconstruction

end HasBNTFusionTensorClause

end MPOTensor
