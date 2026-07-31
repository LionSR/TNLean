/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.BNTUniqueness
import TNLean.MPS.MPDO.BNTMultiplicityNormalization
import TNLean.MPS.MPDO.RFPPositiveFusionDecomposition
import TNLean.MPS.MPDO.VerticalBlockedOperatorRepresentations

/-!
# The two-site multiplicity spectrum from the BNT algebra clause

This file compares the chosen one-site vertical basis in a tensor-attached
BNT algebra clause with a vertical canonical decomposition of the two-site
blocking.  The same-length product law identifies the sectorwise power sums,
and positivity turns them into the multiplicity-spectrum comparison used in
the algebra-to-RFP implication.  The constructions below assume normalized
BNT-refined horizontal form, which is stronger than literal CPSV canonical
form.

## Main results

* `MPOTensor.BNTAlgebraTensorClause.toTwoSiteMultiplicitySpectrum` derives a two-site
  vertical canonical decomposition, its sector relabelling, and the multiplicity-spectrum
  comparison directly from the tensor algebra clause.
* `MPOTensor.BNTAlgebraTensorClause.toTwoSiteExactSectorGauge` additionally retains the
  bond-dimension identifications and exact invertible gauges of the paired sectors.
* `MPOTensor.BNTAlgebraTensorClause.toMultiplicitySpectrumComparison` retains the
  resulting multiplicity-spectrum comparison alone.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Theorem 4.14(ii) and Appendix C.4, lines 2046--2058
-/

open scoped Matrix BigOperators ComplexOrder
open Filter

noncomputable section

namespace MPOTensor

namespace BNTAlgebraTensorClause

/-- A source-derived two-site vertical canonical decomposition together with the
sector relabelling and multiplicity-spectrum equality of Appendix C.4.

**Scope restriction (invertible gauge):** This structure records the matched
sector MPVs and spectrum, but not the line-2057 unitary gauge conclusion.  The
invertible-gauge sub-result and the missing common-target normalization contract
are documented in
`docs/paper-gaps/cpsv16_two_site_sector_unitary_gauge_gap.tex`.

Source: arXiv:1606.00608, Appendix C.4, lines 2046--2058 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
structure TwoSiteMultiplicitySpectrum {M : MPOTensor d D}
    (H : BNTAlgebraTensorClause M) where
  /-- The vertical canonical decomposition of the two-site blocking from
  arXiv:1606.00608, Appendix C.4, lines 2046--2049. -/
  decomposition : CPSVVerticalDecomposition (blockTwo M)
  /-- The bijection matching the one-site product sectors with the two-site sectors from
  arXiv:1606.00608, Appendix C.4, lines 2050--2054. -/
  relabel : Fin H.labelCount ≃ Fin decomposition.labelCount
  /-- The matched one-site and two-site tensors generate the same positive-length matrix
  product vectors.

  **Scope restriction (invertible gauge):** This field does not record the
  line-2057 unitary upgrade.  The restriction is documented in
  `docs/paper-gaps/cpsv16_two_site_sector_unitary_gauge_gap.tex`.

  Source: arXiv:1606.00608, Appendix C.4, lines 2053--2057. -/
  sector_sameMPV : ∀ γ : Fin H.labelCount,
    MPSTensor.SameMPV₂Pos (H.tensor γ) (decomposition.tensor (relabel γ))
  /-- Equality with multiplicity between the matched two-site weights and the products of
  one-site and chi weights from arXiv:1606.00608, Appendix C.4, lines 2054--2058. -/
  spectrum_eq : ∀ γ : Fin H.labelCount,
    Finset.univ.val.map (decomposition.weight (relabel γ)) =
      Finset.univ.val.map fun x : BNTProductMultiplicityIndex
          H.algebraClause.positiveChi.chi H.multiplicity γ =>
        H.weight x.1 x.2.2.1 * H.weight x.2.1 x.2.2.2.1 *
          H.algebraClause.positiveChi.chi.entry x.1 x.2.1 γ x.2.2.2.2

/-- A source-derived two-site multiplicity spectrum together with exact invertible
conjugacies between its paired normal tensors.

**Scope restriction (invertible gauge):** This structure retains the phase-one
invertible conjugacy from Appendix C.4, but not the line-2057 conclusion that the
gauge may be chosen unitary.  The missing common-target normalization contract is
documented in `docs/paper-gaps/cpsv16_two_site_sector_unitary_gauge_gap.tex` and
tracked in issue 4648.  The subsequent scalar-to-unitary normalization is
tracked in issue 4645.

Source: arXiv:1606.00608, Appendix C.4, lines 2053--2057 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
structure TwoSiteExactSectorGauge {M : MPOTensor d D}
    (H : BNTAlgebraTensorClause M) extends TwoSiteMultiplicitySpectrum H where
  /-- Equality of the paired one-site and two-site bond dimensions from
  arXiv:1606.00608, Appendix C.4, lines 2053--2055. -/
  bondDim_eq : ∀ γ : Fin H.labelCount,
    H.bondDim γ = decomposition.bondDim (relabel γ)
  /-- The invertible gauge identifying each pair of normal tensors.

  **Scope restriction (invertible gauge):** This field does not assert that the
  gauge is unitary.  The line-2057 upgrade is documented in
  `docs/paper-gaps/cpsv16_two_site_sector_unitary_gauge_gap.tex`.

  Source: arXiv:1606.00608, Appendix C.4, lines 2053--2057. -/
  gauge : ∀ γ : Fin H.labelCount,
    GL (Fin (decomposition.bondDim (relabel γ))) ℂ
  /-- The paired two-site tensor is the exact conjugate of the one-site tensor,
  with no residual scalar phase, as in arXiv:1606.00608, Appendix C.4,
  lines 2053--2057.

  **Scope restriction (invertible gauge):** Exactness here means phase one; the
  conjugating gauge has not been proved unitary.  The missing line-2057 conclusion
  is documented in
  `docs/paper-gaps/cpsv16_two_site_sector_unitary_gauge_gap.tex`. -/
  tensor_eq : ∀ (γ : Fin H.labelCount) (i : Fin (D * D)),
    decomposition.tensor (relabel γ) i =
      (gauge γ : Matrix (Fin (decomposition.bondDim (relabel γ)))
        (Fin (decomposition.bondDim (relabel γ))) ℂ) *
      (cast (congrArg (MPSTensor (D * D)) (bondDim_eq γ)) (H.tensor γ)) i *
      (↑((gauge γ)⁻¹) : Matrix (Fin (decomposition.bondDim (relabel γ)))
        (Fin (decomposition.bondDim (relabel γ))) ℂ)

/-- The chosen two-site decomposition and relabelling determine the corresponding
multiplicity-spectrum comparison.

Source: arXiv:1606.00608, Appendix C.4, lines 2046--2058 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
noncomputable def TwoSiteMultiplicitySpectrum.toComparison
    {M : MPOTensor d D} {H : BNTAlgebraTensorClause M}
    (S : TwoSiteMultiplicitySpectrum H) :
    BNTMultiplicitySpectrumComparison H.algebraClause.positiveChi.chi
      H.traceScalars where
  oneDim := H.multiplicity
  oneEntry := H.weight
  oneTrace := fun α =>
    (BNTAlgebraTensorClause.traceScalars_traceScalar H α).symm
  twoDim := fun γ => S.decomposition.multiplicity (S.relabel γ)
  twoEntry := fun γ => S.decomposition.weight (S.relabel γ)
  spectrum_eq := S.spectrum_eq

/-- The tensor-attached BNT algebra clause determines the two-site multiplicity
spectrum together with exact invertible gauges of the paired normal tensors.

The chosen one-site tensors and multiplicity entries are exactly those stored
in `H`.  No renormalization maps or pre-existing one-site/two-site sector
correspondence are assumed: full support of the two positive vertical
decompositions derives the sector relabelling, and eventual BNT linear
independence derives the power-sum equality.

**Scope restriction (BNT-refined horizontal form):** `IsHorizontalCF` is the
normalized BNT-refined horizontal form, stronger than the literal CPSV
canonical form used in Appendix C.4 through Proposition 4.13; see
`docs/paper-gaps/cpgsv17_vertical_cf_grouping.tex`.

**Scope restriction (invertible gauge):** The result retains bond-dimension
equality and phase-one invertible conjugacy, but does not prove the line-2057
unitary upgrade.  The missing common-target normalization contract is documented
in `docs/paper-gaps/cpsv16_two_site_sector_unitary_gauge_gap.tex` and tracked in
issue 4648.  The subsequent scalar-to-unitary normalization is tracked in issue
4645.

Source: arXiv:1606.00608, Theorem 4.14(ii) and Appendix C.4, lines 2046--2058
of `Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
noncomputable def toTwoSiteExactSectorGauge
    {M : MPOTensor d D} (H : BNTAlgebraTensorClause M)
    (hHorizontal : IsHorizontalCF M) (hM : IsMPDO M) :
    TwoSiteExactSectorGauge H := by
  classical
  let chi := H.algebraClause.positiveChi.chi
  let productIndex (γ : Fin H.labelCount) :=
    BNTProductMultiplicityIndex chi H.multiplicity γ
  let productEquiv (γ : Fin H.labelCount) :
      Fin (Fintype.card (productIndex γ)) ≃ productIndex γ :=
    (Fintype.equivFin (productIndex γ)).symm
  let productDim (γ : Fin H.labelCount) :=
    Fintype.card (productIndex γ)
  let productEntry : ∀ γ : Fin H.labelCount, Fin (productDim γ) → ℂ :=
    fun γ r ↦
      let x := productEquiv γ r
      H.weight x.1 x.2.2.1 * H.weight x.2.1 x.2.2.2.1 *
        chi.entry x.1 x.2.1 γ x.2.2.2.2
  have hProductPos : ∀ γ r, (0 : ℂ) < productEntry γ r := by
    intro γ r
    exact mul_pos
      (mul_pos (H.weight_pos _ _) (H.weight_pos _ _))
      (H.algebraClause.positiveChi.posEntries _ _ _ _)
  have hProductSum : ∀ γ, ∑ r, productEntry γ r =
      H.traceScalars.traceScalar γ := by
    intro γ
    change (∑ r, productEntry γ r) =
      (verticalBNTTraceScalarFamily H.weight).traceScalar γ
    rw [H.algebraClause.idempotent_coefficient_form_ofChi γ]
    simp only [BNTLabelCoefficientFamily.ofChi_coeff]
    change (∑ r, productEntry γ r) =
      ∑ α, ∑ β, chi.tracePowerCoeff α β γ 1 *
        ((∑ q, H.weight α q) * ∑ r, H.weight β r)
    rw [show (∑ r, productEntry γ r) =
        ∑ x : productIndex γ,
          H.weight x.1 x.2.2.1 * H.weight x.2.1 x.2.2.2.1 *
            chi.entry x.1 x.2.1 γ x.2.2.2.2 by
      exact productEquiv γ |>.sum_comp
        (fun x : productIndex γ ↦
          H.weight x.1 x.2.2.1 * H.weight x.2.1 x.2.2.2.1 *
            chi.entry x.1 x.2.1 γ x.2.2.2.2)]
    simp only [productIndex, BNTProductMultiplicityIndex,
      Fintype.sum_sigma, Fintype.sum_prod_type,
      DiagonalChiFamily.tracePowerCoeff, pow_one]
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro β _
    simp only [← Finset.mul_sum, ← Finset.sum_mul, mul_assoc]
    ring
  have hProductDimPos : ∀ γ, 0 < productDim γ := by
    intro γ
    by_contra h
    have hzero : productDim γ = 0 := Nat.eq_zero_of_not_pos h
    have hsumZero : ∑ r, productEntry γ r = 0 := by
      haveI : IsEmpty (Fin (productDim γ)) :=
        Fintype.card_eq_zero_iff.mp (by simpa using hzero)
      exact Finset.sum_eq_zero fun r _ ↦ isEmptyElim r
    have hTracePos :
        (0 : ℂ) < H.traceScalars.traceScalar γ := by
      change (0 : ℂ) < verticalMultiplicityTrace H.weight γ
      exact verticalMultiplicityTrace_pos H.multiplicity_pos H.weight_pos γ
    exact hTracePos.ne' ((hProductSum γ).symm.trans hsumZero)
  let P : MPSTensor.SectorDecomposition (D * D) := {
    basisCount := H.labelCount
    basisDim := H.bondDim
    basis := H.tensor
    sectors := {
      copies := productDim
      copies_pos := hProductDimPos
      weight := productEntry
      weight_ne_zero := fun γ r ↦ (hProductPos γ r).ne' }
  }
  have hBlockedExpansion : ∀ (L : ℕ), 0 < L →
      mpo (verticalBNTMPO (verticalTensor (blockTwo M))) L =
        ∑ γ, P.coeff L γ • mpo (verticalBNTMPO (H.tensor γ)) L := by
    intro L hL
    have hOne := mpo_verticalBNTMPO_eq_sum_of_coisometry_reconstruction
      H.weight H.tensor (verticalTensor M) H.verticalCoisometry
      H.coisometry H.reconstruction hL
    have hSecond :
        mpo (verticalBNTMPO (verticalTensor (blockTwo M))) L =
          ∑ α, ∑ β,
            ((∑ q, H.weight α q ^ L) * (∑ r, H.weight β r ^ L)) •
              (mpo (verticalBNTMPO (H.tensor α)) L *
                mpo (verticalBNTMPO (H.tensor β)) L) := by
      rw [verticalBNTMPO_verticalTensor_blockTwo, mpo_mulTensor, hOne]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro α _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro β _
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have hProduct (α β : Fin H.labelCount) :
        mpo (verticalBNTMPO (H.tensor α)) L *
            mpo (verticalBNTMPO (H.tensor β)) L =
          ∑ γ, chi.tracePowerCoeff α β γ L •
            mpo (verticalBNTMPO (H.tensor γ)) L := by
      change H.operators.operator L α * H.operators.operator L β =
        ∑ γ, chi.tracePowerCoeff α β γ L • H.operators.operator L γ
      simpa only [chi, BNTLabelCoefficientFamily.ofChi_coeff,
        BNTAlgebraTensorClause.operators,
        ← H.algebraClause.positiveChi.tracePower L hL] using
          H.algebraClause.sameLengthProduct L hL α β
    rw [hSecond]
    simp_rw [hProduct, Finset.smul_sum, smul_smul]
    calc
      (∑ α, ∑ β, ∑ γ,
          (((∑ q, H.weight α q ^ L) *
            (∑ r, H.weight β r ^ L)) *
            chi.tracePowerCoeff α β γ L) •
              mpo (verticalBNTMPO (H.tensor γ)) L) =
          ∑ α, ∑ γ, ∑ β,
            (((∑ q, H.weight α q ^ L) *
              (∑ r, H.weight β r ^ L)) *
              chi.tracePowerCoeff α β γ L) •
                mpo (verticalBNTMPO (H.tensor γ)) L := by
        apply Finset.sum_congr rfl
        intro α _
        rw [Finset.sum_comm]
      _ = ∑ γ, ∑ α, ∑ β,
            (((∑ q, H.weight α q ^ L) *
              (∑ r, H.weight β r ^ L)) *
              chi.tracePowerCoeff α β γ L) •
                mpo (verticalBNTMPO (H.tensor γ)) L := by
        rw [Finset.sum_comm]
      _ = ∑ γ, (∑ α, ∑ β,
            ((∑ q, H.weight α q ^ L) *
              (∑ r, H.weight β r ^ L)) *
              chi.tracePowerCoeff α β γ L) •
                mpo (verticalBNTMPO (H.tensor γ)) L := by
        apply Finset.sum_congr rfl
        intro γ _
        symm
        calc
          (∑ α, ∑ β,
              ((∑ q, H.weight α q ^ L) *
                (∑ r, H.weight β r ^ L)) *
                chi.tracePowerCoeff α β γ L) •
              mpo (verticalBNTMPO (H.tensor γ)) L =
            ∑ α, (∑ β,
              ((∑ q, H.weight α q ^ L) *
                (∑ r, H.weight β r ^ L)) *
                chi.tracePowerCoeff α β γ L) •
              mpo (verticalBNTMPO (H.tensor γ)) L := by
                exact map_sum
                  ((smulAddHom ℂ
                    (Matrix (Fin L → Fin D) (Fin L → Fin D) ℂ)).flip
                      (mpo (verticalBNTMPO (H.tensor γ)) L))
                  (fun α ↦ ∑ β,
                    ((∑ q, H.weight α q ^ L) *
                      (∑ r, H.weight β r ^ L)) *
                      chi.tracePowerCoeff α β γ L)
                  Finset.univ
          _ = ∑ α, ∑ β,
              (((∑ q, H.weight α q ^ L) *
                (∑ r, H.weight β r ^ L)) *
                chi.tracePowerCoeff α β γ L) •
              mpo (verticalBNTMPO (H.tensor γ)) L := by
                apply Finset.sum_congr rfl
                intro α _
                exact map_sum
                  ((smulAddHom ℂ
                    (Matrix (Fin L → Fin D) (Fin L → Fin D) ℂ)).flip
                      (mpo (verticalBNTMPO (H.tensor γ)) L))
                  (fun β ↦ ((∑ q, H.weight α q ^ L) *
                    (∑ r, H.weight β r ^ L)) *
                    chi.tracePowerCoeff α β γ L)
                  Finset.univ
      _ = ∑ γ, P.coeff L γ •
            mpo (verticalBNTMPO (H.tensor γ)) L := by
        apply Finset.sum_congr rfl
        intro γ _
        congr 1
        change (∑ α, ∑ β,
            ((∑ q, H.weight α q ^ L) *
              (∑ r, H.weight β r ^ L)) *
              chi.tracePowerCoeff α β γ L) =
          ∑ r, productEntry γ r ^ L
        rw [show (∑ r, productEntry γ r ^ L) =
            ∑ x : productIndex γ,
              (H.weight x.1 x.2.2.1 * H.weight x.2.1 x.2.2.2.1 *
                chi.entry x.1 x.2.1 γ x.2.2.2.2) ^ L by
          exact productEquiv γ |>.sum_comp
            (fun x : productIndex γ ↦
              (H.weight x.1 x.2.2.1 * H.weight x.2.1 x.2.2.2.1 *
                chi.entry x.1 x.2.1 γ x.2.2.2.2) ^ L)]
        simp only [productIndex, BNTProductMultiplicityIndex,
          Fintype.sum_sigma, Fintype.sum_prod_type,
          DiagonalChiFamily.tracePowerCoeff, mul_pow]
        apply Finset.sum_congr rfl
        intro α _
        apply Finset.sum_congr rfl
        intro β _
        rw [mul_assoc, Fintype.sum_mul_sum, Fintype.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro q _
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.mul_sum]
        ring_nf
  have hPBlocked : MPSTensor.SameMPV₂Pos
      (verticalTensor (blockTwo M)) P.toTensor := by
    intro L hL σ
    let ket : Fin L → Fin D := fun l ↦ (finProdFinEquiv.symm (σ l)).1
    let bra : Fin L → Fin D := fun l ↦ (finProdFinEquiv.symm (σ l)).2
    have hEntry := congrFun (congrFun (hBlockedExpansion L hL) ket) bra
    rw [← MPSTensor.mpv_toMPSTensor_pairConfig
        (verticalBNTMPO (verticalTensor (blockTwo M))) ket bra]
      at hEntry
    simp only [verticalBNTMPO_toMPSTensor, Matrix.sum_apply,
      Matrix.smul_apply, ← MPSTensor.mpv_toMPSTensor_pairConfig,
      smul_eq_mul] at hEntry
    have hPair : (fun l ↦ finProdFinEquiv (ket l, bra l)) = σ := by
      funext l
      exact finProdFinEquiv.apply_symm_apply (σ l)
    rw [hPair] at hEntry
    exact hEntry.trans (P.mpv_toTensor_eq_sum_coeff σ).symm
  let D₂ : CPSVVerticalDecomposition (blockTwo M) := Classical.choice
    (hHorizontal.blockTwo.exists_cpsvVerticalDecomposition
      (blockTwo M) hM.blockTwo)
  let Q : MPSTensor.SectorDecomposition (D * D) := {
    basisCount := D₂.labelCount
    basisDim := D₂.bondDim
    basis := D₂.tensor
    sectors := {
      copies := D₂.multiplicity
      copies_pos := D₂.multiplicity_pos
      weight := D₂.weight
      weight_ne_zero := fun γ r ↦ (D₂.weight_pos γ r).ne' }
  }
  have hQAssembly : MPSTensor.SameMPV₂Pos Q.toTensor
      (verticalAssembledTensor D₂.bondDim D₂.multiplicity
        D₂.weight D₂.tensor) := by
    apply sameMPV₂Pos_toTensorFromBlocks_verticalAssembledTensor_of_equiv
      Q.flatWeight Q.flatBasis D₂.multiplicity D₂.weight D₂.tensor
      Q.flatIndexEquiv.symm
    · intro k
      rfl
    · intro k N hN σ
      rfl
  have hQBlocked : MPSTensor.SameMPV₂Pos
      (verticalTensor (blockTwo M)) Q.toTensor :=
    (MPSTensor.sameMPV₂Pos_of_coisometry_reconstruction
      (verticalTensor (blockTwo M))
      (verticalAssembledTensor D₂.bondDim D₂.multiplicity
        D₂.weight D₂.tensor)
      D₂.verticalCoisometry D₂.coisometry D₂.reconstruction).trans
        hQAssembly.symm
  have hPBNT : MPSTensor.IsCPSVBasisOfNormalTensors P.toTensor
      (fun γ ↦ ⟨H.bondDim γ, H.tensor γ⟩) := {
    blocks_normal := H.isCPSVBNT.blocks_normal
    spans_mpv := fun L _ ↦
      ⟨P.coeff L, fun σ ↦ P.mpv_toTensor_eq_sum_coeff σ⟩
    eventually_li := H.isCPSVBNT.eventually_li
  }
  have hD₂BNTOnP : MPSTensor.IsCPSVBasisOfNormalTensors P.toTensor
      (fun δ ↦ ⟨D₂.bondDim δ, D₂.tensor δ⟩) :=
    D₂.isCPSVBNT.of_sameMPV₂Pos hPBlocked
  have hHBNTOnQ : MPSTensor.IsCPSVBasisOfNormalTensors Q.toTensor
      (fun γ ↦ ⟨H.bondDim γ, H.tensor γ⟩) :=
    hPBNT.of_sameMPV₂Pos (hPBlocked.symm.trans hQBlocked)
  letI : ∀ γ, NeZero (H.bondDim γ) := fun γ ↦
    ⟨(H.isCPSVBNT.blocks_dim_pos γ).ne'⟩
  letI : ∀ δ, NeZero (D₂.bondDim δ) := fun δ ↦
    ⟨(D₂.isCPSVBNT.blocks_dim_pos δ).ne'⟩
  have hForwardMatch : ∀ γ : Fin H.labelCount,
      ∃ δ : Fin D₂.labelCount,
        MPSTensor.MPVBlockPhaseEquiv (H.tensor γ) (D₂.tensor δ) := by
    intro γ
    exact P.exists_phase_match_of_isCPSVBasisOfNormalTensors
      D₂.tensor H.isCPSVBNT.blocks_normal
      H.isCPSVBNT.blocks_not_gaugePhaseEquiv
      D₂.isCPSVBNT.blocks_normal hD₂BNTOnP γ
  have hReverseMatch : ∀ δ : Fin D₂.labelCount,
      ∃ γ : Fin H.labelCount,
        MPSTensor.MPVBlockPhaseEquiv (D₂.tensor δ) (H.tensor γ) := by
    intro δ
    exact Q.exists_phase_match_of_isCPSVBasisOfNormalTensors
      H.tensor D₂.isCPSVBNT.blocks_normal
      D₂.isCPSVBNT.blocks_not_gaugePhaseEquiv
      H.isCPSVBNT.blocks_normal hHBNTOnQ δ
  choose f hfPhase using hForwardMatch
  choose q hqPhase using hReverseMatch
  have hfInjective : Function.Injective f := by
    intro γ₁ γ₂ hEq
    by_contra hNe
    have h₂ : MPSTensor.MPVBlockPhaseEquiv
        (H.tensor γ₂) (D₂.tensor (f γ₁)) := by
      rw [hEq]
      exact hfPhase γ₂
    have hPhase := (hfPhase γ₁).trans h₂.symm
    obtain ⟨hDim, hGauge⟩ :=
      hPhase.dim_eq_and_gaugePhaseEquiv_of_isNormalTensor
        (H.isCPSVBNT.blocks_normal γ₁) (H.isCPSVBNT.blocks_normal γ₂)
    exact H.isCPSVBNT.blocks_not_gaugePhaseEquiv γ₁ γ₂ hNe hDim hGauge
  have hqInjective : Function.Injective q := by
    intro δ₁ δ₂ hEq
    by_contra hNe
    have h₂ : MPSTensor.MPVBlockPhaseEquiv
        (D₂.tensor δ₂) (H.tensor (q δ₁)) := by
      rw [hEq]
      exact hqPhase δ₂
    have hPhase := (hqPhase δ₁).trans h₂.symm
    obtain ⟨hDim, hGauge⟩ :=
      hPhase.dim_eq_and_gaugePhaseEquiv_of_isNormalTensor
        (D₂.isCPSVBNT.blocks_normal δ₁) (D₂.isCPSVBNT.blocks_normal δ₂)
    exact D₂.isCPSVBNT.blocks_not_gaugePhaseEquiv δ₁ δ₂ hNe hDim hGauge
  have hCard : Fintype.card (Fin H.labelCount) =
      Fintype.card (Fin D₂.labelCount) :=
    Nat.le_antisymm (Fintype.card_le_of_injective f hfInjective)
      (Fintype.card_le_of_injective q hqInjective)
  have hfBijective : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hfInjective, hCard⟩
  let sigma : Fin H.labelCount ≃ Fin D₂.labelCount :=
    Equiv.ofBijective f hfBijective
  have hGaugeExists : ∀ γ : Fin H.labelCount,
      ∃ hdim : H.bondDim γ = D₂.bondDim (sigma γ),
        MPSTensor.GaugePhaseEquiv
          (cast (congrArg (MPSTensor (D * D)) hdim) (H.tensor γ))
          (D₂.tensor (sigma γ)) := by
    intro γ
    exact (hfPhase γ).dim_eq_and_gaugePhaseEquiv_of_isNormalTensor
      (H.isCPSVBNT.blocks_normal γ)
      (D₂.isCPSVBNT.blocks_normal (sigma γ))
  choose hdim hGaugePhase using hGaugeExists
  choose gauge zeta hzetaNe hTensor using hGaugePhase
  have hzetaMPV : ∀ (γ : Fin H.labelCount) (N : ℕ), 0 < N →
      ∀ σ : Fin N → Fin (D * D),
        MPSTensor.mpv (D₂.tensor (sigma γ)) σ =
          zeta γ ^ N * MPSTensor.mpv (H.tensor γ) σ := by
    intro γ N _hN σ
    rw [MPSTensor.mpv_eq_pow_mul_of_gaugePhase
      (A := cast (congrArg (MPSTensor (D * D)) (hdim γ)) (H.tensor γ))
      (B := D₂.tensor (sigma γ)) (gauge γ) (zeta γ) (hTensor γ) N σ,
      MPSTensor.mpv_cast_dim (hdim γ) (H.tensor γ) N σ]
  have hzetaNorm : ∀ γ, ‖zeta γ‖ = 1 := by
    intro γ
    have hHH : Tendsto
        (fun N ↦ ‖MPSTensor.mpvOverlap (d := D * D)
          (H.tensor γ) (H.tensor γ) N‖) atTop (nhds (1 : ℝ)) := by
      simpa using (H.isCPSVBNT.blocks_normal γ).selfOverlap_tendsto_one.norm
    have hDD : Tendsto
        (fun N ↦ ‖MPSTensor.mpvOverlap (d := D * D)
          (D₂.tensor (f γ)) (D₂.tensor (f γ)) N‖)
        atTop (nhds (1 : ℝ)) := by
      simpa using
        (D₂.isCPSVBNT.blocks_normal (f γ)).selfOverlap_tendsto_one.norm
    exact MPSTensor.norm_eq_one_of_selfOverlap_scale_pos hHH hDD
      (MPSTensor.mpvOverlap_self_scale_of_mpv_eq_pow_mul_pos
        (hzetaMPV γ))
  let a : ℕ → Fin H.labelCount → ℂ := fun L γ ↦ P.coeff L γ
  let b : ℕ → Fin H.labelCount → ℂ := fun L γ ↦
    zeta γ ^ L * Q.coeff L (sigma γ)
  have hLI : ∀ᶠ L in atTop,
      LinearIndependent ℂ
        (fun γ : Fin H.labelCount ↦
          MPSTensor.mpvState (d := D * D) (H.tensor γ) L) := by
    obtain ⟨L₀, hL₀⟩ := H.isCPSVBNT.eventually_li
    exact Filter.eventually_atTop.mpr
      ⟨L₀ + 1, fun L hL ↦ hL₀ L (by omega)⟩
  have hStateExpansionEq : ∀ᶠ L in atTop,
      ∑ γ : Fin H.labelCount,
          a L γ • MPSTensor.mpvState (d := D * D) (H.tensor γ) L =
        ∑ γ : Fin H.labelCount,
          b L γ • MPSTensor.mpvState (d := D * D) (H.tensor γ) L := by
    refine Filter.eventually_atTop.mpr ⟨1, ?_⟩
    intro L hL
    have hLPos : 0 < L := Nat.zero_lt_of_lt hL
    have hPState : MPSTensor.mpvState (d := D * D) P.toTensor L =
        ∑ γ : Fin H.labelCount, P.coeff L γ •
          MPSTensor.mpvState (d := D * D) (H.tensor γ) L := by
      refine MPSTensor.mpvState_eq_sum_of_decomp (d := D * D)
        P.toTensor H.tensor (N := L) (P.coeff L) ?_
      intro σ
      simpa [smul_eq_mul] using P.mpv_toTensor_eq_sum_coeff σ
    have hQState : MPSTensor.mpvState (d := D * D) Q.toTensor L =
        ∑ δ : Fin D₂.labelCount, Q.coeff L δ •
          MPSTensor.mpvState (d := D * D) (D₂.tensor δ) L := by
      refine MPSTensor.mpvState_eq_sum_of_decomp (d := D * D)
        Q.toTensor D₂.tensor (N := L) (Q.coeff L) ?_
      intro σ
      simpa [smul_eq_mul] using Q.mpv_toTensor_eq_sum_coeff σ
    have hPQState : MPSTensor.mpvState (d := D * D) P.toTensor L =
        MPSTensor.mpvState (d := D * D) Q.toTensor L := by
      apply PiLp.ext
      intro σ
      simpa [MPSTensor.mpvState_apply] using
        (hPBlocked.symm.trans hQBlocked) L hLPos σ
    have hQSubst :
        (∑ δ : Fin D₂.labelCount, Q.coeff L δ •
            MPSTensor.mpvState (d := D * D) (D₂.tensor δ) L) =
          ∑ γ : Fin H.labelCount,
            (zeta γ ^ L * Q.coeff L (sigma γ)) •
              MPSTensor.mpvState (d := D * D) (H.tensor γ) L := by
      calc
        (∑ δ : Fin D₂.labelCount, Q.coeff L δ •
            MPSTensor.mpvState (d := D * D) (D₂.tensor δ) L) =
          ∑ δ : Fin D₂.labelCount,
            (zeta (sigma.symm δ) ^ L * Q.coeff L δ) •
              MPSTensor.mpvState (d := D * D)
                (H.tensor (sigma.symm δ)) L := by
            apply Finset.sum_congr rfl
            intro δ _
            have hMpvState : MPSTensor.mpvState (d := D * D)
                (D₂.tensor δ) L =
              zeta (sigma.symm δ) ^ L •
                MPSTensor.mpvState (d := D * D)
                  (H.tensor (sigma.symm δ)) L := by
              apply PiLp.ext
              intro σ
              have hMpv := hzetaMPV (sigma.symm δ) L hLPos σ
              rw [sigma.apply_symm_apply δ] at hMpv
              simpa only [MPSTensor.mpvState_apply, PiLp.smul_apply,
                smul_eq_mul] using hMpv
            rw [hMpvState, smul_smul]
            congr 1
            ring
        _ = ∑ γ : Fin H.labelCount,
            (zeta γ ^ L * Q.coeff L (sigma γ)) •
              MPSTensor.mpvState (d := D * D) (H.tensor γ) L := by
            simpa only [Equiv.apply_symm_apply] using
              (Equiv.sum_comp sigma.symm
                (fun γ : Fin H.labelCount ↦
                  (zeta γ ^ L * Q.coeff L (sigma γ)) •
                    MPSTensor.mpvState (d := D * D) (H.tensor γ) L))
    calc
      ∑ γ, a L γ • MPSTensor.mpvState (d := D * D) (H.tensor γ) L =
          MPSTensor.mpvState (d := D * D) P.toTensor L := by
        simpa [a] using hPState.symm
      _ = MPSTensor.mpvState (d := D * D) Q.toTensor L := hPQState
      _ = ∑ δ, Q.coeff L δ •
          MPSTensor.mpvState (d := D * D) (D₂.tensor δ) L := hQState
      _ = ∑ γ, b L γ •
          MPSTensor.mpvState (d := D * D) (H.tensor γ) L := by
        simpa [b] using hQSubst
  have hCoeff : ∀ᶠ L in atTop, ∀ γ : Fin H.labelCount,
      a L γ = b L γ := by
    exact MPSTensor.coefficient_eventually_eq_of_eventually_linearIndependent
      (v := fun L γ ↦ MPSTensor.mpvState (d := D * D) (H.tensor γ) L)
      (a := a) (b := b) hLI hStateExpansionEq
  let hCoeffWitness := Filter.eventually_atTop.mp hCoeff
  let L₀ := Classical.choose hCoeffWitness
  have hCoeffAfter : ∀ L, L₀ ≤ L → ∀ γ : Fin H.labelCount,
      a L γ = b L γ := Classical.choose_spec hCoeffWitness
  have hPCoeffPos : ∀ γ L, (0 : ℂ) < P.coeff L γ := by
    intro γ L
    change (0 : ℂ) < ∑ r, productEntry γ r ^ L
    apply Finset.sum_pos
    · intro r _
      exact pow_pos (hProductPos γ r) L
    · exact Finset.univ_nonempty_iff.mpr
        ⟨⟨0, hProductDimPos γ⟩⟩
  have hQCoeffPos : ∀ δ L, (0 : ℂ) < Q.coeff L δ := by
    intro δ L
    change (0 : ℂ) < ∑ r, D₂.weight δ r ^ L
    apply Finset.sum_pos
    · intro r _
      exact pow_pos (D₂.weight_pos δ r) L
    · exact Finset.univ_nonempty_iff.mpr
        ⟨⟨0, D₂.multiplicity_pos δ⟩⟩
  have hzetaOne : ∀ γ, zeta γ = 1 := by
    intro γ
    let L := max L₀ 1
    have hL : L₀ ≤ L := le_max_left _ _
    have hCoeffL := hCoeffAfter L hL γ
    have hCoeffSucc := hCoeffAfter (L + 1) (by omega) γ
    have hCross : zeta γ *
        (P.coeff L γ * Q.coeff (L + 1) (sigma γ)) =
      P.coeff (L + 1) γ * Q.coeff L (sigma γ) := by
      dsimp only [a, b] at hCoeffL hCoeffSucc
      rw [hCoeffL, hCoeffSucc]
      ring
    have hPositiveFactor : (0 : ℂ) <
        P.coeff L γ * Q.coeff (L + 1) (sigma γ) :=
      mul_pos (hPCoeffPos γ L) (hQCoeffPos (sigma γ) (L + 1))
    have hPositiveRight : (0 : ℂ) <
        P.coeff (L + 1) γ * Q.coeff L (sigma γ) :=
      mul_pos (hPCoeffPos γ (L + 1)) (hQCoeffPos (sigma γ) L)
    have hzetaPos : (0 : ℂ) < zeta γ := by
      apply pos_of_mul_pos_left
      · rw [hCross]
        exact hPositiveRight
      · exact hPositiveFactor.le
    obtain ⟨hzetaRePos, hzetaIm⟩ := Complex.pos_iff.mp hzetaPos
    have hzetaEqReal : ((zeta γ).re : ℂ) = zeta γ :=
      Complex.ext (Complex.ofReal_re (zeta γ).re)
        (by rw [Complex.ofReal_im]; exact hzetaIm)
    have hRealOne : (zeta γ).re = 1 := by
      have hNorm := hzetaNorm γ
      rw [← hzetaEqReal, Complex.norm_real,
        Real.norm_of_nonneg hzetaRePos.le] at hNorm
      exact hNorm
    rw [← hzetaEqReal, hRealOne]
    norm_num
  have hSectorSameMPV : ∀ γ : Fin H.labelCount,
      MPSTensor.SameMPV₂Pos (H.tensor γ) (D₂.tensor (sigma γ)) := by
    intro γ L hL σ
    have hMpv := hzetaMPV γ L hL σ
    change (D₂.tensor (sigma γ)).mpv σ =
      zeta γ ^ L * (H.tensor γ).mpv σ at hMpv
    rw [hzetaOne γ, one_pow, one_mul] at hMpv
    exact hMpv.symm
  have hPowerSums : ∀ γ : Fin H.labelCount, ∀ L : ℕ, L₀ < L →
      (∑ r, D₂.weight (sigma γ) r ^ L) =
        ∑ x : BNTProductMultiplicityIndex chi H.multiplicity γ,
          (H.weight x.1 x.2.2.1 * H.weight x.2.1 x.2.2.2.1 *
            chi.entry x.1 x.2.1 γ x.2.2.2.2) ^ L := by
    intro γ L hL
    have hCoeffL := hCoeffAfter L (le_of_lt hL) γ
    dsimp only [a, b] at hCoeffL
    rw [hzetaOne γ, one_pow, one_mul] at hCoeffL
    change (∑ r, productEntry γ r ^ L) =
      (∑ r, D₂.weight (sigma γ) r ^ L) at hCoeffL
    rw [← hCoeffL]
    exact productEquiv γ |>.sum_comp
      (fun x : productIndex γ ↦
        (H.weight x.1 x.2.2.1 * H.weight x.2.1 x.2.2.2.1 *
          chi.entry x.1 x.2.1 γ x.2.2.2.2) ^ L)
  let comparison :=
    BNTMultiplicitySpectrumComparison.ofEventuallyEqualPowerSums
      chi H.traceScalars H.algebraClause.positiveChi.posEntries
      H.multiplicity H.weight H.weight_pos
      (fun α ↦ (BNTAlgebraTensorClause.traceScalars_traceScalar H α).symm)
      (fun γ ↦ D₂.multiplicity (sigma γ))
      (fun γ r ↦ D₂.weight (sigma γ) r)
      (fun γ r ↦ D₂.weight_pos (sigma γ) r)
      hPowerSums
  exact {
    decomposition := D₂
    relabel := sigma
    sector_sameMPV := hSectorSameMPV
    spectrum_eq := by
      intro γ
      have hSpectrum := comparison.spectrum_eq γ
      dsimp only [comparison,
        BNTMultiplicitySpectrumComparison.ofEventuallyEqualPowerSums] at hSpectrum
      convert hSpectrum using 1 <;> rfl
    bondDim_eq := hdim
    gauge := gauge
    tensor_eq := by
      intro γ i
      have hExact := hTensor γ i
      rw [hzetaOne γ, one_smul] at hExact
      exact hExact }

/-- The exact sector gauges determine the two-site multiplicity spectrum under
normalized BNT-refined horizontal form.

**Scope restriction (BNT-refined horizontal form):** `IsHorizontalCF` is
stronger than the literal CPSV canonical form; see
`docs/paper-gaps/cpgsv17_vertical_cf_grouping.tex`.

Source: arXiv:1606.00608, Appendix C.4, lines 2046--2058 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
noncomputable def toTwoSiteMultiplicitySpectrum
    {M : MPOTensor d D} (H : BNTAlgebraTensorClause M)
    (hHorizontal : IsHorizontalCF M) (hM : IsMPDO M) :
    TwoSiteMultiplicitySpectrum H :=
  (H.toTwoSiteExactSectorGauge hHorizontal hM).toTwoSiteMultiplicitySpectrum

/-- The two-site multiplicity spectrum under normalized BNT-refined horizontal
form entails the corresponding multiplicity-spectrum comparison.

**Scope restriction (BNT-refined horizontal form):** `IsHorizontalCF` is
stronger than the literal CPSV canonical form; see
`docs/paper-gaps/cpgsv17_vertical_cf_grouping.tex`.

Source: arXiv:1606.00608, Appendix C.4, lines 2046--2058 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
noncomputable def toMultiplicitySpectrumComparison
    {M : MPOTensor d D} (H : BNTAlgebraTensorClause M)
    (hHorizontal : IsHorizontalCF M) (hM : IsMPDO M) :
    BNTMultiplicitySpectrumComparison H.algebraClause.positiveChi.chi
      H.traceScalars :=
  (H.toTwoSiteMultiplicitySpectrum hHorizontal hM).toComparison

end BNTAlgebraTensorClause

end MPOTensor
