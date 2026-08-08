/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTProjectorSelection
import TNLean.MPS.MPDO.SectorTrace

/-!
# Positivity and zero correlation length of the BNT sectors

For a simple tensor satisfying the saturated area law and zero correlation
length, Appendix C.2 of arXiv:1606.00608 passes from the sector compression
formula
\[
  P_s^{\otimes N}\sigma^{(N)}(K)P_s^{\otimes N}
    =n_s\sigma^{(N)}(\mathcal K_s)
\]
to the corresponding analytic properties of each absorbed BNT
representative \(\mathcal K_s\).

This file proves the first and third properties in that passage.  Positivity
of every \(\sigma^{(N)}(\mathcal K_s)\) follows from the compression formula
and \(n_s>0\).  Zero correlation length follows from the blockwise transfer
equation already used to prove that the copy weights are independent of the
copy index.

## Main results

* `commonWeightAbsorbedBasisMPOTensor_isMPDO_of_projectorSelection`:
  the positive compression formula makes every absorbed representative an
  MPDO.
* `commonWeightAbsorbedBasisMPOTensor_isMPDO_of_sameMPV₂Pos_isSAL`:
  the source projector construction supplies the required compression.
* `commonWeightAbsorbedBasisMPOTensor_isSourceZCL`:
  scale-invariant source zero correlation length restricts to every absorbed BNT representative.
* `IsSimpleCanonicalForm.exists_commonWeightAbsorbedBasisMPOTensor_isSourceZCL`:
  simple canonical data package copy-independent weights and sectorwise source
  zero correlation length.
* `trace_mpo_commonWeightAbsorbedBasisMPOTensor_pos`:
  every nonempty-chain sector normalization is strictly positive.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Appendix C.2, lines 1753--1781.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor

variable {d : ℕ}

/-- The physical-trace transfer of the absorbed representative
\(\mathcal K_s=\mu_s A_s\) is \(\mu_s\mathcal B_s\).

Source: arXiv:1606.00608, Appendix C.2, lines 1660--1665 and 1753--1759. -/
theorem physTraceTransfer_commonWeightAbsorbedBasisMPOTensor
    (S : MPSTensor.SectorDecomposition (d * d))
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q') (s : Fin S.basisCount) :
    physTraceTransfer (commonWeightAbsorbedBasisMPOTensor S hWeight s) =
      S.commonWeight hWeight s • doubledPhysTraceTransfer d (S.basis s) := by
  rw [← doubledPhysTraceTransfer_toMPSTensor,
    commonWeightAbsorbedBasisMPOTensor_toMPSTensor]
  unfold doubledPhysTraceTransfer
  rw [Finset.smul_sum]
  simp only [MPSTensor.SectorDecomposition.commonWeightAbsorbedBasis]

/-- Literal zero correlation length restricts to each common-weight-absorbed BNT
representative:
\[
  \mathcal T_{\mathcal K_s}^2=\mathcal T_{\mathcal K_s}.
\]

**Scope restriction (Case-II normality):** This proves literal physical-trace idempotence for
the absorbed BNT representative, but not spectral normality. Coefficient absorption scales the
transfer spectral radius by the squared modulus of the coefficient, and the global canonical-form
normalization does not make every coefficient unit modulus. Thus the normal Case-I theorem cannot
yet be applied sectorwise. The remaining boundary is recorded in
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`.

Source: arXiv:1606.00608, Appendix C.2, lines 1745--1782. -/
theorem commonWeightAbsorbedBasisMPOTensor_physTraceTransfer_sq_of_literal_ZCL
    {D : ℕ} (M : MPOTensor d D)
    (S : MPSTensor.SectorDecomposition (d * d)) (hTotal : S.totalDim = D)
    (X : (s : Fin S.totalCopies) → GL (Fin (S.flatDim s)) ℂ)
    (hEq : ∀ i : Fin (d * d),
      M.toMPSTensor i =
        cast (by rw [hTotal] :
            Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ =
              Matrix (Fin D) (Fin D) ℂ)
          ((MPSTensor.globalGaugeOfBlocks X :
                Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) *
            S.toTensor i *
            (((MPSTensor.globalGaugeOfBlocks X)⁻¹ :
                GL (Fin S.totalDim) ℂ) :
              Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ)))
    (hZCL_sq : physTraceTransfer M * physTraceTransfer M = physTraceTransfer M)
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q') (s : Fin S.basisCount) :
    physTraceTransfer (commonWeightAbsorbedBasisMPOTensor S hWeight s) *
        physTraceTransfer (commonWeightAbsorbedBasisMPOTensor S hWeight s) =
      physTraceTransfer (commonWeightAbsorbedBasisMPOTensor S hWeight s) := by
  rw [physTraceTransfer_commonWeightAbsorbedBasisMPOTensor]
  have hsquare := weighted_basis_physTraceTransfer_sq_of_literal_ZCL
    S hTotal X hEq hZCL_sq s ⟨0, S.copies_pos s⟩
  rw [S.weight_eq_commonWeight hWeight] at hsquare
  exact hsquare

/-- The scale-invariant source zero-correlation-length equation restricts to every
absorbed BNT representative in the horizontal canonical form.

The nonnilpotence condition is used only to exclude the zero transfer.  The
quadratic equation itself is the corresponding diagonal block of the
zero-correlation-length equation for the full canonical-form tensor.

Source: arXiv:1606.00608, Appendix C.2, lines 1646--1657 and 1781. -/
theorem commonWeightAbsorbedBasisMPOTensor_isSourceZCL
    {D : ℕ} (M : MPOTensor d D)
    (S : MPSTensor.SectorDecomposition (d * d)) (hTotal : S.totalDim = D)
    (X : (s : Fin S.totalCopies) → GL (Fin (S.flatDim s)) ℂ)
    (hEq : ∀ i : Fin (d * d),
      M.toMPSTensor i =
        cast (by rw [hTotal] :
            Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ =
              Matrix (Fin D) (Fin D) ℂ)
          ((MPSTensor.globalGaugeOfBlocks X :
                Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) *
            S.toTensor i *
            (((MPSTensor.globalGaugeOfBlocks X)⁻¹ :
                GL (Fin S.totalDim) ℂ) :
              Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ)))
    (hZCL : IsSourceZCL M)
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q') (s : Fin S.basisCount)
    (hnonNil : ¬ IsNilpotent (doubledPhysTraceTransfer d (S.basis s))) :
    IsSourceZCL (commonWeightAbsorbedBasisMPOTensor S hWeight s) := by
  obtain ⟨lam, hlam, hSq⟩ :=
    exists_weighted_basis_physTraceTransfer_sq_of_isSourceZCL
      S hTotal X hEq hZCL
  have htransfer :=
    physTraceTransfer_commonWeightAbsorbedBasisMPOTensor S hWeight s
  have hbasis : doubledPhysTraceTransfer d (S.basis s) ≠ 0 := by
    intro hzero
    exact hnonNil (by rw [hzero]; exact IsNilpotent.zero)
  have hweighted :
      S.commonWeight hWeight s • doubledPhysTraceTransfer d (S.basis s) ≠ 0 := by
    exact smul_ne_zero (S.commonWeight_ne_zero hWeight s) hbasis
  have hsquare := hSq s ⟨0, S.copies_pos s⟩
  rw [S.weight_eq_commonWeight hWeight] at hsquare
  rw [IsSourceZCL, htransfer]
  exact ⟨hweighted, lam, hlam, hsquare⟩

/-- A simple canonical-form tensor with source zero correlation length admits
canonical-form data whose weights are copy-independent and whose absorbed BNT
representatives all have scale-invariant source zero correlation length.

The chosen data retain the nonnilpotence condition from simplicity, so the
sectorwise zero-correlation-length theorem applies without an additional
hypothesis.

Source: arXiv:1606.00608, Appendix C.2, lines 1628, 1646--1661, and 1781. -/
theorem IsSimpleCanonicalForm.exists_commonWeightAbsorbedBasisMPOTensor_isSourceZCL
    {D : ℕ} {M : MPOTensor d D} (hM : IsSimpleCanonicalForm M)
    (hZCL : IsSourceZCL M) :
    ∃ S : MPSTensor.SectorDecomposition (d * d),
      MPSTensor.IsBNTCanonicalForm S ∧
        (∃ hTotal : S.totalDim = D,
          ∃ X : (s : Fin S.totalCopies) → GL (Fin (S.flatDim s)) ℂ,
          ∀ i : Fin (d * d),
            M.toMPSTensor i =
              cast (by rw [hTotal] :
                  Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ =
                    Matrix (Fin D) (Fin D) ℂ)
                ((MPSTensor.globalGaugeOfBlocks X :
                      Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) *
                  S.toTensor i *
                  (((MPSTensor.globalGaugeOfBlocks X)⁻¹ :
                      GL (Fin S.totalDim) ℂ) :
                    Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ))) ∧
        (∀ j, ¬ IsNilpotent (doubledPhysTraceTransfer d (S.basis j))) ∧
        ∃ hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
          S.weight j q = S.weight j q',
          ∀ s : Fin S.basisCount,
            IsSourceZCL (commonWeightAbsorbedBasisMPOTensor S hWeight s) := by
  obtain ⟨S, hCF, ⟨hTotal, X, hEq⟩, hnonNil, hWeight⟩ :=
    hM.exists_weight_copy_independent_of_isSourceZCL hZCL
  refine ⟨S, hCF, ⟨hTotal, X, hEq⟩, hnonNil, hWeight, fun s ↦ ?_⟩
  exact commonWeightAbsorbedBasisMPOTensor_isSourceZCL
    M S hTotal X hEq hZCL hWeight s (hnonNil s)

/-- If the tensor-power BNT projection selects an absorbed representative,
then that representative generates positive semidefinite operators on every
nonempty chain.

Source: arXiv:1606.00608, Appendix C.2, lines 1753--1759. -/
theorem commonWeightAbsorbedBasisMPOTensor_isMPDO_of_projectorSelection
    {D : ℕ} (M : MPOTensor d D)
    (S : MPSTensor.SectorDecomposition (d * d))
    (hM : MPSTensor.SameMPV₂Pos M.toMPSTensor S.toTensor)
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q')
    {R : (s : Fin S.basisCount) →
      Matrix (Fin (S.basisDim s)) (Fin (S.basisDim s)) ℂ}
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex S.basisDim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse
      (fun j ↦ S.basisMPOTensor j) C)
    (hρ : IsThreeSiteFamilyClosure (fun j ↦ S.basisMPOTensor j) R ρ)
    (hη : EtaStructure ρ) (hR : ∀ s : Fin S.basisCount, R s ≠ 0)
    (hMpdo : IsMPDO M) (s : Fin S.basisCount) :
    IsMPDO (commonWeightAbsorbedBasisMPOTensor S hWeight s) := by
  intro N hN
  let P := sitewisePhysicalMatrix (bntSectorProjection hC hρ hη hR s) N
  have heq : P * mpo M N * P =
      (S.copies s : ℂ) • mpo (commonWeightAbsorbedBasisMPOTensor S hWeight s) N :=
    sitewise_bntSectorProjection_mul_mpo_mul_self
      M S hM hWeight hC hρ hη hR hN s
  have hP : P.IsHermitian := sitewisePhysicalMatrix_isHermitian
    (bntSectorProjection_isOrthogonal hC hρ hη hR s).1 N
  have hcompressed : (P * mpo M N * P).PosSemidef := by
    simpa only [hP.eq] using (hMpdo N hN).mul_mul_conjTranspose_same P
  rw [heq] at hcompressed
  have hcopiesNonneg : (0 : ℂ) ≤ (S.copies s : ℂ) := by
    exact_mod_cast (S.copies_pos s).le
  have hcopiesNe : (S.copies s : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (S.copies_pos s)
  have hrescaled := hcompressed.smul (a := (S.copies s : ℂ)⁻¹)
    (inv_nonneg.mpr hcopiesNonneg)
  simpa only [smul_smul, inv_mul_cancel₀ hcopiesNe, one_smul] using hrescaled

/-- Under the source hypotheses used to construct the BNT projectors, every
absorbed BNT representative generates an MPDO.

**Source hypothesis (biCF):** the one-letter simultaneous span is precisely
the block-injective canonical-form assumption imposed at the start of Case II
in arXiv:1606.00608, line 1628.  It supplies the simultaneous inverse used in
the source proof.  Its relation with finite physical blocking is recorded in
`docs/paper-gaps/cpgsv17_bicf_block_separation.tex`.

The projector construction uses the proved forward
Hayashi--Ruskai--Hayden--Jozsa--Petz--Winter characterization of equality in
strong subadditivity, `hayashi_ssa_equality_characterization_forward`.

Source: arXiv:1606.00608, Appendix C.2, lines 1680--1759. -/
theorem commonWeightAbsorbedBasisMPOTensor_isMPDO_of_sameMPV₂Pos_isSAL
    {D : ℕ} (M : MPOTensor d D)
    (S : MPSTensor.SectorDecomposition (d * d))
    (hM : MPSTensor.SameMPV₂Pos M.toMPSTensor S.toTensor)
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q')
    (hnonNil : ∀ j,
      ¬ IsNilpotent (doubledPhysTraceTransfer d (S.basis j)))
    (hSpan : MPSTensor.WordTupleSpanTop S.basis 1)
    (hSAL : IsSAL M) (s : Fin S.basisCount) :
    IsMPDO (commonWeightAbsorbedBasisMPOTensor S hWeight s) := by
  obtain ⟨C, hC, hη, _hlocal, _hcompression⟩ :=
    exists_bntProjectorSelection_positiveLength_of_sameMPV₂Pos_isSAL
      M S hM hWeight hnonNil hSpan hSAL
  let hClosure :=
    reducedBlockState_four_threeSiteFamilyClosure_nonzero_closing
      M S hM hWeight hnonNil hSAL
  exact commonWeightAbsorbedBasisMPOTensor_isMPDO_of_projectorSelection
    M S hM hWeight hC hClosure.1 hη hClosure.2 (Classical.choose hSAL) s

/-- Every absorbed BNT representative has strictly positive trace on each
nonempty chain.  Positivity comes from the projector compression, while
nonvanishing comes from the zero-correlation-length equation already
restricted to the representative.

This supplies the strict inequality required before normalizing the sector in
the direct-sum entropy identity.  It is not inferred from the weaker displayed
inequality \(p_s\geq 0\).

**Source hypothesis (biCF):** the one-letter simultaneous span is precisely
the block-injective canonical-form assumption imposed at the start of Case II
in arXiv:1606.00608, line 1628.  It supplies the simultaneous inverse used in
the source proof.  Its relation with finite physical blocking is recorded in
`docs/paper-gaps/cpgsv17_bicf_block_separation.tex`.

Source: arXiv:1606.00608, Appendix C.2, lines 1760--1780. -/
theorem trace_mpo_commonWeightAbsorbedBasisMPOTensor_pos
    {D : ℕ} (M : MPOTensor d D)
    (S : MPSTensor.SectorDecomposition (d * d)) (hTotal : S.totalDim = D)
    (X : (s : Fin S.totalCopies) → GL (Fin (S.flatDim s)) ℂ)
    (hEq : ∀ i : Fin (d * d),
      M.toMPSTensor i =
        cast (by rw [hTotal] :
            Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ =
              Matrix (Fin D) (Fin D) ℂ)
          ((MPSTensor.globalGaugeOfBlocks X :
                Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ) *
            S.toTensor i *
            (((MPSTensor.globalGaugeOfBlocks X)⁻¹ :
                GL (Fin S.totalDim) ℂ) :
              Matrix (Fin S.totalDim) (Fin S.totalDim) ℂ)))
    (hM : MPSTensor.SameMPV₂Pos M.toMPSTensor S.toTensor)
    (hZCL : IsSourceZCL M)
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q')
    (hnonNil : ∀ j,
      ¬ IsNilpotent (doubledPhysTraceTransfer d (S.basis j)))
    (hSpan : MPSTensor.WordTupleSpanTop S.basis 1)
    (hSAL : IsSAL M) (s : Fin S.basisCount)
    {N : ℕ} (hN : 0 < N) :
    0 < Matrix.trace (mpo (commonWeightAbsorbedBasisMPOTensor S hWeight s) N) := by
  exact trace_mpo_pos_of_isMPDO_isSourceZCL _
    (commonWeightAbsorbedBasisMPOTensor_isMPDO_of_sameMPV₂Pos_isSAL
      M S hM hWeight hnonNil hSpan hSAL s)
    (commonWeightAbsorbedBasisMPOTensor_isSourceZCL
      M S hTotal X hEq hZCL hWeight s (hnonNil s)) hN

end MPOTensor
