/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.FixedPoint.TraceNonincreasingDirectSum
import TNLean.Channel.PositiveConditionalExpectationDirectSum
import TNLean.MPS.MPDO.BNTAlgebraTensorClauseSpectrum
import TNLean.MPS.MPDO.VerticalSectorRetractions

/-!
# Direct-sum unitary conjugations in Appendix C.4

After relabelling the paired one-site and two-site BNT sectors, a family of
unitary sector conjugacies determines mutually inverse maps between the two
finite sums of simple matrix algebras. The maps are completely positive and
preserve the sum of the block traces.

The unitary sector conjugacies are supplied as a hypothesis in this file.
Their construction from the tensor-attached algebra clause is given in
`BNTAlgebraTensorClauseReflectedTarget`.  The ambient retractions, normalized
multiplicity embeddings, and physical maps are developed separately.

These are the middle conjugations in the converse implication of Appendix
C.4, lines 2069 and 2080. They are distinct from the transported direct-sum
maps in the forward implication at lines 1955--1997.

## Main definitions

* `TwoSiteExactSectorGauge.UnitarySectorConjugacy`
* `UnitarySectorConjugacy.directSumUnitaryT`
* `UnitarySectorConjugacy.directSumUnitaryS`

## Main results

* `UnitarySectorConjugacy.directSumUnitaryS_comp_directSumUnitaryT`
* `UnitarySectorConjugacy.directSumUnitaryT_comp_directSumUnitaryS`
* `UnitarySectorConjugacy.directSumUnitaryT_isKrausDirectSumMap`
* `UnitarySectorConjugacy.directSumUnitaryS_isKrausDirectSumMap`
* `UnitarySectorConjugacy.directSumUnitaryT_isTracePreservingBetweenDirectSums`
* `UnitarySectorConjugacy.directSumUnitaryS_isTracePreservingBetweenDirectSums`
* `UnitarySectorConjugacy.directSumUnitaryT_tensor`
* `UnitarySectorConjugacy.directSumUnitaryS_tensor`

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.4, lines 2053--2080
-/

open scoped Matrix

noncomputable section

namespace MPOTensor

namespace BNTAlgebraTensorClause.TwoSiteExactSectorGauge

variable {d D : ℕ} {M : MPOTensor d D} {H : BNTAlgebraTensorClause M}

/-- The two-site simple-sector algebra after relabelling its summands by the
paired one-site labels.

Source: arXiv:1606.00608, Appendix C.4, lines 2048--2069. -/
abbrev RelabeledTwoSiteSectorAlgebra (S : TwoSiteExactSectorGauge H) :=
  VerticalSectorAlgebra
    (fun γ ↦ S.decomposition.bondDim (S.relabel γ))

/-- Unitary conjugacies between the paired one-site and two-site BNT sectors.

**Scope restriction (supplied unitary sector conjugacies):** The structure
records the unitary conclusion of Appendix C.4, line 2057, as data.  Its
derivation from the tensor-attached algebra clause is supplied by the
mixed-prefix comparison documented in
`docs/paper-gaps/cpsv16_two_site_sector_unitary_gauge_gap.tex`.

Source: arXiv:1606.00608, Appendix C.4, lines 2053--2057. -/
structure UnitarySectorConjugacy (S : TwoSiteExactSectorGauge H) where
  /-- The unitary matrix identifying a paired sector.

  Source: arXiv:1606.00608, Appendix C.4, line 2057. -/
  unitary : ∀ γ : Fin H.labelCount,
    Matrix.unitaryGroup
      (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ
  /-- The two-site BNT tensor is the unitary conjugate of its paired one-site
  BNT tensor.

  Source: arXiv:1606.00608, Appendix C.4, lines 2053--2057. -/
  tensor_eq : ∀ (γ : Fin H.labelCount) (i : Fin (D * D)),
    S.decomposition.tensor (S.relabel γ) i =
      (unitary γ : Matrix (Fin (S.decomposition.bondDim (S.relabel γ)))
        (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ) *
      (cast (congrArg (MPSTensor (D * D)) (S.bondDim_eq γ))
        (H.tensor γ)) i *
      (unitary γ : Matrix (Fin (S.decomposition.bondDim (S.relabel γ)))
        (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ)ᴴ

private theorem reindexAlgEquiv_finCongr_apply_eq_cast
    {p q e : ℕ} (h : p = q) (A : MPSTensor e p) (i : Fin e) :
    Matrix.reindexAlgEquiv ℂ ℂ (finCongr h) (A i) =
      (cast (congrArg (MPSTensor e) h) A) i := by
  subst q
  rfl

/-- The linear equivalence of the paired direct sums induced by the sector
unitaries.  Its forward direction is \(\widetilde T\), and its inverse is
\(\widetilde S\).

Source: arXiv:1606.00608, Appendix C.4, lines 2069 and 2080. -/
noncomputable def UnitarySectorConjugacy.sectorLinearEquiv
    {S : TwoSiteExactSectorGauge H} (C : UnitarySectorConjugacy S) :
    VerticalSectorAlgebra H.bondDim ≃ₗ[ℂ]
      RelabeledTwoSiteSectorAlgebra S :=
  LinearEquiv.piCongrRight fun γ ↦
    (Matrix.unitaryReindexLinearEquiv
      (finCongr (S.bondDim_eq γ)) (C.unitary γ) (C.unitary γ).property).symm

/-- The direct-sum map \(\widetilde T\), given sectorwise by conjugation with
\(U_\gamma\).

Source: arXiv:1606.00608, Appendix C.4, line 2069. -/
noncomputable def UnitarySectorConjugacy.directSumUnitaryT
    {S : TwoSiteExactSectorGauge H} (C : UnitarySectorConjugacy S) :
    VerticalSectorAlgebra H.bondDim →ₗ[ℂ]
      RelabeledTwoSiteSectorAlgebra S :=
  C.sectorLinearEquiv.toLinearMap

/-- The direct-sum map \(\widetilde S\), given sectorwise by conjugation with
\(U_\gamma^\dagger\).

Source: arXiv:1606.00608, Appendix C.4, line 2080. -/
noncomputable def UnitarySectorConjugacy.directSumUnitaryS
    {S : TwoSiteExactSectorGauge H} (C : UnitarySectorConjugacy S) :
    RelabeledTwoSiteSectorAlgebra S →ₗ[ℂ]
      VerticalSectorAlgebra H.bondDim :=
  C.sectorLinearEquiv.symm.toLinearMap

/-- On each paired sector, \(\widetilde T\) reindexes the matrix coordinates
and conjugates by \(U_\gamma\).

Source: arXiv:1606.00608, Appendix C.4, line 2069. -/
@[simp]
theorem UnitarySectorConjugacy.directSumUnitaryT_apply
    {S : TwoSiteExactSectorGauge H} (C : UnitarySectorConjugacy S)
    (X : VerticalSectorAlgebra H.bondDim) (γ : Fin H.labelCount) :
    C.directSumUnitaryT X γ =
      (C.unitary γ : Matrix
        (Fin (S.decomposition.bondDim (S.relabel γ)))
        (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ) *
      Matrix.reindexAlgEquiv ℂ ℂ (finCongr (S.bondDim_eq γ)) (X γ) *
      (C.unitary γ : Matrix
        (Fin (S.decomposition.bondDim (S.relabel γ)))
        (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ)ᴴ := by
  simp [directSumUnitaryT, sectorLinearEquiv,
    Matrix.star_eq_conjTranspose]

/-- On each paired sector, \(\widetilde S\) conjugates by
\(U_\gamma^\dagger\) and returns to the one-site matrix coordinates.

Source: arXiv:1606.00608, Appendix C.4, line 2080. -/
@[simp]
theorem UnitarySectorConjugacy.directSumUnitaryS_apply
    {S : TwoSiteExactSectorGauge H} (C : UnitarySectorConjugacy S)
    (Y : RelabeledTwoSiteSectorAlgebra S) (γ : Fin H.labelCount) :
    C.directSumUnitaryS Y γ =
      (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (S.bondDim_eq γ))).symm
        ((C.unitary γ : Matrix
          (Fin (S.decomposition.bondDim (S.relabel γ)))
          (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ)ᴴ * Y γ *
        (C.unitary γ : Matrix
          (Fin (S.decomposition.bondDim (S.relabel γ)))
          (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ)) := by
  simp [directSumUnitaryS, sectorLinearEquiv,
    Matrix.star_eq_conjTranspose]

private theorem UnitarySectorConjugacy.forwardComponent_isKrausCPTP
    {S : TwoSiteExactSectorGauge H} (C : UnitarySectorConjugacy S)
    (γ : Fin H.labelCount) :
    IsKrausCPTP
      (Matrix.unitaryReindexLinearEquiv
        (finCongr (S.bondDim_eq γ)) (C.unitary γ)
          (C.unitary γ).property).symm.toLinearMap := by
  rw [show (Matrix.unitaryReindexLinearEquiv
      (finCongr (S.bondDim_eq γ)) (C.unitary γ)
        (C.unitary γ).property).symm.toLinearMap =
      singleKrausMap (C.unitary γ) ∘ₗ
        Matrix.equivReindexMap (finCongr (S.bondDim_eq γ)) by
    apply LinearMap.ext
    intro X
    simp [Matrix.unitaryReindexLinearEquiv_symm_apply,
      Matrix.equivReindexMap, Matrix.coe_reindexLinearEquiv,
      Matrix.star_eq_conjTranspose]]
  apply isKrausCPTP_comp
    (Matrix.equivReindexMap_isKrausCPTP (finCongr (S.bondDim_eq γ)))
  apply singleKrausMap_isKrausCPTP
  simpa only [Matrix.star_eq_conjTranspose] using
    Matrix.mem_unitaryGroup_iff'.mp (C.unitary γ).property

private theorem UnitarySectorConjugacy.backwardComponent_isKrausCPTP
    {S : TwoSiteExactSectorGauge H} (C : UnitarySectorConjugacy S)
    (γ : Fin H.labelCount) :
    IsKrausCPTP
      (Matrix.unitaryReindexLinearEquiv
        (finCongr (S.bondDim_eq γ)) (C.unitary γ)
          (C.unitary γ).property).toLinearMap := by
  rw [show (Matrix.unitaryReindexLinearEquiv
      (finCongr (S.bondDim_eq γ)) (C.unitary γ)
        (C.unitary γ).property).toLinearMap =
      Matrix.equivReindexMap (finCongr (S.bondDim_eq γ)).symm ∘ₗ
        singleKrausMap
          ((C.unitary γ : Matrix
            (Fin (S.decomposition.bondDim (S.relabel γ)))
            (Fin (S.decomposition.bondDim (S.relabel γ))) ℂ)ᴴ) by
    apply LinearMap.ext
    intro Y
    simp [Matrix.unitaryReindexLinearEquiv_apply,
      Matrix.equivReindexMap, Matrix.coe_reindexLinearEquiv,
      Matrix.star_eq_conjTranspose]]
  apply isKrausCPTP_comp
  · apply singleKrausMap_isKrausCPTP
    simpa only [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose] using
      Matrix.mem_unitaryGroup_iff.mp (C.unitary γ).property
  · exact Matrix.equivReindexMap_isKrausCPTP
      (finCongr (S.bondDim_eq γ)).symm

/-- The map \(\widetilde T\) is completely positive between the two finite
direct sums.

Source: arXiv:1606.00608, Appendix C.4, line 2069. -/
theorem UnitarySectorConjugacy.directSumUnitaryT_isKrausDirectSumMap
    {S : TwoSiteExactSectorGauge H} (C : UnitarySectorConjugacy S) :
    Matrix.IsKrausDirectSumMap C.directSumUnitaryT := by
  rw [show C.directSumUnitaryT = LinearMap.piMap (fun γ ↦
      (Matrix.unitaryReindexLinearEquiv
        (finCongr (S.bondDim_eq γ)) (C.unitary γ)
          (C.unitary γ).property).symm.toLinearMap) by
    apply LinearMap.ext
    intro X
    rfl]
  exact Matrix.isKrausDirectSumMap_piMap _
    (fun γ ↦ (C.forwardComponent_isKrausCPTP γ).isKrausCP)

/-- The map \(\widetilde S\) is completely positive between the two finite
direct sums.

Source: arXiv:1606.00608, Appendix C.4, line 2080. -/
theorem UnitarySectorConjugacy.directSumUnitaryS_isKrausDirectSumMap
    {S : TwoSiteExactSectorGauge H} (C : UnitarySectorConjugacy S) :
    Matrix.IsKrausDirectSumMap C.directSumUnitaryS := by
  rw [show C.directSumUnitaryS = LinearMap.piMap (fun γ ↦
      (Matrix.unitaryReindexLinearEquiv
        (finCongr (S.bondDim_eq γ)) (C.unitary γ)
          (C.unitary γ).property).toLinearMap) by
    apply LinearMap.ext
    intro Y
    rfl]
  exact Matrix.isKrausDirectSumMap_piMap _
    (fun γ ↦ (C.backwardComponent_isKrausCPTP γ).isKrausCP)

/-- The map \(\widetilde T\) preserves the sum of the traces of its simple
matrix summands.

Source: arXiv:1606.00608, Appendix C.4, line 2069. -/
theorem UnitarySectorConjugacy.directSumUnitaryT_isTracePreservingBetweenDirectSums
    {S : TwoSiteExactSectorGauge H} (C : UnitarySectorConjugacy S) :
    Matrix.IsTracePreservingBetweenDirectSums C.directSumUnitaryT := by
  intro X
  apply Finset.sum_congr rfl
  intro γ _
  exact (C.forwardComponent_isKrausCPTP γ).trace_map (X γ)

/-- The map \(\widetilde S\) preserves the sum of the traces of its simple
matrix summands.

Source: arXiv:1606.00608, Appendix C.4, line 2080. -/
theorem UnitarySectorConjugacy.directSumUnitaryS_isTracePreservingBetweenDirectSums
    {S : TwoSiteExactSectorGauge H} (C : UnitarySectorConjugacy S) :
    Matrix.IsTracePreservingBetweenDirectSums C.directSumUnitaryS := by
  intro Y
  apply Finset.sum_congr rfl
  intro γ _
  exact (C.backwardComponent_isKrausCPTP γ).trace_map (Y γ)

/-- The direct-sum map \(\widetilde S\) is a left inverse of
\(\widetilde T\).

Source: arXiv:1606.00608, Appendix C.4, lines 2069 and 2080. -/
theorem UnitarySectorConjugacy.directSumUnitaryS_comp_directSumUnitaryT
    {S : TwoSiteExactSectorGauge H} (C : UnitarySectorConjugacy S) :
    C.directSumUnitaryS.comp C.directSumUnitaryT = LinearMap.id := by
  apply LinearMap.ext
  intro X
  exact C.sectorLinearEquiv.symm_apply_apply X

/-- The direct-sum map \(\widetilde S\) is a right inverse of
\(\widetilde T\).

Source: arXiv:1606.00608, Appendix C.4, lines 2069 and 2080. -/
theorem UnitarySectorConjugacy.directSumUnitaryT_comp_directSumUnitaryS
    {S : TwoSiteExactSectorGauge H} (C : UnitarySectorConjugacy S) :
    C.directSumUnitaryT.comp C.directSumUnitaryS = LinearMap.id := by
  apply LinearMap.ext
  intro Y
  exact C.sectorLinearEquiv.apply_symm_apply Y

/-- The map \(\widetilde T\) sends the family of one-site BNT tensor letters
to the paired family of two-site BNT tensor letters.

Source: arXiv:1606.00608, Appendix C.4, lines 2053--2069. -/
theorem UnitarySectorConjugacy.directSumUnitaryT_tensor
    {S : TwoSiteExactSectorGauge H} (C : UnitarySectorConjugacy S)
    (i : Fin (D * D)) :
    C.directSumUnitaryT (fun γ ↦ H.tensor γ i) =
      fun γ ↦ S.decomposition.tensor (S.relabel γ) i := by
  funext γ
  rw [directSumUnitaryT_apply, reindexAlgEquiv_finCongr_apply_eq_cast]
  exact (C.tensor_eq γ i).symm

/-- The map \(\widetilde S\) sends the paired family of two-site BNT tensor
letters back to the one-site BNT tensor letters.

Source: arXiv:1606.00608, Appendix C.4, lines 2053--2080. -/
theorem UnitarySectorConjugacy.directSumUnitaryS_tensor
    {S : TwoSiteExactSectorGauge H} (C : UnitarySectorConjugacy S)
    (i : Fin (D * D)) :
    C.directSumUnitaryS
        (fun γ ↦ S.decomposition.tensor (S.relabel γ) i) =
      fun γ ↦ H.tensor γ i := by
  rw [← C.directSumUnitaryT_tensor i]
  change (C.directSumUnitaryS.comp C.directSumUnitaryT)
      (fun γ ↦ H.tensor γ i) = _
  rw [C.directSumUnitaryS_comp_directSumUnitaryT]
  rfl

end BNTAlgebraTensorClause.TwoSiteExactSectorGauge

end MPOTensor
