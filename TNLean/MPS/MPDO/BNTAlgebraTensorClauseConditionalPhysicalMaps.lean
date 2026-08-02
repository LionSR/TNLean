/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.SupportCompletion
import TNLean.MPS.MPDO.BNTAlgebraTensorClauseAmbientSectorMaps
import TNLean.MPS.MPDO.BNTAlgebraTensorClauseDirectSumUnitary
import TNLean.MPS.MPDO.RFPViaTS

/-!
# Conditional physical channels from the BNT algebra clause

Assume the unitary conjugacies between the matched one-site and two-site BNT
sectors in Appendix C.4.  The direct-sum unitary maps can then be placed
between the ambient sector retractions and normalized restorations.  The
resulting raw physical maps are completely positive and have the required
action on every physical closure, but they can lose trace on the zero-sector
complements of the retained vertical canonical forms.

The raw maps are completed on those complements by fixed measure-and-prepare
terms.  The complement terms vanish on the physical closures because the
vertical reconstruction identities place those closures in the retained
supports.  This gives the two trace-preserving completely positive maps of
Definition 4.1, conditionally on the supplied unitary sector conjugacies.

## Main definitions

* `UnitarySectorConjugacy.rawPhysicalT`
* `UnitarySectorConjugacy.rawPhysicalS`
* `UnitarySectorConjugacy.physicalT`
* `UnitarySectorConjugacy.physicalS`

## Main result

* `UnitarySectorConjugacy.isRFPViaTS`

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Definition 4.1, lines 638--660, and Appendix C.4, lines 2053--2085.
-/

open scoped BigOperators ComplexOrder Matrix

noncomputable section

namespace MPOTensor

namespace BNTAlgebraTensorClause

variable {d D : ℕ} {M : MPOTensor d D}

/-! ### Retained physical projections -/

/-- The one-site initial projection of the vertical coisometry.

Source: arXiv:1606.00608, Appendix C.4, lines 2065--2068 and 2081--2083. -/
def oneSiteRetainedProjection (H : BNTAlgebraTensorClause M) :
    Matrix (Fin d) (Fin d) ℂ :=
  H.verticalCoisometryᴴ * H.verticalCoisometry

/-- The one-site retained projection is Hermitian.

Source: arXiv:1606.00608, Appendix C.4, lines 2065--2068. -/
theorem oneSiteRetainedProjection_isHermitian
    (H : BNTAlgebraTensorClause M) :
    H.oneSiteRetainedProjection.IsHermitian := by
  exact (Matrix.isOrthogonalProjection_conjTranspose_mul_of_mul_conjTranspose_eq_one
    H.verticalCoisometry H.coisometry).1

/-- The one-site retained projection is idempotent.

Source: arXiv:1606.00608, Appendix C.4, lines 2065--2068. -/
theorem oneSiteRetainedProjection_mul_self
    (H : BNTAlgebraTensorClause M) :
    H.oneSiteRetainedProjection * H.oneSiteRetainedProjection =
      H.oneSiteRetainedProjection := by
  exact (Matrix.isOrthogonalProjection_conjTranspose_mul_of_mul_conjTranspose_eq_one
    H.verticalCoisometry H.coisometry).2

namespace TwoSiteMultiplicitySpectrum

/-- The two-site initial projection of the relabelled vertical coisometry,
transported from a blocked physical index to a pair of physical indices.

Source: arXiv:1606.00608, Appendix C.4, lines 2070--2079. -/
def twoSiteRetainedProjection {H : BNTAlgebraTensorClause M}
    (S : TwoSiteMultiplicitySpectrum H) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  Matrix.equivReindexMap (blockedIndexEquiv d)
    (S.relabeledTwoSiteCoisometryᴴ * S.relabeledTwoSiteCoisometry)

/-- The relabelled two-site retained projection is Hermitian.

Source: arXiv:1606.00608, Appendix C.4, lines 2070--2079. -/
theorem twoSiteRetainedProjection_isHermitian
    {H : BNTAlgebraTensorClause M} (S : TwoSiteMultiplicitySpectrum H) :
    S.twoSiteRetainedProjection.IsHermitian := by
  rw [twoSiteRetainedProjection, Matrix.equivReindexMap]
  exact (Matrix.isOrthogonalProjection_conjTranspose_mul_of_mul_conjTranspose_eq_one
    S.relabeledTwoSiteCoisometry
    S.relabeledTwoSiteCoisometry_coisometry).1.reindex _

/-- The relabelled two-site retained projection is idempotent.

Source: arXiv:1606.00608, Appendix C.4, lines 2070--2079. -/
theorem twoSiteRetainedProjection_mul_self
    {H : BNTAlgebraTensorClause M} (S : TwoSiteMultiplicitySpectrum H) :
    S.twoSiteRetainedProjection * S.twoSiteRetainedProjection =
      S.twoSiteRetainedProjection := by
  rw [twoSiteRetainedProjection, Matrix.equivReindexMap]
  change
    Matrix.reindexLinearEquiv ℂ ℂ (blockedIndexEquiv d) (blockedIndexEquiv d)
        (S.relabeledTwoSiteCoisometryᴴ * S.relabeledTwoSiteCoisometry) *
      Matrix.reindexLinearEquiv ℂ ℂ (blockedIndexEquiv d) (blockedIndexEquiv d)
        (S.relabeledTwoSiteCoisometryᴴ * S.relabeledTwoSiteCoisometry) =
    Matrix.reindexLinearEquiv ℂ ℂ (blockedIndexEquiv d) (blockedIndexEquiv d)
      (S.relabeledTwoSiteCoisometryᴴ * S.relabeledTwoSiteCoisometry)
  rw [Matrix.reindexLinearEquiv_mul]
  rw [(Matrix.isOrthogonalProjection_conjTranspose_mul_of_mul_conjTranspose_eq_one
    S.relabeledTwoSiteCoisometry
    S.relabeledTwoSiteCoisometry_coisometry).2]

end TwoSiteMultiplicitySpectrum

namespace TwoSiteExactSectorGauge

variable {H : BNTAlgebraTensorClause M} {S : TwoSiteExactSectorGauge H}

/-! ### Raw physical maps -/

/-- The raw refinement map
\(T_0=\widetilde R_2\widetilde T R_1\), expressed through canonical
full-matrix extensions of the sector maps.

**Scope restriction (supplied unitary sector conjugacies):** The middle map
uses the unitary conclusion of Appendix C.4, line 2057, as a hypothesis.  Its
unconditional derivation is documented in
`docs/paper-gaps/cpsv16_two_site_sector_unitary_gauge_gap.tex`.

Source: arXiv:1606.00608, Appendix C.4, lines 2065--2071. -/
def UnitarySectorConjugacy.rawPhysicalT (C : UnitarySectorConjugacy S) :
    Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  S.toTwoSiteMultiplicitySpectrum.twoSiteNormalizedAmbientSectorRestorationExtension.comp
    ((Matrix.directSumMapExtension C.directSumUnitaryT).comp
      H.oneSiteAmbientSectorRetractionExtension)

/-- The raw coarse-graining map
\(S_0=\widetilde R_1\widetilde S R_2\), expressed through canonical
full-matrix extensions of the sector maps.

**Scope restriction (supplied unitary sector conjugacies):** The middle map
uses the unitary conclusion of Appendix C.4, line 2057, as a hypothesis.  Its
unconditional derivation is documented in
`docs/paper-gaps/cpsv16_two_site_sector_unitary_gauge_gap.tex`.

Source: arXiv:1606.00608, Appendix C.4, lines 2078--2083. -/
def UnitarySectorConjugacy.rawPhysicalS (C : UnitarySectorConjugacy S) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ :=
  H.oneSiteNormalizedAmbientSectorRestorationExtension.comp
    ((Matrix.directSumMapExtension C.directSumUnitaryS).comp
      S.toTwoSiteMultiplicitySpectrum.twoSiteAmbientSectorRetractionExtension)

/-- The raw refinement map is completely positive.

Source: arXiv:1606.00608, Appendix C.4, lines 2065--2071. -/
theorem UnitarySectorConjugacy.rawPhysicalT_isKrausCP
    (C : UnitarySectorConjugacy S) :
    IsKrausCP C.rawPhysicalT := by
  apply isKrausCP_comp
  · apply isKrausCP_comp
    · exact H.oneSiteAmbientSectorRetractionExtension_isKrausCP
    · exact C.directSumUnitaryT_isKrausDirectSumMap
  · exact S.toTwoSiteMultiplicitySpectrum
      |>.twoSiteNormalizedAmbientSectorRestorationExtension_isKrausCPTP
      |>.isKrausCP

/-- The raw coarse-graining map is completely positive.

Source: arXiv:1606.00608, Appendix C.4, lines 2078--2083. -/
theorem UnitarySectorConjugacy.rawPhysicalS_isKrausCP
    (C : UnitarySectorConjugacy S) :
    IsKrausCP C.rawPhysicalS := by
  apply isKrausCP_comp
  · apply isKrausCP_comp
    · exact S.toTwoSiteMultiplicitySpectrum
        |>.twoSiteAmbientSectorRetractionExtension_isKrausCP
    · exact C.directSumUnitaryS_isKrausDirectSumMap
  · exact H.oneSiteNormalizedAmbientSectorRestorationExtension_isKrausCPTP.isKrausCP

/-- The canonical full-matrix extension of a trace-preserving map between two
finite direct sums preserves the ordinary matrix trace.

Source: arXiv:1606.00608, Appendix C.4, lines 2069 and 2080. -/
private theorem trace_directSumMapExtension_of_tracePreserving
    {g₁ g₂ : ℕ} {dim₁ : Fin g₁ → ℕ} {dim₂ : Fin g₂ → ℕ}
    (F : VerticalSectorAlgebra dim₁ →ₗ[ℂ] VerticalSectorAlgebra dim₂)
    (hF : Matrix.IsTracePreservingBetweenDirectSums F)
    (X : Matrix (Σ α, Fin (dim₁ α)) (Σ α, Fin (dim₁ α)) ℂ) :
    Matrix.trace (Matrix.directSumMapExtension F X) = Matrix.trace X := by
  rw [Matrix.directSumMapExtension_apply,
    Matrix.trace_directSumDiagonalEmbedding, hF,
    Matrix.sum_trace_directSumDiagonalCompression]

/-- The trace of the raw refinement map is the trace retained by the one-site
vertical support projection.

Source: arXiv:1606.00608, Appendix C.4, lines 2065--2071. -/
theorem UnitarySectorConjugacy.trace_rawPhysicalT
    (C : UnitarySectorConjugacy S) (X : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.trace (C.rawPhysicalT X) =
      Matrix.trace (H.oneSiteRetainedProjection * X) := by
  rw [rawPhysicalT, LinearMap.comp_apply, LinearMap.comp_apply]
  rw [S.toTwoSiteMultiplicitySpectrum
    |>.twoSiteNormalizedAmbientSectorRestorationExtension_isKrausCPTP.trace_map]
  rw [trace_directSumMapExtension_of_tracePreserving C.directSumUnitaryT
    C.directSumUnitaryT_isTracePreservingBetweenDirectSums]
  change Matrix.trace
      (Matrix.directSumDiagonalEmbedding (H.oneSiteAmbientSectorRetraction X)) = _
  rw [Matrix.trace_directSumDiagonalEmbedding]
  change verticalSectorTrace (H.oneSiteAmbientSectorRetraction X) = _
  rw [H.verticalSectorTrace_oneSiteAmbientSectorRetraction,
    Matrix.trace_mul_cycle]
  rfl

/-- The trace of the raw coarse-graining map is the trace retained by the
two-site vertical support projection.

Source: arXiv:1606.00608, Appendix C.4, lines 2078--2083. -/
theorem UnitarySectorConjugacy.trace_rawPhysicalS
    (C : UnitarySectorConjugacy S)
    (X : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix.trace (C.rawPhysicalS X) =
      Matrix.trace
        (S.toTwoSiteMultiplicitySpectrum.twoSiteRetainedProjection * X) := by
  rw [rawPhysicalS, LinearMap.comp_apply, LinearMap.comp_apply]
  rw [H.oneSiteNormalizedAmbientSectorRestorationExtension_isKrausCPTP.trace_map]
  rw [trace_directSumMapExtension_of_tracePreserving C.directSumUnitaryS
    C.directSumUnitaryS_isTracePreservingBetweenDirectSums]
  change Matrix.trace (Matrix.directSumDiagonalEmbedding
      (S.toTwoSiteMultiplicitySpectrum.twoSiteAmbientSectorRetraction X)) = _
  rw [Matrix.trace_directSumDiagonalEmbedding]
  change verticalSectorTrace
      (S.toTwoSiteMultiplicitySpectrum.twoSiteAmbientSectorRetraction X) = _
  rw [S.toTwoSiteMultiplicitySpectrum
      |>.verticalSectorTrace_twoSiteAmbientSectorRetraction,
    Matrix.trace_mul_cycle]
  rw [TwoSiteMultiplicitySpectrum.twoSiteRetainedProjection]
  simp only [Matrix.equivReindexMap]
  let P := S.relabeledTwoSiteCoisometryᴴ * S.relabeledTwoSiteCoisometry
  let Y := Matrix.reindex (blockedIndexEquiv d).symm
    (blockedIndexEquiv d).symm X
  change (P * Y).trace =
    (Matrix.reindex (blockedIndexEquiv d) (blockedIndexEquiv d) P * X).trace
  have hY : Matrix.reindex (blockedIndexEquiv d) (blockedIndexEquiv d) Y = X := by
    simpa only [Y, Matrix.coe_reindexLinearEquiv,
      Matrix.symm_reindexLinearEquiv] using
      (Matrix.reindexLinearEquiv ℂ ℂ (blockedIndexEquiv d)
        (blockedIndexEquiv d)).apply_symm_apply X
  have hmul :
      Matrix.reindex (blockedIndexEquiv d) (blockedIndexEquiv d) P *
          Matrix.reindex (blockedIndexEquiv d) (blockedIndexEquiv d) Y =
        Matrix.reindex (blockedIndexEquiv d) (blockedIndexEquiv d) (P * Y) := by
    exact Matrix.reindexLinearEquiv_mul ℂ ℂ
      (blockedIndexEquiv d) (blockedIndexEquiv d) (blockedIndexEquiv d) P Y
  calc
    (P * Y).trace =
        (Matrix.reindex (blockedIndexEquiv d) (blockedIndexEquiv d)
          (P * Y)).trace := (Matrix.trace_reindex (blockedIndexEquiv d) _).symm
    _ = (Matrix.reindex (blockedIndexEquiv d) (blockedIndexEquiv d) P *
          Matrix.reindex (blockedIndexEquiv d) (blockedIndexEquiv d) Y).trace := by
      rw [hmul]
    _ = (Matrix.reindex (blockedIndexEquiv d) (blockedIndexEquiv d) P * X).trace := by
      rw [hY]

/-! ### Action on tensor letters and physical closures -/

/-- The direct-sum refinement commutes with sector-dependent scalar
multiplication on the matched tensor family.

Source: arXiv:1606.00608, Appendix C.4, lines 2053--2069. -/
private theorem UnitarySectorConjugacy.directSumUnitaryT_smul_tensor
    (C : UnitarySectorConjugacy S) (a : Fin H.labelCount → ℂ)
    (v : Fin (D * D)) :
    C.directSumUnitaryT (fun γ ↦ a γ • H.tensor γ v) =
      fun γ ↦ a γ • S.decomposition.tensor (S.relabel γ) v := by
  funext γ
  calc
    C.directSumUnitaryT (fun δ ↦ a δ • H.tensor δ v) γ =
        a γ • C.directSumUnitaryT (fun δ ↦ H.tensor δ v) γ := by
      simp only [directSumUnitaryT_apply, map_smul, Matrix.mul_smul,
        Matrix.smul_mul]
    _ = a γ • S.decomposition.tensor (S.relabel γ) v := by
      rw [congrFun (C.directSumUnitaryT_tensor v) γ]

/-- The direct-sum coarse-graining commutes with sector-dependent scalar
multiplication on the matched tensor family.

Source: arXiv:1606.00608, Appendix C.4, lines 2053--2080. -/
private theorem UnitarySectorConjugacy.directSumUnitaryS_smul_tensor
    (C : UnitarySectorConjugacy S) (a : Fin H.labelCount → ℂ)
    (v : Fin (D * D)) :
    C.directSumUnitaryS
        (fun γ ↦ a γ • S.decomposition.tensor (S.relabel γ) v) =
      fun γ ↦ a γ • H.tensor γ v := by
  funext γ
  calc
    C.directSumUnitaryS
        (fun δ ↦ a δ • S.decomposition.tensor (S.relabel δ) v) γ =
        a γ • C.directSumUnitaryS
          (fun δ ↦ S.decomposition.tensor (S.relabel δ) v) γ := by
      simp only [directSumUnitaryS_apply, map_smul, Matrix.mul_smul,
        Matrix.smul_mul]
    _ = a γ • H.tensor γ v := by
      rw [congrFun (C.directSumUnitaryS_tensor v) γ]

/-- On a one-site vertical tensor letter, the raw refinement map gives the
corresponding decoded two-site vertical tensor letter.

Source: arXiv:1606.00608, Appendix C.4, lines 2065--2071. -/
theorem UnitarySectorConjugacy.rawPhysicalT_verticalTensor
    (C : UnitarySectorConjugacy S) (v : Fin (D * D)) :
    C.rawPhysicalT (verticalTensor M v) =
      Matrix.equivReindexMap (blockedIndexEquiv d)
        (verticalTensor (blockTwo M) v) := by
  simp only [rawPhysicalT, LinearMap.comp_apply,
    oneSiteAmbientSectorRetractionExtension,
    verticalSectorAmbientRetractionExtension,
    Matrix.directSumMapExtension_apply,
    Matrix.directSumDiagonalCompression_embedding,
    TwoSiteMultiplicitySpectrum.twoSiteNormalizedAmbientSectorRestorationExtension,
    normalizedVerticalSectorAmbientRestorationExtension]
  change S.toTwoSiteMultiplicitySpectrum.twoSiteNormalizedAmbientSectorRestoration
      (C.directSumUnitaryT
        (H.oneSiteAmbientSectorRetraction (verticalTensor M v))) =
    Matrix.equivReindexMap (blockedIndexEquiv d)
      (verticalTensor (blockTwo M) v)
  rw [H.oneSiteAmbientSectorRetraction_verticalTensor,
    C.directSumUnitaryT_smul_tensor
      (fun γ ↦ verticalMultiplicityTrace H.weight γ) v]
  exact S.toTwoSiteMultiplicitySpectrum
    |>.twoSiteNormalizedAmbientSectorRestoration_trace_smul_verticalTensor v

/-- On a decoded two-site vertical tensor letter, the raw coarse-graining map
gives the corresponding one-site vertical tensor letter.

Source: arXiv:1606.00608, Appendix C.4, lines 2078--2083. -/
theorem UnitarySectorConjugacy.rawPhysicalS_verticalTensor
    (C : UnitarySectorConjugacy S) (v : Fin (D * D)) :
    C.rawPhysicalS
        (Matrix.equivReindexMap (blockedIndexEquiv d)
          (verticalTensor (blockTwo M) v)) =
      verticalTensor M v := by
  simp only [rawPhysicalS, LinearMap.comp_apply,
    TwoSiteMultiplicitySpectrum.twoSiteAmbientSectorRetractionExtension,
    verticalSectorAmbientRetractionExtension,
    Matrix.directSumMapExtension_apply,
    Matrix.directSumDiagonalCompression_embedding,
    oneSiteNormalizedAmbientSectorRestorationExtension,
    normalizedVerticalSectorAmbientRestorationExtension]
  change H.oneSiteNormalizedAmbientSectorRestoration
      (C.directSumUnitaryS
        (S.toTwoSiteMultiplicitySpectrum.twoSiteAmbientSectorRetraction
          (Matrix.equivReindexMap (blockedIndexEquiv d)
            (verticalTensor (blockTwo M) v)))) =
    verticalTensor M v
  rw [S.toTwoSiteMultiplicitySpectrum
      |>.twoSiteAmbientSectorRetraction_verticalTensor,
    C.directSumUnitaryS_smul_tensor
      (fun γ ↦ verticalMultiplicityTrace H.weight γ) v]
  exact H.oneSiteNormalizedAmbientSectorRestoration_trace_smul_verticalTensor v

/-- The raw refinement map has the Definition 4.1 action on every one-site
physical closure.

Source: arXiv:1606.00608, Definition 4.1, lines 638--660, and Appendix C.4,
lines 2065--2071. -/
theorem UnitarySectorConjugacy.rawPhysicalT_physClose1
    (C : UnitarySectorConjugacy S) (X : Matrix (Fin D) (Fin D) ℂ) :
    C.rawPhysicalT (physClose1 M X) = physClose2 M X := by
  rw [← contractBondMatrix_verticalTensor_eq_physClose1]
  calc
    C.rawPhysicalT (MPSTensor.contractBondMatrix (verticalTensor M) X) =
        ∑ v : Fin (D * D), X v.modNat v.divNat •
          Matrix.equivReindexMap (blockedIndexEquiv d)
            (verticalTensor (blockTwo M) v) := by
      simp only [MPSTensor.contractBondMatrix_apply, map_sum, map_smul,
        C.rawPhysicalT_verticalTensor]
    _ = Matrix.equivReindexMap (blockedIndexEquiv d)
        (MPSTensor.contractBondMatrix (verticalTensor (blockTwo M)) X) := by
      simp only [MPSTensor.contractBondMatrix_apply, map_sum, map_smul]
    _ = Matrix.equivReindexMap (blockedIndexEquiv d)
        (physClose1 (blockTwo M) X) := by
      rw [contractBondMatrix_verticalTensor_eq_physClose1]
    _ = physClose2 M X := physClose1_blockTwo_eq_physClose2_apply M X

/-- The raw coarse-graining map has the Definition 4.1 action on every
two-site physical closure.

Source: arXiv:1606.00608, Definition 4.1, lines 638--660, and Appendix C.4,
lines 2078--2083. -/
theorem UnitarySectorConjugacy.rawPhysicalS_physClose2
    (C : UnitarySectorConjugacy S) (X : Matrix (Fin D) (Fin D) ℂ) :
    C.rawPhysicalS (physClose2 M X) = physClose1 M X := by
  rw [← physClose1_blockTwo_eq_physClose2_apply M X,
    ← contractBondMatrix_verticalTensor_eq_physClose1]
  calc
    C.rawPhysicalS
        (Matrix.equivReindexMap (blockedIndexEquiv d)
          (MPSTensor.contractBondMatrix (verticalTensor (blockTwo M)) X)) =
        ∑ v : Fin (D * D), X v.modNat v.divNat • verticalTensor M v := by
      simp only [MPSTensor.contractBondMatrix_apply, map_sum, map_smul,
        C.rawPhysicalS_verticalTensor]
    _ = MPSTensor.contractBondMatrix (verticalTensor M) X := by
      rw [MPSTensor.contractBondMatrix_apply]
    _ = physClose1 M X := by
      rw [contractBondMatrix_verticalTensor_eq_physClose1]

/-! ### Support of the source-generated physical closures -/

/-- A matrix reconstructed by expansion along a coisometry is supported on
the coisometry's initial projection.

Source: arXiv:1606.00608, Appendix C.4, lines 2065--2083. -/
private theorem supported_of_eq_conjTranspose_mul_mul
    {r n : ℕ} (U : Matrix (Fin r) (Fin n) ℂ) (hU : U * Uᴴ = 1)
    (Z : Matrix (Fin r) (Fin r) ℂ) :
    (Uᴴ * U) * (Uᴴ * Z * U) * (Uᴴ * U) = Uᴴ * Z * U := by
  calc
    (Uᴴ * U) * (Uᴴ * Z * U) * (Uᴴ * U) =
        Uᴴ * (U * Uᴴ) * Z * (U * Uᴴ) * U := by
      simp only [Matrix.mul_assoc]
    _ = Uᴴ * Z * U := by rw [hU]; simp

/-- Every one-site physical closure is supported on the retained one-site
vertical subspace.

Source: arXiv:1606.00608, Definition 4.1, lines 638--660, and Appendix C.4,
lines 2065--2068. -/
theorem oneSiteRetainedProjection_physClose1
    (H : BNTAlgebraTensorClause M) (X : Matrix (Fin D) (Fin D) ℂ) :
    H.oneSiteRetainedProjection * physClose1 M X *
        H.oneSiteRetainedProjection =
      physClose1 M X := by
  rw [oneSiteRetainedProjection,
    physClose1_eq_of_vertical_reconstruction M
      (verticalAssembledTensor H.bondDim H.multiplicity H.weight H.tensor)
      H.verticalCoisometry H.reconstruction X]
  exact supported_of_eq_conjTranspose_mul_mul H.verticalCoisometry H.coisometry _

/-- Every two-site physical closure is supported on the retained relabelled
two-site vertical subspace.

Source: arXiv:1606.00608, Definition 4.1, lines 638--660, and Appendix C.4,
lines 2070--2079. -/
theorem twoSiteRetainedProjection_physClose2
    (S₀ : TwoSiteMultiplicitySpectrum H) (X : Matrix (Fin D) (Fin D) ℂ) :
    S₀.twoSiteRetainedProjection * physClose2 M X *
        S₀.twoSiteRetainedProjection =
      physClose2 M X := by
  let U := S₀.relabeledTwoSiteCoisometry
  have hBlocked :
      (Uᴴ * U) * physClose1 (blockTwo M) X * (Uᴴ * U) =
        physClose1 (blockTwo M) X := by
    rw [physClose1_eq_of_vertical_reconstruction (blockTwo M)
      (fun v ↦ verticalSectorBlockDiagonal S₀.relabeledTwoSiteBondDim
        S₀.relabeledTwoSiteMultiplicity (fun γ ↦
          Matrix.kroneckerMap (· * ·)
            (Matrix.diagonal (S₀.relabeledTwoSiteWeight γ))
            (S₀.decomposition.tensor (S₀.relabel γ) v)))
      U S₀.relabeledTwoSiteCoisometry_reconstruction_verticalTensor X]
    exact supported_of_eq_conjTranspose_mul_mul U
      S₀.relabeledTwoSiteCoisometry_coisometry _
  rw [← physClose1_blockTwo_eq_physClose2_apply M X,
    TwoSiteMultiplicitySpectrum.twoSiteRetainedProjection,
    Matrix.equivReindexMap]
  change
    Matrix.reindexLinearEquiv ℂ ℂ (blockedIndexEquiv d) (blockedIndexEquiv d)
          (S₀.relabeledTwoSiteCoisometryᴴ * S₀.relabeledTwoSiteCoisometry) *
        Matrix.reindexLinearEquiv ℂ ℂ (blockedIndexEquiv d) (blockedIndexEquiv d)
          (physClose1 (blockTwo M) X) *
      Matrix.reindexLinearEquiv ℂ ℂ (blockedIndexEquiv d) (blockedIndexEquiv d)
        (S₀.relabeledTwoSiteCoisometryᴴ * S₀.relabeledTwoSiteCoisometry) =
    Matrix.reindexLinearEquiv ℂ ℂ (blockedIndexEquiv d) (blockedIndexEquiv d)
      (physClose1 (blockTwo M) X)
  rw [Matrix.reindexLinearEquiv_mul ℂ ℂ
      (blockedIndexEquiv d) (blockedIndexEquiv d) (blockedIndexEquiv d),
    Matrix.reindexLinearEquiv_mul ℂ ℂ
      (blockedIndexEquiv d) (blockedIndexEquiv d) (blockedIndexEquiv d)]
  exact congrArg (Matrix.reindexLinearEquiv ℂ ℂ
    (blockedIndexEquiv d) (blockedIndexEquiv d)) hBlocked

/-! ### Trace-preserving physical completions -/

/-- On an empty input matrix algebra, the zero map is trace-preserving and
completely positive, with the empty Kraus family resolving the empty
identity.

Source: arXiv:1606.00608, Definition 4.1, lines 638--660. -/
private theorem zero_isKrausCPTP_of_isEmpty
    {m n : Type*} [Fintype m] [DecidableEq m] [IsEmpty m]
    [Fintype n] [DecidableEq n] :
    IsKrausCPTP (0 : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ) := by
  refine ⟨0, fun i ↦ Fin.elim0 i, ?_, ?_⟩
  · intro X
    simp
  · ext i j
    exact isEmptyElim i

/-- The completed physical refinement map.  Outside the retained one-site
support it measures the discarded weight and prepares a fixed faithful
two-site density matrix.

**Local fix (zero-sector complement):** The raw retraction can discard a zero
sector.  The measure-and-prepare completion restores trace without changing
the tensor-generated physical closures; see
`docs/paper-gaps/cpgsv17_vertical_isometry_zero_sector.tex`.

**Scope restriction (supplied unitary sector conjugacies):** The middle map
uses the unitary conclusion of Appendix C.4, line 2057, as a hypothesis; see
`docs/paper-gaps/cpsv16_two_site_sector_unitary_gauge_gap.tex`.

Source: arXiv:1606.00608, Definition 4.1, lines 638--660, and Appendix C.4,
lines 2065--2071. -/
def UnitarySectorConjugacy.physicalT (C : UnitarySectorConjugacy S) :
    Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  if hd : d = 0 then 0
  else
    letI : NeZero d := ⟨hd⟩
    Matrix.supportCompletion C.rawPhysicalT H.oneSiteRetainedProjection
      (Matrix.faithfulDensity (Fin d × Fin d))

/-- The completed physical coarse-graining map.  Outside the retained
two-site support it measures the discarded weight and prepares a fixed
faithful one-site density matrix.

**Local fix (zero-sector complement):** The raw retraction can discard a zero
sector.  The measure-and-prepare completion restores trace without changing
the tensor-generated physical closures; see
`docs/paper-gaps/cpgsv17_vertical_isometry_zero_sector.tex`.

**Scope restriction (supplied unitary sector conjugacies):** The middle map
uses the unitary conclusion of Appendix C.4, line 2057, as a hypothesis; see
`docs/paper-gaps/cpsv16_two_site_sector_unitary_gauge_gap.tex`.

Source: arXiv:1606.00608, Definition 4.1, lines 638--660, and Appendix C.4,
lines 2078--2083. -/
def UnitarySectorConjugacy.physicalS (C : UnitarySectorConjugacy S) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ :=
  if hd : d = 0 then 0
  else
    letI : NeZero d := ⟨hd⟩
    Matrix.supportCompletion C.rawPhysicalS
      S.toTwoSiteMultiplicitySpectrum.twoSiteRetainedProjection
      (Matrix.faithfulDensity (Fin d))

/-- The completed physical refinement map is trace-preserving and completely
positive.

**Local fix (zero-sector complement):** The complementary branch restores
the trace discarded by the raw one-site retraction; see
`docs/paper-gaps/cpgsv17_vertical_isometry_zero_sector.tex`.

**Scope restriction (supplied unitary sector conjugacies):** The middle map
uses the supplied line-2057 unitary conjugacies; see
`docs/paper-gaps/cpsv16_two_site_sector_unitary_gauge_gap.tex`.

Source: arXiv:1606.00608, Definition 4.1, lines 638--660, and Appendix C.4,
lines 2065--2071. -/
theorem UnitarySectorConjugacy.physicalT_isKrausCPTP
    (C : UnitarySectorConjugacy S) :
    IsKrausCPTP C.physicalT := by
  rw [physicalT]
  split
  · rename_i hd
    subst d
    exact zero_isKrausCPTP_of_isEmpty
  · rename_i hd
    letI : NeZero d := ⟨hd⟩
    exact Matrix.supportCompletion_isKrausCPTP
      C.rawPhysicalT H.oneSiteRetainedProjection
      (Matrix.faithfulDensity (Fin d × Fin d))
      C.rawPhysicalT_isKrausCP
      H.oneSiteRetainedProjection_isHermitian
      H.oneSiteRetainedProjection_mul_self
      C.trace_rawPhysicalT
      (Matrix.faithfulDensity_posDef (Fin d × Fin d)).posSemidef
      (Matrix.faithfulDensity_trace (Fin d × Fin d))

/-- The completed physical coarse-graining map is trace-preserving and
completely positive.

**Local fix (zero-sector complement):** The complementary branch restores
the trace discarded by the raw two-site retraction; see
`docs/paper-gaps/cpgsv17_vertical_isometry_zero_sector.tex`.

**Scope restriction (supplied unitary sector conjugacies):** The middle map
uses the supplied line-2057 unitary conjugacies; see
`docs/paper-gaps/cpsv16_two_site_sector_unitary_gauge_gap.tex`.

Source: arXiv:1606.00608, Definition 4.1, lines 638--660, and Appendix C.4,
lines 2078--2083. -/
theorem UnitarySectorConjugacy.physicalS_isKrausCPTP
    (C : UnitarySectorConjugacy S) :
    IsKrausCPTP C.physicalS := by
  rw [physicalS]
  split
  · rename_i hd
    subst d
    exact zero_isKrausCPTP_of_isEmpty
  · rename_i hd
    letI : NeZero d := ⟨hd⟩
    exact Matrix.supportCompletion_isKrausCPTP
      C.rawPhysicalS S.toTwoSiteMultiplicitySpectrum.twoSiteRetainedProjection
      (Matrix.faithfulDensity (Fin d))
      C.rawPhysicalS_isKrausCP
      S.toTwoSiteMultiplicitySpectrum.twoSiteRetainedProjection_isHermitian
      S.toTwoSiteMultiplicitySpectrum.twoSiteRetainedProjection_mul_self
      C.trace_rawPhysicalS
      (Matrix.faithfulDensity_posDef (Fin d)).posSemidef
      (Matrix.faithfulDensity_trace (Fin d))

/-- The completed refinement map has the Definition 4.1 action on every
one-site physical closure.

**Local fix (zero-sector complement):** The added complement vanishes on the
retained support of every physical closure; see
`docs/paper-gaps/cpgsv17_vertical_isometry_zero_sector.tex`.

Source: arXiv:1606.00608, Definition 4.1, lines 638--660, and Appendix C.4,
lines 2065--2071. -/
theorem UnitarySectorConjugacy.physicalT_physClose1
    (C : UnitarySectorConjugacy S) (X : Matrix (Fin D) (Fin D) ℂ) :
    C.physicalT (physClose1 M X) = physClose2 M X := by
  rw [physicalT]
  split
  · rename_i hd
    subst d
    exact Subsingleton.elim _ _
  · rename_i hd
    letI : NeZero d := ⟨hd⟩
    calc
      Matrix.supportCompletion C.rawPhysicalT H.oneSiteRetainedProjection
          (Matrix.faithfulDensity (Fin d × Fin d)) (physClose1 M X) =
          C.rawPhysicalT (physClose1 M X) :=
        Matrix.supportCompletion_apply_of_supported
          C.rawPhysicalT H.oneSiteRetainedProjection
          (Matrix.faithfulDensity (Fin d × Fin d)) (physClose1 M X)
          H.oneSiteRetainedProjection_isHermitian
          H.oneSiteRetainedProjection_mul_self
          (oneSiteRetainedProjection_physClose1 H X)
      _ = physClose2 M X := C.rawPhysicalT_physClose1 X

/-- The completed coarse-graining map has the Definition 4.1 action on every
two-site physical closure.

**Local fix (zero-sector complement):** The added complement vanishes on the
retained support of every physical closure; see
`docs/paper-gaps/cpgsv17_vertical_isometry_zero_sector.tex`.

Source: arXiv:1606.00608, Definition 4.1, lines 638--660, and Appendix C.4,
lines 2078--2083. -/
theorem UnitarySectorConjugacy.physicalS_physClose2
    (C : UnitarySectorConjugacy S) (X : Matrix (Fin D) (Fin D) ℂ) :
    C.physicalS (physClose2 M X) = physClose1 M X := by
  rw [physicalS]
  split
  · rename_i hd
    subst d
    exact Subsingleton.elim _ _
  · rename_i hd
    letI : NeZero d := ⟨hd⟩
    calc
      Matrix.supportCompletion C.rawPhysicalS
          S.toTwoSiteMultiplicitySpectrum.twoSiteRetainedProjection
          (Matrix.faithfulDensity (Fin d)) (physClose2 M X) =
          C.rawPhysicalS (physClose2 M X) :=
        Matrix.supportCompletion_apply_of_supported
          C.rawPhysicalS
          S.toTwoSiteMultiplicitySpectrum.twoSiteRetainedProjection
          (Matrix.faithfulDensity (Fin d)) (physClose2 M X)
          S.toTwoSiteMultiplicitySpectrum.twoSiteRetainedProjection_isHermitian
          S.toTwoSiteMultiplicitySpectrum.twoSiteRetainedProjection_mul_self
          (twoSiteRetainedProjection_physClose2
            S.toTwoSiteMultiplicitySpectrum X)
      _ = physClose1 M X := C.rawPhysicalS_physClose2 X

/-- The BNT algebra clause gives the trace-preserving completely positive
maps of Definition 4.1, conditionally on the unitary conjugacies between its
matched one-site and two-site sectors.

**Scope restriction (supplied unitary sector conjugacies):** This theorem
assumes the unitary conclusion of Appendix C.4, line 2057.  Its derivation
from the tensor-attached algebra clause remains open and is documented in
`docs/paper-gaps/cpsv16_two_site_sector_unitary_gauge_gap.tex`.

**Local fix (zero-sector complement):** The raw maps are completed on the
orthogonal complements of the retained vertical sectors as documented in
`docs/paper-gaps/cpgsv17_vertical_isometry_zero_sector.tex`.

Source: arXiv:1606.00608, Definition 4.1, lines 638--660, and Appendix C.4,
lines 2053--2085. -/
theorem UnitarySectorConjugacy.isRFPViaTS
    (C : UnitarySectorConjugacy S) : IsRFPViaTS M := by
  exact ⟨C.physicalS, C.physicalT,
    C.physicalS_isKrausCPTP, C.physicalT_isKrausCPTP,
    C.physicalS_physClose2, C.physicalT_physClose1⟩

end TwoSiteExactSectorGauge

end BNTAlgebraTensorClause

end MPOTensor
