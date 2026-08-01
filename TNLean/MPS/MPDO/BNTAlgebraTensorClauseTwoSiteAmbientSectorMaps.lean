/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTAlgebraTensorClauseAmbientSectorCoordinates
import TNLean.MPS.MPDO.VerticalSectorAmbientMaps

/-!
# Two-site ambient sector maps for the BNT algebra clause

The relabelled two-site vertical canonical decomposition determines a raw
retraction from the product-index physical matrix algebra to its matched
simple-sector algebra and a normalized restoration in the opposite direction.
The canonical equivalence between a pair of physical indices and one blocked
index transports both maps between these two descriptions.

The canonical full-matrix representatives are completely positive.  The raw
retraction is trace-nonincreasing because the retained coisometry may omit a
zero-sector complement, whereas the normalized restoration preserves trace and
is a right inverse.  On weighted two-site vertical tensor letters, both maps
use the multiplicity trace inherited from the matched one-site sector.

## Main definitions

* `twoSiteAmbientSectorRetraction`
* `twoSiteAmbientSectorRetractionExtension`
* `twoSiteNormalizedAmbientSectorRestoration`
* `twoSiteNormalizedAmbientSectorRestorationExtension`

## Main results

* `verticalSectorTrace_twoSiteAmbientSectorRetraction_le`
* `twoSiteNormalizedAmbientSectorRestoration_apply_explicit`
* `twoSiteNormalizedAmbientSectorRestorationExtension_isKrausCPTP`
* `twoSiteAmbientSectorRetraction_comp_normalizedRestoration`
* `twoSiteAmbientSectorRetraction_verticalTensor`
* `twoSiteNormalizedAmbientSectorRestoration_trace_smul_verticalTensor`

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Appendix C.4, lines 2048--2079.
-/

open scoped BigOperators ComplexOrder Matrix

noncomputable section

namespace MPOTensor

namespace BNTAlgebraTensorClause.TwoSiteMultiplicitySpectrum

variable {d D : ℕ} {M : MPOTensor d D} {H : BNTAlgebraTensorClause M}

/-! ### Relabelled two-site ambient sector maps -/

/-- The two-site raw sector retraction \(R_2\) first decodes the two physical
indices, compresses to the retained relabelled sectors, and traces out their
multiplicity coordinates.

Source: arXiv:1606.00608, Appendix C.4, lines 2078--2079. -/
def twoSiteAmbientSectorRetraction (S : TwoSiteMultiplicitySpectrum H) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      S.RelabeledTwoSiteSectorAlgebra :=
  (verticalSectorAmbientRetraction S.relabeledTwoSiteBondDim
      S.relabeledTwoSiteMultiplicity S.relabeledTwoSiteCoisometry).comp
    (Matrix.equivReindexMap (blockedIndexEquiv d).symm)

/-- The two-site raw retraction is the generic ambient retraction after the
canonical identification of a pair of physical indices with one blocked
index.

Source: arXiv:1606.00608, Appendix C.4, lines 2078--2079. -/
@[simp]
theorem twoSiteAmbientSectorRetraction_apply
    (S : TwoSiteMultiplicitySpectrum H)
    (X : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    S.twoSiteAmbientSectorRetraction X =
      verticalSectorAmbientRetraction S.relabeledTwoSiteBondDim
        S.relabeledTwoSiteMultiplicity S.relabeledTwoSiteCoisometry
          (Matrix.equivReindexMap (blockedIndexEquiv d).symm X) := by
  rfl

/-- The canonical full-matrix representative of the two-site raw sector
retraction.

Source: arXiv:1606.00608, Appendix C.4, lines 2078--2079. -/
def twoSiteAmbientSectorRetractionExtension
    (S : TwoSiteMultiplicitySpectrum H) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (Σ γ, Fin (S.relabeledTwoSiteBondDim γ))
        (Σ γ, Fin (S.relabeledTwoSiteBondDim γ)) ℂ :=
  (verticalSectorAmbientRetractionExtension S.relabeledTwoSiteBondDim
      S.relabeledTwoSiteMultiplicity S.relabeledTwoSiteCoisometry).comp
    (Matrix.equivReindexMap (blockedIndexEquiv d).symm)

/-- The canonical full-matrix representative of the two-site raw retraction
is completely positive.

Source: arXiv:1606.00608, Appendix C.4, lines 2078--2079. -/
theorem twoSiteAmbientSectorRetractionExtension_isKrausCP
    (S : TwoSiteMultiplicitySpectrum H) :
    IsKrausCP S.twoSiteAmbientSectorRetractionExtension := by
  apply isKrausCP_comp
  · exact (Matrix.equivReindexMap_isKrausCPTP
      (blockedIndexEquiv d).symm).isKrausCP
  · exact verticalSectorAmbientRetractionExtension_isKrausCP
      S.relabeledTwoSiteBondDim S.relabeledTwoSiteMultiplicity
        S.relabeledTwoSiteCoisometry

/-- The total sector trace after the two-site raw retraction equals the trace
of the corresponding coisometric compression in the blocked physical
coordinate.

Source: arXiv:1606.00608, Appendix C.4, lines 2078--2079. -/
theorem verticalSectorTrace_twoSiteAmbientSectorRetraction
    (S : TwoSiteMultiplicitySpectrum H)
    (X : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    verticalSectorTrace (S.twoSiteAmbientSectorRetraction X) =
      Matrix.trace (S.relabeledTwoSiteCoisometry *
        Matrix.equivReindexMap (blockedIndexEquiv d).symm X *
        S.relabeledTwoSiteCoisometryᴴ) := by
  rw [twoSiteAmbientSectorRetraction_apply,
    verticalSectorAmbientRetraction_apply,
    verticalSectorTrace_retainedVerticalSectorPartialTrace]

/-- The two-site raw retraction does not increase the total trace of a
positive ambient matrix.

**Local fix (zero complement):** The raw retraction may discard the
orthogonal complement of the retained two-site sectors; hence it is only
trace-nonincreasing on positive matrices.  This is documented in
`docs/paper-gaps/cpgsv17_vertical_isometry_zero_sector.tex`.

Source: arXiv:1606.00608, Appendix C.4, lines 2078--2079. -/
theorem verticalSectorTrace_twoSiteAmbientSectorRetraction_le
    (S : TwoSiteMultiplicitySpectrum H)
    (X : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hX : X.PosSemidef) :
    verticalSectorTrace (S.twoSiteAmbientSectorRetraction X) ≤
      Matrix.trace X := by
  calc
    verticalSectorTrace (S.twoSiteAmbientSectorRetraction X) ≤
        Matrix.trace (Matrix.equivReindexMap (blockedIndexEquiv d).symm X) :=
      verticalSectorTrace_verticalSectorAmbientRetraction_le
        S.relabeledTwoSiteBondDim S.relabeledTwoSiteMultiplicity
          S.relabeledTwoSiteCoisometry
          S.relabeledTwoSiteCoisometry_coisometry _
          ((Matrix.equivReindexMap_isKrausCPTP
            (blockedIndexEquiv d).symm).map_posSemidef hX)
    _ = Matrix.trace X :=
      (Matrix.equivReindexMap_isKrausCPTP
        (blockedIndexEquiv d).symm).trace_map X

/-- The normalized two-site restoration \(\widetilde R_2\) prepares each
matched two-site multiplicity matrix with unit trace, returns to the blocked
ambient coordinate, and decodes its physical index.

Source: arXiv:1606.00608, Appendix C.4, lines 2058--2071. -/
def twoSiteNormalizedAmbientSectorRestoration
    (S : TwoSiteMultiplicitySpectrum H) :
    S.RelabeledTwoSiteSectorAlgebra →ₗ[ℂ]
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (Matrix.equivReindexMap (blockedIndexEquiv d)).comp
    (normalizedVerticalSectorAmbientRestoration S.relabeledTwoSiteBondDim
      S.relabeledTwoSiteMultiplicity S.relabeledTwoSiteWeight
        S.relabeledTwoSiteCoisometry)

/-- The normalized two-site restoration is the generic restoration followed
by the canonical decoding of the blocked physical index.

Source: arXiv:1606.00608, Appendix C.4, lines 2058--2071. -/
@[simp]
theorem twoSiteNormalizedAmbientSectorRestoration_apply
    (S : TwoSiteMultiplicitySpectrum H)
    (X : S.RelabeledTwoSiteSectorAlgebra) :
    S.twoSiteNormalizedAmbientSectorRestoration X =
      Matrix.equivReindexMap (blockedIndexEquiv d)
        (normalizedVerticalSectorAmbientRestoration
          S.relabeledTwoSiteBondDim S.relabeledTwoSiteMultiplicity
            S.relabeledTwoSiteWeight S.relabeledTwoSiteCoisometry X) := by
  rfl

/-- In each matched two-site sector, the normalized multiplicity matrix is
divided by the common one-site multiplicity trace \(m_\gamma\).

Source: arXiv:1606.00608, Appendix C.4, lines 2058--2071. -/
theorem normalizedRelabeledTwoSiteEmbedding_apply_oneSiteTrace
    (S : TwoSiteMultiplicitySpectrum H)
    (X : S.RelabeledTwoSiteSectorAlgebra) (γ : Fin H.labelCount) :
    normalizedVerticalSectorEmbedding S.relabeledTwoSiteBondDim
        S.relabeledTwoSiteMultiplicity S.relabeledTwoSiteWeight X γ =
      Matrix.kroneckerMap (· * ·)
        (Matrix.diagonal (fun q ↦
          S.relabeledTwoSiteWeight γ q /
            verticalMultiplicityTrace H.weight γ)) (X γ) := by
  rw [normalizedVerticalSectorEmbedding_apply,
    S.relabeledTwoSiteMultiplicityTrace_eq_oneSite]
  ext ⟨q, i⟩ ⟨r, j⟩
  simp only [Matrix.smul_apply, Matrix.kroneckerMap_apply]
  by_cases hqr : q = r
  · subst r
    simp [div_eq_mul_inv]
    ring
  · simp [hqr]

/-- The normalized two-site restoration has the source formula with
\(\nu_{\sigma(\gamma)}/m_\gamma\) on the matched sector block.

Source: arXiv:1606.00608, Appendix C.4, lines 2058--2071. -/
theorem twoSiteNormalizedAmbientSectorRestoration_apply_explicit
    (S : TwoSiteMultiplicitySpectrum H)
    (X : S.RelabeledTwoSiteSectorAlgebra) :
    S.twoSiteNormalizedAmbientSectorRestoration X =
      Matrix.equivReindexMap (blockedIndexEquiv d)
        (S.relabeledTwoSiteCoisometryᴴ *
          verticalSectorBlockDiagonal S.relabeledTwoSiteBondDim
            S.relabeledTwoSiteMultiplicity (fun γ ↦
              Matrix.kroneckerMap (· * ·)
                (Matrix.diagonal (fun q ↦
                  S.relabeledTwoSiteWeight γ q /
                    verticalMultiplicityTrace H.weight γ)) (X γ)) *
          S.relabeledTwoSiteCoisometry) := by
  have hNormalized :
      normalizedRetainedVerticalSectorEmbedding S.relabeledTwoSiteBondDim
          S.relabeledTwoSiteMultiplicity S.relabeledTwoSiteWeight X =
        verticalSectorBlockDiagonal S.relabeledTwoSiteBondDim
          S.relabeledTwoSiteMultiplicity (fun γ ↦
            Matrix.kroneckerMap (· * ·)
              (Matrix.diagonal (fun q ↦
                S.relabeledTwoSiteWeight γ q /
                  verticalMultiplicityTrace H.weight γ)) (X γ)) := by
    simp only [normalizedRetainedVerticalSectorEmbedding,
      LinearMap.comp_apply]
    apply congrArg (verticalSectorBlockDiagonal
      S.relabeledTwoSiteBondDim S.relabeledTwoSiteMultiplicity)
    funext γ
    exact S.normalizedRelabeledTwoSiteEmbedding_apply_oneSiteTrace X γ
  rw [twoSiteNormalizedAmbientSectorRestoration_apply,
    normalizedVerticalSectorAmbientRestoration_apply, hNormalized]

/-- The canonical full-matrix representative of the normalized two-site
restoration.

Source: arXiv:1606.00608, Appendix C.4, lines 2058--2071. -/
def twoSiteNormalizedAmbientSectorRestorationExtension
    (S : TwoSiteMultiplicitySpectrum H) :
    Matrix (Σ γ, Fin (S.relabeledTwoSiteBondDim γ))
        (Σ γ, Fin (S.relabeledTwoSiteBondDim γ)) ℂ →ₗ[ℂ]
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (Matrix.equivReindexMap (blockedIndexEquiv d)).comp
    (normalizedVerticalSectorAmbientRestorationExtension
      S.relabeledTwoSiteBondDim S.relabeledTwoSiteMultiplicity
        S.relabeledTwoSiteWeight S.relabeledTwoSiteCoisometry)

/-- The canonical full-matrix representative of normalized two-site
restoration is completely positive.

Source: arXiv:1606.00608, Appendix C.4, lines 2058--2071. -/
theorem twoSiteNormalizedAmbientSectorRestorationExtension_isKrausCP
    (S : TwoSiteMultiplicitySpectrum H) :
    IsKrausCP S.twoSiteNormalizedAmbientSectorRestorationExtension := by
  apply isKrausCP_comp
  · exact normalizedVerticalSectorAmbientRestorationExtension_isKrausCP
      S.relabeledTwoSiteBondDim S.relabeledTwoSiteMultiplicity
        S.relabeledTwoSiteWeight
        (fun γ ↦ S.decomposition.multiplicity_pos (S.relabel γ))
        (fun γ q ↦ S.decomposition.weight_pos (S.relabel γ) q)
        S.relabeledTwoSiteCoisometry
  · exact (Matrix.equivReindexMap_isKrausCPTP
      (blockedIndexEquiv d)).isKrausCP

/-- Normalized two-site restoration preserves the total sector trace.

Source: arXiv:1606.00608, Appendix C.4, lines 2058--2071. -/
theorem trace_twoSiteNormalizedAmbientSectorRestoration
    (S : TwoSiteMultiplicitySpectrum H)
    (X : S.RelabeledTwoSiteSectorAlgebra) :
    Matrix.trace (S.twoSiteNormalizedAmbientSectorRestoration X) =
      verticalSectorTrace X := by
  rw [twoSiteNormalizedAmbientSectorRestoration_apply,
    (Matrix.equivReindexMap_isKrausCPTP
      (blockedIndexEquiv d)).trace_map]
  exact trace_normalizedVerticalSectorAmbientRestoration
    S.relabeledTwoSiteBondDim S.relabeledTwoSiteMultiplicity
      S.relabeledTwoSiteWeight
      (fun γ ↦ S.decomposition.multiplicity_pos (S.relabel γ))
      (fun γ q ↦ S.decomposition.weight_pos (S.relabel γ) q)
      S.relabeledTwoSiteCoisometry
      S.relabeledTwoSiteCoisometry_coisometry X

/-- The canonical full-matrix representative of normalized two-site
restoration is completely positive and trace-preserving.

Source: arXiv:1606.00608, Appendix C.4, lines 2058--2071. -/
theorem twoSiteNormalizedAmbientSectorRestorationExtension_isKrausCPTP
    (S : TwoSiteMultiplicitySpectrum H) :
    IsKrausCPTP S.twoSiteNormalizedAmbientSectorRestorationExtension := by
  exact isKrausCPTP_comp
    (normalizedVerticalSectorAmbientRestorationExtension_isKrausCPTP
      S.relabeledTwoSiteBondDim S.relabeledTwoSiteMultiplicity
        S.relabeledTwoSiteWeight
        (fun γ ↦ S.decomposition.multiplicity_pos (S.relabel γ))
        (fun γ q ↦ S.decomposition.weight_pos (S.relabel γ) q)
        S.relabeledTwoSiteCoisometry
        S.relabeledTwoSiteCoisometry_coisometry)
    (Matrix.equivReindexMap_isKrausCPTP (blockedIndexEquiv d))

/-- Two-site raw retraction after normalized restoration is the identity on
the relabelled two-site sector algebra.

Source: arXiv:1606.00608, Appendix C.4, lines 2058--2071 and 2078--2079. -/
theorem twoSiteAmbientSectorRetraction_comp_normalizedRestoration
    (S : TwoSiteMultiplicitySpectrum H) :
    S.twoSiteAmbientSectorRetraction.comp
        S.twoSiteNormalizedAmbientSectorRestoration = LinearMap.id := by
  apply LinearMap.ext
  intro X
  simpa [twoSiteAmbientSectorRetraction,
    twoSiteNormalizedAmbientSectorRestoration,
    Matrix.equivReindexMap, Matrix.coe_reindexLinearEquiv] using
      LinearMap.congr_fun
        (verticalSectorAmbientRetraction_comp_normalizedRestoration
          S.relabeledTwoSiteBondDim S.relabeledTwoSiteMultiplicity
            S.relabeledTwoSiteWeight
            (fun γ ↦ S.decomposition.multiplicity_pos (S.relabel γ))
            (fun γ q ↦ S.decomposition.weight_pos (S.relabel γ) q)
            S.relabeledTwoSiteCoisometry
            S.relabeledTwoSiteCoisometry_coisometry) X

/-- Each assembled two-site vertical tensor letter is the block diagonal of
its native weighted sectors.

Source: arXiv:1606.00608, Appendix C.4, lines 2048--2064. -/
theorem twoSiteVerticalAssembledTensor_eq_verticalSectorBlockDiagonal
    (S : TwoSiteMultiplicitySpectrum H) (v : Fin (D * D)) :
    verticalAssembledTensor S.decomposition.bondDim
        S.decomposition.multiplicity S.decomposition.weight
        S.decomposition.tensor v =
      verticalSectorBlockDiagonal S.decomposition.bondDim
        S.decomposition.multiplicity (fun β ↦
          Matrix.kroneckerMap (· * ·)
            (Matrix.diagonal (S.decomposition.weight β))
            (S.decomposition.tensor β v)) := by
  simpa only [MPSTensor.contractBondMatrix_single_mod_div] using
    contractBondMatrix_verticalAssembledTensor_eq_sectorBlockDiagonal
      S.decomposition.bondDim S.decomposition.multiplicity
        S.decomposition.weight S.decomposition.tensor
        (Matrix.single v.modNat v.divNat 1)

/-- Compressing a two-site vertical tensor letter by the relabelled
coisometry gives the matched weighted sector blocks.

Source: arXiv:1606.00608, Appendix C.4, lines 2048--2064 and 2078--2079. -/
theorem relabeledTwoSiteCoisometry_forward_verticalTensor
    (S : TwoSiteMultiplicitySpectrum H) (v : Fin (D * D)) :
    S.relabeledTwoSiteCoisometry * verticalTensor (blockTwo M) v *
        S.relabeledTwoSiteCoisometryᴴ =
      verticalSectorBlockDiagonal S.relabeledTwoSiteBondDim
        S.relabeledTwoSiteMultiplicity (fun γ ↦
          Matrix.kroneckerMap (· * ·)
            (Matrix.diagonal (S.relabeledTwoSiteWeight γ))
            (S.decomposition.tensor (S.relabel γ) v)) := by
  apply S.relabeledTwoSiteCoisometry_forward
    (X := verticalTensor (blockTwo M) v)
    (Y := fun β ↦ Matrix.kroneckerMap (· * ·)
      (Matrix.diagonal (S.decomposition.weight β))
      (S.decomposition.tensor β v))
  rw [S.decomposition.forward v,
    S.twoSiteVerticalAssembledTensor_eq_verticalSectorBlockDiagonal v]

/-- Expanding the matched weighted sector blocks reconstructs the two-site
vertical tensor letter.

Source: arXiv:1606.00608, Appendix C.4, lines 2048--2064 and 2070--2071. -/
theorem relabeledTwoSiteCoisometry_reconstruction_verticalTensor
    (S : TwoSiteMultiplicitySpectrum H) (v : Fin (D * D)) :
    verticalTensor (blockTwo M) v = S.relabeledTwoSiteCoisometryᴴ *
      verticalSectorBlockDiagonal S.relabeledTwoSiteBondDim
        S.relabeledTwoSiteMultiplicity (fun γ ↦
          Matrix.kroneckerMap (· * ·)
            (Matrix.diagonal (S.relabeledTwoSiteWeight γ))
            (S.decomposition.tensor (S.relabel γ) v)) *
      S.relabeledTwoSiteCoisometry := by
  apply S.relabeledTwoSiteCoisometry_reconstruction
    (X := verticalTensor (blockTwo M) v)
    (Y := fun β ↦ Matrix.kroneckerMap (· * ·)
      (Matrix.diagonal (S.decomposition.weight β))
      (S.decomposition.tensor β v))
  rw [S.decomposition.reconstruction v,
    S.twoSiteVerticalAssembledTensor_eq_verticalSectorBlockDiagonal v]

/-- On a two-site vertical tensor letter, the raw retraction returns each
matched BNT sector multiplied by the one-site multiplicity trace
\(m_\gamma\).

Source: arXiv:1606.00608, Appendix C.4, lines 2048--2064 and 2078--2079. -/
theorem twoSiteAmbientSectorRetraction_verticalTensor
    (S : TwoSiteMultiplicitySpectrum H) (v : Fin (D * D)) :
    S.twoSiteAmbientSectorRetraction
        (Matrix.equivReindexMap (blockedIndexEquiv d)
          (verticalTensor (blockTwo M) v)) =
      fun γ ↦ verticalMultiplicityTrace H.weight γ •
        S.decomposition.tensor (S.relabel γ) v := by
  rw [twoSiteAmbientSectorRetraction_apply]
  have hReindex :
      Matrix.equivReindexMap (blockedIndexEquiv d).symm
          (Matrix.equivReindexMap (blockedIndexEquiv d)
            (verticalTensor (blockTwo M) v)) =
        verticalTensor (blockTwo M) v := by
    simp [Matrix.equivReindexMap, Matrix.coe_reindexLinearEquiv]
  rw [hReindex, verticalSectorAmbientRetraction_apply,
    S.relabeledTwoSiteCoisometry_forward_verticalTensor v,
    retainedVerticalSectorPartialTrace_weightedBlockDiagonal]
  funext γ
  rw [S.relabeledTwoSiteMultiplicityTrace_eq_oneSite]

/-- Normalized two-site restoration sends the one-site-trace-scaled matched
BNT sectors back to the decoded two-site vertical tensor letter.

Source: arXiv:1606.00608, Appendix C.4, lines 2048--2064 and 2070--2071. -/
theorem twoSiteNormalizedAmbientSectorRestoration_trace_smul_verticalTensor
    (S : TwoSiteMultiplicitySpectrum H) (v : Fin (D * D)) :
    S.twoSiteNormalizedAmbientSectorRestoration
        (fun γ ↦ verticalMultiplicityTrace H.weight γ •
          S.decomposition.tensor (S.relabel γ) v) =
      Matrix.equivReindexMap (blockedIndexEquiv d)
        (verticalTensor (blockTwo M) v) := by
  rw [twoSiteNormalizedAmbientSectorRestoration_apply]
  apply congrArg (Matrix.equivReindexMap (blockedIndexEquiv d))
  have hScaled :
      (fun γ ↦ verticalMultiplicityTrace H.weight γ •
          S.decomposition.tensor (S.relabel γ) v) =
        (fun γ ↦ verticalMultiplicityTrace S.relabeledTwoSiteWeight γ •
          S.decomposition.tensor (S.relabel γ) v) := by
    funext γ
    rw [S.relabeledTwoSiteMultiplicityTrace_eq_oneSite]
  rw [hScaled,
    normalizedVerticalSectorAmbientRestoration_trace_smul
      S.relabeledTwoSiteBondDim S.relabeledTwoSiteMultiplicity
        S.relabeledTwoSiteWeight
        (fun γ ↦ S.decomposition.multiplicity_pos (S.relabel γ))
        (fun γ q ↦ S.decomposition.weight_pos (S.relabel γ) q)
        S.relabeledTwoSiteCoisometry]
  exact (S.relabeledTwoSiteCoisometry_reconstruction_verticalTensor v).symm

end BNTAlgebraTensorClause.TwoSiteMultiplicitySpectrum

end MPOTensor
