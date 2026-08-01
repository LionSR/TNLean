/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTAlgebraTensorClause
import TNLean.MPS.MPDO.VerticalSectorAmbientMaps
import TNLean.MPS.MPDO.VerticalSectorGeneration

/-!
# One-site ambient sector maps for the BNT algebra clause

The chosen one-site vertical canonical decomposition determines a raw
retraction from the ambient physical matrix algebra to its simple-sector
algebra and a normalized restoration in the opposite direction.  The raw map
compresses to the retained sectors and takes the multiplicity partial trace.
The normalized map prepares the positive multiplicity matrix with unit trace
and expands through the adjoint coisometry.

The canonical full-matrix representatives are completely positive.  The
normalized restoration preserves trace and is a right inverse of the raw
retraction.  On the weighted vertical tensor letters, the two maps respectively
extract and restore the factor given by the multiplicity trace.

## Main definitions

* `oneSiteAmbientSectorRetraction`
* `oneSiteAmbientSectorRetractionExtension`
* `oneSiteNormalizedAmbientSectorRestoration`
* `oneSiteNormalizedAmbientSectorRestorationExtension`

## Main results

* `verticalSectorTrace_oneSiteAmbientSectorRetraction_le`
* `oneSiteNormalizedAmbientSectorRestorationExtension_isKrausCPTP`
* `oneSiteAmbientSectorRetraction_comp_normalizedRestoration`
* `oneSiteAmbientSectorRetraction_verticalTensor`
* `oneSiteNormalizedAmbientSectorRestoration_trace_smul_verticalTensor`

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Appendix C.4, lines 2048--2051, 2065--2068, and 2081--2083.
-/

open scoped BigOperators ComplexOrder Matrix

noncomputable section

namespace MPOTensor

namespace BNTAlgebraTensorClause

variable {d D : ℕ} {M : MPOTensor d D}

/-- The assembled one-site vertical tensor letter is the block diagonal whose
sector blocks are \(\mu_\alpha \otimes M_\alpha\).

Source: arXiv:1606.00608, Appendix C.4, lines 2048--2051. -/
theorem verticalAssembledTensor_eq_verticalSectorBlockDiagonal
    (H : BNTAlgebraTensorClause M) (v : Fin (D * D)) :
    verticalAssembledTensor H.bondDim H.multiplicity H.weight H.tensor v =
      verticalSectorBlockDiagonal H.bondDim H.multiplicity (fun α ↦
        Matrix.kroneckerMap (· * ·) (Matrix.diagonal (H.weight α))
          (H.tensor α v)) := by
  simpa only [MPSTensor.contractBondMatrix_single_mod_div] using
    contractBondMatrix_verticalAssembledTensor_eq_sectorBlockDiagonal
      H.bondDim H.multiplicity H.weight H.tensor
        (Matrix.single v.modNat v.divNat 1)

/-- The one-site raw sector retraction \(R_1\) compresses to the retained
vertical sectors and traces out their multiplicity coordinates.

Source: arXiv:1606.00608, Appendix C.4, lines 2067--2068. -/
def oneSiteAmbientSectorRetraction (H : BNTAlgebraTensorClause M) :
    Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] VerticalSectorAlgebra H.bondDim :=
  verticalSectorAmbientRetraction H.bondDim H.multiplicity H.verticalCoisometry

/-- The one-site raw retraction is the generic ambient retraction for the
chosen one-site vertical decomposition.

Source: arXiv:1606.00608, Appendix C.4, lines 2067--2068. -/
@[simp]
theorem oneSiteAmbientSectorRetraction_apply
    (H : BNTAlgebraTensorClause M) (X : Matrix (Fin d) (Fin d) ℂ) :
    H.oneSiteAmbientSectorRetraction X =
      verticalSectorAmbientRetraction H.bondDim H.multiplicity
        H.verticalCoisometry X := by
  rfl

/-- The canonical full-matrix representative of the one-site raw retraction.

Source: arXiv:1606.00608, Appendix C.4, lines 2067--2068. -/
def oneSiteAmbientSectorRetractionExtension (H : BNTAlgebraTensorClause M) :
    Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Σ α, Fin (H.bondDim α)) (Σ α, Fin (H.bondDim α)) ℂ :=
  verticalSectorAmbientRetractionExtension H.bondDim H.multiplicity
    H.verticalCoisometry

/-- The canonical full-matrix representative of the one-site raw retraction
is completely positive.

Source: arXiv:1606.00608, Appendix C.4, lines 2067--2068. -/
theorem oneSiteAmbientSectorRetractionExtension_isKrausCP
    (H : BNTAlgebraTensorClause M) :
    IsKrausCP H.oneSiteAmbientSectorRetractionExtension := by
  exact verticalSectorAmbientRetractionExtension_isKrausCP
    H.bondDim H.multiplicity H.verticalCoisometry

/-- The normalized one-site restoration \(\widetilde R_1\) prepares the normalized
multiplicity matrix in each sector and returns to the ambient space.

Source: arXiv:1606.00608, Appendix C.4, lines 2081--2083. -/
def oneSiteNormalizedAmbientSectorRestoration
    (H : BNTAlgebraTensorClause M) :
    VerticalSectorAlgebra H.bondDim →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ :=
  normalizedVerticalSectorAmbientRestoration H.bondDim H.multiplicity H.weight
    H.verticalCoisometry

/-- The normalized one-site restoration is the generic ambient restoration
for the chosen one-site vertical decomposition.

Source: arXiv:1606.00608, Appendix C.4, lines 2081--2083. -/
@[simp]
theorem oneSiteNormalizedAmbientSectorRestoration_apply
    (H : BNTAlgebraTensorClause M) (X : VerticalSectorAlgebra H.bondDim) :
    H.oneSiteNormalizedAmbientSectorRestoration X =
      normalizedVerticalSectorAmbientRestoration H.bondDim H.multiplicity
        H.weight H.verticalCoisometry X := by
  rfl

/-- The canonical full-matrix representative of normalized one-site
restoration.

Source: arXiv:1606.00608, Appendix C.4, lines 2081--2083. -/
def oneSiteNormalizedAmbientSectorRestorationExtension
    (H : BNTAlgebraTensorClause M) :
    Matrix (Σ α, Fin (H.bondDim α)) (Σ α, Fin (H.bondDim α)) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ :=
  normalizedVerticalSectorAmbientRestorationExtension H.bondDim H.multiplicity
    H.weight H.verticalCoisometry

/-- The canonical full-matrix representative of normalized one-site
restoration is completely positive.

Source: arXiv:1606.00608, Appendix C.4, lines 2081--2083. -/
theorem oneSiteNormalizedAmbientSectorRestorationExtension_isKrausCP
    (H : BNTAlgebraTensorClause M) :
    IsKrausCP H.oneSiteNormalizedAmbientSectorRestorationExtension := by
  exact normalizedVerticalSectorAmbientRestorationExtension_isKrausCP
    H.bondDim H.multiplicity H.weight H.multiplicity_pos H.weight_pos
      H.verticalCoisometry

/-- The total sector trace after the one-site raw retraction equals the trace
of the coisometric compression to the retained vertical sectors.

Source: arXiv:1606.00608, Appendix C.4, lines 2067--2068. -/
theorem verticalSectorTrace_oneSiteAmbientSectorRetraction
    (H : BNTAlgebraTensorClause M) (X : Matrix (Fin d) (Fin d) ℂ) :
    verticalSectorTrace (H.oneSiteAmbientSectorRetraction X) =
      Matrix.trace
        (H.verticalCoisometry * X * H.verticalCoisometryᴴ) := by
  rw [oneSiteAmbientSectorRetraction_apply,
    verticalSectorAmbientRetraction_apply,
    verticalSectorTrace_retainedVerticalSectorPartialTrace]

/-- The one-site raw retraction does not increase the total trace of a
positive ambient matrix.

**Local fix (zero-sector complement):** The raw retraction may discard the
orthogonal complement of the retained vertical sectors; hence it is only
trace-nonincreasing on positive matrices.  This is documented in
`docs/paper-gaps/cpgsv17_vertical_isometry_zero_sector.tex`.

Source: arXiv:1606.00608, Appendix C.4, lines 2067--2068. -/
theorem verticalSectorTrace_oneSiteAmbientSectorRetraction_le
    (H : BNTAlgebraTensorClause M) (X : Matrix (Fin d) (Fin d) ℂ)
    (hX : X.PosSemidef) :
    verticalSectorTrace (H.oneSiteAmbientSectorRetraction X) ≤
      Matrix.trace X := by
  exact verticalSectorTrace_verticalSectorAmbientRetraction_le
    H.bondDim H.multiplicity H.verticalCoisometry H.coisometry X hX

/-- Normalized one-site restoration preserves the total sector trace.

Source: arXiv:1606.00608, Appendix C.4, lines 2081--2083. -/
theorem trace_oneSiteNormalizedAmbientSectorRestoration
    (H : BNTAlgebraTensorClause M) (X : VerticalSectorAlgebra H.bondDim) :
    Matrix.trace (H.oneSiteNormalizedAmbientSectorRestoration X) =
      verticalSectorTrace X := by
  exact trace_normalizedVerticalSectorAmbientRestoration
    H.bondDim H.multiplicity H.weight H.multiplicity_pos H.weight_pos
      H.verticalCoisometry H.coisometry X

/-- The canonical full-matrix representative of normalized one-site
restoration is completely positive and trace-preserving.

Source: arXiv:1606.00608, Appendix C.4, lines 2081--2083. -/
theorem oneSiteNormalizedAmbientSectorRestorationExtension_isKrausCPTP
    (H : BNTAlgebraTensorClause M) :
    IsKrausCPTP H.oneSiteNormalizedAmbientSectorRestorationExtension := by
  exact normalizedVerticalSectorAmbientRestorationExtension_isKrausCPTP
    H.bondDim H.multiplicity H.weight H.multiplicity_pos H.weight_pos
      H.verticalCoisometry H.coisometry

/-- One-site raw retraction after normalized restoration is the identity on
the one-site sector algebra.

Source: arXiv:1606.00608, Appendix C.4, lines 2067--2068 and 2081--2083. -/
theorem oneSiteAmbientSectorRetraction_comp_normalizedRestoration
    (H : BNTAlgebraTensorClause M) :
    H.oneSiteAmbientSectorRetraction.comp
        H.oneSiteNormalizedAmbientSectorRestoration = LinearMap.id := by
  exact verticalSectorAmbientRetraction_comp_normalizedRestoration
    H.bondDim H.multiplicity H.weight H.multiplicity_pos H.weight_pos
      H.verticalCoisometry H.coisometry

/-- On a vertical tensor letter, the one-site raw retraction returns each BNT
sector multiplied by its multiplicity trace \(m_\alpha\).

Source: arXiv:1606.00608, Appendix C.4, lines 2048--2051 and 2067--2068. -/
theorem oneSiteAmbientSectorRetraction_verticalTensor
    (H : BNTAlgebraTensorClause M) (v : Fin (D * D)) :
    H.oneSiteAmbientSectorRetraction (verticalTensor M v) =
      fun α ↦ verticalMultiplicityTrace H.weight α • H.tensor α v := by
  rw [oneSiteAmbientSectorRetraction_apply,
    verticalSectorAmbientRetraction_apply, H.forward v,
    H.verticalAssembledTensor_eq_verticalSectorBlockDiagonal v]
  exact retainedVerticalSectorPartialTrace_weightedBlockDiagonal
    H.bondDim H.multiplicity H.weight (fun α ↦ H.tensor α v)

/-- Normalized one-site restoration sends the multiplicity-trace-scaled BNT
sectors back to the corresponding vertical tensor letter.

Source: arXiv:1606.00608, Appendix C.4, lines 2048--2051 and 2081--2083. -/
theorem oneSiteNormalizedAmbientSectorRestoration_trace_smul_verticalTensor
    (H : BNTAlgebraTensorClause M) (v : Fin (D * D)) :
    H.oneSiteNormalizedAmbientSectorRestoration
        (fun α ↦ verticalMultiplicityTrace H.weight α • H.tensor α v) =
      verticalTensor M v := by
  rw [oneSiteNormalizedAmbientSectorRestoration_apply,
    normalizedVerticalSectorAmbientRestoration_trace_smul
      H.bondDim H.multiplicity H.weight H.multiplicity_pos H.weight_pos
        H.verticalCoisometry]
  rw [← H.verticalAssembledTensor_eq_verticalSectorBlockDiagonal v]
  exact (H.reconstruction v).symm

end BNTAlgebraTensorClause

end MPOTensor
