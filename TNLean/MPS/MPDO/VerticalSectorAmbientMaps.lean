/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.VerticalSectorTraceLoss

/-!
# Ambient vertical-sector retractions and restorations

Let \(U\) be the coisometry from an ambient physical space onto the retained
vertical sectors.  The raw retraction compresses by \(U\), extracts the sector
diagonal blocks, and takes the partial trace over each multiplicity space.  The
normalized restoration prepares the normalized positive multiplicity matrix in
each sector and expands the resulting block-diagonal matrix by \(U^\dagger\).

The canonical full-matrix representatives are completely positive.  The raw
retraction is trace-nonincreasing on positive matrices because the orthogonal
complement of the retained sectors may be nonzero.  The normalized restoration
preserves the total sector trace and is a right inverse of the raw retraction.

## Main definitions

* `verticalSectorAmbientRetraction`
* `normalizedVerticalSectorAmbientRestoration`
* `verticalSectorAmbientRetractionExtension`
* `normalizedVerticalSectorAmbientRestorationExtension`

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Appendix C.4, lines 2065--2083.
-/

open scoped BigOperators ComplexOrder Matrix

noncomputable section

namespace MPOTensor

variable {g d : ℕ}

/-- Compress an ambient matrix to the retained vertical sectors and trace out
each multiplicity coordinate.

Source: arXiv:1606.00608, Appendix C.4, lines 2067--2068 and 2078--2079. -/
def verticalSectorAmbientRetraction
    (dim mult : Fin g → ℕ)
    (U : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] VerticalSectorAlgebra dim :=
  (retainedVerticalSectorPartialTrace dim mult).comp (singleKrausMap U)

/-- The ambient retraction is retained-sector partial trace after coisometric
compression.

Source: arXiv:1606.00608, Appendix C.4, lines 2067--2068 and 2078--2079. -/
@[simp]
theorem verticalSectorAmbientRetraction_apply
    (dim mult : Fin g → ℕ)
    (U : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ) (X : Matrix (Fin d) (Fin d) ℂ) :
    verticalSectorAmbientRetraction dim mult U X =
      retainedVerticalSectorPartialTrace dim mult (U * X * Uᴴ) := by
  rfl

/-- In a fixed sector, the ambient retraction is the multiplicity partial
trace of the corresponding diagonal block of the compressed matrix.

Source: arXiv:1606.00608, Appendix C.4, lines 2067--2068 and 2078--2079. -/
theorem verticalSectorAmbientRetraction_apply_sector
    (dim mult : Fin g → ℕ)
    (U : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ) (X : Matrix (Fin d) (Fin d) ℂ) (α : Fin g) :
    verticalSectorAmbientRetraction dim mult U X α =
      Matrix.traceLeft ((U * X * Uᴴ).submatrix
        (fun i ↦ verticalSectorFinEquiv dim mult ⟨α, i⟩)
        (fun i ↦ verticalSectorFinEquiv dim mult ⟨α, i⟩)) := by
  rfl

/-- The canonical full-matrix representative of the ambient retraction, with
the output sector family placed on the block diagonal.

Source: arXiv:1606.00608, Appendix C.4, lines 2067--2068 and 2078--2079. -/
def verticalSectorAmbientRetractionExtension
    (dim mult : Fin g → ℕ)
    (U : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Σ α, Fin (dim α)) (Σ α, Fin (dim α)) ℂ :=
  Matrix.directSumDiagonalEmbedding.comp
    (verticalSectorAmbientRetraction dim mult U)

/-- The full-matrix representative of the ambient retraction factors as
coisometric compression, retained-coordinate reindexing, and the canonical
extension of multiplicity partial trace.

Source: arXiv:1606.00608, Appendix C.4, lines 2067--2068 and 2078--2079. -/
theorem verticalSectorAmbientRetractionExtension_factorization
    (dim mult : Fin g → ℕ)
    (U : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ) :
    verticalSectorAmbientRetractionExtension dim mult U =
      (Matrix.directSumMapExtension (verticalSectorPartialTrace dim mult)).comp
        ((Matrix.equivReindexMap (verticalSectorFinEquiv dim mult).symm).comp
          (singleKrausMap U)) := by
  apply LinearMap.ext
  intro X
  rfl

/-- The canonical full-matrix representative of the ambient retraction is
completely positive.

Source: arXiv:1606.00608, Appendix C.4, lines 2067--2068 and 2078--2079. -/
theorem verticalSectorAmbientRetractionExtension_isKrausCP
    (dim mult : Fin g → ℕ)
    (U : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ) :
    IsKrausCP (verticalSectorAmbientRetractionExtension dim mult U) := by
  rw [verticalSectorAmbientRetractionExtension_factorization]
  apply isKrausCP_comp
  · apply isKrausCP_comp
    · exact singleKrausMap_isKrausCP U
    · exact (Matrix.equivReindexMap_isKrausCPTP
        (verticalSectorFinEquiv dim mult).symm).isKrausCP
  · exact verticalSectorPartialTrace_isKrausDirectSumMap dim mult

/-- Restore a sector family to the ambient space by preparing the normalized
positive multiplicity matrices and expanding along the adjoint coisometry.

Source: arXiv:1606.00608, Appendix C.4, lines 2070--2071 and 2081--2083. -/
def normalizedVerticalSectorAmbientRestoration
    (dim mult : Fin g → ℕ)
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (U : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ) :
    VerticalSectorAlgebra dim →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ :=
  (singleKrausMap Uᴴ).comp
    (normalizedRetainedVerticalSectorEmbedding dim mult weight)

/-- The normalized restoration is the expansion of the retained normalized
sector embedding along the adjoint coisometry.

Source: arXiv:1606.00608, Appendix C.4, lines 2070--2071 and 2081--2083. -/
@[simp]
theorem normalizedVerticalSectorAmbientRestoration_apply
    (dim mult : Fin g → ℕ)
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (U : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ) (X : VerticalSectorAlgebra dim) :
    normalizedVerticalSectorAmbientRestoration dim mult weight U X =
      Uᴴ * normalizedRetainedVerticalSectorEmbedding dim mult weight X * U := by
  simp [normalizedVerticalSectorAmbientRestoration]

/-- The canonical full-matrix representative of the normalized restoration,
with the input restricted to its diagonal sector blocks.

Source: arXiv:1606.00608, Appendix C.4, lines 2070--2071 and 2081--2083. -/
def normalizedVerticalSectorAmbientRestorationExtension
    (dim mult : Fin g → ℕ)
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (U : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ) :
    Matrix (Σ α, Fin (dim α)) (Σ α, Fin (dim α)) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ :=
  (normalizedVerticalSectorAmbientRestoration dim mult weight U).comp
    Matrix.directSumDiagonalCompression

/-- The full-matrix representative of normalized restoration factors as the
canonical normalized preparation, retained-coordinate reindexing, and expansion
along the adjoint coisometry.

Source: arXiv:1606.00608, Appendix C.4, lines 2070--2071 and 2081--2083. -/
theorem normalizedVerticalSectorAmbientRestorationExtension_factorization
    (dim mult : Fin g → ℕ)
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (U : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ) :
    normalizedVerticalSectorAmbientRestorationExtension dim mult weight U =
      (singleKrausMap Uᴴ).comp
        ((Matrix.equivReindexMap (verticalSectorFinEquiv dim mult)).comp
          (Matrix.directSumMapExtension
            (normalizedVerticalSectorEmbedding dim mult weight))) := by
  apply LinearMap.ext
  intro X
  rfl

/-- The canonical full-matrix representative of normalized restoration is
completely positive.

Source: arXiv:1606.00608, Appendix C.4, lines 2070--2071 and 2081--2083. -/
theorem normalizedVerticalSectorAmbientRestorationExtension_isKrausCP
    (dim mult : Fin g → ℕ)
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (hMult : ∀ α, 0 < mult α)
    (hWeight : ∀ α q, (0 : ℂ) < weight α q)
    (U : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ) :
    IsKrausCP
      (normalizedVerticalSectorAmbientRestorationExtension dim mult weight U) := by
  rw [normalizedVerticalSectorAmbientRestorationExtension_factorization]
  apply isKrausCP_comp
  · apply isKrausCP_comp
    · exact normalizedVerticalSectorEmbedding_isKrausDirectSumMap
        dim mult weight hMult hWeight
    · exact (Matrix.equivReindexMap_isKrausCPTP
        (verticalSectorFinEquiv dim mult)).isKrausCP
  · exact singleKrausMap_isKrausCP Uᴴ

/-- The raw ambient retraction does not increase the total trace of a positive
matrix.

**Local fix (zero-sector complement):** The source formula may discard the
orthogonal complement of the retained sectors, so the conclusion is an
inequality rather than ambient trace preservation.  This is documented in
`docs/paper-gaps/cpgsv17_vertical_isometry_zero_sector.tex`.

Source: arXiv:1606.00608, Appendix C.4, lines 2067--2068 and 2078--2079. -/
theorem verticalSectorTrace_verticalSectorAmbientRetraction_le
    (dim mult : Fin g → ℕ)
    (U : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ)
    (hU : U * Uᴴ = 1) (X : Matrix (Fin d) (Fin d) ℂ) (hX : X.PosSemidef) :
    verticalSectorTrace (verticalSectorAmbientRetraction dim mult U X) ≤
      Matrix.trace X := by
  rw [verticalSectorAmbientRetraction_apply,
    verticalSectorTrace_retainedVerticalSectorPartialTrace]
  exact hX.trace_mul_mul_conjTranspose_le_of_mul_conjTranspose_eq_one U hU

/-- Normalized restoration preserves the total trace of a sector family.

Source: arXiv:1606.00608, Appendix C.4, lines 2070--2071 and 2081--2083. -/
theorem trace_normalizedVerticalSectorAmbientRestoration
    (dim mult : Fin g → ℕ)
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (hMult : ∀ α, 0 < mult α)
    (hWeight : ∀ α q, (0 : ℂ) < weight α q)
    (U : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ)
    (hU : U * Uᴴ = 1) (X : VerticalSectorAlgebra dim) :
    Matrix.trace
        (normalizedVerticalSectorAmbientRestoration dim mult weight U X) =
      verticalSectorTrace X := by
  rw [normalizedVerticalSectorAmbientRestoration_apply,
    Matrix.trace_conjTranspose_mul_mul_of_mul_conjTranspose_eq_one U hU,
    trace_normalizedRetainedVerticalSectorEmbedding dim mult weight
      hMult hWeight X]

/-- The canonical full-matrix representative of normalized restoration is
trace-preserving and completely positive.

Source: arXiv:1606.00608, Appendix C.4, lines 2070--2071 and 2081--2083. -/
theorem normalizedVerticalSectorAmbientRestorationExtension_isKrausCPTP
    (dim mult : Fin g → ℕ)
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (hMult : ∀ α, 0 < mult α)
    (hWeight : ∀ α q, (0 : ℂ) < weight α q)
    (U : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ)
    (hU : U * Uᴴ = 1) :
    IsKrausCPTP
      (normalizedVerticalSectorAmbientRestorationExtension dim mult weight U) := by
  apply isKrausCPTP_of_isKrausCP_trace_preserving
    (normalizedVerticalSectorAmbientRestorationExtension_isKrausCP
      dim mult weight hMult hWeight U)
  intro X
  simp only [normalizedVerticalSectorAmbientRestorationExtension,
    LinearMap.comp_apply]
  rw [trace_normalizedVerticalSectorAmbientRestoration
    dim mult weight hMult hWeight U hU]
  exact Matrix.sum_trace_directSumDiagonalCompression X

/-- Ambient retraction after normalized restoration is the identity on the
vertical-sector algebra.

Source: arXiv:1606.00608, Appendix C.4, lines 2067--2068, 2070--2071,
2078--2079, and 2081--2083. -/
theorem verticalSectorAmbientRetraction_comp_normalizedRestoration
    (dim mult : Fin g → ℕ)
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (hMult : ∀ α, 0 < mult α)
    (hWeight : ∀ α q, (0 : ℂ) < weight α q)
    (U : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ)
    (hU : U * Uᴴ = 1) :
    (verticalSectorAmbientRetraction dim mult U).comp
        (normalizedVerticalSectorAmbientRestoration dim mult weight U) =
      LinearMap.id := by
  apply LinearMap.ext
  intro X
  simp only [LinearMap.comp_apply, verticalSectorAmbientRetraction_apply,
    normalizedVerticalSectorAmbientRestoration_apply, LinearMap.id_apply]
  simp only [← Matrix.mul_assoc, hU, Matrix.one_mul]
  rw [Matrix.mul_assoc, hU, Matrix.mul_one]
  simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
    LinearMap.congr_fun
      (retainedVerticalSectorPartialTrace_comp_normalizedEmbedding
        dim mult weight hMult hWeight) X

/-- Restoring a family scaled by its multiplicity traces gives the unnormalized
weighted sector matrix expanded into the ambient space.

Source: arXiv:1606.00608, Appendix C.4, lines 2070--2071 and 2081--2083. -/
theorem normalizedVerticalSectorAmbientRestoration_trace_smul
    (dim mult : Fin g → ℕ)
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (hMult : ∀ α, 0 < mult α)
    (hWeight : ∀ α q, (0 : ℂ) < weight α q)
    (U : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ) (X : VerticalSectorAlgebra dim) :
    normalizedVerticalSectorAmbientRestoration dim mult weight U
        (fun α ↦ verticalMultiplicityTrace weight α • X α) =
      Uᴴ * verticalSectorBlockDiagonal dim mult (fun α ↦
        Matrix.kroneckerMap (· * ·) (Matrix.diagonal (weight α)) (X α)) * U := by
  rw [normalizedVerticalSectorAmbientRestoration_apply,
    normalizedRetainedVerticalSectorEmbedding_trace_smul
      dim mult weight hMult hWeight X]

/-- Retracting an ambient expansion of an unnormalized weighted sector matrix
returns the sector family scaled by its multiplicity traces.

Source: arXiv:1606.00608, Appendix C.4, lines 2067--2068 and 2078--2079. -/
theorem verticalSectorAmbientRetraction_weightedBlockDiagonal
    (dim mult : Fin g → ℕ)
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (U : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ)
    (hU : U * Uᴴ = 1) (X : VerticalSectorAlgebra dim) :
    verticalSectorAmbientRetraction dim mult U
        (Uᴴ * verticalSectorBlockDiagonal dim mult (fun α ↦
          Matrix.kroneckerMap (· * ·) (Matrix.diagonal (weight α)) (X α)) * U) =
      fun α ↦ verticalMultiplicityTrace weight α • X α := by
  rw [verticalSectorAmbientRetraction_apply]
  simp only [← Matrix.mul_assoc, hU, Matrix.one_mul]
  rw [Matrix.mul_assoc, hU, Matrix.mul_one]
  exact retainedVerticalSectorPartialTrace_weightedBlockDiagonal
    dim mult weight X

end MPOTensor
