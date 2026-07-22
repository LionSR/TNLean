/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.VerticalSectorTracePreservation

/-!
# Complete positivity of the transported vertical-sector maps

The normalized vertical-sector embedding is a controlled state preparation,
and the vertical-sector retraction is a controlled partial trace.  After
identifying the retained physical coordinates with the corresponding direct
sums, these maps can be composed with the completely positive physical
refinement and coarse-graining maps.  Thus both transported vertical-sector
maps are completely positive between finite sums of matrix algebras.

The two square composites are trace preserving by the independent
maximal-support argument established earlier.  Complete positivity therefore
gives the Schwarz inequalities for their trace adjoints.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Definition 4.1 and Appendix C.4, lines 1955--1995.
-/

open scoped Matrix MatrixOrder ComplexOrder

noncomputable section

namespace MPOTensor

/-- Transporting a completely positive refinement map through the retained
vertical coordinates preserves complete positivity.

Source: arXiv:1606.00608, Definition 4.1 and Appendix C.4, lines 1955--1979. -/
theorem transportTToVerticalCoordinates_isKrausCP
    {d R₁ R₂ : ℕ}
    (U₁ : Matrix (Fin R₁) (Fin d) ℂ)
    (U₂ : Matrix (Fin R₂) (Fin (d * d)) ℂ)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hT : IsKrausCP T) :
    IsKrausCP (transportTToVerticalCoordinates U₁ U₂ T) := by
  unfold transportTToVerticalCoordinates
  apply isKrausCP_comp
  · apply isKrausCP_comp
    · apply isKrausCP_comp
      · exact singleKrausMap_isKrausCP U₁ᴴ
      · exact hT
    · exact (Matrix.equivReindexMap_isKrausCPTP
        (blockedIndexEquiv d).symm).isKrausCP
  · exact singleKrausMap_isKrausCP U₂

/-- Transporting a completely positive coarse-graining map through the
retained vertical coordinates preserves complete positivity.

Source: arXiv:1606.00608, Definition 4.1 and Appendix C.4, lines 1955--1979. -/
theorem transportSToVerticalCoordinates_isKrausCP
    {d R₁ R₂ : ℕ}
    (U₁ : Matrix (Fin R₁) (Fin d) ℂ)
    (U₂ : Matrix (Fin R₂) (Fin (d * d)) ℂ)
    (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ)
    (hS : IsKrausCP S) :
    IsKrausCP (transportSToVerticalCoordinates U₁ U₂ S) := by
  unfold transportSToVerticalCoordinates
  apply isKrausCP_comp
  · apply isKrausCP_comp
    · exact isKrausCP_comp (singleKrausMap_isKrausCP U₂ᴴ)
        (Matrix.equivReindexMap_isKrausCPTP
          (blockedIndexEquiv d)).isKrausCP
    · exact hS
  · exact singleKrausMap_isKrausCP U₁

/-- In retained coordinates, putting a vertical-sector family on the block
diagonal is block-diagonal embedding followed by the canonical reindexing.

Source: arXiv:1606.00608, Appendix C.4, lines 1955--1971. -/
theorem verticalSectorBlockDiagonal_eq_equivReindexMap_comp_embedding
    {g : ℕ} (dim mult : Fin g → ℕ) :
    verticalSectorBlockDiagonal dim mult =
      (Matrix.equivReindexMap (verticalSectorFinEquiv dim mult)).comp
        Matrix.directSumDiagonalEmbedding :=
  rfl

/-- In retained coordinates, extracting the vertical-sector blocks is the
canonical inverse reindexing followed by diagonal-block compression.

Source: arXiv:1606.00608, Appendix C.4, lines 1955--1971. -/
theorem verticalSectorBlocks_eq_compression_comp_equivReindexMap
    {g : ℕ} (dim mult : Fin g → ℕ) :
    verticalSectorBlocks dim mult =
      Matrix.directSumDiagonalCompression.comp
        (Matrix.equivReindexMap (verticalSectorFinEquiv dim mult).symm) :=
  rfl

/-- The canonical full-matrix extension of the transported refinement map is
the composition of the normalized preparation, retained-coordinate changes,
physical refinement map, and partial trace.

Source: arXiv:1606.00608, Definition 4.1 and Appendix C.4, lines 1955--1979. -/
theorem directSumMapExtension_transportedVerticalSectorT
    {g₁ g₂ d : ℕ}
    (dim₁ mult₁ : Fin g₁ → ℕ)
    (weight₁ : (α : Fin g₁) → Fin (mult₁ α) → ℂ)
    (dim₂ mult₂ : Fin g₂ → ℕ)
    (U₁ : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g₁, mult₁ α), verticalCopyDim dim₁ mult₁ q))
      (Fin d) ℂ)
    (U₂ : Matrix
      (Fin (∑ q : Fin (∑ β : Fin g₂, mult₂ β), verticalCopyDim dim₂ mult₂ q))
      (Fin (d * d)) ℂ)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix.directSumMapExtension
        (transportedVerticalSectorT
          dim₁ mult₁ weight₁ dim₂ mult₂ U₁ U₂ T) =
      (Matrix.directSumMapExtension
        (verticalSectorPartialTrace dim₂ mult₂)).comp
        ((Matrix.equivReindexMap
          (verticalSectorFinEquiv dim₂ mult₂).symm).comp
          ((transportTToVerticalCoordinates U₁ U₂ T).comp
            ((Matrix.equivReindexMap
              (verticalSectorFinEquiv dim₁ mult₁)).comp
              (Matrix.directSumMapExtension
                (normalizedVerticalSectorEmbedding
                  dim₁ mult₁ weight₁))))) := by
  apply LinearMap.ext
  intro X
  rfl

/-- The canonical full-matrix extension of the transported coarse-graining
map is the composition of the normalized preparation, retained-coordinate
changes, physical coarse-graining map, and partial trace.

Source: arXiv:1606.00608, Definition 4.1 and Appendix C.4, lines 1955--1979. -/
theorem directSumMapExtension_transportedVerticalSectorS
    {g₁ g₂ d : ℕ}
    (dim₁ mult₁ : Fin g₁ → ℕ)
    (dim₂ mult₂ : Fin g₂ → ℕ)
    (weight₂ : (β : Fin g₂) → Fin (mult₂ β) → ℂ)
    (U₁ : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g₁, mult₁ α), verticalCopyDim dim₁ mult₁ q))
      (Fin d) ℂ)
    (U₂ : Matrix
      (Fin (∑ q : Fin (∑ β : Fin g₂, mult₂ β), verticalCopyDim dim₂ mult₂ q))
      (Fin (d * d)) ℂ)
    (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ) :
    Matrix.directSumMapExtension
        (transportedVerticalSectorS
          dim₁ mult₁ dim₂ mult₂ weight₂ U₁ U₂ S) =
      (Matrix.directSumMapExtension
        (verticalSectorPartialTrace dim₁ mult₁)).comp
        ((Matrix.equivReindexMap
          (verticalSectorFinEquiv dim₁ mult₁).symm).comp
          ((transportSToVerticalCoordinates U₁ U₂ S).comp
            ((Matrix.equivReindexMap
              (verticalSectorFinEquiv dim₂ mult₂)).comp
              (Matrix.directSumMapExtension
                (normalizedVerticalSectorEmbedding
                  dim₂ mult₂ weight₂))))) := by
  apply LinearMap.ext
  intro X
  rfl

/-- The transported refinement map is completely positive between the finite
sums of vertical simple-sector matrix algebras.

Source: arXiv:1606.00608, Definition 4.1 and Appendix C.4, lines 1955--1979. -/
theorem transportedVerticalSectorT_isKrausDirectSumMap
    {g₁ g₂ d : ℕ}
    (dim₁ mult₁ : Fin g₁ → ℕ)
    (weight₁ : (α : Fin g₁) → Fin (mult₁ α) → ℂ)
    (dim₂ mult₂ : Fin g₂ → ℕ)
    (hMult₁ : ∀ α, 0 < mult₁ α)
    (hWeight₁ : ∀ α q, (0 : ℂ) < weight₁ α q)
    (U₁ : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g₁, mult₁ α), verticalCopyDim dim₁ mult₁ q))
      (Fin d) ℂ)
    (U₂ : Matrix
      (Fin (∑ q : Fin (∑ β : Fin g₂, mult₂ β), verticalCopyDim dim₂ mult₂ q))
      (Fin (d * d)) ℂ)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hT : IsKrausCP T) :
    Matrix.IsKrausDirectSumMap
      (transportedVerticalSectorT
        dim₁ mult₁ weight₁ dim₂ mult₂ U₁ U₂ T) := by
  rw [Matrix.IsKrausDirectSumMap,
    directSumMapExtension_transportedVerticalSectorT]
  have hPrep := normalizedVerticalSectorEmbedding_isKrausDirectSumMap
    dim₁ mult₁ weight₁ hMult₁ hWeight₁
  have hReindex₁ := (Matrix.equivReindexMap_isKrausCPTP
    (verticalSectorFinEquiv dim₁ mult₁)).isKrausCP
  have hTransport := transportTToVerticalCoordinates_isKrausCP U₁ U₂ T hT
  have hReindex₂ := (Matrix.equivReindexMap_isKrausCPTP
    (verticalSectorFinEquiv dim₂ mult₂).symm).isKrausCP
  have hTrace := verticalSectorPartialTrace_isKrausDirectSumMap dim₂ mult₂
  exact isKrausCP_comp
    (isKrausCP_comp
      (isKrausCP_comp (isKrausCP_comp hPrep hReindex₁) hTransport)
      hReindex₂)
    hTrace

/-- The transported coarse-graining map is completely positive between the
finite sums of vertical simple-sector matrix algebras.

Source: arXiv:1606.00608, Definition 4.1 and Appendix C.4, lines 1955--1979. -/
theorem transportedVerticalSectorS_isKrausDirectSumMap
    {g₁ g₂ d : ℕ}
    (dim₁ mult₁ : Fin g₁ → ℕ)
    (dim₂ mult₂ : Fin g₂ → ℕ)
    (weight₂ : (β : Fin g₂) → Fin (mult₂ β) → ℂ)
    (hMult₂ : ∀ β, 0 < mult₂ β)
    (hWeight₂ : ∀ β q, (0 : ℂ) < weight₂ β q)
    (U₁ : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g₁, mult₁ α), verticalCopyDim dim₁ mult₁ q))
      (Fin d) ℂ)
    (U₂ : Matrix
      (Fin (∑ q : Fin (∑ β : Fin g₂, mult₂ β), verticalCopyDim dim₂ mult₂ q))
      (Fin (d * d)) ℂ)
    (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ)
    (hS : IsKrausCP S) :
    Matrix.IsKrausDirectSumMap
      (transportedVerticalSectorS
        dim₁ mult₁ dim₂ mult₂ weight₂ U₁ U₂ S) := by
  rw [Matrix.IsKrausDirectSumMap,
    directSumMapExtension_transportedVerticalSectorS]
  have hPrep := normalizedVerticalSectorEmbedding_isKrausDirectSumMap
    dim₂ mult₂ weight₂ hMult₂ hWeight₂
  have hReindex₂ := (Matrix.equivReindexMap_isKrausCPTP
    (verticalSectorFinEquiv dim₂ mult₂)).isKrausCP
  have hTransport := transportSToVerticalCoordinates_isKrausCP U₁ U₂ S hS
  have hReindex₁ := (Matrix.equivReindexMap_isKrausCPTP
    (verticalSectorFinEquiv dim₁ mult₁).symm).isKrausCP
  have hTrace := verticalSectorPartialTrace_isKrausDirectSumMap dim₁ mult₁
  exact isKrausCP_comp
    (isKrausCP_comp
      (isKrausCP_comp (isKrausCP_comp hPrep hReindex₂) hTransport)
      hReindex₁)
    hTrace

/-- The trace adjoints of the two transported square composites satisfy the
Schwarz inequality under the tensor hypotheses of Appendix C.4.

Complete positivity follows from the Kraus forms of the normalized sector
preparations, physical maps, coordinate changes, and partial traces.  The
independent maximal-support argument gives trace preservation of the square
composites, so their trace adjoints are unital completely positive maps.

Source: arXiv:1606.00608, Definition 4.1 and Appendix C.4, lines 1955--1995. -/
theorem transportedVerticalSector_composites_traceAdjointSchwarz
    {g₁ g₂ d D : ℕ}
    (h : VerticalSectorHypotheses
      (g₁ := g₁) (g₂ := g₂) (d := d) (D := D)) :
    Matrix.IsSchwarzDirectSumMap
        (Matrix.directSumTraceAdjointMap h.SbarTbar) ∧
      Matrix.IsSchwarzDirectSumMap
        (Matrix.directSumTraceAdjointMap h.TbarSbar) := by
  obtain ⟨hSTTrace, hTSTrace, _, _⟩ :=
    transportedVerticalSector_composites_tracePreserving h
  have hT := transportedVerticalSectorT_isKrausDirectSumMap
    h.dim₁ h.mult₁ h.weight₁ h.dim₂ h.mult₂ h.hMult₁ h.hWeight₁
    h.U₁ h.U₂ h.T h.hTCPTP.isKrausCP
  have hS := transportedVerticalSectorS_isKrausDirectSumMap
    h.dim₁ h.mult₁ h.dim₂ h.mult₂ h.weight₂ h.hMult₂ h.hWeight₂
    h.U₁ h.U₂ h.S h.hSCPTP.isKrausCP
  exact ⟨(hT.comp hS).directSumTraceAdjointMap_isSchwarz hSTTrace,
    (hS.comp hT).directSumTraceAdjointMap_isSchwarz hTSTrace⟩

end MPOTensor
