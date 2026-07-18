/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.CoisometricCompression
import TNLean.Channel.KrausCPTP
import TNLean.MPS.MPDO.VerticalSectorCoordinates

/-!
# Positivity and trace loss of the transported vertical-sector maps

The normalized maps of Appendix C.4 act on finite products of matrix
algebras.  This file proves that their formal extensions preserve positive
semidefiniteness and identifies the precise obstruction to trace preservation.

For a vertical coisometry `U`, the matrix `Uᴴ * U` is the active-support
projection on the original physical space.  Compression by `U` loses exactly
the trace outside this projection.  Consequently a transported sector map
preserves the total sector trace on a positive input precisely when its
precompression output is supported on the active sector.

No complete-positivity predicate on finite products, global trace-preservation
claim, or inverse-map conclusion is asserted here.

The rectangular coordinate maps and their omitted zero-sector complements are
documented in `docs/paper-gaps/cpgsv17_vertical_isometry_zero_sector.tex`.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Appendix C.4, lines 1955--1980.
-/

open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace MPOTensor

/-- Pointwise positive semidefiniteness in a finite product of matrix
algebras. -/
def IsVerticalSectorPosSemidef {g : ℕ} {dim : Fin g → ℕ}
    (X : VerticalSectorAlgebra dim) : Prop :=
  ∀ α, (X α).PosSemidef

/-- The total trace on a finite product of matrix algebras. -/
def verticalSectorTrace {g : ℕ} {dim : Fin g → ℕ}
    (X : VerticalSectorAlgebra dim) : ℂ :=
  ∑ α, Matrix.trace (X α)

/-- The trace of a positive diagonal multiplicity matrix is positive. -/
theorem verticalMultiplicityTrace_pos
    {g : ℕ} {mult : Fin g → ℕ}
    {weight : (α : Fin g) → Fin (mult α) → ℂ}
    (hMult : ∀ α, 0 < mult α)
    (hWeight : ∀ α q, (0 : ℂ) < weight α q) (α : Fin g) :
    0 < verticalMultiplicityTrace weight α := by
  apply Finset.sum_pos'
  · intro q _
    exact (hWeight α q).le
  · let q : Fin (mult α) := ⟨0, hMult α⟩
    exact ⟨q, Finset.mem_univ q, hWeight α q⟩

/-- The normalized sector embedding preserves pointwise positive
semidefiniteness. -/
theorem normalizedVerticalSectorEmbedding_posSemidef
    {g : ℕ} (dim mult : Fin g → ℕ)
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (hMult : ∀ α, 0 < mult α)
    (hWeight : ∀ α q, (0 : ℂ) < weight α q)
    (X : VerticalSectorAlgebra dim) (hX : IsVerticalSectorPosSemidef X) :
    ∀ α, (normalizedVerticalSectorEmbedding dim mult weight X α).PosSemidef := by
  intro α
  rw [normalizedVerticalSectorEmbedding_apply]
  have hdiag : (Matrix.diagonal (weight α)).PosSemidef := by
    exact Matrix.PosSemidef.diagonal (fun q ↦ (hWeight α q).le)
  exact (hdiag.kronecker (hX α)).smul
    (inv_nonneg.mpr (verticalMultiplicityTrace_pos hMult hWeight α).le)

/-- The retained normalized embedding sends a pointwise positive sector
family to a positive matrix. -/
theorem normalizedRetainedVerticalSectorEmbedding_posSemidef
    {g : ℕ} (dim mult : Fin g → ℕ)
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (hMult : ∀ α, 0 < mult α)
    (hWeight : ∀ α q, (0 : ℂ) < weight α q)
    (X : VerticalSectorAlgebra dim) (hX : IsVerticalSectorPosSemidef X) :
    (normalizedRetainedVerticalSectorEmbedding dim mult weight X).PosSemidef := by
  have hblock : (Matrix.blockDiagonal'
      (normalizedVerticalSectorEmbedding dim mult weight X)).PosSemidef :=
    Matrix.PosSemidef.blockDiagonal' _
      (normalizedVerticalSectorEmbedding_posSemidef
        dim mult weight hMult hWeight X hX)
  simpa [normalizedRetainedVerticalSectorEmbedding,
    verticalSectorBlockDiagonal, LinearMap.comp_apply, Matrix.reindex_apply] using
      hblock.submatrix (verticalSectorFinEquiv dim mult).symm

/-- Sectorwise partial trace preserves pointwise positive
semidefiniteness. -/
theorem verticalSectorPartialTrace_posSemidef
    {g : ℕ} (dim mult : Fin g → ℕ)
    (Y : VerticalWeightedSectorSpace dim mult)
    (hY : ∀ α, (Y α).PosSemidef) :
    IsVerticalSectorPosSemidef (verticalSectorPartialTrace dim mult Y) := by
  intro α
  exact (hY α).traceLeft

/-- The retained sector partial trace sends a positive ambient matrix to a
pointwise positive sector family. -/
theorem retainedVerticalSectorPartialTrace_posSemidef
    {g : ℕ} (dim mult : Fin g → ℕ)
    (Z : RetainedVerticalSectorMatrix dim mult) (hZ : Z.PosSemidef) :
    IsVerticalSectorPosSemidef (retainedVerticalSectorPartialTrace dim mult Z) := by
  apply verticalSectorPartialTrace_posSemidef
  intro α
  exact hZ.submatrix (fun i ↦ verticalSectorFinEquiv dim mult ⟨α, i⟩)

/-- The trace of a retained block diagonal is the sum of the traces of its
blocks. -/
theorem trace_verticalSectorBlockDiagonal
    {g : ℕ} (dim mult : Fin g → ℕ)
    (Y : VerticalWeightedSectorSpace dim mult) :
    Matrix.trace (verticalSectorBlockDiagonal dim mult Y) =
      ∑ α, Matrix.trace (Y α) := by
  change Matrix.trace ((Matrix.reindex (verticalSectorFinEquiv dim mult)
    (verticalSectorFinEquiv dim mult)) (Matrix.blockDiagonal' Y)) = _
  rw [Matrix.trace_reindex, Matrix.trace_blockDiagonal']

/-- Removing off-diagonal sector blocks does not change the trace. -/
theorem trace_verticalSectorBlockProjection
    {g : ℕ} (dim mult : Fin g → ℕ)
    (Z : RetainedVerticalSectorMatrix dim mult) :
    Matrix.trace (verticalSectorBlockProjection dim mult Z) = Matrix.trace Z := by
  classical
  rw [Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _
  obtain ⟨⟨α, p⟩, rfl⟩ := (verticalSectorFinEquiv dim mult).surjective i
  exact verticalSectorBlockProjection_apply_same dim mult Z α p p

/-- The retained sector partial trace preserves the total trace. -/
theorem verticalSectorTrace_retainedVerticalSectorPartialTrace
    {g : ℕ} (dim mult : Fin g → ℕ)
    (Z : RetainedVerticalSectorMatrix dim mult) :
    verticalSectorTrace (retainedVerticalSectorPartialTrace dim mult Z) =
      Matrix.trace Z := by
  calc
    verticalSectorTrace (retainedVerticalSectorPartialTrace dim mult Z) =
        ∑ α, Matrix.trace (verticalSectorBlocks dim mult Z α) := by
      simp only [verticalSectorTrace, retainedVerticalSectorPartialTrace,
        verticalSectorPartialTrace, LinearMap.comp_apply, LinearMap.coe_mk,
        AddHom.coe_mk]
      apply Finset.sum_congr rfl
      intro α _
      exact (Matrix.trace_eq_trace_traceLeft
        (verticalSectorBlocks dim mult Z α)).symm
    _ = Matrix.trace (verticalSectorBlockProjection dim mult Z) := by
      rw [verticalSectorBlockProjection, LinearMap.comp_apply,
        trace_verticalSectorBlockDiagonal]
    _ = Matrix.trace Z := trace_verticalSectorBlockProjection dim mult Z

/-- The retained normalized embedding preserves the total sector trace. -/
theorem trace_normalizedRetainedVerticalSectorEmbedding
    {g : ℕ} (dim mult : Fin g → ℕ)
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (hMult : ∀ α, 0 < mult α)
    (hWeight : ∀ α q, (0 : ℂ) < weight α q)
    (X : VerticalSectorAlgebra dim) :
    Matrix.trace (normalizedRetainedVerticalSectorEmbedding dim mult weight X) =
      verticalSectorTrace X := by
  rw [normalizedRetainedVerticalSectorEmbedding, LinearMap.comp_apply,
    trace_verticalSectorBlockDiagonal]
  unfold verticalSectorTrace
  apply Finset.sum_congr rfl
  intro α _
  rw [normalizedVerticalSectorEmbedding_apply, Matrix.trace_smul,
    Matrix.trace_kronecker, Matrix.trace_diagonal]
  change (verticalMultiplicityTrace weight α)⁻¹ *
      (verticalMultiplicityTrace weight α * Matrix.trace (X α)) =
    Matrix.trace (X α)
  field_simp [verticalMultiplicityTrace_ne_zero α (hMult α) (hWeight α)]

/-- The matrix immediately before the final two-site active-sector
compression in the transported refinement map. -/
def precompressionVerticalSectorT
    {g₁ d : ℕ}
    (dim₁ mult₁ : Fin g₁ → ℕ)
    (weight₁ : (α : Fin g₁) → Fin (mult₁ α) → ℂ)
    (U₁ : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g₁, mult₁ α), verticalCopyDim dim₁ mult₁ q))
      (Fin d) ℂ)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (X : VerticalSectorAlgebra dim₁) :
    Matrix (Fin (d * d)) (Fin (d * d)) ℂ :=
  Matrix.equivReindexMap (blockedIndexEquiv d).symm
    (T (singleKrausMap U₁ᴴ
      (normalizedRetainedVerticalSectorEmbedding dim₁ mult₁ weight₁ X)))

/-- The matrix immediately before the final one-site active-sector
compression in the transported coarse-graining map. -/
def precompressionVerticalSectorS
    {g₂ d : ℕ}
    (dim₂ mult₂ : Fin g₂ → ℕ)
    (weight₂ : (β : Fin g₂) → Fin (mult₂ β) → ℂ)
    (U₂ : Matrix
      (Fin (∑ q : Fin (∑ β : Fin g₂, mult₂ β), verticalCopyDim dim₂ mult₂ q))
      (Fin (d * d)) ℂ)
    (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ)
    (X : VerticalSectorAlgebra dim₂) : Matrix (Fin d) (Fin d) ℂ :=
  S (Matrix.equivReindexMap (blockedIndexEquiv d)
    (singleKrausMap U₂ᴴ
      (normalizedRetainedVerticalSectorEmbedding dim₂ mult₂ weight₂ X)))

/-- The precompression refinement output is positive on every pointwise
positive sector family. -/
theorem precompressionVerticalSectorT_posSemidef
    {g₁ d : ℕ}
    (dim₁ mult₁ : Fin g₁ → ℕ)
    (weight₁ : (α : Fin g₁) → Fin (mult₁ α) → ℂ)
    (hMult₁ : ∀ α, 0 < mult₁ α)
    (hWeight₁ : ∀ α q, (0 : ℂ) < weight₁ α q)
    (U₁ : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g₁, mult₁ α), verticalCopyDim dim₁ mult₁ q))
      (Fin d) ℂ)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hT : IsKrausCPTP T)
    (X : VerticalSectorAlgebra dim₁) (hX : IsVerticalSectorPosSemidef X) :
    (precompressionVerticalSectorT dim₁ mult₁ weight₁ U₁ T X).PosSemidef := by
  have hEmbed := normalizedRetainedVerticalSectorEmbedding_posSemidef
    dim₁ mult₁ weight₁ hMult₁ hWeight₁ X hX
  have hInput : (singleKrausMap U₁ᴴ
      (normalizedRetainedVerticalSectorEmbedding dim₁ mult₁ weight₁ X)).PosSemidef :=
    hEmbed.mul_mul_conjTranspose_same U₁ᴴ
  have hOutput := hT.map_posSemidef hInput
  exact hOutput.submatrix (blockedIndexEquiv d)

/-- The precompression coarse-graining output is positive on every pointwise
positive sector family. -/
theorem precompressionVerticalSectorS_posSemidef
    {g₂ d : ℕ}
    (dim₂ mult₂ : Fin g₂ → ℕ)
    (weight₂ : (β : Fin g₂) → Fin (mult₂ β) → ℂ)
    (hMult₂ : ∀ β, 0 < mult₂ β)
    (hWeight₂ : ∀ β q, (0 : ℂ) < weight₂ β q)
    (U₂ : Matrix
      (Fin (∑ q : Fin (∑ β : Fin g₂, mult₂ β), verticalCopyDim dim₂ mult₂ q))
      (Fin (d * d)) ℂ)
    (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ)
    (hS : IsKrausCPTP S)
    (X : VerticalSectorAlgebra dim₂) (hX : IsVerticalSectorPosSemidef X) :
    (precompressionVerticalSectorS dim₂ mult₂ weight₂ U₂ S X).PosSemidef := by
  have hEmbed := normalizedRetainedVerticalSectorEmbedding_posSemidef
    dim₂ mult₂ weight₂ hMult₂ hWeight₂ X hX
  have hInput : (singleKrausMap U₂ᴴ
      (normalizedRetainedVerticalSectorEmbedding dim₂ mult₂ weight₂ X)).PosSemidef :=
    hEmbed.mul_mul_conjTranspose_same U₂ᴴ
  have hReindex : (Matrix.equivReindexMap (blockedIndexEquiv d)
      (singleKrausMap U₂ᴴ
        (normalizedRetainedVerticalSectorEmbedding dim₂ mult₂ weight₂ X))).PosSemidef :=
    hInput.submatrix (blockedIndexEquiv d).symm
  exact hS.map_posSemidef hReindex

/-- The transported refinement map preserves pointwise positive
semidefiniteness. -/
theorem transportedVerticalSectorT_posSemidef
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
    (hT : IsKrausCPTP T)
    (X : VerticalSectorAlgebra dim₁) (hX : IsVerticalSectorPosSemidef X) :
    IsVerticalSectorPosSemidef
      (transportedVerticalSectorT dim₁ mult₁ weight₁ dim₂ mult₂ U₁ U₂ T X) := by
  apply retainedVerticalSectorPartialTrace_posSemidef
  have hPre := precompressionVerticalSectorT_posSemidef
    dim₁ mult₁ weight₁ hMult₁ hWeight₁ U₁ T hT X hX
  simpa [transportTToVerticalCoordinates, precompressionVerticalSectorT,
    LinearMap.comp_apply, singleKrausMap_apply] using
      hPre.mul_mul_conjTranspose_same U₂

/-- The transported coarse-graining map preserves pointwise positive
semidefiniteness. -/
theorem transportedVerticalSectorS_posSemidef
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
    (hS : IsKrausCPTP S)
    (X : VerticalSectorAlgebra dim₂) (hX : IsVerticalSectorPosSemidef X) :
    IsVerticalSectorPosSemidef
      (transportedVerticalSectorS dim₁ mult₁ dim₂ mult₂ weight₂ U₁ U₂ S X) := by
  apply retainedVerticalSectorPartialTrace_posSemidef
  have hPre := precompressionVerticalSectorS_posSemidef
    dim₂ mult₂ weight₂ hMult₂ hWeight₂ U₂ S hS X hX
  simpa [transportSToVerticalCoordinates, precompressionVerticalSectorS,
    LinearMap.comp_apply, singleKrausMap_apply] using
      hPre.mul_mul_conjTranspose_same U₁

/-- The precompression refinement output has the same trace as the input
sector family when the input coordinate change is a coisometry. -/
theorem trace_precompressionVerticalSectorT
    {g₁ d : ℕ}
    (dim₁ mult₁ : Fin g₁ → ℕ)
    (weight₁ : (α : Fin g₁) → Fin (mult₁ α) → ℂ)
    (hMult₁ : ∀ α, 0 < mult₁ α)
    (hWeight₁ : ∀ α q, (0 : ℂ) < weight₁ α q)
    (U₁ : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g₁, mult₁ α), verticalCopyDim dim₁ mult₁ q))
      (Fin d) ℂ)
    (hU₁ : U₁ * U₁ᴴ = 1)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hT : IsKrausCPTP T) (X : VerticalSectorAlgebra dim₁) :
    Matrix.trace (precompressionVerticalSectorT dim₁ mult₁ weight₁ U₁ T X) =
      verticalSectorTrace X := by
  rw [precompressionVerticalSectorT,
    (Matrix.equivReindexMap_isKrausCPTP (blockedIndexEquiv d).symm).trace_map,
    hT.trace_map,
    singleKrausMap_apply, Matrix.conjTranspose_conjTranspose,
    Matrix.trace_conjTranspose_mul_mul_of_mul_conjTranspose_eq_one U₁ hU₁,
    trace_normalizedRetainedVerticalSectorEmbedding dim₁ mult₁ weight₁
      hMult₁ hWeight₁ X]

/-- The precompression coarse-graining output has the same trace as the input
sector family when the input coordinate change is a coisometry. -/
theorem trace_precompressionVerticalSectorS
    {g₂ d : ℕ}
    (dim₂ mult₂ : Fin g₂ → ℕ)
    (weight₂ : (β : Fin g₂) → Fin (mult₂ β) → ℂ)
    (hMult₂ : ∀ β, 0 < mult₂ β)
    (hWeight₂ : ∀ β q, (0 : ℂ) < weight₂ β q)
    (U₂ : Matrix
      (Fin (∑ q : Fin (∑ β : Fin g₂, mult₂ β), verticalCopyDim dim₂ mult₂ q))
      (Fin (d * d)) ℂ)
    (hU₂ : U₂ * U₂ᴴ = 1)
    (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ)
    (hS : IsKrausCPTP S) (X : VerticalSectorAlgebra dim₂) :
    Matrix.trace (precompressionVerticalSectorS dim₂ mult₂ weight₂ U₂ S X) =
      verticalSectorTrace X := by
  rw [precompressionVerticalSectorS, hS.trace_map,
    (Matrix.equivReindexMap_isKrausCPTP (blockedIndexEquiv d)).trace_map,
    singleKrausMap_apply, Matrix.conjTranspose_conjTranspose,
    Matrix.trace_conjTranspose_mul_mul_of_mul_conjTranspose_eq_one U₂ hU₂,
    trace_normalizedRetainedVerticalSectorEmbedding dim₂ mult₂ weight₂
      hMult₂ hWeight₂ X]

/-- The total trace after transported refinement is the trace after its final
active-sector compression. -/
theorem verticalSectorTrace_transportedVerticalSectorT
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
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (X : VerticalSectorAlgebra dim₁) :
    verticalSectorTrace
        (transportedVerticalSectorT dim₁ mult₁ weight₁ dim₂ mult₂ U₁ U₂ T X) =
      Matrix.trace
        (U₂ * precompressionVerticalSectorT dim₁ mult₁ weight₁ U₁ T X * U₂ᴴ) := by
  rw [transportedVerticalSectorT, LinearMap.comp_apply, LinearMap.comp_apply,
    verticalSectorTrace_retainedVerticalSectorPartialTrace]
  rfl

/-- The total trace after transported coarse-graining is the trace after its
final active-sector compression. -/
theorem verticalSectorTrace_transportedVerticalSectorS
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
      Matrix (Fin d) (Fin d) ℂ)
    (X : VerticalSectorAlgebra dim₂) :
    verticalSectorTrace
        (transportedVerticalSectorS dim₁ mult₁ dim₂ mult₂ weight₂ U₁ U₂ S X) =
      Matrix.trace
        (U₁ * precompressionVerticalSectorS dim₂ mult₂ weight₂ U₂ S X * U₁ᴴ) := by
  rw [transportedVerticalSectorS, LinearMap.comp_apply, LinearMap.comp_apply,
    verticalSectorTrace_retainedVerticalSectorPartialTrace]
  rfl

/-- Transported refinement is trace-nonincreasing on positive sector
families.  The only loss occurs at the final active-sector compression.

Appendix C.4, lines 1955--1980 of arXiv:1606.00608 supplies the transported
map used here.

**Local fix (zero-sector complement):** Rectangular vertical coordinates may
discard a zero-sector complement, so trace preservation is replaced by the
inequality below.  This obstruction and its elimination on inputs whose
precompression outputs lie in the retained sector are recorded in
`docs/paper-gaps/cpgsv17_vertical_isometry_zero_sector.tex`. -/
theorem transportedVerticalSectorT_trace_le
    {g₁ g₂ d : ℕ}
    (dim₁ mult₁ : Fin g₁ → ℕ)
    (weight₁ : (α : Fin g₁) → Fin (mult₁ α) → ℂ)
    (dim₂ mult₂ : Fin g₂ → ℕ)
    (hMult₁ : ∀ α, 0 < mult₁ α)
    (hWeight₁ : ∀ α q, (0 : ℂ) < weight₁ α q)
    (U₁ : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g₁, mult₁ α), verticalCopyDim dim₁ mult₁ q))
      (Fin d) ℂ)
    (hU₁ : U₁ * U₁ᴴ = 1)
    (U₂ : Matrix
      (Fin (∑ q : Fin (∑ β : Fin g₂, mult₂ β), verticalCopyDim dim₂ mult₂ q))
      (Fin (d * d)) ℂ)
    (hU₂ : U₂ * U₂ᴴ = 1)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hT : IsKrausCPTP T)
    (X : VerticalSectorAlgebra dim₁) (hX : IsVerticalSectorPosSemidef X) :
    verticalSectorTrace
        (transportedVerticalSectorT dim₁ mult₁ weight₁ dim₂ mult₂ U₁ U₂ T X) ≤
      verticalSectorTrace X := by
  rw [verticalSectorTrace_transportedVerticalSectorT]
  calc
    Matrix.trace
        (U₂ * precompressionVerticalSectorT dim₁ mult₁ weight₁ U₁ T X * U₂ᴴ) ≤
        Matrix.trace (precompressionVerticalSectorT dim₁ mult₁ weight₁ U₁ T X) :=
      (precompressionVerticalSectorT_posSemidef dim₁ mult₁ weight₁ hMult₁
        hWeight₁ U₁ T hT X hX).trace_mul_mul_conjTranspose_le_of_mul_conjTranspose_eq_one
          U₂ hU₂
    _ = verticalSectorTrace X :=
      trace_precompressionVerticalSectorT dim₁ mult₁ weight₁ hMult₁ hWeight₁
        U₁ hU₁ T hT X

/-- Transported refinement preserves the trace of a positive sector family
exactly when its precompression output is supported on `U₂ᴴ * U₂`.

Appendix C.4, lines 1955--1980 of arXiv:1606.00608 supplies the transported
map used here.  On the bond contractions of the vertical canonical forms, the
source-generated image-preservation result proves that the precompression
output is supported on the active sector.  Its scope is documented in
`docs/paper-gaps/cpgsv17_vertical_isometry_zero_sector.tex`. -/
theorem transportedVerticalSectorT_trace_eq_iff
    {g₁ g₂ d : ℕ}
    (dim₁ mult₁ : Fin g₁ → ℕ)
    (weight₁ : (α : Fin g₁) → Fin (mult₁ α) → ℂ)
    (dim₂ mult₂ : Fin g₂ → ℕ)
    (hMult₁ : ∀ α, 0 < mult₁ α)
    (hWeight₁ : ∀ α q, (0 : ℂ) < weight₁ α q)
    (U₁ : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g₁, mult₁ α), verticalCopyDim dim₁ mult₁ q))
      (Fin d) ℂ)
    (hU₁ : U₁ * U₁ᴴ = 1)
    (U₂ : Matrix
      (Fin (∑ q : Fin (∑ β : Fin g₂, mult₂ β), verticalCopyDim dim₂ mult₂ q))
      (Fin (d * d)) ℂ)
    (hU₂ : U₂ * U₂ᴴ = 1)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hT : IsKrausCPTP T)
    (X : VerticalSectorAlgebra dim₁) (hX : IsVerticalSectorPosSemidef X) :
    verticalSectorTrace
        (transportedVerticalSectorT dim₁ mult₁ weight₁ dim₂ mult₂ U₁ U₂ T X) =
        verticalSectorTrace X ↔
      U₂ᴴ * U₂ * precompressionVerticalSectorT dim₁ mult₁ weight₁ U₁ T X =
        precompressionVerticalSectorT dim₁ mult₁ weight₁ U₁ T X := by
  rw [verticalSectorTrace_transportedVerticalSectorT,
    ← trace_precompressionVerticalSectorT dim₁ mult₁ weight₁ hMult₁ hWeight₁
      U₁ hU₁ T hT X]
  exact Matrix.PosSemidef.trace_mul_mul_conjTranspose_eq_iff_of_mul_conjTranspose_eq_one
    (precompressionVerticalSectorT_posSemidef dim₁ mult₁ weight₁ hMult₁
      hWeight₁ U₁ T hT X hX) U₂ hU₂

/-- Transported coarse-graining is trace-nonincreasing on positive sector
families.  The only loss occurs at the final active-sector compression.

Appendix C.4, lines 1955--1980 of arXiv:1606.00608 supplies the transported
map used here.

**Local fix (zero-sector complement):** Rectangular vertical coordinates may
discard a zero-sector complement, so trace preservation is replaced by the
inequality below.  This obstruction and its elimination on inputs whose
precompression outputs lie in the retained sector are recorded in
`docs/paper-gaps/cpgsv17_vertical_isometry_zero_sector.tex`. -/
theorem transportedVerticalSectorS_trace_le
    {g₁ g₂ d : ℕ}
    (dim₁ mult₁ : Fin g₁ → ℕ)
    (dim₂ mult₂ : Fin g₂ → ℕ)
    (weight₂ : (β : Fin g₂) → Fin (mult₂ β) → ℂ)
    (hMult₂ : ∀ β, 0 < mult₂ β)
    (hWeight₂ : ∀ β q, (0 : ℂ) < weight₂ β q)
    (U₁ : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g₁, mult₁ α), verticalCopyDim dim₁ mult₁ q))
      (Fin d) ℂ)
    (hU₁ : U₁ * U₁ᴴ = 1)
    (U₂ : Matrix
      (Fin (∑ q : Fin (∑ β : Fin g₂, mult₂ β), verticalCopyDim dim₂ mult₂ q))
      (Fin (d * d)) ℂ)
    (hU₂ : U₂ * U₂ᴴ = 1)
    (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ)
    (hS : IsKrausCPTP S)
    (X : VerticalSectorAlgebra dim₂) (hX : IsVerticalSectorPosSemidef X) :
    verticalSectorTrace
        (transportedVerticalSectorS dim₁ mult₁ dim₂ mult₂ weight₂ U₁ U₂ S X) ≤
      verticalSectorTrace X := by
  rw [verticalSectorTrace_transportedVerticalSectorS]
  calc
    Matrix.trace
        (U₁ * precompressionVerticalSectorS dim₂ mult₂ weight₂ U₂ S X * U₁ᴴ) ≤
        Matrix.trace (precompressionVerticalSectorS dim₂ mult₂ weight₂ U₂ S X) :=
      (precompressionVerticalSectorS_posSemidef dim₂ mult₂ weight₂ hMult₂
        hWeight₂ U₂ S hS X hX).trace_mul_mul_conjTranspose_le_of_mul_conjTranspose_eq_one
          U₁ hU₁
    _ = verticalSectorTrace X :=
      trace_precompressionVerticalSectorS dim₂ mult₂ weight₂ hMult₂ hWeight₂
        U₂ hU₂ S hS X

/-- Transported coarse-graining preserves the trace of a positive sector
family exactly when its precompression output is supported on `U₁ᴴ * U₁`.

Appendix C.4, lines 1955--1980 of arXiv:1606.00608 supplies the transported
map used here.  On the bond contractions of the vertical canonical forms, the
source-generated image-preservation result proves that the precompression
output is supported on the active sector.  Its scope is documented in
`docs/paper-gaps/cpgsv17_vertical_isometry_zero_sector.tex`. -/
theorem transportedVerticalSectorS_trace_eq_iff
    {g₁ g₂ d : ℕ}
    (dim₁ mult₁ : Fin g₁ → ℕ)
    (dim₂ mult₂ : Fin g₂ → ℕ)
    (weight₂ : (β : Fin g₂) → Fin (mult₂ β) → ℂ)
    (hMult₂ : ∀ β, 0 < mult₂ β)
    (hWeight₂ : ∀ β q, (0 : ℂ) < weight₂ β q)
    (U₁ : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g₁, mult₁ α), verticalCopyDim dim₁ mult₁ q))
      (Fin d) ℂ)
    (hU₁ : U₁ * U₁ᴴ = 1)
    (U₂ : Matrix
      (Fin (∑ q : Fin (∑ β : Fin g₂, mult₂ β), verticalCopyDim dim₂ mult₂ q))
      (Fin (d * d)) ℂ)
    (hU₂ : U₂ * U₂ᴴ = 1)
    (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ)
    (hS : IsKrausCPTP S)
    (X : VerticalSectorAlgebra dim₂) (hX : IsVerticalSectorPosSemidef X) :
    verticalSectorTrace
        (transportedVerticalSectorS dim₁ mult₁ dim₂ mult₂ weight₂ U₁ U₂ S X) =
        verticalSectorTrace X ↔
      U₁ᴴ * U₁ * precompressionVerticalSectorS dim₂ mult₂ weight₂ U₂ S X =
        precompressionVerticalSectorS dim₂ mult₂ weight₂ U₂ S X := by
  rw [verticalSectorTrace_transportedVerticalSectorS,
    ← trace_precompressionVerticalSectorS dim₂ mult₂ weight₂ hMult₂ hWeight₂
      U₂ hU₂ S hS X]
  exact Matrix.PosSemidef.trace_mul_mul_conjTranspose_eq_iff_of_mul_conjTranspose_eq_one
    (precompressionVerticalSectorS_posSemidef dim₂ mult₂ weight₂ hMult₂
      hWeight₂ U₂ S hS X hX) U₁ hU₁

end MPOTensor
