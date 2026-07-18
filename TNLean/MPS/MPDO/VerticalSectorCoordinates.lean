/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.VerticalMapTransport
import TNLean.MPS.MPDO.VerticalSectorRetractions

/-!
# Vertical-sector direct-sum coordinates

The one-site and two-site vertical canonical forms are represented by matrices
on a single retained physical space.  The normalized sector maps of Appendix
C.4 are instead defined on a dependent family of matrix algebras.  This file
identifies the dependent family with the block-diagonal matrices on the
retained space and composes this identification with the physical refinement
and coarse-graining maps.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Appendix C.4, lines 1955--1979.
-/

open scoped ComplexOrder Matrix

noncomputable section

namespace MPOTensor

/-- Identify the simple-block coordinate in one multiplicity copy with the
corresponding coordinate in the flattened copy family.

Source: arXiv:1606.00608, Appendix C.4, lines 1955--1971. -/
def verticalCopyFinEquiv {g : ℕ} (dim mult : Fin g → ℕ)
    (p : Σ α : Fin g, Fin (mult α)) :
    Fin (dim p.1) ≃ Fin (verticalCopyDim dim mult (finSigmaFinEquiv p)) :=
  finCongr (by simp [verticalCopyDim])

/-- The canonical identification of a vertical label, a multiplicity index,
and a simple-block index with the flattened retained physical coordinate.

Source: arXiv:1606.00608, Appendix C.4, lines 1955--1971. -/
def verticalSectorFinEquiv {g : ℕ} (dim mult : Fin g → ℕ) :
    (Σ α : Fin g, Fin (mult α) × Fin (dim α)) ≃
      Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q) :=
  ((Equiv.sigmaCongrRight fun α =>
      (Equiv.sigmaEquivProd (Fin (mult α)) (Fin (dim α))).symm).trans
    (Equiv.sigmaAssoc (fun α (_ : Fin (mult α)) => Fin (dim α))).symm).trans
      ((Equiv.sigmaCongr finSigmaFinEquiv (verticalCopyFinEquiv dim mult)).trans
        finSigmaFinEquiv)

@[simp]
theorem verticalSectorFinEquiv_outer_symm {g : ℕ} (dim mult : Fin g → ℕ)
    (α : Fin g) (a : Fin (mult α)) (i : Fin (dim α)) :
    finSigmaFinEquiv.symm (verticalSectorFinEquiv dim mult ⟨α, (a, i)⟩) =
      ⟨finSigmaFinEquiv ⟨α, a⟩,
        Fin.cast (by simp [verticalCopyDim]) i⟩ := by
  rw [Equiv.symm_apply_eq]
  unfold verticalSectorFinEquiv
  simp only [Equiv.trans_apply]
  rw [Equiv.sigmaCongrRight_apply]
  simp only [Equiv.sigmaEquivProd, Equiv.sigmaAssoc,
    Equiv.coe_fn_symm_mk]
  unfold Equiv.sigmaCongr
  simp only [Equiv.trans_apply]
  rw [Equiv.sigmaCongrRight_apply, Equiv.sigmaCongrLeft_apply]
  apply Fin.ext
  simp [finSigmaFinEquiv_apply, verticalCopyFinEquiv, finCongr_apply]

@[simp]
theorem verticalSectorFinEquiv_copy {g : ℕ} (dim mult : Fin g → ℕ)
    (α : Fin g) (a : Fin (mult α)) (i : Fin (dim α)) :
    finSigmaFinEquiv.symm
        (finSigmaFinEquiv.symm
          (verticalSectorFinEquiv dim mult ⟨α, (a, i)⟩)).1 =
      ⟨α, a⟩ := by
  rw [verticalSectorFinEquiv_outer_symm]
  exact finSigmaFinEquiv.symm_apply_apply ⟨α, a⟩

/-- Matrices on the flattened retained physical space of a vertical canonical
form. -/
abbrev RetainedVerticalSectorMatrix {g : ℕ} (dim mult : Fin g → ℕ) :=
  Matrix
    (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
    (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q)) ℂ

/-- Put a family of vertical-sector matrices on the block diagonal of the
flattened retained physical space.

Source: arXiv:1606.00608, Appendix C.4, lines 1955--1971. -/
def verticalSectorBlockDiagonal {g : ℕ} (dim mult : Fin g → ℕ) :
    VerticalWeightedSectorSpace dim mult →ₗ[ℂ]
      RetainedVerticalSectorMatrix dim mult where
  toFun Y := Matrix.reindex (verticalSectorFinEquiv dim mult)
    (verticalSectorFinEquiv dim mult) (Matrix.blockDiagonal' Y)
  map_add' Y Z := by
    rw [Matrix.blockDiagonal'_add]
    exact (Matrix.reindexLinearEquiv ℂ ℂ (verticalSectorFinEquiv dim mult)
      (verticalSectorFinEquiv dim mult)).map_add _ _
  map_smul' c Y := by
    rw [Matrix.blockDiagonal'_smul]
    exact (Matrix.reindexLinearEquiv ℂ ℂ (verticalSectorFinEquiv dim mult)
      (verticalSectorFinEquiv dim mult)).map_smul c _

/-- Extract each vertical-sector diagonal block from a matrix on the retained
physical coordinate space.

Source: arXiv:1606.00608, Appendix C.4, lines 1955--1971. -/
def verticalSectorBlocks {g : ℕ} (dim mult : Fin g → ℕ) :
    RetainedVerticalSectorMatrix dim mult →ₗ[ℂ]
      VerticalWeightedSectorSpace dim mult where
  toFun Z α := Z.submatrix
    (fun i => verticalSectorFinEquiv dim mult ⟨α, i⟩)
    (fun i => verticalSectorFinEquiv dim mult ⟨α, i⟩)
  map_add' Z W := by
    funext α i j
    rfl
  map_smul' c Z := by
    funext α i j
    rfl

@[simp]
theorem verticalSectorBlockDiagonal_apply_same {g : ℕ}
    (dim mult : Fin g → ℕ) (Y : VerticalWeightedSectorSpace dim mult)
    (α : Fin g) (i j : Fin (mult α) × Fin (dim α)) :
    verticalSectorBlockDiagonal dim mult Y
        (verticalSectorFinEquiv dim mult ⟨α, i⟩)
        (verticalSectorFinEquiv dim mult ⟨α, j⟩) = Y α i j := by
  simp [verticalSectorBlockDiagonal, Matrix.reindex_apply,
    Matrix.blockDiagonal'_apply_eq]

@[simp]
theorem verticalSectorBlockDiagonal_apply_ne {g : ℕ}
    (dim mult : Fin g → ℕ) (Y : VerticalWeightedSectorSpace dim mult)
    {α β : Fin g} (hαβ : α ≠ β)
    (i : Fin (mult α) × Fin (dim α))
    (j : Fin (mult β) × Fin (dim β)) :
    verticalSectorBlockDiagonal dim mult Y
        (verticalSectorFinEquiv dim mult ⟨α, i⟩)
        (verticalSectorFinEquiv dim mult ⟨β, j⟩) = 0 := by
  simp [verticalSectorBlockDiagonal, Matrix.reindex_apply,
    Matrix.blockDiagonal'_apply_ne, hαβ]

/-- Extracting the diagonal blocks after placing a sector family on the block
diagonal recovers the original family.

Source: arXiv:1606.00608, Appendix C.4, lines 1955--1971. -/
theorem verticalSectorBlocks_comp_verticalSectorBlockDiagonal {g : ℕ}
    (dim mult : Fin g → ℕ) :
    (verticalSectorBlocks dim mult).comp
      (verticalSectorBlockDiagonal dim mult) = LinearMap.id := by
  apply LinearMap.ext
  intro Y
  funext α i j
  simp [verticalSectorBlocks, verticalSectorBlockDiagonal,
    Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.blockDiagonal'_apply_eq]

/-- The projection of a retained-coordinate matrix onto its vertical-sector
diagonal blocks.

Source: arXiv:1606.00608, Appendix C.4, lines 1955--1971. -/
def verticalSectorBlockProjection {g : ℕ} (dim mult : Fin g → ℕ) :=
  (verticalSectorBlockDiagonal dim mult).comp (verticalSectorBlocks dim mult)

/-- The vertical-sector block projection leaves every diagonal sector block
unchanged.

Source: arXiv:1606.00608, Appendix C.4, lines 1955--1971. -/
theorem verticalSectorBlockProjection_apply_same {g : ℕ}
    (dim mult : Fin g → ℕ)
    (Z : RetainedVerticalSectorMatrix dim mult)
    (α : Fin g) (i j : Fin (mult α) × Fin (dim α)) :
    verticalSectorBlockProjection dim mult Z
        (verticalSectorFinEquiv dim mult ⟨α, i⟩)
        (verticalSectorFinEquiv dim mult ⟨α, j⟩) =
      Z (verticalSectorFinEquiv dim mult ⟨α, i⟩)
        (verticalSectorFinEquiv dim mult ⟨α, j⟩) := by
  simp [verticalSectorBlockProjection, verticalSectorBlockDiagonal,
    verticalSectorBlocks, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.blockDiagonal'_apply_eq]

/-- The vertical-sector block projection sets the matrix entries between
distinct sectors to zero.

Source: arXiv:1606.00608, Appendix C.4, lines 1955--1971. -/
theorem verticalSectorBlockProjection_apply_ne {g : ℕ}
    (dim mult : Fin g → ℕ)
    (Z : RetainedVerticalSectorMatrix dim mult)
    {α β : Fin g} (hαβ : α ≠ β)
    (i : Fin (mult α) × Fin (dim α))
    (j : Fin (mult β) × Fin (dim β)) :
    verticalSectorBlockProjection dim mult Z
        (verticalSectorFinEquiv dim mult ⟨α, i⟩)
        (verticalSectorFinEquiv dim mult ⟨β, j⟩) = 0 := by
  simp [verticalSectorBlockProjection, verticalSectorBlockDiagonal,
    verticalSectorBlocks, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.blockDiagonal'_apply_ne, hαβ]

/-- Projection onto the vertical-sector diagonal blocks is idempotent.

Source: arXiv:1606.00608, Appendix C.4, lines 1955--1971. -/
theorem verticalSectorBlockProjection_comp_self {g : ℕ}
    (dim mult : Fin g → ℕ) :
    (verticalSectorBlockProjection dim mult).comp
      (verticalSectorBlockProjection dim mult) =
        verticalSectorBlockProjection dim mult := by
  apply LinearMap.ext
  intro Z
  simp only [verticalSectorBlockProjection, LinearMap.comp_apply]
  have h := LinearMap.congr_fun
    (verticalSectorBlocks_comp_verticalSectorBlockDiagonal dim mult)
    (verticalSectorBlocks dim mult Z)
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at h
  rw [h]

/-- The normalized vertical-sector embedding, written as a matrix on the
flattened retained physical space.

Source: arXiv:1606.00608, Appendix C.4, lines 1962--1979. -/
def normalizedRetainedVerticalSectorEmbedding {g : ℕ}
    (dim mult : Fin g → ℕ)
    (weight : (α : Fin g) → Fin (mult α) → ℂ) :=
  (verticalSectorBlockDiagonal dim mult).comp
    (normalizedVerticalSectorEmbedding dim mult weight)

/-- Extract the vertical-sector diagonal blocks from a retained-coordinate
matrix and take the partial trace over each multiplicity factor.

Source: arXiv:1606.00608, Appendix C.4, lines 1962--1979. -/
def retainedVerticalSectorPartialTrace {g : ℕ} (dim mult : Fin g → ℕ) :=
  (verticalSectorPartialTrace dim mult).comp (verticalSectorBlocks dim mult)

/-- The retained-coordinate partial trace is a left inverse of the normalized
retained-coordinate sector embedding.

Source: arXiv:1606.00608, Appendix C.4, lines 1962--1979. -/
theorem retainedVerticalSectorPartialTrace_comp_normalizedEmbedding
    {g : ℕ} (dim mult : Fin g → ℕ)
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (hMult : ∀ α, 0 < mult α) (hWeight : ∀ α q, (0 : ℂ) < weight α q) :
    (retainedVerticalSectorPartialTrace dim mult).comp
      (normalizedRetainedVerticalSectorEmbedding dim mult weight) =
        LinearMap.id := by
  apply LinearMap.ext
  intro X
  simp only [retainedVerticalSectorPartialTrace,
    normalizedRetainedVerticalSectorEmbedding, LinearMap.comp_apply]
  have hBlock := LinearMap.congr_fun
    (verticalSectorBlocks_comp_verticalSectorBlockDiagonal dim mult)
    (normalizedVerticalSectorEmbedding dim mult weight X)
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at hBlock
  rw [hBlock]
  exact LinearMap.congr_fun
    (verticalSectorPartialTrace_comp_normalizedVerticalSectorEmbedding
      dim mult weight hMult hWeight) X

/-- Scaling every sector matrix by its multiplicity trace before normalized
embedding gives the unnormalized weighted direct sum on the retained space.

Source: arXiv:1606.00608, Appendix C.4, lines 1962--1979. -/
theorem normalizedRetainedVerticalSectorEmbedding_trace_smul
    {g : ℕ} (dim mult : Fin g → ℕ)
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (hMult : ∀ α, 0 < mult α) (hWeight : ∀ α q, (0 : ℂ) < weight α q)
    (X : VerticalSectorAlgebra dim) :
    normalizedRetainedVerticalSectorEmbedding dim mult weight
        (fun α => verticalMultiplicityTrace weight α • X α) =
      verticalSectorBlockDiagonal dim mult (fun α =>
        Matrix.kroneckerMap (· * ·) (Matrix.diagonal (weight α)) (X α)) := by
  apply congrArg (verticalSectorBlockDiagonal dim mult)
  funext α i j
  simp only [normalizedVerticalSectorEmbedding_apply, Matrix.smul_apply,
    Matrix.kroneckerMap_apply, smul_eq_mul]
  field_simp [verticalMultiplicityTrace_ne_zero α (hMult α) (hWeight α)]

/-- Taking the retained-coordinate sector partial trace of an unnormalized
weighted direct sum multiplies each simple-sector matrix by the trace of its
multiplicity matrix.

Source: arXiv:1606.00608, Appendix C.4, lines 1962--1979. -/
theorem retainedVerticalSectorPartialTrace_weightedBlockDiagonal
    {g : ℕ} (dim mult : Fin g → ℕ)
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (X : VerticalSectorAlgebra dim) :
    retainedVerticalSectorPartialTrace dim mult
        (verticalSectorBlockDiagonal dim mult (fun α =>
          Matrix.kroneckerMap (· * ·) (Matrix.diagonal (weight α)) (X α))) =
      fun α => verticalMultiplicityTrace weight α • X α := by
  funext α i j
  simp only [retainedVerticalSectorPartialTrace, verticalSectorBlocks,
    verticalSectorBlockDiagonal, Matrix.reindex_apply, LinearMap.coe_mk,
    AddHom.coe_mk, LinearMap.coe_comp, Function.comp_apply,
    Matrix.submatrix_submatrix, verticalSectorPartialTrace_apply,
    Matrix.traceLeft_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.blockDiagonal'_apply_eq, Matrix.kroneckerMap_apply,
    Matrix.diagonal_apply_eq, verticalMultiplicityTrace, Matrix.smul_apply,
    smul_eq_mul]
  rw [Finset.sum_mul]

/-- The contracted assembled vertical tensor is the weighted direct sum
grouped by the vertical BNT labels.

Source: arXiv:1606.00608, Appendix C.4, lines 1955--1979. -/
theorem contractBondMatrix_verticalAssembledTensor_eq_sectorBlockDiagonal
    {g D : ℕ} (dim mult : Fin g → ℕ)
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (A : (α : Fin g) → MPSTensor (D * D) (dim α))
    (X : Matrix (Fin D) (Fin D) ℂ) :
    MPSTensor.contractBondMatrix (verticalAssembledTensor dim mult weight A) X =
      verticalSectorBlockDiagonal dim mult (fun α =>
        Matrix.kroneckerMap (· * ·) (Matrix.diagonal (weight α))
          (MPSTensor.contractBondMatrix (A α) X)) := by
  rw [contractBondMatrix_verticalAssembledTensor]
  ext i j
  obtain ⟨p, rfl⟩ := (verticalSectorFinEquiv dim mult).surjective i
  obtain ⟨q, rfl⟩ := (verticalSectorFinEquiv dim mult).surjective j
  rcases p with ⟨α, ⟨a, i⟩⟩
  rcases q with ⟨β, ⟨b, j⟩⟩
  by_cases hαβ : α = β
  · subst β
    by_cases hab : a = b
    · subst b
      let p := finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨α, a⟩)
      have hp : p = ⟨α, a⟩ := finSigmaFinEquiv.symm_apply_apply ⟨α, a⟩
      have hdim : dim p.1 = dim α := congrArg (fun q => dim q.1) hp
      have hweight : weight p.1 p.2 = weight α a :=
        congrArg (fun q => weight q.1 q.2) hp
      let contracted (q : Σ γ : Fin g, Fin (mult γ)) :=
        MPSTensor.contractBondMatrix (A q.1) X
      let packed (q : Σ γ : Fin g, Fin (mult γ)) :
          Σ r : Σ γ : Fin g, Fin (mult γ),
            Matrix (Fin (dim r.1)) (Fin (dim r.1)) ℂ :=
        ⟨q, contracted q⟩
      have hpacked : packed p = packed ⟨α, a⟩ := congrArg packed hp
      have hcontracted : HEq (contracted p) (contracted ⟨α, a⟩) :=
        (Sigma.mk.inj_iff.mp hpacked).2
      have hentry :=
        (Fin.heq_fun₂_iff hdim.symm hdim.symm).mp hcontracted.symm i j
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
        verticalSectorFinEquiv_outer_symm]
      rw [Matrix.blockDiagonal'_apply_eq]
      rw [verticalSectorBlockDiagonal_apply_same]
      simp only [verticalCopyWeights, verticalCopyBlocks]
      change weight p.1 p.2 * contracted p (Fin.cast _ i) (Fin.cast _ j) = _
      rw [hweight]
      simp only [Matrix.kroneckerMap_apply, Matrix.diagonal_apply_eq,
        contracted]
      congr 1
      exact hentry.symm
    · have hcopy : finSigmaFinEquiv ⟨α, a⟩ ≠
          finSigmaFinEquiv ⟨α, b⟩ := by
        intro h
        have hp := finSigmaFinEquiv.injective h
        cases hp
        exact hab rfl
      simp [verticalCopyWeights, verticalCopyBlocks,
        Matrix.reindex_apply, Matrix.submatrix_apply,
        Matrix.blockDiagonal'_apply_ne, Matrix.kroneckerMap_apply,
        hab, hcopy]
  · have hcopy : finSigmaFinEquiv ⟨α, a⟩ ≠
        finSigmaFinEquiv ⟨β, b⟩ := by
      intro h
      have hp := finSigmaFinEquiv.injective h
      cases hp
      exact hαβ rfl
    simp [verticalCopyWeights, verticalCopyBlocks,
      Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.blockDiagonal'_apply_ne, hαβ, hcopy]

/-- The refinement map on the finite direct products of vertical simple-sector
matrix algebras.

This is the composition \(\widetilde R_2 T_{\mathrm v} R_1\) from the source.
The partial trace defines it on the full retained matrix space; agreement with
the source formula is proved on the weighted block-diagonal image below.  No
image-preservation, inverse-map, complete-positivity, or trace-preservation
statement is part of this definition.

Source: arXiv:1606.00608, Appendix C.4, lines 1972--1979. -/
def transportedVerticalSectorT
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
    VerticalSectorAlgebra dim₁ →ₗ[ℂ] VerticalSectorAlgebra dim₂ :=
  retainedVerticalSectorPartialTrace dim₂ mult₂ ∘ₗ
    transportTToVerticalCoordinates U₁ U₂ T ∘ₗ
      normalizedRetainedVerticalSectorEmbedding dim₁ mult₁ weight₁

/-- The coarse-graining map on the finite direct products of vertical
simple-sector matrix algebras.

This is the composition \(\widetilde R_1 S_{\mathrm v} R_2\) from the source.
The partial trace defines it on the full retained matrix space; agreement with
the source formula is proved on the weighted block-diagonal image below.  No
image-preservation, inverse-map, complete-positivity, or trace-preservation
statement is part of this definition.

Source: arXiv:1606.00608, Appendix C.4, lines 1972--1979. -/
def transportedVerticalSectorS
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
    VerticalSectorAlgebra dim₂ →ₗ[ℂ] VerticalSectorAlgebra dim₁ :=
  retainedVerticalSectorPartialTrace dim₁ mult₁ ∘ₗ
    transportSToVerticalCoordinates U₁ U₂ S ∘ₗ
      normalizedRetainedVerticalSectorEmbedding dim₂ mult₂ weight₂

/-- The transported refinement map sends multiplicity-trace-scaled one-site
sector operators to the corresponding scaled two-site sector operators.

Source: arXiv:1606.00608, Appendix C.4, lines 1972--1979. -/
theorem transportedVerticalSectorT_trace_smul
    {g₁ g₂ d : ℕ}
    (dim₁ mult₁ : Fin g₁ → ℕ)
    (weight₁ : (α : Fin g₁) → Fin (mult₁ α) → ℂ)
    (dim₂ mult₂ : Fin g₂ → ℕ)
    (weight₂ : (β : Fin g₂) → Fin (mult₂ β) → ℂ)
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
    (X₁ : VerticalSectorAlgebra dim₁) (X₂ : VerticalSectorAlgebra dim₂)
    (hT : transportTToVerticalCoordinates U₁ U₂ T
        (verticalSectorBlockDiagonal dim₁ mult₁ (fun α =>
          Matrix.kroneckerMap (· * ·) (Matrix.diagonal (weight₁ α)) (X₁ α))) =
      verticalSectorBlockDiagonal dim₂ mult₂ (fun β =>
        Matrix.kroneckerMap (· * ·) (Matrix.diagonal (weight₂ β)) (X₂ β))) :
    transportedVerticalSectorT dim₁ mult₁ weight₁ dim₂ mult₂ U₁ U₂ T
        (fun α => verticalMultiplicityTrace weight₁ α • X₁ α) =
      fun β => verticalMultiplicityTrace weight₂ β • X₂ β := by
  simp only [transportedVerticalSectorT, LinearMap.comp_apply]
  rw [normalizedRetainedVerticalSectorEmbedding_trace_smul
    dim₁ mult₁ weight₁ hMult₁ hWeight₁ X₁]
  rw [hT]
  exact retainedVerticalSectorPartialTrace_weightedBlockDiagonal
    dim₂ mult₂ weight₂ X₂

/-- The transported coarse-graining map sends multiplicity-trace-scaled
two-site sector operators to the corresponding scaled one-site sector
operators.

Source: arXiv:1606.00608, Appendix C.4, lines 1972--1979. -/
theorem transportedVerticalSectorS_trace_smul
    {g₁ g₂ d : ℕ}
    (dim₁ mult₁ : Fin g₁ → ℕ)
    (weight₁ : (α : Fin g₁) → Fin (mult₁ α) → ℂ)
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
    (X₁ : VerticalSectorAlgebra dim₁) (X₂ : VerticalSectorAlgebra dim₂)
    (hS : transportSToVerticalCoordinates U₁ U₂ S
        (verticalSectorBlockDiagonal dim₂ mult₂ (fun β =>
          Matrix.kroneckerMap (· * ·) (Matrix.diagonal (weight₂ β)) (X₂ β))) =
      verticalSectorBlockDiagonal dim₁ mult₁ (fun α =>
        Matrix.kroneckerMap (· * ·) (Matrix.diagonal (weight₁ α)) (X₁ α))) :
    transportedVerticalSectorS dim₁ mult₁ dim₂ mult₂ weight₂ U₁ U₂ S
        (fun β => verticalMultiplicityTrace weight₂ β • X₂ β) =
      fun α => verticalMultiplicityTrace weight₁ α • X₁ α := by
  simp only [transportedVerticalSectorS, LinearMap.comp_apply]
  rw [normalizedRetainedVerticalSectorEmbedding_trace_smul
    dim₂ mult₂ weight₂ hMult₂ hWeight₂ X₂]
  rw [hS]
  exact retainedVerticalSectorPartialTrace_weightedBlockDiagonal
    dim₁ mult₁ weight₁ X₁

/-- On the operators obtained by contracting the one-site and two-site
vertical canonical forms, the normalized refinement map has the action stated
in Appendix C.4.

Source: arXiv:1606.00608, Appendix C.4, lines 1955--1979. -/
theorem transportedVerticalSectorT_contractBondMatrix_trace_smul
    {g₁ g₂ d D : ℕ}
    (dim₁ mult₁ : Fin g₁ → ℕ)
    (weight₁ : (α : Fin g₁) → Fin (mult₁ α) → ℂ)
    (dim₂ mult₂ : Fin g₂ → ℕ)
    (weight₂ : (β : Fin g₂) → Fin (mult₂ β) → ℂ)
    (hMult₁ : ∀ α, 0 < mult₁ α)
    (hWeight₁ : ∀ α q, (0 : ℂ) < weight₁ α q)
    (M : MPOTensor d D)
    (A₁ : (α : Fin g₁) → MPSTensor (D * D) (dim₁ α))
    (A₂ : (β : Fin g₂) → MPSTensor (D * D) (dim₂ β))
    (U₁ : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g₁, mult₁ α), verticalCopyDim dim₁ mult₁ q))
      (Fin d) ℂ)
    (U₂ : Matrix
      (Fin (∑ q : Fin (∑ β : Fin g₂, mult₂ β), verticalCopyDim dim₂ mult₂ q))
      (Fin (d * d)) ℂ)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hReconstruct₁ : ∀ ab, verticalTensor M ab =
      U₁ᴴ * verticalAssembledTensor dim₁ mult₁ weight₁ A₁ ab * U₁)
    (hForward₂ : ∀ ab, U₂ * verticalTensor (blockTwo M) ab * U₂ᴴ =
      verticalAssembledTensor dim₂ mult₂ weight₂ A₂ ab)
    (X : Matrix (Fin D) (Fin D) ℂ)
    (hT : T (physClose1 M X) = physClose2 M X) :
    transportedVerticalSectorT dim₁ mult₁ weight₁ dim₂ mult₂ U₁ U₂ T
        (fun α => verticalMultiplicityTrace weight₁ α •
          MPSTensor.contractBondMatrix (A₁ α) X) =
      fun β => verticalMultiplicityTrace weight₂ β •
        MPSTensor.contractBondMatrix (A₂ β) X := by
  apply transportedVerticalSectorT_trace_smul
    dim₁ mult₁ weight₁ dim₂ mult₂ weight₂ hMult₁ hWeight₁ U₁ U₂ T
  rw [← contractBondMatrix_verticalAssembledTensor_eq_sectorBlockDiagonal]
  rw [← contractBondMatrix_verticalAssembledTensor_eq_sectorBlockDiagonal]
  exact transportTToVerticalCoordinates_contractBondMatrix M
    (verticalAssembledTensor dim₁ mult₁ weight₁ A₁)
    (verticalAssembledTensor dim₂ mult₂ weight₂ A₂)
    U₁ U₂ T hReconstruct₁ hForward₂ X hT

/-- On the operators obtained by contracting the one-site and two-site
vertical canonical forms, the normalized coarse-graining map has the action
stated in Appendix C.4.

Source: arXiv:1606.00608, Appendix C.4, lines 1955--1979. -/
theorem transportedVerticalSectorS_contractBondMatrix_trace_smul
    {g₁ g₂ d D : ℕ}
    (dim₁ mult₁ : Fin g₁ → ℕ)
    (weight₁ : (α : Fin g₁) → Fin (mult₁ α) → ℂ)
    (dim₂ mult₂ : Fin g₂ → ℕ)
    (weight₂ : (β : Fin g₂) → Fin (mult₂ β) → ℂ)
    (hMult₂ : ∀ β, 0 < mult₂ β)
    (hWeight₂ : ∀ β q, (0 : ℂ) < weight₂ β q)
    (M : MPOTensor d D)
    (A₁ : (α : Fin g₁) → MPSTensor (D * D) (dim₁ α))
    (A₂ : (β : Fin g₂) → MPSTensor (D * D) (dim₂ β))
    (U₁ : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g₁, mult₁ α), verticalCopyDim dim₁ mult₁ q))
      (Fin d) ℂ)
    (U₂ : Matrix
      (Fin (∑ q : Fin (∑ β : Fin g₂, mult₂ β), verticalCopyDim dim₂ mult₂ q))
      (Fin (d * d)) ℂ)
    (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ)
    (hForward₁ : ∀ ab, U₁ * verticalTensor M ab * U₁ᴴ =
      verticalAssembledTensor dim₁ mult₁ weight₁ A₁ ab)
    (hReconstruct₂ : ∀ ab, verticalTensor (blockTwo M) ab =
      U₂ᴴ * verticalAssembledTensor dim₂ mult₂ weight₂ A₂ ab * U₂)
    (X : Matrix (Fin D) (Fin D) ℂ)
    (hS : S (physClose2 M X) = physClose1 M X) :
    transportedVerticalSectorS dim₁ mult₁ dim₂ mult₂ weight₂ U₁ U₂ S
        (fun β => verticalMultiplicityTrace weight₂ β •
          MPSTensor.contractBondMatrix (A₂ β) X) =
      fun α => verticalMultiplicityTrace weight₁ α •
        MPSTensor.contractBondMatrix (A₁ α) X := by
  apply transportedVerticalSectorS_trace_smul
    dim₁ mult₁ weight₁ dim₂ mult₂ weight₂ hMult₂ hWeight₂ U₁ U₂ S
  rw [← contractBondMatrix_verticalAssembledTensor_eq_sectorBlockDiagonal]
  rw [← contractBondMatrix_verticalAssembledTensor_eq_sectorBlockDiagonal]
  exact transportSToVerticalCoordinates_contractBondMatrix M
    (verticalAssembledTensor dim₁ mult₁ weight₁ A₁)
    (verticalAssembledTensor dim₂ mult₂ weight₂ A₂)
    U₁ U₂ S hForward₁ hReconstruct₂ X hS

end MPOTensor
