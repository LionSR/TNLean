/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.FixedPoint.DirectSumKraus
import TNLean.Channel.PartialTrace
import TNLean.MPS.MPDO.Defs

/-!
# Normalized vertical-sector embeddings and partial-trace retractions

For a vertical canonical decomposition with multiplicity matrices
\(\mu_\alpha\), Appendix C.4 introduces the normalized maps
\[
  X_\alpha \longmapsto
    \frac{\mu_\alpha}{\operatorname{tr}(\mu_\alpha)}\otimes X_\alpha
\]
and their inverse maps on the displayed weighted sectors.  Partial trace over
the multiplicity factor gives a canonical extension of the inverse map to the
full block matrix space.  The maps below satisfy the exact retraction identity.
The construction depends only on the sector dimensions, multiplicities, and
positive weights, and therefore applies to either vertical canonical
decomposition in Appendix C.4.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Appendix C.4, lines 1957--1971.
-/

open scoped BigOperators ComplexOrder Matrix

noncomputable section

namespace MPOTensor

/-- The direct product of the simple matrix algebras carried by the vertical
BNT labels.

Source: arXiv:1606.00608, Appendix C.4, lines 1957--1961. -/
abbrev VerticalSectorAlgebra {g : ℕ} (dim : Fin g → ℕ) :=
  (α : Fin g) → Matrix (Fin (dim α)) (Fin (dim α)) ℂ

/-- The ambient block space whose \(\alpha\)-component contains
\(\operatorname{span}\{\mu_\alpha\}\otimes M_{d_\alpha}\).

Source: arXiv:1606.00608, Appendix C.4, lines 1957--1961. -/
abbrev VerticalWeightedSectorSpace {g : ℕ} (dim mult : Fin g → ℕ) :=
  (α : Fin g) → Matrix (Fin (mult α) × Fin (dim α))
    (Fin (mult α) × Fin (dim α)) ℂ

/-- The sum \(m_\alpha=\sum_q\mu_{\alpha,q}\) of the diagonal entries of
the multiplicity matrix \(\mu_\alpha\), equal to
\(\operatorname{tr}(\mu_\alpha)\).

Source: arXiv:1606.00608, Appendix C.4, lines 1955--1971. -/
def verticalMultiplicityTrace {g : ℕ} {mult : Fin g → ℕ}
    (weight : (α : Fin g) → Fin (mult α) → ℂ) (α : Fin g) : ℂ :=
  ∑ q, weight α q

/-- Positivity and nonempty multiplicity imply that the multiplicity trace is
nonzero.

Source: arXiv:1606.00608, Proposition 4.13, lines 1901--1921, and
Appendix C.4, lines 1955--1971. -/
theorem verticalMultiplicityTrace_ne_zero {g : ℕ} {mult : Fin g → ℕ}
    {weight : (α : Fin g) → Fin (mult α) → ℂ}
    (α : Fin g) (hMult : 0 < mult α) (hWeight : ∀ q, (0 : ℂ) < weight α q) :
    verticalMultiplicityTrace weight α ≠ 0 := by
  apply ne_of_gt
  apply Finset.sum_pos'
  · intro q _
    exact (hWeight q).le
  · let q : Fin (mult α) := ⟨0, hMult⟩
    exact ⟨q, Finset.mem_univ q, hWeight q⟩

/-- The normalized embedding of the vertical sector algebra into the weighted
sector blocks, mapping
\(X_\alpha\mapsto m_\alpha^{-1}\mu_\alpha\otimes X_\alpha\) on each sector.

Source: arXiv:1606.00608, Appendix C.4, lines 1962--1971. -/
def normalizedVerticalSectorEmbedding {g : ℕ} (dim mult : Fin g → ℕ)
    (weight : (α : Fin g) → Fin (mult α) → ℂ) :
    VerticalSectorAlgebra dim →ₗ[ℂ] VerticalWeightedSectorSpace dim mult where
  toFun X α := (verticalMultiplicityTrace weight α)⁻¹ •
    Matrix.kroneckerMap (· * ·) (Matrix.diagonal (weight α)) (X α)
  map_add' X Y := by
    funext α i j
    simp [Matrix.kroneckerMap_apply, mul_add]
  map_smul' c X := by
    funext α i j
    simp [Matrix.kroneckerMap_apply]
    ring

@[simp]
theorem normalizedVerticalSectorEmbedding_apply {g : ℕ} (dim mult : Fin g → ℕ)
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (X : VerticalSectorAlgebra dim) (α : Fin g) :
    normalizedVerticalSectorEmbedding dim mult weight X α =
      (verticalMultiplicityTrace weight α)⁻¹ •
        Matrix.kroneckerMap (· * ·) (Matrix.diagonal (weight α)) (X α) :=
  rfl

/-- Partial trace over each multiplicity factor, extending the inverse map from
the weighted sectors to their ambient block spaces. On a weighted sector it
satisfies
\(\widetilde R_\mu(\lambda_\alpha\mu_\alpha\otimes X_\alpha)
=\lambda_\alpha m_\alpha X_\alpha\).

Source: arXiv:1606.00608, Appendix C.4, lines 1962--1971. -/
def verticalSectorPartialTrace {g : ℕ} (dim mult : Fin g → ℕ) :
    VerticalWeightedSectorSpace dim mult →ₗ[ℂ] VerticalSectorAlgebra dim where
  toFun Y α := Matrix.traceLeft (Y α)
  map_add' X Y := by
    funext α
    exact Matrix.traceLeft_add (X α) (Y α)
  map_smul' c X := by
    funext α
    exact Matrix.traceLeft_smul c (X α)

@[simp]
theorem verticalSectorPartialTrace_apply {g : ℕ} (dim mult : Fin g → ℕ)
    (Y : VerticalWeightedSectorSpace dim mult) (α : Fin g) :
    verticalSectorPartialTrace dim mult Y α = Matrix.traceLeft (Y α) :=
  rfl

/-- Exchange the multiplicity and simple-matrix coordinates within every
vertical sector.

Source: arXiv:1606.00608, Appendix C.4, lines 1961--1970. -/
def verticalSectorSwapEquiv {g : ℕ} (dim mult : Fin g → ℕ) :
    (Σ α, Fin (mult α) × Fin (dim α)) ≃
      (Σ α, Fin (dim α) × Fin (mult α)) where
  toFun x := ⟨x.1, x.2.swap⟩
  invFun x := ⟨x.1, x.2.swap⟩
  left_inv x := by
    obtain ⟨α, i, j⟩ := x
    rfl
  right_inv x := by
    obtain ⟨α, i, j⟩ := x
    rfl

/-- The normalized embedding of the simple vertical-sector algebras is
completely positive as a map between finite sums of matrix algebras.

Source: arXiv:1606.00608, Appendix C.4, lines 1957--1968. -/
theorem normalizedVerticalSectorEmbedding_isKrausDirectSumMap
    {g : ℕ} (dim mult : Fin g → ℕ)
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (hMult : ∀ α, 0 < mult α)
    (hWeight : ∀ α q, (0 : ℂ) < weight α q) :
    Matrix.IsKrausDirectSumMap
      (normalizedVerticalSectorEmbedding dim mult weight) := by
  let ρ : (α : Fin g) → Matrix (Fin (mult α)) (Fin (mult α)) ℂ :=
    fun α ↦ (verticalMultiplicityTrace weight α)⁻¹ •
      Matrix.diagonal (weight α)
  have hTrace (α : Fin g) : 0 < verticalMultiplicityTrace weight α := by
    apply Finset.sum_pos'
    · intro q _
      exact (hWeight α q).le
    · let q : Fin (mult α) := ⟨0, hMult α⟩
      exact ⟨q, Finset.mem_univ q, hWeight α q⟩
  have hρ (α : Fin g) : (ρ α).PosSemidef := by
    dsimp only [ρ]
    exact (Matrix.PosSemidef.diagonal (fun q ↦ (hWeight α q).le)).smul
      (inv_nonneg.mpr (hTrace α).le)
  have hρTrace (α : Fin g) : Matrix.trace (ρ α) = 1 := by
    simp only [ρ, Matrix.trace_smul, Matrix.trace_diagonal]
    change (verticalMultiplicityTrace weight α)⁻¹ *
      verticalMultiplicityTrace weight α = 1
    field_simp [ne_of_gt (hTrace α)]
  let P :
      Matrix (Σ α, Fin (dim α)) (Σ α, Fin (dim α)) ℂ →ₗ[ℂ]
        Matrix (Σ α, Fin (dim α) × Fin (mult α))
          (Σ α, Fin (dim α) × Fin (mult α)) ℂ :=
    Matrix.controlledKrausMap
      (fun α ↦ Fintype.card (Fin (mult α)))
      (fun α j ↦ Matrix.preparationKraus (ρ α) (hρ α)
        ((Fintype.equivFin (Fin (mult α))).symm j))
  have hP : IsKrausCPTP P := by
    dsimp only [P]
    apply Matrix.controlledKrausMap_isKrausCPTP
    intro α
    exact Matrix.preparationKraus_resolution (ρ α) (hρ α) (hρTrace α)
  change IsKrausCP
    (Matrix.directSumMapExtension
      (normalizedVerticalSectorEmbedding dim mult weight))
  rw [show Matrix.directSumMapExtension
      (normalizedVerticalSectorEmbedding dim mult weight) =
        Matrix.equivReindexMap (verticalSectorSwapEquiv dim mult).symm ∘ₗ P by
    apply LinearMap.ext
    intro Z
    ext ⟨α, ⟨q, i⟩⟩ ⟨β, ⟨s, j⟩⟩
    by_cases hαβ : α = β
    · subst β
      simp only [Matrix.directSumMapExtension_apply,
        Matrix.directSumDiagonalEmbedding_apply,
        Matrix.blockDiagonal'_apply_eq,
        normalizedVerticalSectorEmbedding_apply,
        Matrix.directSumDiagonalCompression_apply,
        Matrix.smul_apply,
        Matrix.kroneckerMap_apply,
        LinearMap.comp_apply,
        Matrix.equivReindexMap,
        LinearEquiv.coe_toLinearMap,
        Matrix.coe_reindexLinearEquiv,
        Matrix.reindex_apply,
        Matrix.submatrix_apply,
        verticalSectorSwapEquiv]
      change _ = P Z ⟨α, (i, q)⟩ ⟨α, (j, s)⟩
      dsimp only [P]
      rw [Matrix.controlledKrausMap_sameBlock_apply,
        Matrix.rectangularKrausMap_equiv
          (Fintype.equivFin (Fin (mult α))),
        Matrix.rectangularKrausMap_preparationKraus_eq]
      change _ = Matrix.kroneckerMap (fun x y : ℂ ↦ x * y)
        (Z.submatrix (Sigma.mk α) (Sigma.mk α)) (ρ α) (i, q) (j, s)
      simp only [Matrix.kroneckerMap_apply, Matrix.submatrix_apply, ρ,
        Matrix.smul_apply, smul_eq_mul]
      ring
    · rw [Matrix.directSumMapExtension_apply,
        Matrix.directSumDiagonalEmbedding_apply,
        Matrix.blockDiagonal'_apply_ne _ _ _ hαβ]
      simp only [LinearMap.comp_apply, Matrix.equivReindexMap,
        LinearEquiv.coe_toLinearMap, Matrix.coe_reindexLinearEquiv,
        Matrix.reindex_apply, verticalSectorSwapEquiv]
      change 0 = P Z ⟨α, (i, q)⟩ ⟨β, (j, s)⟩
      dsimp only [P]
      rw [Matrix.controlledKrausMap_apply_of_ne _ _ _ hαβ]]
  exact isKrausCP_comp hP.isKrausCP
    (Matrix.equivReindexMap_isKrausCPTP
      (verticalSectorSwapEquiv dim mult).symm).isKrausCP

/-- Partial trace over the multiplicity coordinate is completely positive as
a map between the finite sums of vertical-sector matrix algebras.

Source: arXiv:1606.00608, Appendix C.4, lines 1961--1970. -/
theorem verticalSectorPartialTrace_isKrausDirectSumMap
    {g : ℕ} (dim mult : Fin g → ℕ) :
    Matrix.IsKrausDirectSumMap
      (verticalSectorPartialTrace dim mult) := by
  change IsKrausCP
    (Matrix.directSumMapExtension (verticalSectorPartialTrace dim mult))
  rw [show Matrix.directSumMapExtension (verticalSectorPartialTrace dim mult) =
      Matrix.controlledPartialTraceRightLM
          (α := fun α : Fin g ↦ Fin (dim α))
          (β := fun α : Fin g ↦ Fin (mult α)) ∘ₗ
        Matrix.equivReindexMap (verticalSectorSwapEquiv dim mult) by
    apply LinearMap.ext
    intro Y
    ext ⟨α, i⟩ ⟨β, j⟩
    by_cases hαβ : α = β
    · subst β
      simp only [Matrix.directSumMapExtension_apply,
        Matrix.directSumDiagonalEmbedding_apply,
        Matrix.blockDiagonal'_apply_eq,
        verticalSectorPartialTrace_apply,
        Matrix.directSumDiagonalCompression_apply,
        Matrix.traceLeft_apply,
        LinearMap.comp_apply,
        Matrix.controlledPartialTraceRightLM_sameBlock_apply,
        Matrix.partialTraceRight_apply,
        Matrix.submatrix_apply,
        Matrix.equivReindexMap,
        LinearEquiv.coe_toLinearMap,
        Matrix.coe_reindexLinearEquiv,
        Matrix.reindex_apply,
        verticalSectorSwapEquiv]
      rfl
    · rw [Matrix.directSumMapExtension_apply,
        Matrix.directSumDiagonalEmbedding_apply,
        Matrix.blockDiagonal'_apply_ne _ _ _ hαβ,
        LinearMap.comp_apply,
        Matrix.controlledPartialTraceRightLM,
        Matrix.controlledKrausMap_apply_of_ne _ _ _ hαβ]]
  exact isKrausCP_comp
    (Matrix.equivReindexMap_isKrausCPTP
      (verticalSectorSwapEquiv dim mult)).isKrausCP
    (Matrix.controlledPartialTraceRightLM_isKrausCPTP
      (α := fun α : Fin g ↦ Fin (dim α))
      (β := fun α : Fin g ↦ Fin (mult α))).isKrausCP

/-- Partial trace is a left inverse of the normalized vertical-sector
embedding.

Source: arXiv:1606.00608, Appendix C.4, lines 1962--1971. -/
theorem verticalSectorPartialTrace_comp_normalizedVerticalSectorEmbedding
    {g : ℕ} (dim mult : Fin g → ℕ)
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (hMult : ∀ α, 0 < mult α) (hWeight : ∀ α q, (0 : ℂ) < weight α q) :
    (verticalSectorPartialTrace dim mult).comp
      (normalizedVerticalSectorEmbedding dim mult weight) = LinearMap.id := by
  apply LinearMap.ext
  intro X
  funext α
  ext i j
  simp only [LinearMap.comp_apply, verticalSectorPartialTrace_apply,
    normalizedVerticalSectorEmbedding_apply, Matrix.traceLeft_smul,
    Matrix.traceLeft_kronecker, Matrix.trace_diagonal, Matrix.smul_apply]
  rw [show ∑ x, weight α x = verticalMultiplicityTrace weight α by rfl]
  simp only [smul_eq_mul, LinearMap.id_apply]
  field_simp [verticalMultiplicityTrace_ne_zero α (hMult α) (hWeight α)]

end MPOTensor
