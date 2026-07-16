/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
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

/-- The ambient block space containing
`span {μ_α} ⊗ M_{dim α}` for every vertical BNT label.

Source: arXiv:1606.00608, Appendix C.4, lines 1957--1961. -/
abbrev VerticalWeightedSectorSpace {g : ℕ} (dim mult : Fin g → ℕ) :=
  (α : Fin g) → Matrix (Fin (mult α) × Fin (dim α))
    (Fin (mult α) × Fin (dim α)) ℂ

/-- The trace of the diagonal multiplicity matrix
`diag (weight α)`, namely `m_α = ∑_q weight α q`.

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
sector blocks:
`X_α ↦ (diag (weight α) / m_α) ⊗ X_α`.

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

/-- Partial trace over each multiplicity factor, extending the inverse map
`λ_α μ_α ⊗ X_α ↦ λ_α m_α X_α` from the weighted sectors to
their ambient block spaces.

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
