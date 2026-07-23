/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.EigenvectorProjection
import TNLean.MPS.MPDO.TopologicalDensityDecomposition

/-!
# Spectral families of terminal matrices

The positive terminal matrices of a tensor-attached BNT fusion clause have
rank-one spectral decompositions. This file indexes all eigenvectors across
all BNT labels, including zero-eigenvalue modes, and extends each eigenvector
projection by zero to the other labels.

## Main statements

* `MPOTensor.BNTFusionTensorClause.terminalEigenvalue_nonneg`: every terminal
  eigenvalue is nonnegative.
* `MPOTensor.BNTFusionTensorClause.terminalEigenvectorProjection_isOrthogonalProjection`:
  the zero-extended family consists pointwise of orthogonal projections.
* `MPOTensor.BNTFusionTensorClause.terminalEigenvectorProjection_mul_eq_zero_of_ne`:
  distinct spectral indices give pointwise orthogonal projections.
* `MPOTensor.BNTFusionTensorClause.sum_terminalEigenvectorProjection`: the
  projections resolve the identity on every final bond space.
* `MPOTensor.BNTFusionTensorClause.terminalMatrix_eq_sum`: the
  eigenvalue-weighted family reconstructs every terminal matrix.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  lines 1010--1012
-/

open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace MPOTensor.BNTFusionTensorClause

variable {d D : ℕ} {M : MPOTensor d D}

/-- The dependent type of a final BNT label together with one eigenvector
index of its terminal matrix. Zero-eigenvalue modes are retained.

Source: arXiv:1606.00608, lines 1010--1012. -/
abbrev TerminalSpectralIndex (H : BNTFusionTensorClause M) :=
  (γ : Fin H.labelCount) × Fin (H.bondDim γ)

/-- The terminal matrix obtained by closing the horizontal operator leg of a
final BNT tensor and leaving its bond indices open.

Source: arXiv:1606.00608, lines 1010--1012. -/
def terminalMatrix (H : BNTFusionTensorClause M) (γ : Fin H.labelCount) :
    Matrix (Fin (H.bondDim γ)) (Fin (H.bondDim γ)) ℂ :=
  physTraceTransfer (verticalBNTMPO (H.tensor γ))

/-- Every terminal matrix of an MPDO BNT fusion clause is positive
semidefinite.

Source: arXiv:1606.00608, lines 1010--1012. -/
theorem terminalMatrix_posSemidef
    (H : BNTFusionTensorClause M) (hM : IsMPDO M) (γ : Fin H.labelCount) :
    (H.terminalMatrix γ).PosSemidef :=
  H.physTraceTransfer_verticalBNTMPO_posSemidef hM γ

/-- The eigenvalue attached to a terminal spectral index. The definition
retains zero eigenvalues.

Source: arXiv:1606.00608, lines 1010--1012. -/
def terminalEigenvalue
    (H : BNTFusionTensorClause M) (hM : IsMPDO M)
    (s : H.TerminalSpectralIndex) : ℝ :=
  (H.terminalMatrix_posSemidef hM s.1).isHermitian.eigenvalues s.2

/-- Every terminal eigenvalue is nonnegative; zero modes remain members of
the indexed family.

Source: arXiv:1606.00608, lines 1010--1012. -/
theorem terminalEigenvalue_nonneg
    (H : BNTFusionTensorClause M) (hM : IsMPDO M)
    (s : H.TerminalSpectralIndex) :
    0 ≤ H.terminalEigenvalue hM s :=
  (H.terminalMatrix_posSemidef hM s.1).eigenvalues_nonneg s.2

/-- The rank-one projection onto one eigenvector of a fixed terminal matrix.

Source: arXiv:1606.00608, lines 1010--1012. -/
def terminalEigenvectorProjectionAt
    (H : BNTFusionTensorClause M) (hM : IsMPDO M)
    (γ : Fin H.labelCount) (k : Fin (H.bondDim γ)) :
    Matrix (Fin (H.bondDim γ)) (Fin (H.bondDim γ)) ℂ :=
  (H.terminalMatrix_posSemidef hM γ).isHermitian.eigenvectorProjection k

/-- Every local terminal eigenvector projection is an orthogonal projection.

Source: arXiv:1606.00608, lines 1010--1012. -/
theorem terminalEigenvectorProjectionAt_isOrthogonalProjection
    (H : BNTFusionTensorClause M) (hM : IsMPDO M)
    (γ : Fin H.labelCount) (k : Fin (H.bondDim γ)) :
    IsOrthogonalProjection (H.terminalEigenvectorProjectionAt hM γ k) :=
  (H.terminalMatrix_posSemidef hM γ).isHermitian
    |>.isOrthogonalProjection_eigenvectorProjection k

/-- A terminal eigenvector projection extended by zero to every different BNT
label.

Source: arXiv:1606.00608, lines 1010--1012. -/
def terminalEigenvectorProjection
    (H : BNTFusionTensorClause M) (hM : IsMPDO M)
    (s : H.TerminalSpectralIndex) (γ : Fin H.labelCount) :
    Matrix (Fin (H.bondDim γ)) (Fin (H.bondDim γ)) ℂ :=
  if h : s.1 = γ then
    h ▸ H.terminalEigenvectorProjectionAt hM s.1 s.2
  else
    0

/-- On its own BNT label, the zero-extended projection is the corresponding
local eigenvector projection.

Source: arXiv:1606.00608, lines 1010--1012. -/
@[simp]
theorem terminalEigenvectorProjection_same
    (H : BNTFusionTensorClause M) (hM : IsMPDO M)
    (γ : Fin H.labelCount) (k : Fin (H.bondDim γ)) :
    H.terminalEigenvectorProjection hM ⟨γ, k⟩ γ =
      H.terminalEigenvectorProjectionAt hM γ k := by
  simp [terminalEigenvectorProjection]

/-- On a different BNT label, an extended terminal eigenvector projection
vanishes.

Source: arXiv:1606.00608, lines 1010--1012. -/
@[simp]
theorem terminalEigenvectorProjection_of_ne
    (H : BNTFusionTensorClause M) (hM : IsMPDO M)
    (δ γ : Fin H.labelCount) (k : Fin (H.bondDim δ)) (hδγ : δ ≠ γ) :
    H.terminalEigenvectorProjection hM ⟨δ, k⟩ γ = 0 := by
  simp [terminalEigenvectorProjection, hδγ]

/-- The zero-extended terminal spectral family consists pointwise of
orthogonal projections.

Source: arXiv:1606.00608, lines 1010--1012. -/
theorem terminalEigenvectorProjection_isOrthogonalProjection
    (H : BNTFusionTensorClause M) (hM : IsMPDO M)
    (s : H.TerminalSpectralIndex) (γ : Fin H.labelCount) :
    IsOrthogonalProjection (H.terminalEigenvectorProjection hM s γ) := by
  rcases s with ⟨δ, k⟩
  by_cases hδγ : δ = γ
  · subst γ
    simpa using H.terminalEigenvectorProjectionAt_isOrthogonalProjection hM δ k
  · simp [H.terminalEigenvectorProjection_of_ne hM δ γ k hδγ,
      IsOrthogonalProjection]

/-- Distinct terminal spectral indices give orthogonal projections at every
BNT label.

Source: arXiv:1606.00608, lines 1010--1012. -/
theorem terminalEigenvectorProjection_mul_eq_zero_of_ne
    (H : BNTFusionTensorClause M) (hM : IsMPDO M)
    (s t : H.TerminalSpectralIndex) (hst : s ≠ t)
    (γ : Fin H.labelCount) :
    H.terminalEigenvectorProjection hM s γ *
        H.terminalEigenvectorProjection hM t γ = 0 := by
  rcases s with ⟨δ, k⟩
  rcases t with ⟨ε, l⟩
  by_cases hδγ : δ = γ
  · subst γ
    by_cases hεδ : ε = δ
    · subst ε
      have hkl : k ≠ l := by
        intro hkl
        subst l
        exact hst rfl
      simpa [terminalEigenvectorProjectionAt] using
        ((H.terminalMatrix_posSemidef hM δ).isHermitian
          |>.eigenvectorProjection_mul_eq_zero_of_ne hkl)
    · simp [H.terminalEigenvectorProjection_of_ne hM ε δ l hεδ]
  · simp [H.terminalEigenvectorProjection_of_ne hM δ γ k hδγ]

/-- The terminal eigenvector projections resolve the identity on every final
bond space.

Source: arXiv:1606.00608, lines 1010--1012. -/
theorem sum_terminalEigenvectorProjection
    (H : BNTFusionTensorClause M) (hM : IsMPDO M)
    (γ : Fin H.labelCount) :
    ∑ s : H.TerminalSpectralIndex,
        H.terminalEigenvectorProjection hM s γ = 1 := by
  rw [Fintype.sum_sigma, Finset.sum_eq_single γ]
  · simpa [terminalEigenvectorProjectionAt] using
      (H.terminalMatrix_posSemidef hM γ).isHermitian.sum_eigenvectorProjection
  · intro δ _ hδγ
    simp [H.terminalEigenvectorProjection_of_ne hM δ γ _ hδγ]
  · simp

/-- The terminal matrix at each BNT label is the eigenvalue-weighted sum of
the zero-extended eigenvector projections. Zero-eigenvalue modes remain in
the sum and contribute zero.

Source: arXiv:1606.00608, lines 1010--1012. -/
theorem terminalMatrix_eq_sum
    (H : BNTFusionTensorClause M) (hM : IsMPDO M)
    (γ : Fin H.labelCount) :
    H.terminalMatrix γ =
      ∑ s : H.TerminalSpectralIndex,
        H.terminalEigenvalue hM s •
          H.terminalEigenvectorProjection hM s γ := by
  rw [Fintype.sum_sigma, Finset.sum_eq_single γ]
  · simpa [terminalEigenvalue, terminalEigenvectorProjectionAt] using
      (H.terminalMatrix_posSemidef hM γ).isHermitian
        |>.eq_sum_eigenvalues_smul_eigenvectorProjection
  · intro δ _ hδγ
    simp [H.terminalEigenvectorProjection_of_ne hM δ γ _ hδγ]
  · simp

end MPOTensor.BNTFusionTensorClause
