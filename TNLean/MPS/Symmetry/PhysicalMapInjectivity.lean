/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.Injectivity
import Mathlib.LinearAlgebra.Matrix.Rank
import TNLean.Algebra.RectangularPolar

/-!
# The physical coefficient matrix of an injective tensor

The coefficient matrix of a matrix product tensor has one row per physical
letter and one column per pair of virtual indices. Full column rank of this
matrix implies the one-site spanning condition for its letters.
This is the matrix interpretation used in the polar deformation of
Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.D.2.
-/

open scoped Matrix MatrixOrder ComplexOrder

namespace MPSTensor

/-- The physical map, with virtual matrix entries arranged as columns.
Source: arXiv:1010.3732, Section II.D.2, `eq:1d-iso:polardec`. -/
def physicalCoefficientMatrix {d D : ℕ}
    (A : Fin d → Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Fin d) (Fin D × Fin D) ℂ :=
  fun i p => A i p.1 p.2

/-- Interpret a physical coefficient matrix as a family of virtual matrices. -/
def tensorOfPhysicalCoefficientMatrix {d D : ℕ}
    (P : Matrix (Fin d) (Fin D × Fin D) ℂ) :
    Fin d → Matrix (Fin D) (Fin D) ℂ :=
  fun i a b => P i (a, b)

@[simp]
theorem physicalCoefficientMatrix_tensorOfPhysicalCoefficientMatrix
    {d D : ℕ} (P : Matrix (Fin d) (Fin D × Fin D) ℂ) :
    physicalCoefficientMatrix (tensorOfPhysicalCoefficientMatrix P) = P := rfl

/-- Currying identifies virtual-pair vectors with virtual matrices. -/
def virtualPairMatrixEquiv (D : ℕ) :
    ((Fin D × Fin D) → ℂ) ≃ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ where
  toFun v := fun i j => v (i, j)
  invFun M := fun p => M p.1 p.2
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem map_physicalRowSpan {d D : ℕ}
    (A : Fin d → Matrix (Fin D) (Fin D) ℂ) :
    Submodule.map (virtualPairMatrixEquiv D).toLinearMap
      (Submodule.span ℂ (Set.range (physicalCoefficientMatrix A).row)) =
      Submodule.span ℂ (Set.range A) := by
  rw [Submodule.map_span]
  congr 1
  ext M
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨v, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨(physicalCoefficientMatrix A).row i, ⟨i, rfl⟩, rfl⟩

/-- Full column rank of the physical coefficient matrix implies that the
letters span the complete virtual matrix algebra. Source: arXiv:1010.3732,
Section II.D.2, injectivity preceding `eq:1d-iso:polardec`. -/
theorem isInjective_of_physicalCoefficientMatrix_mulVec_injective
    {d D : ℕ} (A : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (h : Function.Injective (physicalCoefficientMatrix A).mulVec) :
    Kraus.IsInjective A := by
  let P := physicalCoefficientMatrix A
  have hrank : P.rank = Fintype.card (Fin D × Fin D) := by
    rw [Matrix.rank]
    exact (LinearMap.finrank_range_of_inj h).trans
      (Module.finrank_eq_card_basis (Pi.basisFun ℂ (Fin D × Fin D)))
  have hrows : Submodule.span ℂ (Set.range P.row) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank_eq_finrank_span_row, hrank]
    exact (Module.finrank_eq_card_basis (Pi.basisFun ℂ (Fin D × Fin D))).symm
  unfold Kraus.IsInjective
  rw [← map_physicalRowSpan A, hrows]
  simp only [Submodule.map_top, LinearEquiv.range]

/-- One-site injectivity gives full column rank of the physical coefficient
matrix. Together with the converse above, this identifies the spanning
condition with the polar-decomposition hypothesis of arXiv:1010.3732,
Section II.D.2. -/
theorem physicalCoefficientMatrix_mulVec_injective_of_isInjective
    {d D : ℕ} (A : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hA : Kraus.IsInjective A) :
    Function.Injective (physicalCoefficientMatrix A).mulVec := by
  let P := physicalCoefficientMatrix A
  have hrows : Submodule.span ℂ (Set.range P.row) = ⊤ := by
    apply (Submodule.map_injective_of_injective
      (virtualPairMatrixEquiv D).injective)
    rw [map_physicalRowSpan A, hA, Submodule.map_top, LinearEquiv.range]
  have hrank : P.rank = Fintype.card (Fin D × Fin D) := by
    rw [Matrix.rank_eq_finrank_span_row, hrows, finrank_top]
    exact Module.finrank_eq_card_basis (Pi.basisFun ℂ (Fin D × Fin D))
  have hker : Module.finrank ℂ (LinearMap.ker P.mulVecLin) = 0 := by
    have hsum := LinearMap.finrank_range_add_finrank_ker P.mulVecLin
    rw [← Matrix.rank] at hsum
    rw [hrank, Module.finrank_eq_card_basis (Pi.basisFun ℂ (Fin D × Fin D))] at hsum
    omega
  exact (LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hker))

/-- The symmetric polar interpolation of a full-column-rank physical map
is an injective one-site tensor at each parameter in the unit interval.
This is the pointwise injectivity step, separate from a uniform
parent-Hamiltonian gap. Source: arXiv:1010.3732, Section II.D.2. -/
theorem isInjective_tensorOf_isometric_polarInterpolant
    {d D : ℕ}
    {W : Matrix (Fin d) (Fin D × Fin D) ℂ}
    {Q : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ}
    (hW : Wᴴ * W = 1) (hQ : Q.PosDef)
    {γ : ℝ} (hγ₀ : 0 ≤ γ) (hγ₁ : γ ≤ 1) :
    Kraus.IsInjective
      (tensorOfPhysicalCoefficientMatrix (W * Matrix.polarInterpolant Q γ)) := by
  apply isInjective_of_physicalCoefficientMatrix_mulVec_injective
  simpa only [physicalCoefficientMatrix_tensorOfPhysicalCoefficientMatrix] using
    Matrix.isometric_mul_posDef_mulVec_injective hW
      (Matrix.polarInterpolant_posDef hQ hγ₀ hγ₁)

/-- Each local polar interpolant is normal, so an individual parent
Hamiltonian has a finite-range gap. Uniformity over the parameter requires
additional estimates. -/
theorem isNormal_tensorOf_isometric_polarInterpolant
    {d D : ℕ}
    {W : Matrix (Fin d) (Fin D × Fin D) ℂ}
    {Q : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ}
    (hW : Wᴴ * W = 1) (hQ : Q.PosDef)
    {γ : ℝ} (hγ₀ : 0 ≤ γ) (hγ₁ : γ ≤ 1) :
    Kraus.IsNormal
      (tensorOfPhysicalCoefficientMatrix (W * Matrix.polarInterpolant Q γ)) :=
  (isInjective_tensorOf_isometric_polarInterpolant hW hQ hγ₀ hγ₁).isNormal

/-- Every one-site injective tensor whose physical coefficient map
intertwines unitary actions has a continuous, symmetric, one-site injective
polar deformation to an isometric physical map. Source:
Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.D.2.

The theorem is local. It does not assert a uniform spectral gap for the
associated parent Hamiltonians. -/
theorem exists_symmetric_injective_polar_tensor_path
    {d D : ℕ} (A : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hA : Kraus.IsInjective A)
    (U : Matrix (Fin d) (Fin d) ℂ)
    (R : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hR : R ∈ Matrix.unitaryGroup (Fin D × Fin D) ℂ)
    (hsym : U * physicalCoefficientMatrix A = physicalCoefficientMatrix A * R) :
    ∃ (Q : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)
      (W : Matrix (Fin d) (Fin D × Fin D) ℂ),
      Q.PosDef ∧ Wᴴ * W = 1 ∧
      A = tensorOfPhysicalCoefficientMatrix (W * Matrix.polarInterpolant Q 1) ∧
      (∀ γ : ℝ, 0 ≤ γ → γ ≤ 1 →
        Kraus.IsInjective
          (tensorOfPhysicalCoefficientMatrix (W * Matrix.polarInterpolant Q γ))) ∧
      Continuous (fun γ : ℝ => W * Matrix.polarInterpolant Q γ) ∧
      Continuous (fun γ : ℝ =>
        tensorOfPhysicalCoefficientMatrix (W * Matrix.polarInterpolant Q γ)) ∧
      (∀ γ : ℝ, U * (W * Matrix.polarInterpolant Q γ) =
        (W * Matrix.polarInterpolant Q γ) * R) := by
  obtain ⟨Q, W, hQ, hW, hPend, _, _, hcont, _, hsympath⟩ :=
    Matrix.exists_symmetric_polar_deformation_of_injective
      (physicalCoefficientMatrix A)
      (physicalCoefficientMatrix_mulVec_injective_of_isInjective A hA)
      U R hU hR hsym
  refine ⟨Q, W, hQ, hW, ?_, ?_, hcont, ?_, hsympath⟩
  · simpa only [← hPend] using
      (show A = tensorOfPhysicalCoefficientMatrix (physicalCoefficientMatrix A) from rfl)
  · intro γ hγ₀ hγ₁
    exact isInjective_tensorOf_isometric_polarInterpolant hW hQ hγ₀ hγ₁
  · apply continuous_pi
    intro i
    apply continuous_matrix
    intro a b
    exact hcont.matrix_elem i (a, b)

end MPSTensor
