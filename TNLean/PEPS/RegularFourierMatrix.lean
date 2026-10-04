/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularMinimalRepresentation


/-!
# Actual matrix coordinates of the regular Fourier decomposition

Every finite group determines positive irreducible dimensions dᵢ, unitary
irreducible representations Dᵢ with distinct characters, and an isometric
matrix Q such that the original left-regular matrices are
Q (⊕ᵢ Dᵢ(g) ⊗ I_{dᵢ}) Q†. Their single-copy sum is unitary and semi-regular,
with character multiplicity one in every sector.

These choices depend only on the finite group, with no lattice geometry in the
statement. Source: SCP10, arXiv:1001.3807, Section 7, lines 2947–3019.
-/

noncomputable section
open scoped Matrix
namespace TNLean.PEPS
private theorem fourier_matrix_intertwiner
    {G K : Type*} [Group G] [Fintype G] [DecidableEq G]
    [Fintype K] [DecidableEq K]
    (U : G →* Matrix G G ℂ) (L : G →* Matrix K K ℂ)
    (b : OrthonormalBasis K ℂ (EuclideanSpace ℂ G))
    (hb : ∀ g, LinearMap.toMatrix b.toBasis b.toBasis (Matrix.toEuclideanLin (U g)) = L g) :
    ∃ Q : Matrix G K ℂ, Q.IsIsometry ∧ ∀ g, U g = Q * L g * Q.conjTranspose := by
  let c := EuclideanSpace.basisFun G ℂ
  let Q := c.toBasis.toMatrix b
  have hQ : Q.IsIsometry := c.toMatrix_orthonormalBasis_conjTranspose_mul_self b
  have hInv : Q.conjTranspose = b.toBasis.toMatrix c := by
    calc
      _ = (b.toBasis.toMatrix c * Q) * Q.conjTranspose := by
        rw [show b.toBasis.toMatrix c * Q = 1 from
          Module.Basis.toMatrix_mul_toMatrix_flip b.toBasis c.toBasis, Matrix.one_mul]
      _ = _ := by
        rw [Matrix.mul_assoc, c.toMatrix_orthonormalBasis_self_mul_conjTranspose b,
          Matrix.mul_one]
  refine ⟨Q, hQ, ?_⟩
  intro g
  have h := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
    c.toBasis b.toBasis c.toBasis b.toBasis (Matrix.toEuclideanLin (U g))
  rw [hb] at h
  rw [hInv]
  simpa only [Q, c, OrthonormalBasis.coe_toBasis, Matrix.toEuclideanLin_eq_toLin_orthonormal,
    LinearMap.toMatrix_toLin] using h.symm

/-- Positive sector dimensions give the single-copy dimension and its comparison
with the sum of their squares. Source: SCP10, Section 7, lines 2955–2988. -/
theorem positive_dimension_bounds {I : Type*} [Fintype I]
    (d : I → ℕ) (hd : ∀ i, 0 < d i) :
    Fintype.card (Σ i, Fin (d i)) = ∑ i, d i ∧
    (∑ i, d i) ≤ ∑ i, d i ^ 2 ∧
    ((∑ i, d i) < ∑ i, d i ^ 2 ↔ ∃ i, 1 < d i) := by
  have hle (i) : d i ≤ d i ^ 2 := by nlinarith [hd i]
  refine ⟨by simp only [Fintype.card_sigma, Fintype.card_fin],
    Finset.sum_le_sum (fun i _ => hle i), ?_⟩
  constructor
  · intro h
    by_contra hn
    have heq (i) : d i = 1 := by
      have hi := hd i
      have hnot : ¬ 1 < d i := fun h => hn ⟨i, h⟩
      omega
    simp only [heq, one_pow] at h
    exact (lt_irrefl _) h
  · rintro ⟨i, hi⟩
    exact Finset.sum_lt_sum (fun j _ => hle j)
      ⟨i, Finset.mem_univ _, by nlinarith⟩

/-- An actual regular matrix intertwiner identifies the regular dimension with
the sum of the squared irreducible dimensions.
Source: SCP10, Section 7, lines 2947–2954. -/
theorem card_eq_sum_sq_of_regular_intertwiner
    {G I : Type*} [Group G] [Fintype G] [DecidableEq G] [Fintype I] [DecidableEq I]
    (d : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (Q : Matrix G (Σ i, Fin (d i) × Fin (d i)) ℂ) (hQ : Q.IsIsometry)
    (hreg : ∀ g, leftRegularMatrix G g =
      Q * multiplicityRestoredRepresentation d D g * Q.conjTranspose) :
    Fintype.card G = ∑ i, d i ^ 2 := by
  have hco : Q.IsCoisometry := by
    change Q * Q.conjTranspose = 1
    have h := hreg 1
    simpa only [map_one, Matrix.mul_one] using h.symm
  have hcard := Nat.le_antisymm (Matrix.IsIsometry.card_le Q hQ)
    (Matrix.IsCoisometry.card_le Q hco)
  simpa only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin, pow_two]
    using hcard.symm


/-- The actual regular matrix decomposition has regular dimension ∑ᵢdᵢ² and
single-copy dimension ∑ᵢdᵢ; strict reduction is equivalent to some dᵢ > 1.
Source: SCP10, Section 7, lines 2947–2988. -/
theorem bondDimensions_of_regular_intertwiner
    {G I : Type*} [Group G] [Fintype G] [DecidableEq G] [Fintype I] [DecidableEq I]
    (d : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i) (Q : Matrix G (Σ i, Fin (d i) × Fin (d i)) ℂ)
    (hQ : Q.IsIsometry)
    (hreg : ∀ g, leftRegularMatrix G g =
      Q * multiplicityRestoredRepresentation d D g * Q.conjTranspose) :
    Fintype.card G = ∑ i, d i ^ 2 ∧
    Fintype.card (Σ i, Fin (d i)) = ∑ i, d i ∧
    (∑ i, d i) ≤ Fintype.card G ∧
    ((∑ i, d i) < Fintype.card G ↔ ∃ i, 1 < d i) := by
  have hcard := card_eq_sum_sq_of_regular_intertwiner d D Q hQ hreg
  rw [hcard]
  exact ⟨rfl, positive_dimension_bounds d hd⟩

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- A finite group determines the actual unitary matrix Fourier coordinates and
the corresponding multiplicity-one semi-regular representation.
Source: SCP10, Section 7, lines 2947–3019. -/
theorem exists_minimalSemiRegular_leftRegular_matrix :
    ∃ (K : ℕ) (d : Fin K → ℕ)
      (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
      (Q : Matrix G (Σ i, Fin (d i) × Fin (d i)) ℂ),
      (∀ i, 0 < d i) ∧
      (∀ i g, D i g ∈ Matrix.unitaryGroup (Fin (d i)) ℂ) ∧
      (∀ i, Representation.IsIrreducible (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i))) ∧
      (∀ i j, i ≠ j →
        Representation.character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i)) ≠
          Representation.character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D j))) ∧
      Q.IsIsometry ∧
      (∀ g, leftRegularMatrix G g =
        Q * multiplicityRestoredRepresentation d D g * Q.conjTranspose) ∧
      (∀ g, blockMatrixRepresentation d D g ∈ Matrix.unitaryGroup (Σ i, Fin (d i)) ℂ) ∧
      Representation.IsSemiRegular
        (Matrix.toLinAlgEquiv'.toMonoidHom.comp (blockMatrixRepresentation d D)) ∧
      (∀ i, Representation.characterMultiplicity
        (Matrix.toLinAlgEquiv'.toMonoidHom.comp (blockMatrixRepresentation d D))
        (Representation.character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i))) = 1) := by
  obtain ⟨K, d, b, D, hd, hunit, hirr, hcross, hFourier, hUunit, hSemi, hmult⟩ :=
    exists_minimalSemiRegular_leftRegular_fourier (G := G)
  obtain ⟨Q, hQ, hreg⟩ := fourier_matrix_intertwiner
    (leftRegularMatrix G) (multiplicityRestoredRepresentation d D) b hFourier
  exact ⟨K, d, D, Q, hd, hunit, hirr, hcross, hQ, hreg, hUunit, hSemi, hmult⟩
end TNLean.PEPS
