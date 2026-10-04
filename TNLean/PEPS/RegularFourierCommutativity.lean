/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.SemiRegularBondDimension

/-!
# Strict dimension reduction and noncommutativity

In the actual regular Fourier decomposition, a sector has dimension greater
than one exactly when the finite group is noncommutative. Consequently, the
smallest semi-regular representation has dimension strictly less than the
regular representation exactly for noncommutative groups.

This is a mathematical consequence of the construction in SCP10, Section 7,
lines 2947–2988, rather than a separately printed theorem. The dimension-one
statement for irreducibles of a commutative group is Mathlib's Schur-lemma
corollary. The converse uses the faithful regular representation and its
actual Fourier basis.
-/

open scoped Matrix Kronecker
namespace TNLean.PEPS
open Representation
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

private theorem matrix_mul_comm_of_dimension_one {d : ℕ} (hd : d = 1)
    (A B : Matrix (Fin d) (Fin d) ℂ) : A * B = B * A := by
  have : Subsingleton (Fin d) := by rw [hd]; infer_instance
  ext i j
  simp only [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Subsingleton.elim i k, Subsingleton.elim j k, mul_comm]

/-- Some sector in the actual regular Fourier decomposition has dimension greater
than one precisely when the group is noncommutative. Mathematical consequence of
SCP10, Section 7, lines 2947–2988. -/
theorem exists_dimension_gt_one_iff_not_mul_comm_of_fourier
    {I : Type*} [Fintype I] [DecidableEq I] (d : I → ℕ)
    (b : OrthonormalBasis (Σ i, Fin (d i) × Fin (d i)) ℂ (EuclideanSpace ℂ G))
    (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i)
    (hirr : ∀ i, IsIrreducible (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i)))
    (hfourier : ∀ g, LinearMap.toMatrix b.toBasis b.toBasis
      (euclideanMatrixRepresentation (leftRegularMatrix G) g) =
      multiplicityRestoredRepresentation d D g) :
    (∃ i, 1 < d i) ↔ ¬ ∀ g h : G, g * h = h * g := by
  classical
  constructor
  · rintro ⟨i, hi⟩ hcomm
    have : IsMulCommutative G := isMulCommutative_iff.mpr hcomm
    have := hirr i
    have hone : d i = 1 := by
      simpa using IsIrreducible.finrank_eq_one_of_isMulCommutative
        (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i))
    omega
  · intro hnoncomm
    by_contra hdim
    have hone : ∀ i, d i = 1 := by
      intro i
      have hpos := hd i
      have hnot : ¬ 1 < d i := fun hi => hdim ⟨i, hi⟩
      omega
    let ρ := euclideanMatrixRepresentation (leftRegularMatrix G)
    have hfaithful : Function.Injective ρ :=
      (linearIndependent_of_isSemiRegular ρ
        (isSemiRegular_leftRegular.of_equiv (leftRegularEuclideanMatrixEquiv (G := G)))).injective
    apply hnoncomm
    intro g h
    apply hfaithful
    apply (LinearMap.toMatrixAlgEquiv b.toBasis).injective
    change LinearMap.toMatrix b.toBasis b.toBasis
      (euclideanMatrixRepresentation (leftRegularMatrix G) (g * h)) =
      LinearMap.toMatrix b.toBasis b.toBasis
        (euclideanMatrixRepresentation (leftRegularMatrix G) (h * g))
    rw [hfourier, hfourier]
    change Matrix.blockDiagonal' (fun i => D i (g * h) ⊗ₖ (1 : Matrix _ _ ℂ)) =
      Matrix.blockDiagonal' (fun i => D i (h * g) ⊗ₖ (1 : Matrix _ _ ℂ))
    congr 1
    funext i
    rw [map_mul, map_mul, matrix_mul_comm_of_dimension_one (hone i)]

/-- The single-copy Fourier dimension is strictly smaller than the group order
precisely for noncommutative groups. Mathematical consequence of SCP10,
Section 7, lines 2947–2988. -/
theorem sum_dimensions_lt_card_iff_not_mul_comm_of_fourier
    {I : Type*} [Fintype I] [DecidableEq I] (d : I → ℕ)
    (b : OrthonormalBasis (Σ i, Fin (d i) × Fin (d i)) ℂ (EuclideanSpace ℂ G))
    (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i)
    (hirr : ∀ i, IsIrreducible (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i)))
    (hfourier : ∀ g, LinearMap.toMatrix b.toBasis b.toBasis
      (euclideanMatrixRepresentation (leftRegularMatrix G) g) =
      multiplicityRestoredRepresentation d D g) :
    (∑ i, d i) < Fintype.card G ↔ ¬ ∀ g h : G, g * h = h * g :=
  (bondDimensions_of_fourierBasis d hd b).2.2.2.trans
    (exists_dimension_gt_one_iff_not_mul_comm_of_fourier d b D hd hirr hfourier)

universe v

omit [DecidableEq G] in
/-- A group-derived smallest semi-regular representation has strictly smaller
virtual dimension than the regular representation exactly when the group is
noncommutative. Mathematical consequence of SCP10, Section 7, lines 2947–2988. -/
theorem exists_smallestSemiRegular_dimension_strict_iff_not_mul_comm :
    ∃ (K : ℕ) (d : Fin K → ℕ)
      (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ),
      (∀ i, 0 < d i) ∧
      (∀ g, blockMatrixRepresentation d D g ∈
        Matrix.unitaryGroup (Σ i, Fin (d i)) ℂ) ∧
      IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (blockMatrixRepresentation d D)) ∧
      ((∑ i, d i) < Fintype.card G ↔ ¬ ∀ g h : G, g * h = h * g) ∧
      ∀ (V : Type v) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
        (σ : Representation ℂ G V), σ.IsSemiRegular →
        (∑ i, d i) ≤ Module.finrank ℂ V := by
  classical
  obtain ⟨K, d, b, D, hd, hunit, hirr, hcross, hFourier, hUunit, hSemi, hmult⟩ :=
    exists_minimalSemiRegular_leftRegular_fourier (G := G)
  refine ⟨K, d, D, hd, hUunit, hSemi,
    sum_dimensions_lt_card_iff_not_mul_comm_of_fourier d b D hd hirr hFourier, ?_⟩
  intro V _ _ _ σ hσ
  simpa using finrank_blockMatrixRepresentation_le_of_isSemiRegular d D hirr
    (Function.injective_iff_pairwise_ne.mpr hcross) σ hσ
end TNLean.PEPS
