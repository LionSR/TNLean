/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Injectivity.SemiRegular.SemiRegularBondDimension

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

It also contains the following results.

* `TNLean.PEPS.positive_dimensions_of_sum_sq_eq_six`,
  `TNLean.PEPS.exists_smallestSemiRegular_dimension_four_of_order_six`: the smallest semi-regular
  dimension at noncommutative order six.
-/

section RegularFourierCommutativity

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

end RegularFourierCommutativity

section RegularOrderSixDimension

/-!
## The smallest semi-regular dimension at noncommutative order six

Positive integer dimensions with square-sum six and at least one dimension
larger than one consist of one two-dimensional sector and two one-dimensional
sectors. Applying this arithmetic to the actual regular Fourier decomposition
shows that every noncommutative finite group of order six has a unitary
multiplicity-one semi-regular representation of dimension four. Every
finite-dimensional complex semi-regular representation has dimension at least
four; the comparison representation need not be unitary.

These are auxiliary consequences of Schuch, Cirac, and Pérez-García,
arXiv:1001.3807, Section 7, `Papers/1001.3807/paper_v3.tex`, lines 2947–3019.
No irreducible-character table or classification of groups of order six is
assumed. The representation is the actual single-copy block construction
derived from the regular Fourier basis.
-/

open scoped BigOperators Matrix
namespace TNLean.PEPS

/-- A positive square-sum of six with a nontrivial dimension has precisely the
pattern 2,1,1 and dimension sum four. This arithmetic is auxiliary to the
single-copy construction in SCP10, Section 7, lines 2947–2988. -/
theorem positive_dimensions_of_sum_sq_eq_six {I : Type*} [Fintype I]
    (d : I → ℕ) (hd : ∀ i, 0 < d i) (hsq : ∑ i, d i ^ 2 = 6)
    (hlarge : ∃ i, 1 < d i) :
    ∃ j, d j = 2 ∧ (∀ i, i ≠ j → d i = 1) ∧
      Fintype.card I = 3 ∧ ∑ i, d i = 4 := by
  classical
  obtain ⟨j, hj⟩ := hlarge
  have hle (i : I) : d i ^ 2 ≤ 6 := by
    rw [← hsq]
    exact Finset.single_le_sum (f := fun k => d k ^ 2)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hjtwo : d j = 2 := by nlinarith [hle j]
  have hsplit := Finset.sum_erase_add (s := Finset.univ) (fun i => d i ^ 2)
    (Finset.mem_univ j)
  have herase : ∑ i ∈ Finset.univ.erase j, d i ^ 2 = 2 := by
    rw [hjtwo, hsq] at hsplit
    norm_num at hsplit
    omega
  have hone (i : I) (hi : i ≠ j) : d i = 1 := by
    have hi_mem : i ∈ Finset.univ.erase j := by simp [hi]
    have hi_le : d i ^ 2 ≤ 2 := by
      calc
        _ ≤ ∑ k ∈ Finset.univ.erase j, d k ^ 2 :=
          Finset.single_le_sum (f := fun k => d k ^ 2) (fun _ _ => Nat.zero_le _) hi_mem
        _ = 2 := herase
    nlinarith [hd i]
  have hsum : ∑ i ∈ Finset.univ.erase j, d i = 2 := by
    calc
      _ = ∑ i ∈ Finset.univ.erase j, d i ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [hone i (Finset.mem_erase.mp hi).1, one_pow]
      _ = 2 := herase
  have hcount : (Finset.univ.erase j).card = 2 := by
    have h := hsum
    simpa only [Finset.sum_congr rfl (fun i hi => hone i (Finset.mem_erase.mp hi).1),
      Finset.sum_const, smul_eq_mul, mul_one] using h
  refine ⟨j, hjtwo, hone, ?_, ?_⟩
  · have h := Finset.card_erase_add_one (Finset.mem_univ j)
    simpa only [hcount, Finset.card_univ] using h.symm
  · have h := Finset.sum_erase_add (s := Finset.univ) d (Finset.mem_univ j)
    rw [hsum, hjtwo] at h
    exact h.symm

universe u v
variable {G : Type u} [Group G] [Fintype G]

/-- A noncommutative finite group of order six determines an actual unitary
multiplicity-one semi-regular block representation of dimension four, and four
is no greater than the dimension of any finite-dimensional semi-regular
representation. Its irreducible dimensions are one 2 and two 1s.
Source: consequence of SCP10, Section 7, lines 2947–3019, using the regular
Fourier decomposition and the universal semi-regular dimension comparison. -/
theorem exists_smallestSemiRegular_dimension_four_of_order_six
    (hG : Fintype.card G = 6) (hnoncomm : ¬ ∀ g h : G, g * h = h * g) :
    ∃ (K : ℕ) (d : Fin K → ℕ)
      (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ),
      K = 3 ∧ (∀ i, 0 < d i) ∧
      (∃ j, d j = 2 ∧ ∀ i, i ≠ j → d i = 1) ∧
      Fintype.card (Σ i, Fin (d i)) = 4 ∧
      (∀ i g, D i g ∈ Matrix.unitaryGroup (Fin (d i)) ℂ) ∧
      (∀ i, Representation.IsIrreducible (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i))) ∧
      (∀ i j, i ≠ j →
        Representation.character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i)) ≠
          Representation.character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D j))) ∧
      (∀ g, blockMatrixRepresentation d D g ∈ Matrix.unitaryGroup (Σ i, Fin (d i)) ℂ) ∧
      Representation.IsSemiRegular
        (Matrix.toLinAlgEquiv'.toMonoidHom.comp (blockMatrixRepresentation d D)) ∧
      (∀ i, Representation.characterMultiplicity
        (Matrix.toLinAlgEquiv'.toMonoidHom.comp (blockMatrixRepresentation d D))
        (Representation.character (Matrix.toLinAlgEquiv'.toMonoidHom.comp (D i))) = 1) ∧
      ∀ (V : Type v) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
        (σ : Representation ℂ G V), σ.IsSemiRegular → 4 ≤ Module.finrank ℂ V := by
  classical
  obtain ⟨K, d, b, D, hd, hunit, hirr, hcross, hfourier, hUunit, hSemi, hmult⟩ :=
    exists_minimalSemiRegular_leftRegular_fourier (G := G)
  have hsq : ∑ i, d i ^ 2 = 6 := (card_eq_sum_sq_of_fourierBasis d b).symm.trans hG
  have hlarge := (exists_dimension_gt_one_iff_not_mul_comm_of_fourier
    d b D hd hirr hfourier).mpr hnoncomm
  obtain ⟨j, hj, hone, hK, hsum⟩ := positive_dimensions_of_sum_sq_eq_six d hd hsq hlarge
  refine ⟨K, d, D, by simpa using hK, hd, ⟨j, hj, hone⟩, ?_, hunit, hirr,
    hcross, hUunit, hSemi, hmult, ?_⟩
  · simpa only [Fintype.card_sigma, Fintype.card_fin] using hsum
  · intro V _ _ _ σ hσ
    have h := finrank_blockMatrixRepresentation_le_of_isSemiRegular d D hirr
      (Function.injective_iff_pairwise_ne.mpr hcross) σ hσ
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_sigma,
      Fintype.card_fin, hsum] using h

end TNLean.PEPS

end RegularOrderSixDimension
