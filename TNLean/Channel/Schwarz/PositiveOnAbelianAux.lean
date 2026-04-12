/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Basic
import TNLean.Channel.Schwarz.PositiveMapProperties
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Positive maps on abelian domains — auxiliary infrastructure

This companion file contains the definitions and proof infrastructure for
positivity on commuting matrix domains (Wolf Proposition 1.6):

* Core definitions: `BlockPositive`, `PairwiseCommuteImages`,
  `blockQuadraticForm`, `IsPositiveOnCommuting`.
* Normal-matrix generator commutativity (`NormalGenerators`).
* Diagonal-family Schwarz inequality (`DiagonalFamily`).
* Block amplification via simultaneous diagonalization, proving
  `quadraticForm_nonneg_of_isPositiveMap_of_commuting_images` (Wolf Prop 1.6).

The normal-operator diagonalization and the main interface theorem
`map_conjTranspose_mul_map_le_of_normal_of_subunital` (Wolf Prop 5.1)
are in `PositiveOnAbelian.lean`.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators TNMatrixCFC
open Matrix Finset Complex Module.End

namespace PositiveOnAbelian

variable {D : ℕ}

/-- Multiplicativity of `Matrix.toEuclideanLin`: lifting matrix multiplication to the
Euclidean linear map level. -/
lemma toEuclideanLin_mul (A B : Matrix (Fin D) (Fin D) ℂ) :
    (Matrix.toEuclideanLin A : EuclideanSpace ℂ (Fin D) →ₗ[ℂ] EuclideanSpace ℂ (Fin D)) *
      Matrix.toEuclideanLin B = Matrix.toEuclideanLin (A * B) := by
  simp only [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact (Matrix.toLin_mul (EuclideanSpace.basisFun (Fin D) ℂ).toBasis
    (EuclideanSpace.basisFun (Fin D) ℂ).toBasis
    (EuclideanSpace.basisFun (Fin D) ℂ).toBasis A B).symm

/-- Quadratic-form positivity for a block matrix with matrix entries.

This is the concrete finite-dimensional formulation of positivity used in the
current file: for every block vector `ψ`, the quadratic form of the block matrix
is nonnegative. -/
def BlockPositive {n D : ℕ}
    (a : Matrix (Fin n) (Fin n) (Matrix (Fin D) (Fin D) ℂ)) : Prop :=
  ∀ ψ : Fin n → Fin D → ℂ,
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, star (ψ i) ⬝ᵥ (a i j).mulVec (ψ j)

/-- The block images of `a` under `T` commute pairwise. -/
def PairwiseCommuteImages {n D : ℕ}
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (a : Matrix (Fin n) (Fin n) (Matrix (Fin D) (Fin D) ℂ)) : Prop :=
  ∀ i j k l, Commute (T (a i j)) (T (a k l))

/-- The quadratic form obtained after applying a linear map `T` blockwise. -/
noncomputable def blockQuadraticForm {n D : ℕ}
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (a : Matrix (Fin n) (Fin n) (Matrix (Fin D) (Fin D) ℂ))
    (ψ : Fin n → Fin D → ℂ) : ℂ :=
  ∑ i : Fin n, ∑ j : Fin n, star (ψ i) ⬝ᵥ (T (a i j)).mulVec (ψ j)

/-- A map is **positive on commuting block families** if it preserves
block-quadratic-form positivity whenever the image family is pairwise commuting.

This is the concrete stand-in for "the restriction to a commutative
`*`-subalgebra is completely positive" that is sufficient for the normal-input
Schwarz argument used later in the project. -/
def IsPositiveOnCommuting
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) : Prop :=
  ∀ {n : ℕ} (a : Matrix (Fin n) (Fin n) (Matrix (Fin D) (Fin D) ℂ)),
    BlockPositive a →
    PairwiseCommuteImages T a →
    ∀ ψ : Fin n → Fin D → ℂ, 0 ≤ blockQuadraticForm T a ψ

section NormalGenerators

variable {A : Matrix (Fin D) (Fin D) ℂ}

/-- A normal matrix commutes with its adjoint. -/
lemma commute_conjTranspose_of_normal
    (hA : Aᴴ * A = A * Aᴴ) : Commute A Aᴴ := by
  simpa [Commute] using hA.symm

/-- For a normal matrix `A`, the generator `A` commutes with `Aᴴ * A`. -/
private lemma commute_conjTranspose_mul_self_of_normal
    (hA : Aᴴ * A = A * Aᴴ) : Commute A (Aᴴ * A) :=
  (commute_conjTranspose_of_normal (A := A) hA).mul_right (Commute.refl A)

/-- For a normal matrix `A`, the generator `Aᴴ` commutes with `Aᴴ * A`. -/
private lemma conjTranspose_commute_conjTranspose_mul_self_of_normal
    (hA : Aᴴ * A = A * Aᴴ) : Commute Aᴴ (Aᴴ * A) :=
  (Commute.refl Aᴴ).mul_right
    (Commute.symm (commute_conjTranspose_of_normal (A := A) hA))

/-- For a normal matrix `A`, the generators `{A, Aᴴ, Aᴴ * A, 1}` commute pairwise. -/
private lemma normal_generators_pairwise_commute
    (hA : Aᴴ * A = A * Aᴴ) :
    Commute A Aᴴ ∧
      Commute A (Aᴴ * A) ∧
      Commute A (1 : Matrix (Fin D) (Fin D) ℂ) ∧
      Commute Aᴴ (Aᴴ * A) ∧
      Commute Aᴴ (1 : Matrix (Fin D) (Fin D) ℂ) ∧
      Commute (Aᴴ * A) (1 : Matrix (Fin D) (Fin D) ℂ) :=
  ⟨commute_conjTranspose_of_normal (A := A) hA,
   commute_conjTranspose_mul_self_of_normal (A := A) hA,
   Commute.one_right A,
   conjTranspose_commute_conjTranspose_mul_self_of_normal (A := A) hA,
   Commute.one_right Aᴴ,
   Commute.one_right (Aᴴ * A)⟩

end NormalGenerators

section DiagonalFamily

/-- A rectangular Kraus-type map `X ↦ ∑ᵢ Kᵢ X Kᵢ†`. -/
private noncomputable def rectKrausMap {ι m n : Type*}
    [Fintype ι] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (K : ι → Matrix m n ℂ) (X : Matrix n n ℂ) : Matrix m m ℂ :=
  ∑ i : ι, K i * X * (K i)ᴴ

/-- Kadison--Schwarz for a unital rectangular Kraus family. -/
private lemma rect_kadison_schwarz_le
    {ι m n : Type*} [Fintype ι] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (K : ι → Matrix m n ℂ)
    (h_unital : ∑ i : ι, K i * (K i)ᴴ = (1 : Matrix m m ℂ))
    (X : Matrix n n ℂ) :
    (rectKrausMap K X)ᴴ * rectKrausMap K X ≤ rectKrausMap K (Xᴴ * X) := by
  classical
  let P : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
    Matrix.fromBlocks (Xᴴ * X) Xᴴ X 1
  have hP : P.PosSemidef := by
    let A : Matrix (n ⊕ n) (n ⊕ Fin 0) ℂ :=
      Matrix.fromBlocks Xᴴ 0 1 0
    simpa [A, P, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose] using
      Matrix.posSemidef_self_mul_conjTranspose A
  let K₂ : ι → Matrix (m ⊕ m) (n ⊕ n) ℂ :=
    fun i => Matrix.fromBlocks (K i) 0 0 (K i)
  have h_term (i : ι) :
      K₂ i * P * (K₂ i)ᴴ =
        Matrix.fromBlocks (K i * (Xᴴ * X) * (K i)ᴴ) (K i * Xᴴ * (K i)ᴴ)
          (K i * X * (K i)ᴴ) (K i * (K i)ᴴ) := by
    simp [K₂, P, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose, Matrix.mul_assoc]
  have h_sum_psd : (∑ i : ι, K₂ i * P * (K₂ i)ᴴ).PosSemidef :=
    Matrix.posSemidef_sum (s := Finset.univ) (x := fun i => K₂ i * P * (K₂ i)ᴴ)
      (fun i _ => hP.mul_mul_conjTranspose_same (B := K₂ i))
  -- Key identity: the block sum equals the expected block matrix.
  have h_sfb :
      ∀ (A' B' C' D' : ι → Matrix m m ℂ),
        (∑ i : ι, Matrix.fromBlocks (A' i) (B' i) (C' i) (D' i)) =
          Matrix.fromBlocks (∑ i : ι, A' i) (∑ i : ι, B' i)
            (∑ i : ι, C' i) (∑ i : ι, D' i) := by
    intros A' B' C' D'
    ext i j
    rcases i with i' | i' <;> rcases j with j' | j' <;>
      simp [Matrix.sum_apply]
  have h_block_eq :
      (∑ i : ι, K₂ i * P * (K₂ i)ᴴ) =
        Matrix.fromBlocks (rectKrausMap K (Xᴴ * X)) ((rectKrausMap K X)ᴴ)
          ((rectKrausMap K X)ᴴᴴ) (1 : Matrix m m ℂ) := by
    simp_rw [h_term]
    rw [h_sfb]
    exact Matrix.fromBlocks_inj.mpr
      ⟨by simp [rectKrausMap],
       by calc
           (∑ i : ι, K i * Xᴴ * (K i)ᴴ) = rectKrausMap K Xᴴ := by simp [rectKrausMap]
           _ = (rectKrausMap K X)ᴴ := by
               simp [rectKrausMap, Matrix.conjTranspose_sum,
                 Matrix.conjTranspose_mul, Matrix.mul_assoc],
       by simp [rectKrausMap, conjTranspose_conjTranspose],
       by simpa using h_unital⟩
  have h_block_psd :
      (Matrix.fromBlocks (rectKrausMap K (Xᴴ * X)) ((rectKrausMap K X)ᴴ)
        ((rectKrausMap K X)ᴴᴴ) (1 : Matrix m m ℂ)).PosSemidef := by
    simpa [h_block_eq] using h_sum_psd
  haveI : Invertible (1 : Matrix m m ℂ) := invertibleOne
  rw [Matrix.le_iff]
  simpa [inv_one, Matrix.mul_assoc, conjTranspose_conjTranspose] using
    (Matrix.PosDef.fromBlocks₂₂ (A := rectKrausMap K (Xᴴ * X))
      (B := (rectKrausMap K X)ᴴ) (D := (1 : Matrix m m ℂ)) Matrix.PosDef.one).1 h_block_psd

/-- The single-column Kraus operators used to package a finite positive family as a
unital rectangular Kraus map after adjoining one zero coordinate. -/
private noncomputable def familyMainKraus {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : ι → Matrix (Fin D) (Fin D) ℂ) (ip : ι × Fin D) :
    Matrix (Fin D) (Option ι) ℂ :=
  fun r o => if o = some ip.1 then C ip.1 r ip.2 else 0

/-- The defect Kraus operators supported on the adjoined zero coordinate. -/
private noncomputable def familyDefectKraus {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix (Fin D) (Fin D) ℂ) (p : Fin D) : Matrix (Fin D) (Option ι) ℂ :=
  fun r o => if o = none then S r p else 0

/-- The full unital Kraus family attached to a finite PSD family and its defect. -/
private noncomputable def familyKraus {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : ι → Matrix (Fin D) (Fin D) ℂ) (S : Matrix (Fin D) (Fin D) ℂ) :
    ((ι × Fin D) ⊕ Fin D) → Matrix (Fin D) (Option ι) ℂ
  | Sum.inl ip => familyMainKraus C ip
  | Sum.inr p => familyDefectKraus S p

private lemma familyMain_term_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : ι → Matrix (Fin D) (Fin D) ℂ) (z : ι → ℂ) (i : ι) (p : Fin D) :
    rectKrausMap (fun _ : Unit => familyMainKraus C (i, p))
      (Matrix.diagonal (fun o : Option ι => o.elim 0 z))
      = z i • (familyMainKraus C (i, p) * (familyMainKraus C (i, p))ᴴ) := by
  ext r s
  simp only [rectKrausMap, univ_unique, PUnit.default_eq_unit, sum_const, card_singleton,
    smul_apply, Matrix.mul_apply, familyMainKraus, diagonal_apply, mul_ite, ite_mul, zero_mul,
    mul_zero, sum_ite_eq', mem_univ, ↓reduceIte, conjTranspose_apply, RCLike.star_def,
    Option.elim_some, one_smul, smul_eq_mul]
  ring

private lemma familyMain_outer_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : ι → Matrix (Fin D) (Fin D) ℂ) (i : ι) :
    (∑ p : Fin D, familyMainKraus C (i, p) * (familyMainKraus C (i, p))ᴴ) = C i * (C i)ᴴ := by
  ext r s
  have hL :
      (∑ p : Fin D, familyMainKraus C (i, p) * (familyMainKraus C (i, p))ᴴ) r s =
        ∑ p : Fin D, C i r p * (starRingEnd ℂ) (C i s p) := by
    simp [Matrix.sum_apply, familyMainKraus, Matrix.mul_apply]
  rw [hL]
  simp [Matrix.mul_apply]

private lemma familyDefect_outer_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix (Fin D) (Fin D) ℂ) :
    (∑ p : Fin D, familyDefectKraus (ι := ι) S p * (familyDefectKraus (ι := ι) S p)ᴴ) =
      S * Sᴴ := by
  ext r s
  have hL :
      ((∑ p : Fin D,
          familyDefectKraus (ι := ι) S p * (familyDefectKraus (ι := ι) S p)ᴴ)) r s =
        ∑ p : Fin D, S r p * (starRingEnd ℂ) (S s p) := by
    simp [Matrix.sum_apply, familyDefectKraus, Matrix.mul_apply]
  rw [hL]
  simp [Matrix.mul_apply]

private lemma familyDefect_term_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix (Fin D) (Fin D) ℂ) (z : ι → ℂ) (p : Fin D) :
    rectKrausMap (fun _ : Unit => familyDefectKraus (ι := ι) S p)
      (Matrix.diagonal (fun o : Option ι => o.elim 0 z)) = 0 := by
  ext r s
  simp [rectKrausMap, familyDefectKraus, Matrix.mul_apply, Matrix.diagonal_apply]

/-- The diagonal / finite-spectrum Schwarz inequality for a positive family
`{Bᵢ}` with `∑ᵢ Bᵢ ≤ 1`. This is the direct diagonal case needed for the
normal-input Schwarz inequality. -/
theorem diagonal_family_schwarz_le
    {ι : Type*} [Fintype ι]
    (B : ι → Matrix (Fin D) (Fin D) ℂ)
    (hB : ∀ i, (B i).PosSemidef)
    (hsub : ∑ i, B i ≤ (1 : Matrix (Fin D) (Fin D) ℂ))
    (z : ι → ℂ) :
    (∑ i, (starRingEnd ℂ (z i)) • B i) * (∑ i, z i • B i)
      ≤ ∑ i, ((starRingEnd ℂ (z i)) * z i) • B i := by
  classical
  have hBfac : ∀ i, ∃ C : Matrix (Fin D) (Fin D) ℂ, B i = C * Cᴴ := by
    intro i
    exact CStarAlgebra.nonneg_iff_eq_mul_star_self.mp
      ((Matrix.nonneg_iff_posSemidef).mpr (hB i))
  choose C hC using hBfac
  have hdef_psd : (1 - ∑ i, B i).PosSemidef := by
    rw [← Matrix.nonneg_iff_posSemidef]
    exact sub_nonneg.mpr hsub
  obtain ⟨S, hS⟩ := CStarAlgebra.nonneg_iff_eq_mul_star_self.mp
    ((Matrix.nonneg_iff_posSemidef).mpr hdef_psd)
  let K : ((ι × Fin D) ⊕ Fin D) → Matrix (Fin D) (Option ι) ℂ := familyKraus C S
  let X : Matrix (Option ι) (Option ι) ℂ := Matrix.diagonal (fun o : Option ι => o.elim 0 z)
  have hK_unital : ∑ a, K a * (K a)ᴴ = (1 : Matrix (Fin D) (Fin D) ℂ) := by
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
    calc
      (∑ x, ∑ x_1, K (Sum.inl (x, x_1)) * (K (Sum.inl (x, x_1)))ᴴ) +
          ∑ x, K (Sum.inr x) * (K (Sum.inr x))ᴴ = (∑ x, C x * (C x)ᴴ) + S * Sᴴ := by
              simp [K, familyKraus, familyMain_outer_sum, familyDefect_outer_sum]
      _ = (∑ x, B x) + (1 - ∑ i, B i) := by
            have hS' : S * Sᴴ = 1 - ∑ i, B i := by
              simpa [Matrix.star_eq_conjTranspose] using hS.symm
            simp [hC, hS']
      _ = 1 := by simp [sub_eq_add_neg, add_comm]
  have hMainTerm (i : ι) (p : Fin D) :
      familyMainKraus C (i, p) * X * (familyMainKraus C (i, p))ᴴ =
        z i • (familyMainKraus C (i, p) * (familyMainKraus C (i, p))ᴴ) := by
    simpa [X, rectKrausMap] using familyMain_term_eq (C := C) (z := z) i p
  have hDefTerm (p : Fin D) :
      familyDefectKraus (ι := ι) S p * X * (familyDefectKraus (ι := ι) S p)ᴴ = 0 := by
    simpa [X, rectKrausMap] using familyDefect_term_zero (ι := ι) (S := S) (z := z) p
  have hmap : rectKrausMap K X = ∑ i, z i • B i := by
    rw [rectKrausMap, Fintype.sum_sum_type, Fintype.sum_prod_type]
    calc
      (∑ x, ∑ x_1, K (Sum.inl (x, x_1)) * X * (K (Sum.inl (x, x_1)))ᴴ) +
          ∑ x, K (Sum.inr x) * X * (K (Sum.inr x))ᴴ =
            (∑ x, z x • ∑ x_1, familyMainKraus C (x, x_1) * (familyMainKraus C (x, x_1))ᴴ) +
              ∑ x : Fin D, 0 := by
              simp [K, familyKraus, hMainTerm, hDefTerm, Finset.smul_sum]
      _ = ∑ x, z x • (C x * (C x)ᴴ) := by simp [familyMain_outer_sum]
      _ = ∑ x, z x • B x := by simp [hC]
  let zsq : ι → ℂ := fun i => (starRingEnd ℂ (z i)) * z i
  have hXsq_fun :
      (fun i : Option ι => (starRingEnd ℂ) (i.elim 0 z) * i.elim 0 z) =
        (fun i : Option ι => i.elim 0 zsq) := by
    funext i
    cases i <;> simp [zsq]
  have hXsq : Xᴴ * X = Matrix.diagonal (fun o : Option ι => o.elim 0 zsq) := by
    simp [X, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, hXsq_fun]
  have hMainTermSq (i : ι) (p : Fin D) :
      familyMainKraus C (i, p) * (Xᴴ * X) * (familyMainKraus C (i, p))ᴴ =
        zsq i • (familyMainKraus C (i, p) * (familyMainKraus C (i, p))ᴴ) := by
    rw [hXsq]
    simpa [rectKrausMap, zsq] using familyMain_term_eq (C := C) (z := zsq) i p
  have hDefTermSq (p : Fin D) :
      familyDefectKraus (ι := ι) S p * (Xᴴ * X) *
        (familyDefectKraus (ι := ι) S p)ᴴ = 0 := by
    rw [hXsq]
    simpa [rectKrausMap] using familyDefect_term_zero (ι := ι) (S := S) (z := zsq) p
  have hmap_star : rectKrausMap K (Xᴴ * X) = ∑ i, zsq i • B i := by
    rw [rectKrausMap, Fintype.sum_sum_type, Fintype.sum_prod_type]
    calc
      (∑ x, ∑ x_1, K (Sum.inl (x, x_1)) * (Xᴴ * X) * (K (Sum.inl (x, x_1)))ᴴ) +
          ∑ x, K (Sum.inr x) * (Xᴴ * X) * (K (Sum.inr x))ᴴ =
            (∑ x, zsq x •
              ∑ x_1, familyMainKraus C (x, x_1) * (familyMainKraus C (x, x_1))ᴴ) +
              ∑ x : Fin D, 0 := by
              simp [K, familyKraus, hMainTermSq, hDefTermSq, Finset.smul_sum]
      _ = ∑ x, zsq x • (C x * (C x)ᴴ) := by simp [familyMain_outer_sum]
      _ = ∑ x, zsq x • B x := by simp [hC]
  have hks := rect_kadison_schwarz_le (K := K) hK_unital X
  have hBherm : ∀ i, (B i)ᴴ = B i := fun i => (hB i).isHermitian.eq
  simpa [hmap, hmap_star, zsq, hBherm,
    Matrix.conjTranspose_sum, Matrix.conjTranspose_smul] using hks

end DiagonalFamily

/-- Wolf Proposition 1.6 in the block-quadratic-form form used later in the
construction: positivity upgrades to positivity of every finite amplification once
all block images commute pairwise.

**Proof outline**: Use `exists_diagonal_family_of_normal` and `diagonal_family_schwarz_le`
by simultaneously diagonalizing the commuting Hermitian images of the block entries
and reducing to the scalar case. This requires Wolf Prop 1.6 (abelian subalgebra
implies CP) and is tracked separately. -/
-- Block Hermiticity: a BlockPositive block matrix satisfies (a j i)ᴴ = a i j.
-- Proof: 0 ≤ Q(ψ) means Q(ψ) nonneg real, so Q = conj Q. Conjugating and
-- relabeling yields the Hermiticity of the big nD×nD block matrix.
private lemma blockHermitian_of_blockPositive {n D : ℕ}
    {a : Matrix (Fin n) (Fin n) (Matrix (Fin D) (Fin D) ℂ)}
    (ha : BlockPositive a) :
    ∀ i j, (a j i)ᴴ = a i j := by
  classical
  let A : Matrix (Fin n × Fin D) (Fin n × Fin D) ℂ :=
    fun p q => a p.1 q.1 p.2 q.2
  have hAsym : A.toEuclideanLin.IsSymmetric := by
    rw [LinearMap.isSymmetric_iff_inner_map_self_real]
    intro x
    let ψ : Fin n → Fin D → ℂ := fun i r => x.ofLp (i, r)
    set q : ℂ := star x.ofLp ⬝ᵥ A.mulVec x.ofLp
    have hq' : 0 ≤ ∑ i : Fin n, ∑ j : Fin n,
        star (ψ i) ⬝ᵥ (a i j).mulVec (ψ j) := ha ψ
    have hq'' : 0 ≤ ∑ i : Fin n, ∑ j : Fin n, ∑ r : Fin D,
        (starRingEnd ℂ) (x.ofLp (i, r)) * ∑ s : Fin D, a i j r s * x.ofLp (j, s) := by
      simpa [ψ, dotProduct, Matrix.mulVec, mul_assoc] using hq'
    have hinnerSum (i : Fin n) (r : Fin D) :
        (∑ x_2 : Fin n × Fin D, a i x_2.1 r x_2.2 * x.ofLp x_2) =
          ∑ j : Fin n, ∑ s : Fin D, a i j r s * x.ofLp (j, s) := by
      rw [Fintype.sum_prod_type]
    have hq : 0 ≤ q := by
      dsimp [q, A]
      simp only [dotProduct, Matrix.mulVec]
      rw [Fintype.sum_prod_type]
      convert hq'' using 1
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      rw [hinnerSum i r, Finset.mul_sum]
      rfl
    have hqreal : star q = q := by
      have hqim : q.im = 0 := (Complex.nonneg_iff.mp hq).2.symm
      apply Complex.ext
      · simp
      · simp [hqim]
    have hinner : inner ℂ (A.toEuclideanLin x) x = star q := by
      calc
        inner ℂ (A.toEuclideanLin x) x = x.ofLp ⬝ᵥ star (A.toEuclideanLin x).ofLp := by
          simp only [EuclideanSpace.inner_eq_star_dotProduct]
        _ = x.ofLp ⬝ᵥ star (A.mulVec x.ofLp) := by
          simp [Matrix.ofLp_toLpLin (p := 2) (q := 2), Matrix.toLin'_apply]
        _ = star (A.mulVec x.ofLp ⬝ᵥ star x.ofLp) := by rw [Matrix.dotProduct_star]
        _ = star (star x.ofLp ⬝ᵥ A.mulVec x.ofLp) := by rw [dotProduct_comm]
        _ = star q := by rfl
    calc
      star (inner ℂ (A.toEuclideanLin x) x) = star (star q) := by rw [hinner]
      _ = q := by simp
      _ = star q := hqreal.symm
      _ = inner ℂ (A.toEuclideanLin x) x := by rw [hinner]
  have hAherm : A.IsHermitian := (Matrix.isHermitian_iff_isSymmetric (A := A)).2 hAsym
  intro i j
  ext r s
  simpa [A] using congrArg
    (fun N : Matrix (Fin n × Fin D) (Fin n × Fin D) ℂ => N (i, r) (j, s)) hAherm.eq

-- Weighted sum ∑ conj(w i) w j • a i j is PSD for block-positive a.
-- Proof: BlockPositive applied to ψ i = w i • v gives PSD of weighted sum.
private lemma weighted_block_sum_posSemidef {n D : ℕ}
    {a : Matrix (Fin n) (Fin n) (Matrix (Fin D) (Fin D) ℂ)}
    (ha : BlockPositive a) (w : Fin n → ℂ) :
    (∑ i, ∑ j, (starRingEnd ℂ (w i) * w j) • a i j).PosSemidef := by
  classical
  let B : Matrix (Fin D) (Fin D) ℂ := ∑ i, ∑ j, (starRingEnd ℂ (w i) * w j) • a i j
  have hBH : ∀ i j, (a j i)ᴴ = a i j := blockHermitian_of_blockPositive ha
  have hBherm : B.IsHermitian := by
    change Bᴴ = B
    calc
      Bᴴ = ∑ i, ∑ j, star (starRingEnd ℂ (w i) * w j) • (a i j)ᴴ := by
        simp [B, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul]
      _ = ∑ i, ∑ j, star (starRingEnd ℂ (w i) * w j) • a j i := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        simpa using congrArg
          (fun N : Matrix (Fin D) (Fin D) ℂ => star (starRingEnd ℂ (w i) * w j) • N) (hBH j i)
      _ = ∑ i, ∑ j, (starRingEnd ℂ (w i) * w j) • a i j := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        simp [mul_comm]
      _ = B := by rfl
  have hBnonneg : ∀ v : Fin D → ℂ, 0 ≤ star v ⬝ᵥ B.mulVec v := by
    intro v
    let ψ : Fin n → Fin D → ℂ := fun i => w i • v
    have hψ : 0 ≤ ∑ i : Fin n, ∑ j : Fin n, star (ψ i) ⬝ᵥ (a i j).mulVec (ψ j) := ha ψ
    have hψ' : 0 ≤ ∑ i : Fin n, ∑ j : Fin n,
        (starRingEnd ℂ (w i) * w j) * (star v ⬝ᵥ (a i j).mulVec v) := by
      simpa [ψ, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        mul_comm, mul_left_comm, mul_assoc] using hψ
    convert hψ' using 1
    simp [B, Matrix.sum_mulVec, Matrix.smul_mulVec, dotProduct_sum, dotProduct_smul,
      smul_eq_mul, mul_assoc]
  exact Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hBherm hBnonneg

-- Commuting images whose scalar matrices are all PSD give a nonneg block form.
-- This is the simultaneous-diagonalisation core: for pairwise-commuting images,
-- the block quadratic form is nonneg whenever every scalar matrix is PSD.
-- Proved via the joint-eigenspace decomposition
-- (LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute).
set_option maxHeartbeats 1600000 in
-- Elaborating the joint-eigenspace decomposition and the finite-index reduction
-- requires more heartbeats than the default.
private lemma blockForm_nonneg_of_scalarPSD_of_commuting {n D : ℕ}
    (M : Fin n → Fin n → Matrix (Fin D) (Fin D) ℂ)
    (hMadj : ∀ i j, (M j i)ᴴ = M i j)
    (hcomm : ∀ i j k l, Commute (M i j) (M k l))
    (hscalar : ∀ (w : Fin n → ℂ) (e : Fin D → ℂ),
      0 ≤ ∑ i, ∑ j, starRingEnd ℂ (w i) * w j *
        (star e ⬝ᵥ (M i j).mulVec e))
    (ψ : Fin n → Fin D → ℂ) :
    0 ≤ ∑ i, ∑ j, star (ψ i) ⬝ᵥ (M i j).mulVec (ψ j) := by
  classical
  let H : Fin n → Fin n → Matrix (Fin D) (Fin D) ℂ :=
    fun i j => (1 / 2 : ℂ) • (M i j + (M i j)ᴴ)
  let K : Fin n → Fin n → Matrix (Fin D) (Fin D) ℂ :=
    fun i j => (Complex.I / 2 : ℂ) • ((M i j)ᴴ - M i j)
  let ι := ((Fin n × Fin n) ⊕ (Fin n × Fin n))
  let T : ι → EuclideanSpace ℂ (Fin D) →ₗ[ℂ] EuclideanSpace ℂ (Fin D)
    | Sum.inl ij => Matrix.toEuclideanLin (H ij.1 ij.2)
    | Sum.inr ij => Matrix.toEuclideanLin (K ij.1 ij.2)
  have hH : ∀ i j, (H i j).IsHermitian := by
    intro i j
    ext r s
    simp [H, add_comm]
  have hK : ∀ i j, (K i j).IsHermitian := by
    intro i j
    ext r s
    simp only [sub_eq_add_neg, smul_add, smul_neg, conjTranspose_apply, add_apply, smul_apply,
      RCLike.star_def, smul_eq_mul, neg_apply, star_add, star_mul', star_div₀, conj_I,
      star_ofNat, RingHomCompTriple.comp_apply, RingHom.id_apply, star_neg, K]
    ring
  have hTsymm : ∀ idx, (T idx).IsSymmetric := by
    intro idx
    cases idx with
    | inl ij =>
        rcases ij with ⟨i, j⟩
        simpa [T] using (Matrix.isHermitian_iff_isSymmetric (A := H i j)).mp (hH i j)
    | inr ij =>
        rcases ij with ⟨i, j⟩
        simpa [T] using (Matrix.isHermitian_iff_isSymmetric (A := K i j)).mp (hK i j)
  have hEuclMul := toEuclideanLin_mul (D := D)
  have htoEuclComm {A B : Matrix (Fin D) (Fin D) ℂ} (hAB : Commute A B) :
      Commute (Matrix.toEuclideanLin A : EuclideanSpace ℂ (Fin D) →ₗ[ℂ] EuclideanSpace ℂ (Fin D))
        (Matrix.toEuclideanLin B) :=
    hEuclMul A B |>.trans (congrArg Matrix.toEuclideanLin hAB.eq) |>.trans (hEuclMul B A).symm
  have hcommAdjLeft : ∀ i j k l, Commute (M i j)ᴴ (M k l) := by
    intro i j k l
    simpa [hMadj j i] using hcomm j i k l
  have hcommAdjRight : ∀ i j k l, Commute (M i j) (M k l)ᴴ := by
    intro i j k l
    simpa [hMadj l k] using hcomm i j l k
  have hcommAdjAdj : ∀ i j k l, Commute (M i j)ᴴ (M k l)ᴴ := by
    intro i j k l
    simpa [hMadj j i, hMadj l k] using hcomm j i l k
  have hHH : ∀ i j k l, Commute (H i j) (H k l) := by
    intro i j k l
    have h1 : Commute (M i j + (M i j)ᴴ) (M k l) :=
      (hcomm i j k l).add_left (hcommAdjLeft i j k l)
    have h2 : Commute (M i j + (M i j)ᴴ) (M k l)ᴴ :=
      (hcommAdjRight i j k l).add_left (hcommAdjAdj i j k l)
    have hsum : Commute (M i j + (M i j)ᴴ) (M k l + (M k l)ᴴ) := h1.add_right h2
    simpa [H, Matrix.smul_mul, Matrix.mul_smul, mul_comm, mul_left_comm, mul_assoc] using
      (hsum.smul_left (1 / 2 : ℂ)).smul_right (1 / 2 : ℂ)
  have hHK : ∀ i j k l, Commute (H i j) (K k l) := by
    intro i j k l
    have h1 : Commute (M i j + (M i j)ᴴ) (M k l) :=
      (hcomm i j k l).add_left (hcommAdjLeft i j k l)
    have h2 : Commute (M i j + (M i j)ᴴ) (M k l)ᴴ :=
      (hcommAdjRight i j k l).add_left (hcommAdjAdj i j k l)
    have hsub : Commute (M i j + (M i j)ᴴ) ((M k l)ᴴ - M k l) := h2.sub_right h1
    simpa [H, K, Matrix.smul_mul, Matrix.mul_smul, mul_comm, mul_left_comm, mul_assoc] using
      (hsub.smul_left (1 / 2 : ℂ)).smul_right (Complex.I / 2 : ℂ)
  have hKK : ∀ i j k l, Commute (K i j) (K k l) := by
    intro i j k l
    have h1 : Commute ((M i j)ᴴ - M i j) (M k l) :=
      (hcommAdjLeft i j k l).sub_left (hcomm i j k l)
    have h2 : Commute ((M i j)ᴴ - M i j) (M k l)ᴴ :=
      (hcommAdjAdj i j k l).sub_left (hcommAdjRight i j k l)
    have hsub : Commute ((M i j)ᴴ - M i j) ((M k l)ᴴ - M k l) := h2.sub_right h1
    simpa [K, Matrix.smul_mul, Matrix.mul_smul, mul_comm, mul_left_comm, mul_assoc] using
      (hsub.smul_left (Complex.I / 2 : ℂ)).smul_right (Complex.I / 2 : ℂ)
  have hTcomm : Pairwise (fun x y => Commute (T x) (T y)) := by
    intro x y _
    cases x with
    | inl x =>
        rcases x with ⟨i, j⟩
        cases y with
        | inl y =>
            rcases y with ⟨k, l⟩
            simpa [T] using htoEuclComm (hHH i j k l)
        | inr y =>
            rcases y with ⟨k, l⟩
            simpa [T] using htoEuclComm (hHK i j k l)
    | inr x =>
        rcases x with ⟨i, j⟩
        cases y with
        | inl y =>
            rcases y with ⟨k, l⟩
            simpa [T] using (htoEuclComm (hHK k l i j)).symm
        | inr y =>
            rcases y with ⟨k, l⟩
            simpa [T] using htoEuclComm (hKK i j k l)
  let V : (ι → ℂ) → Submodule ℂ (EuclideanSpace ℂ (Fin D)) :=
    fun γ => ⨅ idx, Module.End.eigenspace (T idx) (γ idx)
  have hFullOrtho :
      OrthogonalFamily ℂ (fun γ : ι → ℂ => V γ) fun γ => (V γ).subtypeₗᵢ := by
    simpa [V] using LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces (T := T) hTsymm
  have hFullTop : (⨆ γ : ι → ℂ, V γ) = ⊤ := by
    simpa [V] using LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute (T := T) hTsymm hTcomm
  let σ : Type := ∀ idx : ι, Eigenvalues (T idx)
  let W : σ → Submodule ℂ (EuclideanSpace ℂ (Fin D)) :=
    fun α => ⨅ idx, Module.End.eigenspace (T idx) ((α idx : Eigenvalues (T idx)) : ℂ)
  have hWOrtho :
      OrthogonalFamily ℂ (fun α : σ => W α) fun α => (W α).subtypeₗᵢ := by
    let f : σ → ι → ℂ := fun α idx => ((α idx : Eigenvalues (T idx)) : ℂ)
    have hf : Function.Injective f := by
      intro α β h
      funext idx
      apply Subtype.ext
      exact congrFun h idx
    simpa [W, V, f] using hFullOrtho.comp (f := f) hf
  have hWleV : (⨆ α : σ, W α) ≤ ⨆ γ : ι → ℂ, V γ := by
    refine iSup_le ?_
    intro α
    exact le_iSup_of_le (fun idx => ((α idx : Eigenvalues (T idx)) : ℂ)) <| by
      simp [W, V]
  have hVleW : (⨆ γ : ι → ℂ, V γ) ≤ ⨆ α : σ, W α := by
    refine iSup_le ?_
    intro γ
    by_cases hγ : V γ = ⊥
    · simp [hγ]
    · have hEig : ∀ idx, Module.End.HasEigenvalue (T idx) (γ idx) := by
        intro idx
        apply Module.End.hasEigenvalue_iff.mpr
        intro hbot
        apply hγ
        apply le_antisymm
        · have hle : V γ ≤ Module.End.eigenspace (T idx) (γ idx) := by
            exact iInf_le (fun j => Module.End.eigenspace (T j) (γ j)) idx
          simpa [V, hbot] using hle
        · exact bot_le
      let α : σ := fun idx => ⟨γ idx, hEig idx⟩
      exact le_iSup_of_le α <| by
        simp [W, V, α]
  have hWTop : (⨆ α : σ, W α) = ⊤ := by
    calc
      (⨆ α : σ, W α) = ⨆ γ : ι → ℂ, V γ := by exact le_antisymm hWleV hVleW
      _ = ⊤ := hFullTop
  have hWInternal : DirectSum.IsInternal (fun α : σ => W α) := by
    apply hWOrtho.isInternal_iff.mpr
    rw [hWTop, Submodule.top_orthogonal_eq_bot]
  let s := Σ α : σ, Fin (Module.finrank ℂ (W α))
  let b : OrthonormalBasis s ℂ (EuclideanSpace ℂ (Fin D)) :=
    hWInternal.collectedOrthonormalBasis hWOrtho (fun α => stdOrthonormalBasis ℂ (W α))
  let χ : s → ι → ℂ := fun a idx => ((a.1 idx : Eigenvalues (T idx)) : ℂ)
  have hbmem (a : s) : b a ∈ W a.1 := by
    change
      (hWInternal.collectedOrthonormalBasis hWOrtho
        (fun α => stdOrthonormalBasis ℂ (W α)) a) ∈ W a.1
    exact hWInternal.collectedOrthonormalBasis_mem
      (hV := hWOrtho) (v := fun α => stdOrthonormalBasis ℂ (W α)) a
  have hTb (idx : ι) (a : s) : T idx (b a) = (χ a idx) • b a := by
    have hbmem' : b a ∈ ⨅ j, Module.End.eigenspace (T j) ((a.1 j : Eigenvalues (T j)) : ℂ) := by
      change b a ∈ W a.1
      exact hbmem a
    exact (Module.End.mem_eigenspace_iff).mp ((Submodule.mem_iInf _).mp hbmem' idx)
  let eig : s → Fin n → Fin n → ℂ := fun a i j =>
    χ a (Sum.inl (i, j)) + Complex.I * χ a (Sum.inr (i, j))
  have hM_decomp (i j : Fin n) : M i j = H i j + Complex.I • K i j := by
    ext r s
    simp only [one_div, smul_add, sub_eq_add_neg, smul_neg, add_apply, smul_apply, smul_eq_mul,
      conjTranspose_apply, RCLike.star_def, neg_apply, H, K]
    ring_nf
    norm_num [Complex.I_sq]
    ring
  have hMb (a : s) (i j : Fin n) :
      Matrix.toEuclideanLin (M i j) (b a) = eig a i j • b a := by
    have hlin : Matrix.toEuclideanLin (M i j) =
        Matrix.toEuclideanLin (H i j) + Complex.I • Matrix.toEuclideanLin (K i j) := by
      simpa [H, K] using congrArg Matrix.toEuclideanLin (hM_decomp i j)
    rw [hlin]
    calc
      Matrix.toEuclideanLin (H i j) (b a) + Complex.I • Matrix.toEuclideanLin (K i j) (b a)
          = χ a (Sum.inl (i, j)) • b a + Complex.I • (χ a (Sum.inr (i, j)) • b a) := by
              rw [hTb (Sum.inl (i, j)) a, hTb (Sum.inr (i, j)) a]
      _ = eig a i j • b a := by
            simp [eig, add_smul, smul_smul]
  let ψE : Fin n → EuclideanSpace ℂ (Fin D) := fun i => WithLp.toLp 2 (ψ i)
  let c : Fin n → s → ℂ := fun i a => inner ℂ (b a) (ψE i)
  have hcoeff (i j : Fin n) (v : EuclideanSpace ℂ (Fin D)) (a : s) :
      inner ℂ (b a) (Matrix.toEuclideanLin (M i j) v) = eig a i j * inner ℂ (b a) v := by
    let v' : EuclideanSpace ℂ (Fin D) := ∑ x, inner ℂ (b x) v • b x
    have hv' : v' = v := by
      simpa [v'] using b.sum_repr' v
    calc
      inner ℂ (b a) (Matrix.toEuclideanLin (M i j) v)
          = inner ℂ (b a) (Matrix.toEuclideanLin (M i j) v') := by rw [← hv']
      _ = inner ℂ (b a) (∑ x, (inner ℂ (b x) v * eig x i j) • b x) := by
            rw [show v' = ∑ x, inner ℂ (b x) v • b x by rfl, map_sum]
            apply congrArg (inner ℂ (b a))
            apply Finset.sum_congr rfl
            intro x _
            rw [map_smul, hMb x i j, smul_smul]
      _ = inner ℂ (b a) v * eig a i j := by
            simpa using Orthonormal.inner_right_fintype (hv := b.orthonormal)
              (l := fun x => inner ℂ (b x) v * eig x i j) a
      _ = eig a i j * inner ℂ (b a) v := by ring
  have hformTerm (i j : Fin n) :
      star (ψ i) ⬝ᵥ (M i j).mulVec (ψ j) =
        inner ℂ (ψE i) (Matrix.toEuclideanLin (M i j) (ψE j)) := by
    simp [ψE, EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLin'_apply, dotProduct_comm]
  have hterm (i j : Fin n) :
      inner ℂ (ψE i) (Matrix.toEuclideanLin (M i j) (ψE j)) =
        ∑ a : s, starRingEnd ℂ (c i a) * c j a * eig a i j := by
    calc
      inner ℂ (ψE i) (Matrix.toEuclideanLin (M i j) (ψE j))
          = ∑ a : s, inner ℂ (ψE i) (b a) * inner ℂ (b a)
              (Matrix.toEuclideanLin (M i j) (ψE j)) := by
              symm
              exact b.sum_inner_mul_inner (ψE i) (Matrix.toEuclideanLin (M i j) (ψE j))
      _ = ∑ a : s, starRingEnd ℂ (c i a) * (eig a i j * c j a) := by
            have hleft (a : s) : inner ℂ (ψE i) (b a) = starRingEnd ℂ (c i a) := by
              simp [c]
            have hright (a : s) :
                inner ℂ (b a) (Matrix.toEuclideanLin (M i j) (ψE j)) = eig a i j * c j a := by
              simpa [c] using hcoeff i j (ψE j) a
            apply Finset.sum_congr rfl
            intro a _
            rw [hleft a, hright a]
      _ = ∑ a : s, starRingEnd ℂ (c i a) * c j a * eig a i j := by
            apply Finset.sum_congr rfl
            intro a _
            ring
  have hrewrite :
      ∑ i : Fin n, ∑ j : Fin n, inner ℂ (ψE i) (Matrix.toEuclideanLin (M i j) (ψE j)) =
        ∑ a : s, ∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (c i a) * c j a * eig a i j := by
    calc
      ∑ i : Fin n, ∑ j : Fin n, inner ℂ (ψE i) (Matrix.toEuclideanLin (M i j) (ψE j))
          = ∑ i : Fin n, ∑ j : Fin n, ∑ a : s, starRingEnd ℂ (c i a) * c j a * eig a i j := by
              simp_rw [hterm]
      _ = ∑ i : Fin n, ∑ a : s, ∑ j : Fin n, starRingEnd ℂ (c i a) * c j a * eig a i j := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_comm]
      _ = ∑ a : s, ∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (c i a) * c j a * eig a i j := by
            rw [Finset.sum_comm]
  have heigScalar (a : s) (i j : Fin n) :
      star (b a).ofLp ⬝ᵥ (M i j).mulVec (b a).ofLp = eig a i j := by
    have hinner : inner ℂ (b a) (Matrix.toEuclideanLin (M i j) (b a)) = eig a i j := by
      rw [hMb a i j]
      simp [inner_smul_right]
    simpa [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLin'_apply,
      dotProduct_comm] using hinner
  have hnonneg :
      0 ≤ ∑ a : s, ∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (c i a) * c j a * eig a i j := by
    apply Finset.sum_nonneg
    intro a _
    have hs := hscalar (fun i => c i a) (b a).ofLp
    convert hs using 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [heigScalar a i j]
  calc
    0 ≤ ∑ a : s, ∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (c i a) * c j a * eig a i j :=
      hnonneg
    _ = ∑ i : Fin n, ∑ j : Fin n, inner ℂ (ψE i) (Matrix.toEuclideanLin (M i j) (ψE j)) := by
      rw [← hrewrite]
    _ = ∑ i : Fin n, ∑ j : Fin n, star (ψ i) ⬝ᵥ (M i j).mulVec (ψ j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [← hformTerm i j]

set_option maxHeartbeats 1600000 in
-- Elaborating the simultaneous-diagonalization argument expands enough definitions
-- that the default heartbeat limit may time out.
theorem quadraticForm_nonneg_of_isPositiveMap_of_commuting_images
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsPositiveMap T)
    {n : ℕ}
    (a : Matrix (Fin n) (Fin n) (Matrix (Fin D) (Fin D) ℂ))
    (ha : BlockPositive a)
    (hcomm : PairwiseCommuteImages T a)
    (ψ : Fin n → Fin D → ℂ) :
    0 ≤ blockQuadraticForm T a ψ := by
  classical
  simp only [blockQuadraticForm]
  -- Step 1: Block Hermiticity
  have hBH : ∀ i j, (a j i)ᴴ = a i j := blockHermitian_of_blockPositive ha
  -- Step 2: T preserves adjoints, giving (T(a j i))ᴴ = T(a i j)
  have hTadj : ∀ i j, (T (a j i))ᴴ = T (a i j) := by
    intro i j
    conv_lhs => rw [(hBH j i).symm]
    simp [hT.map_conjTranspose]
  -- Step 3: Apply the core lemma with M i j = T(a i j)
  apply blockForm_nonneg_of_scalarPSD_of_commuting (fun i j => T (a i j))
  · -- Block Hermiticity of images
    intro i j; exact hTadj i j
  · -- Pairwise commutativity
    intro i j k l; exact hcomm i j k l
  · -- Scalar PSD: for all w e, ∑ij conj(w i) w j ⟨e, T(a ij) e⟩ ≥ 0
    intro w e
    -- This equals ⟨e, T(B_w) e⟩ where B_w = ∑ij conj(w_i) w_j a_ij is PSD.
    have hpsd := hT _ (weighted_block_sum_posSemidef ha w)
    -- The sum equals star e ⬝ᵥ T(B_w).mulVec e where B_w is PSD.
    -- B_w = ∑ij conj(w_i) w_j • a_ij
    -- T(B_w) is PSD by positivity of T.
    -- We show the scalar quadratic form equals e† T(B_w) e ≥ 0.
    convert hpsd.dotProduct_mulVec_nonneg e using 1
    simp only [map_sum, LinearMap.map_smul]
    -- Need: ∑ij c_ij * (e† T(a_ij) e) = e† (∑ij c_ij • T(a_ij)) e
    -- The two sides are equal by linearity (rearranging finite sums).
    -- LHS: ∑_p ∑_q c_pq * (e† T(a_pq) e) where c_pq = conj(w_p)*w_q
    -- RHS: e† (∑_p ∑_q c_pq • T(a_pq)) e
    -- These are equal because scalar * dot-product = dot-product of scalar * matrix.
    simp only [dotProduct, mulVec, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    simp only [Finset.mul_sum, Finset.sum_mul]
    -- Rearrange sums: (q:n, p:n, r:D, s:D) → (r:D, s:D, p:n, q:n)
    -- by four applications of Finset.sum_comm
    -- Rearrange sum order: (n,n,D,D) → (D,D,n,n) via Finset.sum_comm
    -- Step 1: swap inner n↔D for each outer n
    conv_lhs => arg 2; ext x; rw [Finset.sum_comm]
    -- Step 2: swap outer n↔D
    rw [Finset.sum_comm]
    -- Step 3: swap inner n↔D for each outer D
    conv_lhs => arg 2; ext r; arg 2; ext x; rw [Finset.sum_comm]
    -- Step 4: swap second n↔D
    conv_lhs => arg 2; ext r; rw [Finset.sum_comm]
    -- Now both sides sum over (D,D,n,n); match term-by-term
    apply Finset.sum_congr rfl; intro r _
    apply Finset.sum_congr rfl; intro s _
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro q _
    ring

/-- A positive map is positive on commuting block families.

This packages `quadraticForm_nonneg_of_isPositiveMap_of_commuting_images` into a
single reusable predicate. -/
private lemma isPositiveOnCommuting_of_isPositiveMap
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsPositiveMap T) :
    IsPositiveOnCommuting T := by
  intro n a ha hcomm ψ
  exact quadraticForm_nonneg_of_isPositiveMap_of_commuting_images hT a ha hcomm ψ


end PositiveOnAbelian
