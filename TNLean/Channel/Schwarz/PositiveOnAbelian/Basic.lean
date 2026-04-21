/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Basic
import TNLean.Channel.Schwarz.PositiveMapProperties
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Foundational positive-on-abelian matrix lemmas

This file contains the basic finite-dimensional matrix definitions used in the
positive-on-abelian Schwarz argument, together with the diagonal-family
Schwarz inequality that treats commuting families after simultaneous
diagonalization has reduced them to a scalar problem.

## Main definitions

* `BlockPositive` — block-matrix positivity phrased through quadratic forms.
* `PairwiseCommuteImages` — pairwise commutativity of the block images of a
  linear map.
* `blockQuadraticForm` — the quadratic form obtained after applying a linear
  map blockwise.
* `IsPositiveOnCommuting` — positivity on commuting block families.

## Main statements

* `diagonal_family_schwarz_le` — the diagonal / finite-spectrum Schwarz
  inequality for a positive family with $\sum_i B_i \le 1$.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Proposition 1.6 and
  Proposition 5.1][Wolf2012QChannels]

## Tags

positive map, commuting family, Schwarz inequality, normal operator
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators TNMatrixCFC
open Matrix Finset Complex Module.End

namespace PositiveOnAbelian

variable {D : ℕ}

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
    simpa only [A, P, Matrix.fromBlocks_conjTranspose, conjTranspose_conjTranspose,
      conjTranspose_one, conjTranspose_zero, Matrix.fromBlocks_multiply, Matrix.mul_zero,
      add_zero, mul_one, one_mul] using Matrix.posSemidef_self_mul_conjTranspose A
  let K₂ : ι → Matrix (m ⊕ m) (n ⊕ n) ℂ :=
    fun i => Matrix.fromBlocks (K i) 0 0 (K i)
  have h_term (i : ι) :
      K₂ i * P * (K₂ i)ᴴ =
        Matrix.fromBlocks (K i * (Xᴴ * X) * (K i)ᴴ) (K i * Xᴴ * (K i)ᴴ)
          (K i * X * (K i)ᴴ) (K i * (K i)ᴴ) := by
    simp only [Matrix.fromBlocks_multiply, Matrix.zero_mul, add_zero, Matrix.mul_one, zero_add,
      Matrix.fromBlocks_conjTranspose, conjTranspose_zero, Matrix.mul_assoc, Matrix.mul_zero, K₂,
      P]
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
      simp only [Matrix.sum_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  have h_block_eq :
      (∑ i : ι, K₂ i * P * (K₂ i)ᴴ) =
        Matrix.fromBlocks (rectKrausMap K (Xᴴ * X)) ((rectKrausMap K X)ᴴ)
          ((rectKrausMap K X)ᴴᴴ) (1 : Matrix m m ℂ) := by
    simp_rw [h_term]
    rw [h_sfb]
    exact Matrix.fromBlocks_inj.mpr
      ⟨by simp only [rectKrausMap],
       by calc
           (∑ i : ι, K i * Xᴴ * (K i)ᴴ) = rectKrausMap K Xᴴ := by
             simp only [rectKrausMap]
           _ = (rectKrausMap K X)ᴴ := by
               simp only [rectKrausMap, Matrix.mul_assoc, Matrix.conjTranspose_sum,
                 Matrix.conjTranspose_mul, conjTranspose_conjTranspose],
       by simp only [rectKrausMap, conjTranspose_conjTranspose],
       by simpa only using h_unital⟩
  have h_block_psd :
      (Matrix.fromBlocks (rectKrausMap K (Xᴴ * X)) ((rectKrausMap K X)ᴴ)
        ((rectKrausMap K X)ᴴᴴ) (1 : Matrix m m ℂ)).PosSemidef := by
    simpa only [conjTranspose_conjTranspose, h_block_eq] using h_sum_psd
  haveI : Invertible (1 : Matrix m m ℂ) := invertibleOne
  rw [Matrix.le_iff]
  simpa only [inv_one, mul_one, conjTranspose_conjTranspose] using
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
    simp only [Matrix.sum_apply, Matrix.mul_apply, familyMainKraus, conjTranspose_apply,
      RCLike.star_def, ite_mul, zero_mul, sum_ite_eq', mem_univ, ↓reduceIte]
  rw [hL]
  simp only [Matrix.mul_apply, conjTranspose_apply, RCLike.star_def]

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
    simp only [Matrix.sum_apply, Matrix.mul_apply, familyDefectKraus, conjTranspose_apply,
      RCLike.star_def, ite_mul, zero_mul, sum_ite_eq', mem_univ, ↓reduceIte]
  rw [hL]
  simp only [Matrix.mul_apply, conjTranspose_apply, RCLike.star_def]

private lemma familyDefect_term_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix (Fin D) (Fin D) ℂ) (z : ι → ℂ) (p : Fin D) :
    rectKrausMap (fun _ : Unit => familyDefectKraus (ι := ι) S p)
      (Matrix.diagonal (fun o : Option ι => o.elim 0 z)) = 0 := by
  ext r s
  simp only [rectKrausMap, univ_unique, PUnit.default_eq_unit, sum_const, card_singleton,
    smul_apply, Matrix.mul_apply, familyDefectKraus, Matrix.diagonal_apply, mul_ite, ite_mul,
    zero_mul, mul_zero, sum_ite_eq', mem_univ, ↓reduceIte, conjTranspose_apply, RCLike.star_def,
    Option.elim_none, nsmul_zero, zero_apply]

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
              simp only [familyKraus, familyMain_outer_sum, familyDefect_outer_sum, K]
      _ = (∑ x, B x) + (1 - ∑ i, B i) := by
            have hS' : S * Sᴴ = 1 - ∑ i, B i := by
              simpa only [Matrix.star_eq_conjTranspose] using hS.symm
            simp only [hS', hC, add_sub_cancel]
      _ = 1 := by simp only [sub_eq_add_neg, add_comm, add_neg_cancel_left]
  have hMainTerm (i : ι) (p : Fin D) :
      familyMainKraus C (i, p) * X * (familyMainKraus C (i, p))ᴴ =
        z i • (familyMainKraus C (i, p) * (familyMainKraus C (i, p))ᴴ) := by
    simpa only [rectKrausMap, univ_unique, PUnit.default_eq_unit, sum_const, card_singleton,
      one_smul] using familyMain_term_eq (C := C) (z := z) i p
  have hDefTerm (p : Fin D) :
      familyDefectKraus (ι := ι) S p * X * (familyDefectKraus (ι := ι) S p)ᴴ = 0 := by
    simpa only [rectKrausMap, univ_unique, PUnit.default_eq_unit, sum_const, card_singleton,
      one_smul] using familyDefect_term_zero (ι := ι) (S := S) (z := z) p
  have hmap : rectKrausMap K X = ∑ i, z i • B i := by
    rw [rectKrausMap, Fintype.sum_sum_type, Fintype.sum_prod_type]
    calc
      (∑ x, ∑ x_1, K (Sum.inl (x, x_1)) * X * (K (Sum.inl (x, x_1)))ᴴ) +
          ∑ x, K (Sum.inr x) * X * (K (Sum.inr x))ᴴ =
            (∑ x, z x • ∑ x_1, familyMainKraus C (x, x_1) * (familyMainKraus C (x, x_1))ᴴ) +
              ∑ x : Fin D, 0 := by
              simp only [familyKraus, hMainTerm, hDefTerm, sum_const_zero, add_zero, smul_sum,
                K]
      _ = ∑ x, z x • (C x * (C x)ᴴ) := by
        simp only [familyMain_outer_sum, sum_const_zero, add_zero]
      _ = ∑ x, z x • B x := by simp only [hC]
  let zsq : ι → ℂ := fun i => (starRingEnd ℂ (z i)) * z i
  have hXsq_fun :
      (fun i : Option ι => (starRingEnd ℂ) (i.elim 0 z) * i.elim 0 z) =
        (fun i : Option ι => i.elim 0 zsq) := by
    funext i
    cases i <;> simp only [Option.elim_none, map_zero, mul_zero, Option.elim_some, zsq]
  have hXsq : Xᴴ * X = Matrix.diagonal (fun o : Option ι => o.elim 0 zsq) := by
    simp only [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Pi.star_apply,
      RCLike.star_def, hXsq_fun, X]
  have hMainTermSq (i : ι) (p : Fin D) :
      familyMainKraus C (i, p) * (Xᴴ * X) * (familyMainKraus C (i, p))ᴴ =
        zsq i • (familyMainKraus C (i, p) * (familyMainKraus C (i, p))ᴴ) := by
    rw [hXsq]
    simpa only [rectKrausMap, univ_unique, PUnit.default_eq_unit, sum_const, card_singleton,
      one_smul] using familyMain_term_eq (C := C) (z := zsq) i p
  have hDefTermSq (p : Fin D) :
      familyDefectKraus (ι := ι) S p * (Xᴴ * X) *
        (familyDefectKraus (ι := ι) S p)ᴴ = 0 := by
    rw [hXsq]
    simpa only [rectKrausMap, univ_unique, PUnit.default_eq_unit, sum_const, card_singleton,
      one_smul] using familyDefect_term_zero (ι := ι) (S := S) (z := zsq) p
  have hmap_star : rectKrausMap K (Xᴴ * X) = ∑ i, zsq i • B i := by
    rw [rectKrausMap, Fintype.sum_sum_type, Fintype.sum_prod_type]
    calc
      (∑ x, ∑ x_1, K (Sum.inl (x, x_1)) * (Xᴴ * X) * (K (Sum.inl (x, x_1)))ᴴ) +
          ∑ x, K (Sum.inr x) * (Xᴴ * X) * (K (Sum.inr x))ᴴ =
            (∑ x, zsq x •
              ∑ x_1, familyMainKraus C (x, x_1) * (familyMainKraus C (x, x_1))ᴴ) +
              ∑ x : Fin D, 0 := by
              simp only [familyKraus, hMainTermSq, hDefTermSq, sum_const_zero, add_zero,
                smul_sum, K]
      _ = ∑ x, zsq x • (C x * (C x)ᴴ) := by
        simp only [familyMain_outer_sum, sum_const_zero, add_zero]
      _ = ∑ x, zsq x • B x := by simp only [hC]
  have hks := rect_kadison_schwarz_le (K := K) hK_unital X
  have hBherm : ∀ i, (B i)ᴴ = B i := fun i => (hB i).isHermitian.eq
  simpa only [ge_iff_le, hmap, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    RCLike.star_def, hBherm, hmap_star] using hks

end DiagonalFamily

end PositiveOnAbelian
