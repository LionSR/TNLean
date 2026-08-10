/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.SpectatorBoundaryGram

/-!
# Tail virtual Gram operator

This file identifies the adjoint-self composition of the tail virtual map with right
multiplication by an iterated transfer-map value. It also bounds the fourth power of the
operator norm of the tail virtual map by the squared entrywise mass of that value.

## Main results

- `MPSTensor.tailVirtualMapES_adjoint_comp_self_apply`
- `MPSTensor.tailVirtualMapES_norm_four_pow_le_transferMap_pow_one_entry_norm_sq`
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

section FrobeniusCoordinate

open scoped Matrix.Norms.Frobenius

/-! ### Exact adjoint-self formula with matrix input -/

/-- The adjoint-self composition of the tail virtual map acts by right multiplication by the
iterated transfer map applied to the identity. -/
theorem tailVirtualMapES_adjoint_comp_self_apply (A : MPSTensor d D) (K : ℕ)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    (tailVirtualMapES A K).adjoint (tailVirtualMapES A K
      (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D) X)) =
    Matrix.frobeniusEquivEuclidean (Fin D) (Fin D) (X * ((transferMap A) ^ K) 1) := by
  rw [tailVirtualMapES_adjoint_apply]
  simp_rw [boundaryFamilyEquiv_tailVirtualMapES_apply,
    (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).symm_apply_apply]
  have hsum : (∑ u : Cfg d K, evalWord A (List.ofFn u) * (evalWord A (List.ofFn u))ᴴ) =
      ((transferMap (d := d) (D := D) A) ^ K) 1 := by
    symm
    simpa only [Matrix.mul_one] using transferMap_pow_apply' A K 1
  simpa only [Matrix.mul_assoc, Matrix.mul_sum] using
    congrArg (fun M => Matrix.frobeniusEquivEuclidean (Fin D) (Fin D) (X * M)) hsum

/-! ### Entrywise Cauchy–Schwarz for Frobenius-vectorised matrix product -/

/-- The squared norm of a Frobenius-vectorized matrix is the sum of its squared entry
norms. -/
private lemma frobeniusEquivEuclidean_norm_sq (X : Matrix (Fin D) (Fin D) ℂ) :
    ‖Matrix.frobeniusEquivEuclidean (Fin D) (Fin D) X‖ ^ 2 =
      ∑ i : Fin D, ∑ j : Fin D, ‖X i j‖ ^ 2 := by
  let U := Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)
  calc
    ‖U X‖ ^ 2 = (∑ p : (Fin D × Fin D), ‖(U X) p‖ ^ 2) := by
      rw [EuclideanSpace.norm_sq_eq]
    _ = (∑ p : (Fin D × Fin D), ‖X p.2 p.1‖ ^ 2) := by
      dsimp [U, Matrix.frobeniusEquivEuclidean]
    _ = (∑ j : Fin D, ∑ i : Fin D, ‖X i j‖ ^ 2) := by
      simpa only [Finset.univ_product_univ] using
        (Finset.sum_product'
          (s := (Finset.univ : Finset (Fin D)))
          (t := (Finset.univ : Finset (Fin D)))
          (f := fun j i ↦ ‖X i j‖ ^ 2))
    _ = ∑ i : Fin D, ∑ j : Fin D, ‖X i j‖ ^ 2 := Finset.sum_comm

/-- The squared Frobenius-vector norm of a matrix product is at most the product of the
squared Frobenius-vector norms. -/
private lemma frobenius_vec_mul_norm_sq_le (X M : Matrix (Fin D) (Fin D) ℂ) :
    ‖(Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)) (X * M)‖ ^ 2 ≤
    ‖(Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)) X‖ ^ 2 *
    ‖(Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)) M‖ ^ 2 := by
  let U := Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)
  have hUX := frobeniusEquivEuclidean_norm_sq X
  have hUM := frobeniusEquivEuclidean_norm_sq M
  have hUprod := frobeniusEquivEuclidean_norm_sq (X * M)
  rw [hUprod, hUX, hUM]
  calc
    (∑ i : Fin D, ∑ j : Fin D, ‖(X * M) i j‖ ^ 2) =
        (∑ i : Fin D, ∑ j : Fin D, ‖∑ k : Fin D, X i k * M k j‖ ^ 2) := by
      simp [Matrix.mul_apply]
    _ ≤ (∑ i : Fin D, ∑ j : Fin D,
        (∑ k : Fin D, ‖X i k‖ ^ 2) * (∑ k : Fin D, ‖M k j‖ ^ 2)) := by
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
      calc
        ‖∑ k : Fin D, X i k * M k j‖ ^ 2 ≤
            (∑ k : Fin D, ‖X i k * M k j‖) ^ 2 := by
          gcongr
          exact norm_sum_le _ _
        _ = (∑ k : Fin D, ‖X i k‖ * ‖M k j‖) ^ 2 := by
          simp_rw [norm_mul]
        _ ≤ (∑ k : Fin D, ‖X i k‖ ^ 2) * (∑ k : Fin D, ‖M k j‖ ^ 2) :=
          Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) (s := Finset.univ)
            (f := fun k => ‖X i k‖) (g := fun k => ‖M k j‖)
    _ = (∑ i : Fin D, ∑ k : Fin D, ‖X i k‖ ^ 2) *
        (∑ k : Fin D, ∑ j : Fin D, ‖M k j‖ ^ 2) := by
      have htemp : (∑ i : Fin D, ∑ j : Fin D,
          (∑ k : Fin D, ‖X i k‖ ^ 2) * (∑ k : Fin D, ‖M k j‖ ^ 2)) =
          (∑ i : Fin D, ∑ k : Fin D, ‖X i k‖ ^ 2) *
          (∑ k : Fin D, ∑ j : Fin D, ‖M k j‖ ^ 2) := by
        calc
          (∑ i : Fin D, ∑ j : Fin D,
              (∑ k : Fin D, ‖X i k‖ ^ 2) * (∑ k : Fin D, ‖M k j‖ ^ 2))
          = (∑ i : Fin D, (∑ k : Fin D, ‖X i k‖ ^ 2) *
              (∑ j : Fin D, ∑ k : Fin D, ‖M k j‖ ^ 2)) := by
            simp_rw [← Finset.mul_sum]
          _ = (∑ i : Fin D, ∑ k : Fin D, ‖X i k‖ ^ 2) *
              (∑ j : Fin D, ∑ k : Fin D, ‖M k j‖ ^ 2) := by
            rw [← Finset.sum_mul]
          _ = (∑ i : Fin D, ∑ k : Fin D, ‖X i k‖ ^ 2) *
              (∑ k : Fin D, ∑ j : Fin D, ‖M k j‖ ^ 2) := by
            congr 1
            rw [Finset.sum_comm]
      exact htemp

/-! ### Fourth-power operator-norm bound by entrywise mass -/

/-- The fourth power of the tail virtual map norm is bounded by the squared entrywise mass
of the iterated transfer map applied to the identity. -/
theorem tailVirtualMapES_norm_four_pow_le_transferMap_pow_one_entry_norm_sq
    (A : MPSTensor d D) (K : ℕ) :
    ‖tailVirtualMapES A K‖ ^ 4 ≤
      ∑ p : (Fin D × Fin D),
        ‖(((transferMap (d := d) (D := D) A) ^ K) 1) p.1 p.2‖ ^ 2 := by
  let M := ((transferMap (d := d) (D := D) A) ^ K) 1
  let U := Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)
  have hnorm_adj_sq : ‖(tailVirtualMapES A K).adjoint ∘L (tailVirtualMapES A K)‖ =
      ‖tailVirtualMapES A K‖ * ‖tailVirtualMapES A K‖ :=
    ContinuousLinearMap.norm_adjoint_comp_self (tailVirtualMapES A K)
  have hsq : ‖tailVirtualMapES A K‖ ^ 2 = ‖(tailVirtualMapES A K).adjoint ∘L
      (tailVirtualMapES A K)‖ := by
    simpa only [pow_two] using hnorm_adj_sq.symm
  let S := (tailVirtualMapES A K).adjoint ∘L (tailVirtualMapES A K)
  have hS_bound (x : EuclideanSpace ℂ (Fin D × Fin D)) : ‖S x‖ ≤ ‖x‖ * ‖U M‖ := by
    let X := U.symm x
    have hx : x = U X := (U.apply_symm_apply x).symm
    have hSx : S (U X) = U (X * M) := by
      dsimp [S]
      simpa [M, U, ContinuousLinearMap.coe_comp] using
        tailVirtualMapES_adjoint_comp_self_apply A K X
    rw [hx, hSx]
    have h_sq : ‖U (X * M)‖ ^ 2 ≤ ‖U X‖ ^ 2 * ‖U M‖ ^ 2 := by
      simpa [U] using frobenius_vec_mul_norm_sq_le X M
    rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)), mul_pow]
    exact h_sq
  have hS_opNorm : ‖S‖ ≤ ‖U M‖ :=
    ContinuousLinearMap.opNorm_le_bound S (norm_nonneg _) fun x => by
      simpa [mul_comm] using hS_bound x
  have hU_sq : ‖U M‖ ^ 2 = ∑ i : Fin D, ∑ j : Fin D, ‖M i j‖ ^ 2 := by
    simpa only [U] using frobeniusEquivEuclidean_norm_sq M
  have hRHS : (∑ p : (Fin D × Fin D), ‖M p.1 p.2‖ ^ 2) = ‖U M‖ ^ 2 := by
    rw [hU_sq, Fintype.sum_prod_type]
  calc
    ‖tailVirtualMapES A K‖ ^ 4 = (‖tailVirtualMapES A K‖ ^ 2) ^ 2 := by ring
    _ = ‖S‖ ^ 2 := by rw [hsq]
    _ ≤ ‖U M‖ ^ 2 := by nlinarith [hS_opNorm, norm_nonneg (U M)]
    _ = ∑ p : (Fin D × Fin D), ‖M p.1 p.2‖ ^ 2 := by rw [hRHS]

end FrobeniusCoordinate

end MPSTensor
