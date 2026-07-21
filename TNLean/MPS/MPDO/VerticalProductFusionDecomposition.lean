/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.VerticalBlockedOperatorRepresentations
import TNLean.MPS.Tactic.Basic

/-!
# Positive fusion decompositions of vertical product tensors

This file begins the construction of the positive unitary decompositions of
the products of vertical basis-of-normal-tensors sectors in CPSV16,
Appendix C.4, lines 2020--2029.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.4, lines 2020--2029
-/

open scoped Matrix BigOperators Kronecker

noncomputable section

namespace MPOTensor

/-- The Kronecker square of a rectangular vertical coisometry, with both
product index spaces encoded by the standard finite-product equivalence. -/
noncomputable def verticalCoisometrySquare {d n : ℕ}
    (U : Matrix (Fin n) (Fin d) ℂ) :
    Matrix (Fin (n * n)) (Fin (d * d)) ℂ :=
  (U ⊗ₖ U).submatrix finProdFinEquiv.symm finProdFinEquiv.symm

/-- Equality of all positive-length closed MPOs gives equality of the
corresponding positive-length matrix product vectors after joining each ket
and bra index into one doubled physical index.

This bridge converts the closed-operator identities preceding the Figure 11
argument into matrix-product-vector identities. It does not isolate any fixed
pair of vertical BNT labels.

Source: CPSV16, Appendix C.4, lines 2011--2020. -/
theorem sameMPV₂Pos_toMPSTensor_of_mpo_eq
    {d D₁ D₂ : ℕ} (M₁ : MPOTensor d D₁) (M₂ : MPOTensor d D₂)
    (h : ∀ L, 0 < L → mpo M₁ L = mpo M₂ L) :
    MPSTensor.SameMPV₂Pos M₁.toMPSTensor M₂.toMPSTensor := by
  mpv_ext
  let ket : Fin N → Fin d := fun n ↦ (σ n).divNat
  let bra : Fin N → Fin d := fun n ↦ (σ n).modNat
  have hpair : (fun n ↦ finProdFinEquiv (ket n, bra n)) = σ := by
    funext n
    exact finProdFinEquiv.apply_symm_apply (σ n)
  calc
    MPSTensor.mpv M₁.toMPSTensor σ =
        MPSTensor.mpv M₁.toMPSTensor
          (fun n ↦ finProdFinEquiv (ket n, bra n)) := by rw [hpair]
    _ = mpo M₁ N ket bra := MPSTensor.mpv_toMPSTensor_pairConfig M₁ ket bra
    _ = mpo M₂ N ket bra := by rw [h N hN]
    _ = MPSTensor.mpv M₂.toMPSTensor
          (fun n ↦ finProdFinEquiv (ket n, bra n)) :=
      (MPSTensor.mpv_toMPSTensor_pairConfig M₂ ket bra).symm
    _ = MPSTensor.mpv M₂.toMPSTensor σ := by rw [hpair]

/-- Squaring an exact one-site vertical reconstruction gives an exact
two-site reconstruction through the Kronecker square of the same coisometry.

The retained two-site tensor is the product of two copies of the retained
one-site tensor. This is a tensor-level identity; it does not infer support
of any fixed pair of BNT labels from the closed-chain sum.

Source: CPSV16, Appendix C.4, lines 2015--2025. -/
theorem verticalTensor_blockTwo_squared_coisometry_reconstruction
    {d D n : ℕ} (M : MPOTensor d D) (A : MPSTensor (D * D) n)
    (U : Matrix (Fin n) (Fin d) ℂ) (hU : U * Uᴴ = 1)
    (hReconstruct : ∀ ab, verticalTensor M ab = Uᴴ * A ab * U) :
    verticalCoisometrySquare U * (verticalCoisometrySquare U)ᴴ = 1 ∧
      ∀ ab, verticalTensor (blockTwo M) ab =
        (verticalCoisometrySquare U)ᴴ *
          (mulTensor (verticalBNTMPO A) (verticalBNTMPO A)).toMPSTensor ab *
            verticalCoisometrySquare U := by
  constructor
  · unfold verticalCoisometrySquare
    rw [Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv _ _ _ finProdFinEquiv.symm _,
      Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hU,
      Matrix.one_kronecker_one, Matrix.submatrix_one_equiv]
  · intro ab
    rw [← verticalBNTMPO_toMPSTensor (verticalTensor (blockTwo M)),
      verticalBNTMPO_verticalTensor_blockTwo]
    obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective ab
    unfold verticalCoisometrySquare
    simp only [toMPSTensor, mulTensor_apply, verticalBNTMPO_apply,
      MPSTensor.finProdFinEquiv_divNat, MPSTensor.finProdFinEquiv_modNat]
    rw [Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv _ _ _ finProdFinEquiv.symm _,
      Matrix.submatrix_mul_equiv _ _ _ finProdFinEquiv.symm _]
    congr 1
    rw [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hReconstruct, hReconstruct, Matrix.conjTranspose_kronecker,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]

end MPOTensor
