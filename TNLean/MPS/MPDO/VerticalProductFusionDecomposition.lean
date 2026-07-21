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

open scoped Matrix

noncomputable section

namespace MPOTensor

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

end MPOTensor
