/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Examples.CZX.CZXPlusIdentity
import TNLean.MPS.Examples.CZX.CZXUnitary
import TNLean.MPS.MPDO.DirectSum
import TNLean.MPS.MPDO.IdentityTensor

/-!
# CZX plus identity: projectors on even rings and inverses on odd rings

**Source.** Construction of this development. The input is the CZX operator of the review,
arXiv:2011.12127, Appendix A, "The CZX MPU", `Papers/2011.12127/TN-Review-main.tex`
lines 2582–2601, which is unitary and squares to `(-1)^N I`; the family `O_N = I_N + U_N`
does not occur in the review.

**Formalized here.** The bond-three tensor `N = δ ⊕ M` of `CZXPlusIdentity` generates
`O_N = I_N + U_N` at every length. For even `N > 0` the operator `O_N / 2` is an orthogonal
projector (self-adjoint and idempotent); for odd `N > 0` the operator `O_N` is invertible with
inverse `(I_N - U_N) / 2`. Both follow from unitarity of `U_N` and `U_N² = (-1)^N I_N`.

## Main results

* `CZXCompression.plusTensor_eq_directSum`, `CZXCompression.mpo_plusTensor`: the bond-three
  tensor is the direct sum of the identity tensor and the CZX tensor, so it generates
  `I_N + U_N`.
* `CZXCompression.isStarProjection_half_one_add_mpo_czxTensor`: for even `N > 0`, `O_N / 2`
  is an orthogonal projector.
* `CZXCompression.one_add_mpo_czxTensor_mul_half_one_sub`,
  `CZXCompression.half_one_sub_mul_one_add_mpo_czxTensor`,
  `CZXCompression.inv_one_add_mpo_czxTensor`: for odd `N`, `(I_N - U_N) / 2` is the two-sided
  inverse of `O_N`.

## References

- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- J. I. Cirac, D. Pérez-García,
  N. Schuch, F. Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*
-/

noncomputable section

open scoped Matrix

namespace CZXCompression

open MPSTensor

/-! ### The operator family of the bond-three tensor -/

/-- Bridge: the bond-three tensor `N = δ ⊕ M` is the direct sum of the bond-one identity
tensor and the CZX tensor. -/
theorem plusTensor_eq_directSum :
    plusTensor = MPOTensor.directSum (MPOTensor.idTensor 2) czxTensor := by
  funext i j
  ext a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [plusTensor, plusIntTensor, czxTensor, czxIntTensor, MPOTensor.directSum,
      MPOTensor.idTensor, finSumFinEquiv, Fin.addCases, Fin.castLT,
      Fin.subNat]

/-- Bridge: the bond-three tensor generates `O_N = I_N + U_N` at every length. -/
theorem mpo_plusTensor (N : ℕ) :
    MPOTensor.mpo plusTensor N = 1 + MPOTensor.mpo czxTensor N := by
  rw [plusTensor_eq_directSum, MPOTensor.mpo_directSum, MPOTensor.mpo_idTensor]

variable {N : ℕ} [NeZero N]

/-! ### Even rings -/

/-- On even rings the CZX operator is an involution. -/
theorem mpo_czxTensor_mul_self_of_even (hN : Even N) :
    MPOTensor.mpo czxTensor N * MPOTensor.mpo czxTensor N = 1 := by
  rw [mpo_czxTensor_mul_self, hN.neg_one_pow, one_smul]

/-- On even rings the CZX operator is self-adjoint: a unitary involution equals its adjoint. -/
theorem star_mpo_czxTensor_of_even (hN : Even N) :
    star (MPOTensor.mpo czxTensor N) = MPOTensor.mpo czxTensor N := by
  have hU := Matrix.mem_unitaryGroup_iff.mp (mpo_czxTensor_mem_unitaryGroup (N := N))
  calc star (MPOTensor.mpo czxTensor N)
      = (MPOTensor.mpo czxTensor N * MPOTensor.mpo czxTensor N) *
          star (MPOTensor.mpo czxTensor N) := by
        rw [mpo_czxTensor_mul_self_of_even hN, one_mul]
    _ = MPOTensor.mpo czxTensor N := by rw [mul_assoc, hU, mul_one]

/-- **Source-aligned:** `lem:asymex_plus_parity`, even case. For even `N > 0`, the operator
`O_N / 2 = (I_N + U_N) / 2` is an orthogonal projector. -/
theorem isStarProjection_half_one_add_mpo_czxTensor (hN : Even N) :
    IsStarProjection ((2 : ℂ)⁻¹ • (1 + MPOTensor.mpo czxTensor N)) := by
  set U := MPOTensor.mpo czxTensor N
  have hUU : U * U = 1 := mpo_czxTensor_mul_self_of_even hN
  have hstar : star U = U := star_mpo_czxTensor_of_even hN
  refine ⟨?_, ?_⟩
  · rw [IsIdempotentElem, smul_mul_smul_comm, add_mul, mul_add, mul_add, hUU, one_mul,
      mul_one, one_mul]
    rw [show (1 : Matrix _ _ ℂ) + U + (U + 1) = (2 : ℂ) • (1 + U) by
      rw [two_smul]; abel, smul_smul]
    norm_num
  · rw [IsSelfAdjoint, star_smul, star_add, star_one, hstar, star_inv₀, star_ofNat]

/-! ### Odd rings -/

/-- On odd rings the CZX operator squares to minus the identity. -/
theorem mpo_czxTensor_mul_self_of_odd (hN : Odd N) :
    MPOTensor.mpo czxTensor N * MPOTensor.mpo czxTensor N = -1 := by
  rw [mpo_czxTensor_mul_self, hN.neg_one_pow, neg_one_smul]

/-- **Source-aligned:** `lem:asymex_plus_parity`, odd case, right inverse. For odd `N > 0`,
`O_N (I_N - U_N) / 2 = I_N`. -/
theorem one_add_mpo_czxTensor_mul_half_one_sub (hN : Odd N) :
    (1 + MPOTensor.mpo czxTensor N) * ((2 : ℂ)⁻¹ • (1 - MPOTensor.mpo czxTensor N)) = 1 := by
  rw [mul_smul_comm, add_mul, mul_sub, mul_sub, mpo_czxTensor_mul_self_of_odd hN, one_mul,
    mul_one, one_mul, show (1 : Matrix _ _ ℂ) - MPOTensor.mpo czxTensor N +
      (MPOTensor.mpo czxTensor N - -1) = (2 : ℂ) • 1 by rw [two_smul]; abel, smul_smul]
  norm_num

/-- **Source-aligned:** `lem:asymex_plus_parity`, odd case, left inverse. For odd `N > 0`,
`(I_N - U_N) / 2 · O_N = I_N`. -/
theorem half_one_sub_mul_one_add_mpo_czxTensor (hN : Odd N) :
    ((2 : ℂ)⁻¹ • (1 - MPOTensor.mpo czxTensor N)) * (1 + MPOTensor.mpo czxTensor N) = 1 := by
  rw [smul_mul_assoc, sub_mul, mul_add, mul_add, mpo_czxTensor_mul_self_of_odd hN, one_mul,
    mul_one, one_mul, show (1 : Matrix _ _ ℂ) + MPOTensor.mpo czxTensor N -
      (MPOTensor.mpo czxTensor N + -1) = (2 : ℂ) • 1 by rw [two_smul]; abel, smul_smul]
  norm_num

/-- **Source-aligned:** `lem:asymex_plus_parity`, odd case. For odd `N > 0`, the operator
`O_N = I_N + U_N` is invertible, with inverse `(I_N - U_N) / 2`. -/
theorem inv_one_add_mpo_czxTensor (hN : Odd N) :
    (1 + MPOTensor.mpo czxTensor N)⁻¹ = (2 : ℂ)⁻¹ • (1 - MPOTensor.mpo czxTensor N) :=
  Matrix.inv_eq_right_inv (one_add_mpo_czxTensor_mul_half_one_sub hN)

end CZXCompression
