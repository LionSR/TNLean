/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.IsingFusionAlgebra

/-!
# Ising anyon chain: the fusion rules of σ with the vacuum

**Source.** Bultinck, Mariën, Williamson, Sahinoglu, Haegeman, Verstraete 2017
(arXiv:1511.08090), Appendix D.2 "Ising string-net",
`References/1511.08090/AnyonsPEPS.tex` lines 1305–1323: the fusion rule `1 × σ = σ × 1 = σ`
(lines 1308–1312).
The operators are built from the `G`-symbols "similarly as for the Fibonacci model" (line 1323),
whose operator blocks "satisfy the Fibonacci fusion rules" (line 1268); for Ising the source prints
only the fusion rules of the category, so the operator identities here are the Ising analogue of
line 1268, implied but not printed.

**Formalized here.** At every positive length, `O_1 O_σ = O_σ O_1 = O_σ` for the periodic
operator `O_σ` of `√2 A_σ`, and hence for the periodic operator of the unscaled tensor `A_σ`:
by `MPOTensor.mpo_smul`, rescaling the tensor by `(√2)⁻¹` rescales its length-`N` operator by
`(√2)⁻ᴺ`, and both identities are homogeneous of degree one in `O_σ`.

**Local fix (sigma scaling):** the tensors omit the factors `v_e v_f` of the `G`-symbols
(lines 1257–1260) and store the `σ` tensor multiplied by `√2`; the identities are proved for
these `v`-free tensors. Documented in
`docs/paper-gaps/bmwshv17_ising_boundary_tensor_normalization.tex`.

Each identity is one application of `MPSTensor.mpo_mul_eq_of_zsqrt2_conj` with a signed
permutation gauge of `IsingFusionAlgebra`; the letter identities are decided over `ℤ[√2]`.

## Main results

* `IsingTwist.isingOne_mul_isingSigma`, `IsingTwist.isingSigma_mul_isingOne`.
* `IsingTwist.isingOne_mul_isingSigma_normalized`,
  `IsingTwist.isingSigma_normalized_mul_isingOne`: the same identities for the unscaled
  tensor `A_σ`.

## References
- [arXiv:1511.08090](https://arxiv.org/abs/1511.08090) -- N. Bultinck, M. Mariën,
  D. J. Williamson, M. B. Sahinoglu, J. Haegeman, F. Verstraete, *Anyons and matrix product
  operator algebras*
-/

open scoped Matrix

namespace IsingTwist

open MPSTensor Zsqrtd

/-- **`O_1 O_σ = O_σ`.** Source: arXiv:1511.08090, lines 1308–1312 and 1323: the fusion rule
`1 × σ = σ` for the periodic operators of the tensors built as in lines 1257–1268, at every positive
length. This is the Ising analogue of line 1268, which states the operator fusion rules only for the
Fibonacci blocks. -/
theorem isingOne_mul_isingSigma {N : ℕ} (hN : 0 < N) :
    MPOTensor.mpo isingOne N * MPOTensor.mpo isingSigma N = MPOTensor.mpo isingSigma N :=
  mpo_mul_eq_of_zsqrt2_conj isingOneZ isingSigmaZ isingSigmaZ (z := 8) isingGaugeOneSigmaZ
    isingGaugeOneSigmaZᵀ 1 one_ne_zero (by rw [one_smul]; decide +kernel)
    (by rw [one_smul]; decide +kernel)
    (isingConj_of_rho_eq isingOneZ_eq_zero_of_rho_ne isingSigmaZ_eq_zero_of_rho_ne
      isingSigmaZ_eq_zero_of_rho_ne fun i j _ => by
      rw [one_smul]
      refine (mul_mulTensorR_mul_transpose_eq_list _ _ _ _ _ _ _ _
        isingOneZ_eq_smul_single isingSigmaZ_eq_smul_single isingOneNext isingOneNext_nodup
        isingOneCoef_eq_zero _ i j).trans ?_
      rw [isingSigmaZ_eq_smul_single i j, padZsqrt2_smul_single]
      revert i j
      decide +kernel) hN

/-- **`O_σ O_1 = O_σ`.** Source: arXiv:1511.08090, lines 1308–1312 and 1323: the fusion rule
`σ × 1 = σ` for the periodic operators of the tensors built as in lines 1257–1268, at every positive
length. This is the Ising analogue of line 1268, which states the operator fusion rules only for the
Fibonacci blocks. -/
theorem isingSigma_mul_isingOne {N : ℕ} (hN : 0 < N) :
    MPOTensor.mpo isingSigma N * MPOTensor.mpo isingOne N = MPOTensor.mpo isingSigma N :=
  mpo_mul_eq_of_zsqrt2_conj isingSigmaZ isingOneZ isingSigmaZ (z := 8) isingGaugeSigmaOneZ
    isingGaugeSigmaOneZᵀ 1 one_ne_zero (by rw [one_smul]; decide +kernel)
    (by rw [one_smul]; decide +kernel)
    (isingConj_of_rho_eq isingSigmaZ_eq_zero_of_rho_ne isingOneZ_eq_zero_of_rho_ne
      isingSigmaZ_eq_zero_of_rho_ne fun i j _ => by
      rw [one_smul]
      refine (mul_mulTensorR_mul_transpose_eq_list _ _ _ _ _ _ _ _
        isingSigmaZ_eq_smul_single isingOneZ_eq_smul_single isingSigmaNext isingSigmaNext_nodup
        isingSigmaCoef_eq_zero _ i j).trans ?_
      rw [isingSigmaZ_eq_smul_single i j, padZsqrt2_smul_single]
      revert i j
      decide +kernel) hN

/-- **`O_1 O_σ = O_σ` for the unscaled tensor.** Source: arXiv:1511.08090, lines 1308–1312 and 1323,
as in `isingOne_mul_isingSigma`: for `(√2)⁻¹ • isingSigma`, the unscaled tensor `A_σ`
of this module (`v`-free, see the module's Local fix; the stored `isingSigma` is `√2 A_σ`),
the fusion rule `1 × σ = σ` holds at every positive length. -/
theorem isingOne_mul_isingSigma_normalized {N : ℕ} (hN : 0 < N) :
    MPOTensor.mpo isingOne N * MPOTensor.mpo ((Real.sqrt 2 : ℂ)⁻¹ • isingSigma) N =
      MPOTensor.mpo ((Real.sqrt 2 : ℂ)⁻¹ • isingSigma) N := by
  rw [MPOTensor.mpo_smul, Matrix.mul_smul, isingOne_mul_isingSigma hN]

/-- **`O_σ O_1 = O_σ` for the unscaled tensor.** Source: arXiv:1511.08090, lines 1308–1312 and 1323,
as in `isingSigma_mul_isingOne`: for `(√2)⁻¹ • isingSigma`, the unscaled tensor `A_σ`
of this module (`v`-free, see the module's Local fix; the stored `isingSigma` is `√2 A_σ`),
the fusion rule `σ × 1 = σ` holds at every positive length. -/
theorem isingSigma_normalized_mul_isingOne {N : ℕ} (hN : 0 < N) :
    MPOTensor.mpo ((Real.sqrt 2 : ℂ)⁻¹ • isingSigma) N * MPOTensor.mpo isingOne N =
      MPOTensor.mpo ((Real.sqrt 2 : ℂ)⁻¹ • isingSigma) N := by
  rw [MPOTensor.mpo_smul, Matrix.smul_mul, isingSigma_mul_isingOne hN]

end IsingTwist
