/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.IsingFusionAlgebra

/-!
# Ising anyon chain: the fusion rules of σ with the fermion

**Source.** Bultinck, Mariën, Williamson, Sahinoglu, Haegeman, Verstraete 2017
(arXiv:1511.08090), Appendix D.2 "Ising string-net",
`References/1511.08090/AnyonsPEPS.tex` lines 1305–1323: the fusion rule `ψ × σ = σ × ψ = σ`
(lines 1308–1312) and the
F-symbols `F^{ψσψ}_{σσσ} = F^{σψσ}_{ψσσ} = -1` (lines 1320–1321).
The operators are built from the `G`-symbols "similarly as for the Fibonacci model" (line 1323),
whose operator blocks "satisfy the Fibonacci fusion rules" (line 1268); for Ising the source prints
only the fusion rules of the category, so the operator identities here are the Ising analogue of
line 1268, implied but not printed.

**Formalized here.** At every positive length, `O_ψ O_σ = O_σ O_ψ = O_σ` for the periodic
operator `O_σ` of `√2 A_σ`; both sides are linear in `O_σ`, so the identities hold for every
rescaling of the `σ` tensor.

**Local fix (sigma scaling):** the tensors omit the factors `v_e v_f` of the `G`-symbols
(lines 1257–1260) and store the `σ` tensor multiplied by `√2`; the identities are proved for
these `v`-free tensors. Documented in
`docs/paper-gaps/bmwshv17_ising_boundary_tensor_normalization.tex`.

Each identity is one application of `MPSTensor.mpo_mul_eq_of_zsqrt2_conj` with a signed
permutation gauge of `IsingFusionAlgebra`; the letter identities are decided over `ℤ[√2]`.

## Main results

* `IsingTwist.isingPsi_mul_isingSigma`, `IsingTwist.isingSigma_mul_isingPsi`.

## References
- [arXiv:1511.08090](https://arxiv.org/abs/1511.08090) -- N. Bultinck, M. Mariën,
  D. J. Williamson, M. B. Sahinoglu, J. Haegeman, F. Verstraete, *Anyons and matrix product
  operator algebras*
-/

open scoped Matrix

namespace IsingTwist

open MPSTensor Zsqrtd

/-- **`O_ψ O_σ = O_σ`.** Source: arXiv:1511.08090, lines 1308–1312 and 1323: the fusion rule
`ψ × σ = σ` for the periodic operators of the tensors built as in lines 1257–1268, at every positive
length. This is the Ising analogue of line 1268, which states the operator fusion rules only for the
Fibonacci blocks. The gauge carries the F-symbol `F^{ψσψ}_{σσσ} = -1` of line 1320. -/
theorem isingPsi_mul_isingSigma {N : ℕ} (hN : 0 < N) :
    MPOTensor.mpo isingPsi N * MPOTensor.mpo isingSigma N = MPOTensor.mpo isingSigma N :=
  mpo_mul_eq_of_zsqrt2_conj isingPsiZ isingSigmaZ isingSigmaZ (z := 8) isingGaugePsiSigmaZ
    isingGaugePsiSigmaZᵀ 1 one_ne_zero (by rw [one_smul]; decide +kernel)
    (by rw [one_smul]; decide +kernel)
    (isingConj_of_rho_eq isingPsiZ_eq_zero_of_rho_ne isingSigmaZ_eq_zero_of_rho_ne
      isingSigmaZ_eq_zero_of_rho_ne fun i j _ => by
      rw [one_smul]
      refine (mul_mulTensorR_mul_transpose_eq_list _ _ _ _ _ _ _ _
        isingPsiZ_eq_smul_single isingSigmaZ_eq_smul_single isingPsiNext isingPsiNext_nodup
        isingPsiCoef_eq_zero _ i j).trans ?_
      rw [isingSigmaZ_eq_smul_single i j, padZsqrt2_smul_single]
      revert i j
      decide +kernel) hN

/-- **`O_σ O_ψ = O_σ`.** Source: arXiv:1511.08090, lines 1308–1312 and 1323: the fusion rule
`σ × ψ = σ` for the periodic operators of the tensors built as in lines 1257–1268, at every positive
length. This is the Ising analogue of line 1268, which states the operator fusion rules only for the
Fibonacci blocks. The gauge carries the F-symbol `F^{σψσ}_{ψσσ} = -1` of line 1321. -/
theorem isingSigma_mul_isingPsi {N : ℕ} (hN : 0 < N) :
    MPOTensor.mpo isingSigma N * MPOTensor.mpo isingPsi N = MPOTensor.mpo isingSigma N :=
  mpo_mul_eq_of_zsqrt2_conj isingSigmaZ isingPsiZ isingSigmaZ (z := 8) isingGaugeSigmaPsiZ
    isingGaugeSigmaPsiZᵀ 1 one_ne_zero (by rw [one_smul]; decide +kernel)
    (by rw [one_smul]; decide +kernel)
    (isingConj_of_rho_eq isingSigmaZ_eq_zero_of_rho_ne isingPsiZ_eq_zero_of_rho_ne
      isingSigmaZ_eq_zero_of_rho_ne fun i j _ => by
      rw [one_smul]
      refine (mul_mulTensorR_mul_transpose_eq_list _ _ _ _ _ _ _ _
        isingSigmaZ_eq_smul_single isingPsiZ_eq_smul_single isingSigmaNext isingSigmaNext_nodup
        isingSigmaCoef_eq_zero _ i j).trans ?_
      rw [isingSigmaZ_eq_smul_single i j, padZsqrt2_smul_single]
      revert i j
      decide +kernel) hN

end IsingTwist
