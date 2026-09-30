/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Examples.Ising.IsingFusionAlgebra

/-!
# Ising anyon chain: the fusion rules of the vacuum and fermion operators

**Source.** Bultinck, Mariën, Williamson, Sahinoglu, Haegeman, Verstraete 2017
(arXiv:1511.08090), Appendix D.2 "Ising string-net",
`References/1511.08090/AnyonsPEPS.tex` lines 1305–1323: the fusion rules `1 × 1 = 1`,
`1 × ψ = ψ × 1 = ψ`, `ψ × ψ = 1` (lines 1308–1312).
The operators are built from the `G`-symbols "similarly as for the Fibonacci model" (line 1323),
whose operator blocks "satisfy the Fibonacci fusion rules" (line 1268); for Ising the source prints
only the fusion rules of the category, so the operator identities here are the Ising analogue of
line 1268, implied but not printed.

**Formalized here.** At every positive length, `O_1 O_1 = O_1`, `O_1 O_ψ = O_ψ O_1 = O_ψ`
and `O_ψ O_ψ = O_1` for the periodic operators of `A_1` and `A_ψ`. Consequently
`O_ψᴴ O_ψ = O_1`, so `O_ψ` is a partial isometry with initial projection `O_1`; since `O_1` is not
the identity at any positive length, `O_ψ` is not unitary on the whole physical space.

**Local fix (sigma scaling):** the tensors omit the factors `v_e v_f` of the `G`-symbols
(lines 1257–1260) and store the `σ` tensor multiplied by `√2`; the identities are proved for
these `v`-free tensors. Documented in
`docs/paper-gaps/bmwshv17_ising_boundary_tensor_normalization.tex`.

Each identity is one application of `MPSTensor.mpo_mul_eq_of_zsqrt2_conj` with a signed
permutation gauge of `IsingFusionAlgebra`; the letter identities are decided over `ℤ[√2]`.

## Main results

* `IsingTwist.isingOne_mul_isingOne`, `IsingTwist.isingOne_mul_isingPsi`,
  `IsingTwist.isingPsi_mul_isingOne`, `IsingTwist.isingPsi_mul_isingPsi`.
* `IsingTwist.isingPsi_conjTranspose_mul_isingPsi`: `O_ψᴴ O_ψ = O_1`.
* `IsingTwist.mpo_isingOne_ne_one`, `IsingTwist.mpo_isingPsi_notMem_unitaryGroup`: `O_1 ≠ 1`, and
  `O_ψ` is not unitary.

## References
- [arXiv:1511.08090](https://arxiv.org/abs/1511.08090) -- N. Bultinck, M. Mariën,
  D. J. Williamson, M. B. Sahinoglu, J. Haegeman, F. Verstraete, *Anyons and matrix product
  operator algebras*
-/

open scoped Matrix

namespace IsingTwist

open MPSTensor Zsqrtd

/-- **`O_1 O_1 = O_1`.** Source: arXiv:1511.08090, lines 1308–1312 and 1323: the fusion rule
`1 × 1 = 1` for the periodic operators of the tensors built as in lines 1257–1268, at every positive
length. This is the Ising analogue of line 1268, which states the operator fusion rules only for the
Fibonacci blocks. -/
theorem isingOne_mul_isingOne {N : ℕ} (hN : 0 < N) :
    MPOTensor.mpo isingOne N * MPOTensor.mpo isingOne N = MPOTensor.mpo isingOne N :=
  isingFusion_of_signedPerm isingOneZ isingOneZ isingOneZ isingOneZ_eq_smul_single
    isingOneZ_eq_smul_single isingOneZ_eq_smul_single isingOneNext isingOneNext_nodup
    isingOneCoef_eq_zero isingOneZ_eq_zero_of_rho_ne isingOneZ_eq_zero_of_rho_ne
    isingOneZ_eq_zero_of_rho_ne (z := 6) isingGaugeOneOneZ
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hN

/-- **`O_1 O_ψ = O_ψ`.** Source: arXiv:1511.08090, lines 1308–1312 and 1323: the fusion rule
`1 × ψ = ψ` for the periodic operators of the tensors built as in lines 1257–1268, at every positive
length. This is the Ising analogue of line 1268, which states the operator fusion rules only for the
Fibonacci blocks. The gauge is that of `A_ψ ⋆ A_ψ`. -/
theorem isingOne_mul_isingPsi {N : ℕ} (hN : 0 < N) :
    MPOTensor.mpo isingOne N * MPOTensor.mpo isingPsi N = MPOTensor.mpo isingPsi N :=
  isingFusion_of_signedPerm isingOneZ isingPsiZ isingPsiZ isingOneZ_eq_smul_single
    isingPsiZ_eq_smul_single isingPsiZ_eq_smul_single isingOneNext isingOneNext_nodup
    isingOneCoef_eq_zero isingOneZ_eq_zero_of_rho_ne isingPsiZ_eq_zero_of_rho_ne
    isingPsiZ_eq_zero_of_rho_ne (z := 6) isingGaugePsiPsiZ
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hN

/-- **`O_ψ O_1 = O_ψ`.** Source: arXiv:1511.08090, lines 1308–1312 and 1323: the fusion rule
`ψ × 1 = ψ` for the periodic operators of the tensors built as in lines 1257–1268, at every positive
length. This is the Ising analogue of line 1268, which states the operator fusion rules only for the
Fibonacci blocks. The gauge is that of `A_1 ⋆ A_1`. -/
theorem isingPsi_mul_isingOne {N : ℕ} (hN : 0 < N) :
    MPOTensor.mpo isingPsi N * MPOTensor.mpo isingOne N = MPOTensor.mpo isingPsi N :=
  isingFusion_of_signedPerm isingPsiZ isingOneZ isingPsiZ isingPsiZ_eq_smul_single
    isingOneZ_eq_smul_single isingPsiZ_eq_smul_single isingPsiNext isingPsiNext_nodup
    isingPsiCoef_eq_zero isingPsiZ_eq_zero_of_rho_ne isingOneZ_eq_zero_of_rho_ne
    isingPsiZ_eq_zero_of_rho_ne (z := 6) isingGaugeOneOneZ
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hN

/-- **`O_ψ O_ψ = O_1`.** Source: arXiv:1511.08090, lines 1308–1312 and 1323: the fusion rule
`ψ × ψ = 1` for the periodic operators of the tensors built as in lines 1257–1268, at every positive
length. This is the Ising analogue of line 1268, which states the operator fusion rules only for the
Fibonacci blocks. -/
theorem isingPsi_mul_isingPsi {N : ℕ} (hN : 0 < N) :
    MPOTensor.mpo isingPsi N * MPOTensor.mpo isingPsi N = MPOTensor.mpo isingOne N :=
  isingFusion_of_signedPerm isingPsiZ isingPsiZ isingOneZ isingPsiZ_eq_smul_single
    isingPsiZ_eq_smul_single isingOneZ_eq_smul_single isingPsiNext isingPsiNext_nodup
    isingPsiCoef_eq_zero isingPsiZ_eq_zero_of_rho_ne isingPsiZ_eq_zero_of_rho_ne
    isingOneZ_eq_zero_of_rho_ne (z := 6) isingGaugePsiPsiZ
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hN

/-- **`O_ψ` is a partial isometry onto the closed paths.** Project result, from
`mpo_isingPsi_conjTranspose` and `isingPsi_mul_isingPsi`: at every positive length
`O_ψᴴ O_ψ = O_1`, the projector onto the closed fusion paths. -/
theorem isingPsi_conjTranspose_mul_isingPsi {N : ℕ} (hN : 0 < N) :
    (MPOTensor.mpo isingPsi N)ᴴ * MPOTensor.mpo isingPsi N = MPOTensor.mpo isingOne N := by
  rw [mpo_isingPsi_conjTranspose hN, isingPsi_mul_isingPsi hN]

/-- **The vacuum operator is not the identity.** Project result: at every positive length the
constant configuration with the label `(1, ψ, ψ)` is not a closed fusion path, so the diagonal
entry of `O_1` there is `0`. -/
theorem mpo_isingOne_ne_one {N : ℕ} (hN : 0 < N) : MPOTensor.mpo isingOne N ≠ 1 := by
  intro h
  have hentry := congrFun (congrFun h fun _ => 1) fun _ => 1
  rw [mpo_isingOne_apply hN, Matrix.one_apply_eq] at hentry
  have hopen : ¬ IsAdmissiblePath (N := N) fun _ => (1 : Fin 10) := fun hp =>
    absurd (hp ⟨0, hN⟩) (by decide : ¬ isingRight 1 = isingLeft 1)
  simp [hopen] at hentry

/-- **The fermion operator is not unitary.** Project result: at every positive length
`O_ψᴴ O_ψ = O_1 ≠ 1` (`isingPsi_conjTranspose_mul_isingPsi`, `mpo_isingOne_ne_one`), so `O_ψ` is
a partial isometry on the closed paths but not a unitary of the whole physical space. -/
theorem mpo_isingPsi_notMem_unitaryGroup {N : ℕ} (hN : 0 < N) :
    MPOTensor.mpo isingPsi N ∉ Matrix.unitaryGroup (Fin N → Fin 10) ℂ := fun hU =>
  mpo_isingOne_ne_one hN <| by
    rw [← isingPsi_conjTranspose_mul_isingPsi hN]
    exact Matrix.mem_unitaryGroup_iff'.1 hU

end IsingTwist
