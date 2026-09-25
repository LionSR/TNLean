/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.IsingFusionAlgebra

/-!
# Ising anyon chain: the fusion rule `σ × σ = 1 + ψ`

**Source.** Bultinck, Mariën, Williamson, Sahinoglu, Haegeman, Verstraete 2017
(arXiv:1511.08090), Appendix D.2 "Ising string-net",
`References/1511.08090/AnyonsPEPS.tex` lines 1305–1323: the only nontrivial fusion rule of the
Ising category is `σ × σ = 1 + ψ` (line 1312), with the F-symbols `F^{σσσ}_{σ a b} = ± 1/√2`
(lines 1316–1319). The operators are built from the `G`-symbols "similarly as for the Fibonacci
model" (line 1323), whose operator blocks "satisfy the Fibonacci fusion rules" (line 1268); for
Ising the source prints only the fusion rule of the category, so the operator identity here is
the Ising analogue of line 1268, implied but not printed. The same abstract rule
`D_σ² = 1 + D_ψ` is printed by Aasen, Mong, Fendley 2016 (arXiv:1601.07185),
`References/1601.07185/source/Ising-Defects.tex` lines 1051–1055, for a different realization:
defect operators of the Ising lattice model on spin and dual-spin configurations, with their own
normalization `2^{-L/2}`.

**Formalized here.** At every positive length `N`, the periodic operators of the Ising tensors
satisfy `O_N(√2 A_σ)² = 2^N (O_N(A_1) + O_N(A_ψ))`, hence `O_σ² = O_1 + O_ψ` for the periodic
operator `O_σ` of the rescaled tensor `(√2)⁻¹ (√2 A_σ)`.

**Local fix (sigma scaling):** the tensors omit the factors `v_e v_f` of the `G`-symbols
(lines 1257–1260) and store the `σ` tensor multiplied by `√2`, so that every entry lies in
`ℤ[√2]`; the identities are proved for these `v`-free tensors. Documented in
`docs/paper-gaps/bmwshv17_ising_boundary_tensor_normalization.tex`.

The stacked tensor `(√2 A_σ) ⋆ (√2 A_σ)` has bond dimension `16`. Its bond coordinates are
changed by the matrix `G` whose rows are `√2 e_8`, `√2 e_13`, `e_2 + e_7` (the channel `1`),
`√2 e_12`, `√2 e_9`, `e_2 - e_7` (the channel `ψ`), and `√2 e_i` for the ten remaining
coordinates; the rows `e_2 ± e_7` are `√2` times the F-move `(e_2 ± e_7)/√2` of the `σσσ`
F-symbols. Then `G Gᵀ = GᵀG = 2`, and every conjugated letter `G X Gᵀ` is `2` times the
direct sum of `2 A_1`, `2 A_ψ` and a zero block of size `10`; the letter identities are decided
over `ℤ[√2]`, sector by sector of the middle label `ρ`.

## Main definitions

* `IsingTwist.isingGaugeSigmaSigmaZ`: the change of bond coordinates of the stacked tensor.
* `IsingTwist.isingOnePsiZ`: the direct sum `2 A_1 ⊕ 2 A_ψ` over `ℤ[√2]`.

## Main results

* `IsingTwist.isingSigma_mul_isingSigma`: `O_N(√2 A_σ)² = 2^N (O_N(A_1) + O_N(A_ψ))`.
* `IsingTwist.isingSigma_normalized_mul_self`: `O_σ² = O_1 + O_ψ` for the rescaled tensor.

## References
- [arXiv:1511.08090](https://arxiv.org/abs/1511.08090) -- N. Bultinck, M. Mariën,
  D. J. Williamson, M. B. Sahinoglu, J. Haegeman, F. Verstraete, *Anyons and matrix product
  operator algebras*
- [arXiv:1601.07185](https://arxiv.org/abs/1601.07185) -- D. Aasen, R. S. K. Mong, P. Fendley,
  *Topological defects on the lattice I: the Ising model*

## Provenance
The change of bond coordinates was found by solving the intertwiner equations numerically; this
is a verification record, not the source.
-/

open scoped Matrix

namespace IsingTwist

open MPSTensor Zsqrtd

/-- The first column of each row of the change of bond coordinates. -/
def isingSigmaSigmaCol : Fin 16 → Fin 16 := ![8, 13, 2, 12, 9, 2, 0, 1, 3, 4, 5, 6, 10, 11, 14, 15]

/-- The second column of each row: `7` in the two F-move rows, a repeat of the first column
elsewhere (with the coefficient `0`). -/
def isingSigmaSigmaCol' : Fin 16 → Fin 16 := ![8, 13, 7, 12, 9, 7, 0, 1, 3, 4, 5, 6, 10, 11, 14, 15]

/-- The first coefficient of each row: `1` in the two F-move rows, `√2` elsewhere. -/
def isingSigmaSigmaCoef : Fin 16 → ℤ√2 := fun x => if x = 2 ∨ x = 5 then 1 else sqrtd

/-- The second coefficient of each row: `±1` in the two F-move rows. -/
def isingSigmaSigmaCoef' : Fin 16 → ℤ√2 := ![0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The change of bond coordinates of `(√2 A_σ) ⋆ (√2 A_σ)`: the rows are `√2 e_8`,
`√2 e_13`,
`e_2 + e_7`, `√2 e_12`, `√2 e_9`, `e_2 - e_7`, and `√2 e_i` for the remaining coordinates
`i = 0, 1, 3, 4, 5, 6, 10, 11, 14, 15`. -/
def isingGaugeSigmaSigmaZ : Matrix (Fin 16) (Fin 16) (ℤ√2) :=
  twoTermMatrix isingSigmaSigmaCol isingSigmaSigmaCol' isingSigmaSigmaCoef isingSigmaSigmaCoef'

/-- The direct sum `2 A_1 ⊕ 2 A_ψ` over `ℤ√2`, in the bond order of `MPOTensor.directSum`. -/
def isingOnePsiZ (h h' : Fin 10) : Matrix (Fin 6) (Fin 6) (ℤ√2) :=
  (Matrix.fromBlocks ((2 : ℤ√2) • isingOneZ h h') 0 0 ((2 : ℤ√2) • isingPsiZ h h')).submatrix
    (finSumFinEquiv (m := 3) (n := 3)).symm (finSumFinEquiv (m := 3) (n := 3)).symm

theorem isingGaugeSigmaSigmaZ_mul_transpose :
    isingGaugeSigmaSigmaZ * isingGaugeSigmaSigmaZᵀ = (2 : ℤ√2) • 1 := by
  rw [show isingGaugeSigmaSigmaZ * isingGaugeSigmaSigmaZᵀ =
      isingGaugeSigmaSigmaZ * 1 * isingGaugeSigmaSigmaZᵀ by rw [Matrix.mul_one],
    isingGaugeSigmaSigmaZ, twoTermMatrix_mul_mul_transpose]
  decide +kernel

/-- The transpose of the change of bond coordinates also has at most two nonzero entries in
each row. -/
theorem isingGaugeSigmaSigmaZ_transpose :
    isingGaugeSigmaSigmaZᵀ =
      twoTermMatrix ![6, 7, 2, 8, 9, 10, 11, 2, 0, 4, 12, 13, 3, 1, 14, 15]
        ![6, 7, 5, 8, 9, 10, 11, 5, 0, 4, 12, 13, 3, 1, 14, 15]
        (fun c => if c = 2 ∨ c = 7 then 1 else sqrtd)
        ![0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem isingGaugeSigmaSigmaZ_transpose_mul :
    isingGaugeSigmaSigmaZᵀ * isingGaugeSigmaSigmaZ = (2 : ℤ√2) • 1 := by
  rw [show isingGaugeSigmaSigmaZᵀ * isingGaugeSigmaSigmaZ =
      isingGaugeSigmaSigmaZᵀ * 1 * isingGaugeSigmaSigmaZᵀᵀ by
      rw [Matrix.mul_one, Matrix.transpose_transpose],
    isingGaugeSigmaSigmaZ_transpose, twoTermMatrix_mul_mul_transpose]
  decide +kernel

theorem isingOnePsiZ_eq_zero_of_rho_ne (h h' : Fin 10) (hne : isingRho h ≠ isingRho h') :
    isingOnePsiZ h h' = 0 := by
  rw [isingOnePsiZ, isingOneZ_eq_zero_of_rho_ne h h' hne, isingPsiZ_eq_zero_of_rho_ne h h' hne]
  simp

/-- The letter identity of `σ × σ = 1 + ψ` on the letters whose two labels carry the same
middle label `ρ`, decided over `ℤ√2` from the scaled-matrix-unit form of the stacked letters. -/
private theorem isingSigmaSigma_conj_of_rho_eq : ∀ h h' : Fin 10, isingRho h' = isingRho h →
    isingGaugeSigmaSigmaZ * mulZsqrt2Tensor isingSigmaZ isingSigmaZ h h' *
        isingGaugeSigmaSigmaZᵀ = (2 : ℤ√2) • padZsqrt2 10 (isingOnePsiZ h h') := by
  intro h h'
  rw [mul_mulTensorR_mul_transpose_eq_list _ _ _ _ _ _ _ _ isingSigmaZ_eq_smul_single
    isingSigmaZ_eq_smul_single isingSigmaNext isingSigmaNext_nodup isingSigmaCoef_eq_zero]
  revert h h'
  decide +kernel

/-- **The letter identity of `σ × σ = 1 + ψ`.** Every letter of `(√2 A_σ) ⋆ (√2 A_σ)`,
conjugated by the change of bond coordinates, is `2` times the direct sum of `2 A_1`, `2 A_ψ`
and a zero block. -/
theorem isingSigmaSigma_conj (h h' : Fin 10) :
    isingGaugeSigmaSigmaZ * mulZsqrt2Tensor isingSigmaZ isingSigmaZ h h' *
        isingGaugeSigmaSigmaZᵀ = (2 : ℤ√2) • padZsqrt2 10 (isingOnePsiZ h h') :=
  isingConj_of_rho_eq (z := 10) isingSigmaZ_eq_zero_of_rho_ne isingSigmaZ_eq_zero_of_rho_ne
    isingOnePsiZ_eq_zero_of_rho_ne isingSigmaSigma_conj_of_rho_eq h h'

theorem complexOfZsqrt2_isingOnePsiZ (h h' : Fin 10) :
    complexOfZsqrt2 (isingOnePsiZ h h') =
      ((2 : ℂ) • MPOTensor.directSum isingOne isingPsi) h h' := by
  ext a b
  simp only [isingOnePsiZ, MPOTensor.directSum, complexOfZsqrt2_apply, Matrix.submatrix_apply,
    Pi.smul_apply, Matrix.smul_apply]
  rcases (finSumFinEquiv (m := 3) (n := 3)).symm a with a | a <;>
    rcases (finSumFinEquiv (m := 3) (n := 3)).symm b with b | b <;>
    simp [isingOne, isingPsi, map_ofNat]

/-- **`O_σ O_σ = O_1 + O_ψ`, scaled form.** Source: arXiv:1511.08090, lines 1312 and 1323: the
fusion rule `σ × σ = 1 + ψ` for the periodic operators of the tensors built as in lines
1257–1268, at every positive length; this is the Ising analogue of line 1268, which states the
operator fusion rules only for the Fibonacci blocks. The square of the periodic operator of
`√2 A_σ` is `2^N` times the sum of the periodic operators of `A_1` and `A_ψ`. -/
theorem isingSigma_mul_isingSigma {N : ℕ} (hN : 0 < N) :
    MPOTensor.mpo isingSigma N * MPOTensor.mpo isingSigma N =
      (2 : ℂ) ^ N • (MPOTensor.mpo isingOne N + MPOTensor.mpo isingPsi N) := by
  rw [show isingSigma = fun i j => complexOfZsqrt2 (isingSigmaZ i j) from rfl,
    mpo_mul_eq_of_zsqrt2_conj isingSigmaZ isingSigmaZ isingOnePsiZ (z := 10) isingGaugeSigmaSigmaZ
      isingGaugeSigmaSigmaZᵀ 2 (by decide) isingGaugeSigmaSigmaZ_mul_transpose
      isingGaugeSigmaSigmaZ_transpose_mul isingSigmaSigma_conj hN]
  rw [show (fun i j => complexOfZsqrt2 (isingOnePsiZ i j)) =
      (2 : ℂ) • MPOTensor.directSum isingOne isingPsi from
      funext fun i => funext fun j => complexOfZsqrt2_isingOnePsiZ i j,
    MPOTensor.mpo_smul, MPOTensor.mpo_directSum]

/-- **`O_σ² = O_1 + O_ψ`.** Source: arXiv:1511.08090, lines 1312 and 1323, as in
`isingSigma_mul_isingSigma`: for the rescaled tensor `(√2)⁻¹ • isingSigma`, the square of its
periodic operator is the sum of the periodic operators of `A_1` and `A_ψ` at every positive
length. The same abstract rule `D_σ² = 1 + D_ψ` is printed for a different realization, the Ising
defect operators, in arXiv:1601.07185, `Ising-Defects.tex` lines 1051–1055. -/
theorem isingSigma_normalized_mul_self {N : ℕ} (hN : 0 < N) :
    MPOTensor.mpo (((Real.sqrt 2 : ℂ))⁻¹ • isingSigma) N *
        MPOTensor.mpo (((Real.sqrt 2 : ℂ))⁻¹ • isingSigma) N =
      MPOTensor.mpo isingOne N + MPOTensor.mpo isingPsi N := by
  have h2 : ((Real.sqrt 2 : ℂ))⁻¹ ^ N * ((Real.sqrt 2 : ℂ))⁻¹ ^ N * (2 : ℂ) ^ N = 1 := by
    rw [← mul_pow, ← mul_pow, ← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    simp
  rw [MPOTensor.mpo_smul, Matrix.smul_mul, Matrix.mul_smul, isingSigma_mul_isingSigma hN,
    smul_smul, smul_smul, h2, one_smul]

end IsingTwist
