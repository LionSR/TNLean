/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Symmetry.MPOSymmetry.Dimension
import TNLean.MPS.Symmetry.MPOSymmetry.IsingFusion

/-!
# The Perron–Frobenius dimensions of the Ising fusion ring

**Source.** Bultinck, Mariën, Williamson, Sahinoglu, Haegeman, Verstraete 2017
(arXiv:1511.08090), Appendix D.2.1, `References/1511.08090/AnyonsPEPS.tex` lines 1306–1312: the
Ising labels `1, σ, ψ`, the fusion rules `N_{11}^1 = N_{1σ}^σ = N_{1ψ}^ψ = N_{σσ}^ψ = 1` up to the
allowed permutations of the labels, the only non-trivial rule `σ × σ = 1 + ψ`, and the quantum
dimensions `d_1 = 1`, `d_σ = √2`, `d_ψ = 1`. The Perron–Frobenius dimension is the spectral
radius of the fusion matrix (arXiv:2204.05940, `References/2204.05940/source/mpo.tex`
line 6068).

**Formalized here.** For the structure constants `IsingTwist.isingFusion` (labels `0 = 1`,
`1 = ψ`, `2 = σ`), which the Ising matrix product operators realize at every length
(`IsingTwist.isMPOFusionAlgebra_ising`): the fusion matrices `N_ψ` and `N_σ`, the characteristic
polynomial `λ³ - 2λ` and the spectrum `{0, √2, -√2}` of `N_σ`, the dimension relation
`∑_b N_{ab}^c δ_b = δ_a δ_c` for `δ = (1, 1, √2)`, hence `d_1 = d_ψ = 1` and `d_σ = √2` by
`MPOTensor.perronFrobeniusDim_eq_of_dimension_relation`, and the invertibility of `ψ` and
non-invertibility of `σ`.

## Main results

* `IsingTwist.fusionMatrix_isingFusion_psi`, `IsingTwist.fusionMatrix_isingFusion_sigma`: the
  fusion matrices of `ψ` and `σ`.
* `IsingTwist.spectrum_fusionMatrix_isingFusion_sigma`: the eigenvalues of `N_σ` are `0, ±√2`.
* `IsingTwist.isingFusion_dimension_relation`: `(1, 1, √2)` satisfies the dimension relation.
* `IsingTwist.perronFrobeniusDim_isingFusion_sigma`: `d_σ = √2`.
* `IsingTwist.perronFrobeniusDim_isingFusion_psi`, `IsingTwist.perronFrobeniusDim_isingFusion_one`:
  `d_ψ = d_1 = 1`.
* `IsingTwist.isInvertibleLabel_isingFusion_psi`,
  `IsingTwist.not_isInvertibleLabel_isingFusion_sigma`: `ψ` is invertible and `σ` is not.

## References
- [arXiv:1511.08090](https://arxiv.org/abs/1511.08090) -- N. Bultinck, M. Mariën,
  D. J. Williamson, M. B. Sahinoglu, J. Haegeman, F. Verstraete, *Anyons and matrix product
  operator algebras*
- [arXiv:2204.05940](https://arxiv.org/abs/2204.05940) -- A. Molnár, J. Garre-Rubio,
  D. Pérez-García, N. Schuch, J. I. Cirac, *Matrix product operator algebras I: representations
  of weak Hopf algebras and projected entangled pair states*
-/

open MPOTensor Polynomial

namespace IsingTwist

/-- The quantum dimensions `d_1 = 1`, `d_ψ = 1`, `d_σ = √2` of the Ising labels in the order
`(1, ψ, σ)` (arXiv:1511.08090, line 1312). -/
noncomputable def isingDimension : Fin 3 → ℝ := ![1, 1, √2]

/-- The fusion matrix of `ψ` in the order `(1, ψ, σ)` (arXiv:1511.08090, lines 1308–1312). -/
theorem fusionMatrix_isingFusion_psi :
    fusionMatrix isingFusion 1 = !![0, 1, 0; 1, 0, 0; 0, 0, 1] := by
  ext b c; fin_cases b <;> fin_cases c <;> rfl

/-- The fusion matrix of `σ` in the order `(1, ψ, σ)` (arXiv:1511.08090, lines 1308–1312). -/
theorem fusionMatrix_isingFusion_sigma :
    fusionMatrix isingFusion 2 = !![0, 0, 1; 0, 0, 1; 1, 1, 0] := by
  ext b c; fin_cases b <;> fin_cases c <;> rfl

/-- The characteristic polynomial of `N_σ` is `λ³ - 2λ`. -/
theorem charpoly_fusionMatrix_isingFusion_sigma :
    ((fusionMatrix isingFusion 2).map ((↑) : ℕ → ℂ)).charpoly = X ^ 3 - 2 * X := by
  rw [fusionMatrix_isingFusion_sigma, Matrix.charpoly, Matrix.det_fin_three]
  simp
  ring

/-- **The eigenvalues of `N_σ`** are `0` and `±√2` (arXiv:1511.08090, lines 1308–1312). -/
theorem spectrum_fusionMatrix_isingFusion_sigma :
    spectrum ℂ ((fusionMatrix isingFusion 2).map ((↑) : ℕ → ℂ)) =
      {0, ((√2 : ℝ) : ℂ), -((√2 : ℝ) : ℂ)} := by
  ext μ
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, charpoly_fusionMatrix_isingFusion_sigma]
  have hs : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hfac : μ ^ 3 - 2 * μ = μ * ((μ - (√2 : ℝ)) * (μ - -((√2 : ℝ) : ℂ))) := by
    linear_combination μ * hs
  simp only [IsRoot.def, eval_sub, eval_pow, eval_mul, eval_X, eval_ofNat, hfac, mul_eq_zero,
    sub_eq_zero, Set.mem_insert_iff, Set.mem_singleton_iff]

/-- **The quantum dimensions satisfy the dimension relation** `∑_b N_{ab}^c d_b = d_a d_c`
(arXiv:1511.08090, lines 1306–1312; arXiv:2204.05940, mpo.tex line 6068). -/
theorem isingFusion_dimension_relation (a c : Fin 3) :
    ∑ b, (isingFusion a b c : ℝ) * isingDimension b = isingDimension a * isingDimension c := by
  have h : (√2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  fin_cases a <;> fin_cases c <;>
    simp [isingFusion, isingDimension, Fin.sum_univ_three, h]
  norm_num

/-- The Ising quantum dimensions are positive. -/
theorem isingDimension_pos (b : Fin 3) : 0 < isingDimension b := by
  fin_cases b <;> simp [isingDimension]

/-- **The Perron–Frobenius dimension of `σ` is `√2`** (arXiv:1511.08090, line 1312):
`d_σ = ρ(N_σ) = √2`. -/
theorem perronFrobeniusDim_isingFusion_sigma : perronFrobeniusDim isingFusion 2 = √2 :=
  perronFrobeniusDim_eq_of_dimension_relation isingDimension_pos isingFusion_dimension_relation 2

/-- The Perron–Frobenius dimension of `ψ` is `d_ψ = 1` (arXiv:1511.08090, line 1312). -/
theorem perronFrobeniusDim_isingFusion_psi : perronFrobeniusDim isingFusion 1 = 1 :=
  perronFrobeniusDim_eq_of_dimension_relation isingDimension_pos isingFusion_dimension_relation 1

/-- The Perron–Frobenius dimension of the unit is `d_1 = 1` (arXiv:1511.08090, line 1312). -/
theorem perronFrobeniusDim_isingFusion_one : perronFrobeniusDim isingFusion 0 = 1 :=
  perronFrobeniusDim_eq_of_dimension_relation isingDimension_pos isingFusion_dimension_relation 0

/-- **`ψ` is invertible**, with inverse `ψ`: `ψ × ψ = 1` (arXiv:1511.08090, lines 1308–1312). -/
theorem isInvertibleLabel_isingFusion_psi : IsInvertibleLabel isingFusion 0 1 :=
  ⟨1, fun c => by fin_cases c <;> simp [isingFusion]⟩

/-- **`σ` is not invertible**: `σ × σ = 1 + ψ` is the only product of `σ` containing `1`
(arXiv:1511.08090, line 1311). -/
theorem not_isInvertibleLabel_isingFusion_sigma : ¬ IsInvertibleLabel isingFusion 0 2 := by
  rintro ⟨b, hb⟩
  fin_cases b
  · have := (hb 2).1; simp [isingFusion] at this
  · have := (hb 2).1; simp [isingFusion] at this
  · have := (hb 1).1; simp [isingFusion] at this

end IsingTwist
