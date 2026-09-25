/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.NumberTheory.Real.GoldenRatio
import TNLean.MPS.Examples.Fibonacci.FibonacciAnomaly
import TNLean.MPS.Symmetry.MPOSymmetry.Dimension

/-!
# The Perron–Frobenius dimensions of the Fibonacci fusion ring

**Source.** Bultinck, Mariën, Williamson, Sahinoglu, Haegeman, Verstraete 2017
(arXiv:1511.08090), Appendix D.1.1, `References/1511.08090/AnyonsPEPS.tex` lines 1240–1244: the
Fibonacci labels `1, τ` with fusion rules `N_{11}^1 = N_{τ1}^τ = N_{1τ}^τ = N_{ττ}^1 = N_{ττ}^τ = 1`
and the quantum dimensions `d_1 = 1`, `d_τ = (1 + √5)/2 = φ`. The Perron–Frobenius dimension is
the spectral radius of the fusion matrix (arXiv:2204.05940,
`References/2204.05940/source/mpo.tex` line 6068).

**Formalized here.** For the structure constants `FibonacciCompression.fibNim`, which the
Fibonacci matrix product operators realize at every length
(`FibonacciCompression.isMPOFusionAlgebra_fibBlock`): the characteristic polynomial
`λ² - λ - 1` and the spectrum `{φ, -φ⁻¹}` of `N_τ`, the dimension relation
`∑_b N_{ab}^c δ_b = δ_a δ_c` for `δ = (1, φ)`, hence `d_1 = 1` and `d_τ = φ` by
`MPOTensor.perronFrobeniusDim_eq_of_dimension_relation`, and the fact that `τ` is not invertible.

## Main results

* `FibonacciCompression.charpoly_fusionMatrix_fibNim_tau`,
  `FibonacciCompression.spectrum_fusionMatrix_fibNim_tau`: `N_τ` has characteristic polynomial
  `λ² - λ - 1` and eigenvalues `φ` and `-φ⁻¹`.
* `FibonacciCompression.fibNim_dimension_relation`: `(1, φ)` satisfies the dimension relation.
* `FibonacciCompression.perronFrobeniusDim_fibNim_tau`: `d_τ = φ`.
* `FibonacciCompression.perronFrobeniusDim_fibNim_one`: `d_1 = 1`.
* `FibonacciCompression.not_isInvertibleLabel_fibNim_tau`: `τ` has no inverse.

## References
- [arXiv:1511.08090](https://arxiv.org/abs/1511.08090) -- N. Bultinck, M. Mariën,
  D. J. Williamson, M. B. Sahinoglu, J. Haegeman, F. Verstraete, *Anyons and matrix product
  operator algebras*
- [arXiv:2204.05940](https://arxiv.org/abs/2204.05940) -- A. Molnár, J. Garre-Rubio,
  D. Pérez-García, N. Schuch, J. I. Cirac, *Matrix product operator algebras I: representations
  of weak Hopf algebras and projected entangled pair states*
-/

open scoped goldenRatio

open MPOTensor Polynomial Real

namespace FibonacciCompression

/-- The quantum dimensions `d_1 = 1`, `d_τ = φ` of the Fibonacci labels (arXiv:1511.08090,
line 1244). -/
noncomputable def fibDim : Fin 2 → ℝ := ![1, φ]

/-- The fusion matrix of `τ` in the order `(1, τ)` is `N_τ = [[0, 1], [1, 1]]`
(arXiv:1511.08090, lines 1240–1243). -/
theorem fusionMatrix_fibNim_tau : fusionMatrix fibNim 1 = !![0, 1; 1, 1] := by
  ext b c; fin_cases b <;> fin_cases c <;> rfl

/-- The characteristic polynomial of the Fibonacci fusion matrix `N_τ` is `λ² - λ - 1`. -/
theorem charpoly_fusionMatrix_fibNim_tau :
    ((fusionMatrix fibNim 1).map ((↑) : ℕ → ℂ)).charpoly = X ^ 2 - X - 1 := by
  rw [fusionMatrix_fibNim_tau, Matrix.charpoly_fin_two]
  simp [Matrix.trace_fin_two, Matrix.det_fin_two]
  ring

/-- **The eigenvalues of `N_τ`** are the golden ratio `φ` and `-φ⁻¹` (arXiv:1511.08090,
line 1244, with the fusion rules of lines 1240–1243). -/
theorem spectrum_fusionMatrix_fibNim_tau :
    spectrum ℂ ((fusionMatrix fibNim 1).map ((↑) : ℕ → ℂ)) = {(φ : ℂ), -((φ : ℂ)⁻¹)} := by
  ext μ
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, charpoly_fusionMatrix_fibNim_tau]
  have hinv : -((φ : ℂ)⁻¹) = (ψ : ℂ) := by
    rw [← Complex.ofReal_inv, inv_goldenRatio, Complex.ofReal_neg, neg_neg]
  have hfac : μ ^ 2 - μ - 1 = (μ - φ) * (μ - ψ) := by
    have hs : ((φ : ℂ) + ψ) = 1 := by exact_mod_cast goldenRatio_add_goldenConj
    have hp : ((φ : ℂ) * ψ) = -1 := by exact_mod_cast goldenRatio_mul_goldenConj
    linear_combination μ * hs - hp
  simp only [IsRoot.def, eval_sub, eval_pow, eval_X, eval_one, hfac, mul_eq_zero, sub_eq_zero,
    Set.mem_insert_iff, Set.mem_singleton_iff, hinv]

/-- The Fibonacci quantum dimensions are positive. -/
theorem fibDim_pos (b : Fin 2) : 0 < fibDim b := by
  fin_cases b
  · simp [fibDim]
  · simpa [fibDim] using goldenRatio_pos

/-- **The quantum dimensions satisfy the dimension relation** `∑_b N_{ab}^c d_b = d_a d_c`
(arXiv:1511.08090, lines 1240–1244; arXiv:2204.05940, mpo.tex line 6068). -/
theorem fibNim_dimension_relation (a c : Fin 2) :
    ∑ b, (fibNim a b c : ℝ) * fibDim b = fibDim a * fibDim c := by
  have h := goldenRatio_sq
  fin_cases a <;> fin_cases c <;>
    simp [fibNim, fibFusionMatrix, fibDim, Fin.sum_univ_two, Matrix.one_apply]
  linear_combination -h

/-- **The Perron–Frobenius dimension of `τ` is the golden ratio** (arXiv:1511.08090, line 1244):
`d_τ = ρ(N_τ) = φ`. -/
theorem perronFrobeniusDim_fibNim_tau : perronFrobeniusDim fibNim 1 = φ :=
  perronFrobeniusDim_eq_of_dimension_relation (δ := fibDim)
    fibDim_pos fibNim_dimension_relation 1

/-- The Perron–Frobenius dimension of the unit label is `d_1 = 1` (arXiv:1511.08090,
line 1244). -/
theorem perronFrobeniusDim_fibNim_one : perronFrobeniusDim fibNim 0 = 1 :=
  perronFrobeniusDim_eq_of_dimension_relation (δ := fibDim)
    fibDim_pos fibNim_dimension_relation 0

/-- **`τ` is not invertible** (arXiv:1511.08090, lines 1240–1243): `τ × b` contains `1` only
for `b = τ`, and `τ × τ` also contains `τ`. -/
theorem not_isInvertibleLabel_fibNim_tau : ¬ IsInvertibleLabel fibNim 0 1 := by
  rintro ⟨b, hb⟩
  fin_cases b
  · have := (hb 0).1; simp [fibNim, fibFusionMatrix] at this
  · have := (hb 1).1; simp [fibNim, fibFusionMatrix] at this

end FibonacciCompression
