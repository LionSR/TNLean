/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.Algebra.NonnegativeMatrixSpectralRadius
import TNLean.MPS.Symmetry.MPOSymmetry.Defs

/-!
# Perron–Frobenius dimensions of fusion rings

**Source.** Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac 2022 (arXiv:2204.05940),
`References/2204.05940/source/mpo.tex` line 6068: for structure constants `N_{ab}^c` the matrix
`N_a` with `(N_a)_b^c = N_{ab}^c` is nonnegative; positive numbers `d_b` with
`∑_b N_{ab}^c d_b = d_a d_c` form a positive eigenvector of `N_a`, and "as `N_a` is a
non-negative matrix, this implies that the corresponding eigenvalue, `d_a`, is the spectral
radius of `N_a`", the Perron–Frobenius dimension of `a`.

**Formalized here.** The fusion matrix `N_a` of a label, its Perron–Frobenius dimension as the
spectral radius of `N_a` over `ℂ`, the Perron–Frobenius theorem for `N_a` (`d_a` is an
eigenvalue with a nonnegative eigenvector, from
`Matrix.exists_nonneg_mulVec_eq_spectralRadius_smul`), and the characterization quoted above: a
positive left eigenvector `δ N_a = λ δ` forces `λ = d_a`. The same holds for a positive right
eigenvector, which is how a positive real fusion character (`MPOTensor.IsFusionCharacter`)
determines every dimension.

## Main definitions

* `MPOTensor.fusionMatrix`: the matrix `(N_a)_{bc} = N_{ab}^c` of a label `a`.
* `MPOTensor.perronFrobeniusDim`: the spectral radius `d_a` of `N_a`.

## Main results

* `MPOTensor.exists_nonneg_eigenvector_perronFrobeniusDim`,
  `MPOTensor.perronFrobeniusDim_mem_spectrum`: `d_a` is an eigenvalue of `N_a` with a nonzero
  nonnegative eigenvector.
* `MPOTensor.perronFrobeniusDim_eq_of_pos_left_eigenvector`: a positive left eigenvector of
  `N_a` with eigenvalue `λ` gives `d_a = λ`.
* `MPOTensor.perronFrobeniusDim_eq_of_dimension_relation`: positive `δ_b` with
  `∑_b N_{ab}^c δ_b = δ_a δ_c` are the Perron–Frobenius dimensions.
* `MPOTensor.perronFrobeniusDim_eq_of_isFusionCharacter`: a positive real fusion character is the
  Perron–Frobenius dimension.

## References
- [arXiv:2204.05940](https://arxiv.org/abs/2204.05940) -- A. Molnár, J. Garre-Rubio,
  D. Pérez-García, N. Schuch, J. I. Cirac, *Matrix product operator algebras I: representations
  of weak Hopf algebras and projected entangled pair states*
-/

open scoped Matrix ENNReal NNReal

namespace MPOTensor

variable {ι : Type*}

/-- **Fusion matrix of a label** (arXiv:2204.05940, mpo.tex line 6068): the nonnegative integer
matrix `N_a` with entries `(N_a)_{bc} = N_{ab}^c`. -/
def fusionMatrix (N : ι → ι → ι → ℕ) (a : ι) : Matrix ι ι ℕ :=
  Matrix.of fun b c => N a b c

@[simp]
theorem fusionMatrix_apply (N : ι → ι → ι → ℕ) (a b c : ι) : fusionMatrix N a b c = N a b c :=
  rfl

variable [Fintype ι]

/-- **Perron–Frobenius dimension of a label** (arXiv:2204.05940, mpo.tex line 6068): the spectral
radius `d_a = ρ(N_a)` of the fusion matrix, the largest modulus of a complex eigenvalue of `N_a`.
The spectral radius of a matrix is finite, so it is recorded as a real number. -/
noncomputable def perronFrobeniusDim [DecidableEq ι] (N : ι → ι → ι → ℕ) (a : ι) : ℝ :=
  (spectralRadius ℂ ((fusionMatrix N a).map ((↑) : ℕ → ℂ))).toReal

omit [Fintype ι] in
/-- The complex fusion matrix is the complexification of the real one. -/
theorem fusionMatrix_map_natCast_complex (N : ι → ι → ι → ℕ) (a : ι) :
    (fusionMatrix N a).map ((↑) : ℕ → ℂ) =
      ((fusionMatrix N a).map ((↑) : ℕ → ℝ)).map ((↑) : ℝ → ℂ) := by
  ext b c; simp

/-- **A nonnegative eigenvector for the Perron–Frobenius dimension** (the Perron–Frobenius
theorem for the nonnegative matrix `N_a`, as used in arXiv:2204.05940, mpo.tex line 6068):
there is a nonzero vector `v` with nonnegative entries and `N_a v = d_a v`. -/
theorem exists_nonneg_eigenvector_perronFrobeniusDim [DecidableEq ι] (N : ι → ι → ι → ℕ)
    (a : ι) : ∃ v : ι → ℝ, v ≠ 0 ∧ (∀ b, 0 ≤ v b) ∧
      (fusionMatrix N a).map ((↑) : ℕ → ℝ) *ᵥ v = perronFrobeniusDim N a • v := by
  have : Nonempty ι := ⟨a⟩
  rw [perronFrobeniusDim, fusionMatrix_map_natCast_complex]
  exact Matrix.exists_nonneg_mulVec_eq_spectralRadius_smul fun b c => by simp

/-- **The Perron–Frobenius dimension is an eigenvalue** of the fusion matrix `N_a`
(arXiv:2204.05940, mpo.tex line 6068). -/
theorem perronFrobeniusDim_mem_spectrum [DecidableEq ι] (N : ι → ι → ι → ℕ) (a : ι) :
    (perronFrobeniusDim N a : ℂ) ∈ spectrum ℂ ((fusionMatrix N a).map ((↑) : ℕ → ℂ)) := by
  obtain ⟨v, hv0, -, hv⟩ := exists_nonneg_eigenvector_perronFrobeniusDim N a
  rw [fusionMatrix_map_natCast_complex]
  exact Matrix.ofReal_mem_spectrum_of_mulVec_eq hv0 hv

/-- **A positive left eigenvector gives the Perron–Frobenius dimension** (arXiv:2204.05940,
mpo.tex line 6068). If real numbers `δ_b > 0` satisfy `∑_b δ_b N_{ab}^c = λ δ_c` for every `c`,
then `λ = d_a`. -/
theorem perronFrobeniusDim_eq_of_pos_left_eigenvector [DecidableEq ι] {N : ι → ι → ι → ℕ}
    {a : ι} {lam : ℝ} {δ : ι → ℝ} (hδ : ∀ b, 0 < δ b)
    (h : ∀ c, ∑ b, δ b * N a b c = lam * δ c) : perronFrobeniusDim N a = lam := by
  have : Nonempty ι := ⟨a⟩
  have hmap := fusionMatrix_map_natCast_complex N a
  have hvec : δ ᵥ* (fusionMatrix N a).map ((↑) : ℕ → ℝ) = lam • δ := by
    ext c; simpa [Matrix.vecMul, dotProduct] using h c
  have hr := Matrix.spectralRadius_map_ofReal_eq_of_pos_vecMul_eq
    (fun b c => by simp) hδ hvec
  have hlam : 0 ≤ lam := by
    have hc := h a
    have hsum : 0 ≤ ∑ b, δ b * N a b a :=
      Finset.sum_nonneg fun b _ => mul_nonneg (hδ b).le (Nat.cast_nonneg _)
    rw [hc] at hsum
    exact nonneg_of_mul_nonneg_left hsum (hδ a)
  rw [perronFrobeniusDim, hmap, hr, ENNReal.toReal_ofReal hlam]

/-- **Positive dimensions satisfying the dimension relation are the Perron–Frobenius
dimensions** (arXiv:2204.05940, mpo.tex line 6068). If `δ_b > 0` and
`∑_b N_{ab}^c δ_b = δ_a δ_c` for all `a` and `c`, then `δ_a = d_a` for every label `a`. -/
theorem perronFrobeniusDim_eq_of_dimension_relation [DecidableEq ι] {N : ι → ι → ι → ℕ}
    {δ : ι → ℝ} (hδ : ∀ b, 0 < δ b) (h : ∀ a c, ∑ b, (N a b c : ℝ) * δ b = δ a * δ c)
    (a : ι) : perronFrobeniusDim N a = δ a :=
  perronFrobeniusDim_eq_of_pos_left_eigenvector hδ fun c => by
    rw [← h a c]; exact Finset.sum_congr rfl fun b _ => mul_comm _ _

/-- **A positive right eigenvector gives the Perron–Frobenius dimension.** If real numbers
`χ_c > 0` satisfy `∑_c N_{ab}^c χ_c = λ χ_b` for every `b`, then `λ = d_a`: the fusion matrix
and its transpose have the same spectrum. -/
theorem perronFrobeniusDim_eq_of_pos_right_eigenvector [DecidableEq ι] {N : ι → ι → ι → ℕ}
    {a : ι} {lam : ℝ} {χ : ι → ℝ} (hχ : ∀ c, 0 < χ c)
    (h : ∀ b, ∑ c, (N a b c : ℝ) * χ c = lam * χ b) : perronFrobeniusDim N a = lam := by
  have : Nonempty ι := ⟨a⟩
  have hmap : (fusionMatrix N a).map ((↑) : ℕ → ℂ) =
      (((fusionMatrix N a).map ((↑) : ℕ → ℝ))ᵀ.map ((↑) : ℝ → ℂ))ᵀ := by
    ext b c; simp
  have hvec : χ ᵥ* ((fusionMatrix N a).map ((↑) : ℕ → ℝ))ᵀ = lam • χ := by
    ext b; simpa [Matrix.vecMul, dotProduct, mul_comm] using h b
  have hr := Matrix.spectralRadius_map_ofReal_eq_of_pos_vecMul_eq
    (fun b c => by simp) hχ hvec
  have hlam : 0 ≤ lam := by
    have hsum : 0 ≤ ∑ c, (N a a c : ℝ) * χ c :=
      Finset.sum_nonneg fun c _ => mul_nonneg (Nat.cast_nonneg _) (hχ c).le
    rw [h a] at hsum
    exact nonneg_of_mul_nonneg_left hsum (hχ a)
  rw [perronFrobeniusDim, hmap, spectralRadius, Matrix.spectrum_transpose, ← spectralRadius,
    hr, ENNReal.toReal_ofReal hlam]

/-- **A positive real fusion character is the Perron–Frobenius dimension.** A fusion character
`χ_a χ_b = ∑_c N_{ab}^c χ_c` with positive real values makes `χ` a positive right eigenvector of
every fusion matrix `N_a`, with eigenvalue `χ_a`, so `χ_a = d_a`. -/
theorem perronFrobeniusDim_eq_of_isFusionCharacter [DecidableEq ι] {N : ι → ι → ι → ℕ} {e : ι}
    {χ : ι → ℝ} (hχ : IsFusionCharacter N e χ) (hpos : ∀ b, 0 < χ b) (a : ι) :
    perronFrobeniusDim N a = χ a :=
  perronFrobeniusDim_eq_of_pos_right_eigenvector hpos fun b => (hχ.2 a b).symm

end MPOTensor
