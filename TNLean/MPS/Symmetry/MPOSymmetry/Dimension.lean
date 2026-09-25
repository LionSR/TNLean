/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
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
spectral radius of `N_a` over `ℂ`, and the characterization quoted above: a positive left
eigenvector `δ N_a = λ δ` forces `λ = d_a`. The argument is the comparison of the positive
functional `δ` with the entrywise moduli of an arbitrary complex eigenvector, so it uses neither
irreducibility of `N_a` nor the existence part of the Perron–Frobenius theorem. The same holds
for a positive right eigenvector, which is how a positive real fusion character
(`MPOTensor.IsFusionCharacter`) determines every dimension.

## Main definitions

* `MPOTensor.fusionMatrix`: the matrix `(N_a)_{bc} = N_{ab}^c` of a label `a`.
* `MPOTensor.perronFrobeniusDim`: the spectral radius `d_a` of `N_a`.

## Main results

* `Matrix.spectralRadius_map_ofReal_eq_of_pos_vecMul_eq`: a nonnegative real matrix with a
  positive left eigenvector has spectral radius equal to its eigenvalue.
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

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every complex eigenvalue `μ` of a nonnegative real matrix `M` with a positive left
eigenvector `δ ᵥ* M = r • δ` satisfies `‖μ‖ ≤ r`: pairing `δ` with the entrywise moduli of an
eigenvector `v` gives `‖μ‖ ∑ δ_i ‖v_i‖ ≤ ∑_{i,j} δ_i M_{ij} ‖v_j‖ = r ∑ δ_j ‖v_j‖`. -/
theorem norm_le_of_mem_spectrum_of_pos_vecMul_eq {M : Matrix ι ι ℝ} (hM : ∀ i j, 0 ≤ M i j)
    {δ : ι → ℝ} (hδ : ∀ i, 0 < δ i) {r : ℝ} (h : δ ᵥ* M = r • δ) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ (M.map ((↑) : ℝ → ℂ))) : ‖μ‖ ≤ r := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at hμ
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hμ
  have hev : ∀ i, ∑ j, (M i j : ℂ) * v j = μ * v i := by
    intro i
    have := congrFun hv i
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      sub_eq_zero] at this
    simpa [Matrix.mulVec, dotProduct] using this.symm
  -- entrywise bound `‖μ‖ ‖v_i‖ ≤ ∑_j M_{ij} ‖v_j‖`
  have hrow : ∀ i, ‖μ‖ * ‖v i‖ ≤ ∑ j, M i j * ‖v j‖ := by
    intro i
    calc ‖μ‖ * ‖v i‖ = ‖∑ j, (M i j : ℂ) * v j‖ := by rw [hev i, norm_mul]
      _ ≤ ∑ j, ‖(M i j : ℂ) * v j‖ := norm_sum_le _ _
      _ = ∑ j, M i j * ‖v j‖ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hM i j)]
  have hcol : ∀ j, ∑ i, δ i * M i j = r * δ j := by
    intro j
    simpa [Matrix.vecMul, dotProduct] using congrFun h j
  set S := ∑ i, δ i * ‖v i‖ with hS
  have hSpos : 0 < S := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hv0
    exact Finset.sum_pos' (fun j _ => mul_nonneg (hδ j).le (norm_nonneg _))
      ⟨i, Finset.mem_univ _, mul_pos (hδ i) (norm_pos_iff.2 hi)⟩
  have hbound : ‖μ‖ * S ≤ r * S := by
    calc ‖μ‖ * S = ∑ i, δ i * (‖μ‖ * ‖v i‖) := by
          rw [hS, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ ∑ i, δ i * ∑ j, M i j * ‖v j‖ :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hrow i) (hδ i).le
      _ = ∑ j, (∑ i, δ i * M i j) * ‖v j‖ := by
          simp_rw [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
      _ = r * S := by
          simp_rw [hcol, hS, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
  exact le_of_mul_le_mul_right hbound hSpos

/-- A positive left eigenvector `δ ᵥ* M = r • δ` of a real matrix makes `r` an eigenvalue of `M`
over `ℂ`. -/
theorem ofReal_mem_spectrum_of_pos_vecMul_eq [Nonempty ι] {M : Matrix ι ι ℝ} {δ : ι → ℝ}
    (hδ : ∀ i, 0 < δ i) {r : ℝ} (h : δ ᵥ* M = r • δ) :
    (r : ℂ) ∈ spectrum ℂ (M.map ((↑) : ℝ → ℂ)) := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not]
  refine Matrix.exists_vecMul_eq_zero_iff.1 ⟨fun i => (δ i : ℂ), ?_, ?_⟩
  · intro h0
    obtain ⟨i⟩ := ‹Nonempty ι›
    have := congrFun h0 i
    simp only [Pi.zero_apply, Complex.ofReal_eq_zero] at this
    exact (hδ i).ne' this
  · ext j
    have hj := congrFun h j
    simp only [Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul] at hj
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.vecMul_sub, Matrix.vecMul_smul,
      Matrix.vecMul_one, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_eq_zero]
    simp only [Matrix.vecMul, dotProduct, Matrix.map_apply]
    exact_mod_cast hj.symm

/-- **Spectral radius from a positive left eigenvector.** A nonnegative real matrix `M` with a
positive left eigenvector `δ ᵥ* M = r • δ` has spectral radius `r` over `ℂ`. -/
theorem spectralRadius_map_ofReal_eq_of_pos_vecMul_eq [Nonempty ι] {M : Matrix ι ι ℝ}
    (hM : ∀ i j, 0 ≤ M i j) {δ : ι → ℝ} (hδ : ∀ i, 0 < δ i) {r : ℝ} (h : δ ᵥ* M = r • δ) :
    spectralRadius ℂ (M.map ((↑) : ℝ → ℂ)) = ENNReal.ofReal r := by
  have hr := ofReal_mem_spectrum_of_pos_vecMul_eq hδ h
  have hr0 : 0 ≤ r := by
    have := norm_le_of_mem_spectrum_of_pos_vecMul_eq hM hδ h hr
    rw [Complex.norm_real, Real.norm_eq_abs] at this
    exact (abs_nonneg r).trans this
  refine le_antisymm (iSup₂_le fun μ hμ => ?_) (le_iSup₂_of_le (r : ℂ) hr ?_)
  · rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
    exact ENNReal.ofReal_le_ofReal (norm_le_of_mem_spectrum_of_pos_vecMul_eq hM hδ h hμ)
  · rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, Complex.norm_real, Real.norm_of_nonneg hr0]

/-- The spectrum of a complex matrix is that of its transpose. -/
theorem spectrum_transpose_complex (A : Matrix ι ι ℂ) : spectrum ℂ Aᵀ = spectrum ℂ A := by
  ext μ
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.mem_spectrum_iff_isRoot_charpoly,
    Matrix.charpoly_transpose]

end Matrix

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

/-- **A positive left eigenvector gives the Perron–Frobenius dimension** (arXiv:2204.05940,
mpo.tex line 6068). If real numbers `δ_b > 0` satisfy `∑_b δ_b N_{ab}^c = λ δ_c` for every `c`,
then `λ = d_a`. -/
theorem perronFrobeniusDim_eq_of_pos_left_eigenvector [DecidableEq ι] {N : ι → ι → ι → ℕ}
    {a : ι} {lam : ℝ} {δ : ι → ℝ} (hδ : ∀ b, 0 < δ b)
    (h : ∀ c, ∑ b, δ b * N a b c = lam * δ c) : perronFrobeniusDim N a = lam := by
  have : Nonempty ι := ⟨a⟩
  have hmap : (fusionMatrix N a).map ((↑) : ℕ → ℂ) =
      ((fusionMatrix N a).map ((↑) : ℕ → ℝ)).map ((↑) : ℝ → ℂ) := by
    ext b c; simp
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
  rw [perronFrobeniusDim, hmap, spectralRadius, Matrix.spectrum_transpose_complex, ← spectralRadius,
    hr, ENNReal.toReal_ofReal hlam]

/-- **A positive real fusion character is the Perron–Frobenius dimension.** A fusion character
`χ_a χ_b = ∑_c N_{ab}^c χ_c` with positive real values makes `χ` a positive right eigenvector of
every fusion matrix `N_a`, with eigenvalue `χ_a`, so `χ_a = d_a`. -/
theorem perronFrobeniusDim_eq_of_isFusionCharacter [DecidableEq ι] {N : ι → ι → ι → ℕ} {e : ι}
    {χ : ι → ℝ} (hχ : IsFusionCharacter N e χ) (hpos : ∀ b, 0 < χ b) (a : ι) :
    perronFrobeniusDim N a = χ a :=
  perronFrobeniusDim_eq_of_pos_right_eigenvector hpos fun b => (hχ.2 a b).symm

end MPOTensor
