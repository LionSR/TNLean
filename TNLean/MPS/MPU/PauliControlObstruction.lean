/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.SpinCover.Basic
import Mathlib.Data.Matrix.Block
import TNLean.Algebra.GeneralizeDecide
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# A controlled Pauli unitary whose coefficient space contains no unitary

Let `nⱼ` be the eight rational unit vectors obtained by dividing the rows of
`coordinateInt` by fifteen. The operator `witness` acts on a target qubit and
three control qubits, with block `nⱼ · σ` at control label `j`. Each block is
Hermitian and squares to the identity, so the full operator is unitary.

The three right coefficients in `witness_eq_sum_pauli_kronecker` span the space
of diagonal matrices with entries `v · nⱼ`, where `v` ranges over `ℂ³`.
This space has dimension three and contains no unitary matrix. Indeed, unit
modulus of its first six entries would force the three coordinates of `v`
to be nonzero and pairwise orthogonal in the real plane `ℂ`, which is impossible.

This is the rational controlled Pauli construction in Section 2 of
`docs/audits/2026-10-02_mpu_schmidt_unitary_obstruction.tex`. It obstructs a
unitary basis in the original right coefficient space. It does not obstruct
an efficient circuit for the witness. The consecutive matrix product ranks
and a general circuit complexity theorem are not asserted in this module.
-/

open scoped Matrix BigOperators Kronecker
noncomputable section
namespace MPUPauliControl

/-- The eight rational Pauli axes, multiplied by fifteen. They are the three coordinate
axes and `(3/5, 4/5, 0)`, followed by their images under the reflection
`O = I - (2/3)J`. Source: Section 2 of
`docs/audits/2026-10-02_mpu_schmidt_unitary_obstruction.tex`. -/
def coordinateInt : Fin 8 → Fin 3 → ℤ :=
  ![![15, 0, 0], ![0, 15, 0], ![0, 0, 15], ![9, 12, 0],
    ![5, -10, -10], ![-10, 5, -10], ![-10, -10, 5], ![-5, -2, -14]]

/-- The eight complex coordinates `v · nⱼ` of a linear combination of the right coefficients. -/
def controlLinearCombination (v : Fin 3 → ℂ) (j : Fin 8) : ℂ :=
  ∑ k, ((coordinateInt j k : ℂ) / 15) * v k

/-- No complex linear combination of the three coordinate functions has unit modulus
at every control label. Source: the rank-three obstruction in Section 2 of
`docs/audits/2026-10-02_mpu_schmidt_unitary_obstruction.tex`. -/
theorem not_forall_normSq_controlLinearCombination (v : Fin 3 → ℂ) :
    ¬ ∀ j, Complex.normSq (controlLinearCombination v j) = 1 := by
  intro hv
  have h₀ := hv 0
  have h₁ := hv 1
  have h₂ := hv 2
  have h₃ := hv 3
  have h₄ := hv 4
  have h₅ := hv 5
  norm_num [controlLinearCombination, coordinateInt, Fin.sum_univ_three]
    at h₀ h₁ h₂ h₃ h₄ h₅
  norm_num [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im] at h₀ h₁ h₂ h₃ h₄ h₅
  have h₀₁ : (v 0).re * (v 1).re + (v 0).im * (v 1).im = 0 := by
    linear_combination (25 / 24) * h₃ - (3 / 8) * h₀ - (2 / 3) * h₁
  have h₀₂ : (v 0).re * (v 2).re + (v 0).im * (v 2).im = 0 := by
    linear_combination (3 / 4) * h₄ + (3 / 2) * h₅ -
      (3 / 4) * h₀ - (1 / 2) * h₁ - h₂ + h₀₁
  have h₁₂ : (v 1).re * (v 2).re + (v 1).im * (v 2).im = 0 := by
    linear_combination (3 / 2) * h₄ + (3 / 4) * h₅ -
      (1 / 2) * h₀ - (3 / 4) * h₁ - h₂ + h₀₁
  clear hv h₃ h₄ h₅
  have hz : ∀ i, v i ≠ 0 := by
    intro i hi
    fin_cases i <;> simp_all
  have ho : Pairwise (fun i j : Fin 3 => inner ℝ (v i) (v j) = 0) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [real_inner_eq_re_inner (𝕜 := ℂ), RCLike.inner_apply, mul_comm] <;>
      linarith only [h₀₁, h₀₂, h₁₂]
  have hdim :=
    (linearIndependent_of_ne_zero_of_inner_eq_zero (𝕜 := ℝ) hz ho).fintype_card_le_finrank
  norm_num [Complex.finrank_real_complex] at hdim

/-- The diagonal operator whose entries are `v · nⱼ`. -/
def controlDiagonal (v : Fin 3 → ℂ) : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.diagonal (controlLinearCombination v)

/-- Every operator in this three-parameter diagonal family fails to be unitary. -/
theorem controlDiagonal_not_mem_unitaryGroup (v : Fin 3 → ℂ) :
    controlDiagonal v ∉ Matrix.unitaryGroup (Fin 8) ℂ := by
  intro hu
  apply not_forall_normSq_controlLinearCombination v
  intro j
  have h := congrArg (fun A : Matrix (Fin 8) (Fin 8) ℂ => A j j) hu.2
  simp only [Matrix.star_eq_conjTranspose, controlDiagonal, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h
  change controlLinearCombination v j *
    (starRingEnd ℂ) (controlLinearCombination v j) = 1 at h
  rw [Complex.mul_conj] at h
  exact_mod_cast h

/-- The Pauli operator with a real coefficient vector. -/
def pauliCombination (v : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ k, (v k : ℂ) • SpinCover.pauli k

/-- A real Pauli combination squares to its squared Euclidean length times the identity. -/
theorem pauliCombination_mul_self (v : Fin 3 → ℝ) :
    pauliCombination v * pauliCombination v =
      ((∑ k, v k ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    refine Complex.ext ?_ ?_ <;>
    simp [pauliCombination, SpinCover.pauli, Matrix.mul_apply,
      Fin.sum_univ_two, Fin.sum_univ_three, Matrix.smul_apply, smul_eq_mul,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, pow_two] <;> ring

/-- Every real Pauli combination is Hermitian. -/
theorem pauliCombination_conjTranspose (v : Fin 3 → ℝ) :
    (pauliCombination v).conjTranspose = pauliCombination v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliCombination, SpinCover.pauli, Matrix.conjTranspose_apply,
      Fin.sum_univ_three]

/-- Each integer coordinate row has squared Euclidean length `15²`. -/
theorem coordinateInt_sum_sq (j : Fin 8) : ∑ k, coordinateInt j k ^ 2 = 225 := by
  revert_decide_kernel j

/-- The one-qubit Hermitian block selected by a control label. -/
def oneSite (j : Fin 8) : Matrix (Fin 2) (Fin 2) ℂ :=
  pauliCombination (fun k => (coordinateInt j k : ℝ) / 15)

/-- Each of the eight selected Pauli blocks is unitary. -/
theorem oneSite_mem_unitaryGroup (j : Fin 8) :
    oneSite j ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    oneSite, pauliCombination_conjTranspose, pauliCombination_mul_self]
  have h : ∑ k, (coordinateInt j k : ℝ) ^ 2 = 225 := by
    exact_mod_cast coordinateInt_sum_sq j
  have hn : ∑ k, ((coordinateInt j k : ℝ) / 15) ^ 2 = 1 := by
    rw [show (∑ k, ((coordinateInt j k : ℝ) / 15) ^ 2) =
      (∑ k, (coordinateInt j k : ℝ) ^ 2) / 15 ^ 2 by
      simp only [div_pow, Finset.sum_div]]
    rw [h]
    norm_num
  rw [hn]
  norm_num

/-- The controlled Pauli operator on one target qubit and three control qubits. -/
def witness : Matrix (Fin 2 × Fin 8) (Fin 2 × Fin 8) ℂ :=
  Matrix.blockDiagonal oneSite

/-- The sixteen-dimensional controlled Pauli witness is unitary. The proof uses its
eight two-dimensional blocks, without expanding the full matrix product. -/
theorem witness_mem_unitaryGroup : witness ∈ Matrix.unitaryGroup (Fin 2 × Fin 8) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, witness,
    Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
  have h : (fun j => oneSite j * (oneSite j).conjTranspose) = 1 := by
    funext j
    exact (oneSite_mem_unitaryGroup j).2
  rw [h, Matrix.blockDiagonal_one]

/-- The complex linear map from coefficient vectors to diagonal control operators. -/
def controlCoefficientMap : (Fin 3 → ℂ) →ₗ[ℂ] Matrix (Fin 8) (Fin 8) ℂ where
  toFun := controlDiagonal
  map_add' v w := by
    ext i j
    by_cases hij : i = j <;>
      simp [controlDiagonal, hij, controlLinearCombination,
        mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    ext i j
    simp [controlDiagonal, Matrix.diagonal_apply, controlLinearCombination, Finset.mul_sum,
      mul_left_comm]

/-- The right coefficient space in the displayed Pauli tensor expansion. -/
def controlCoefficientSpace : Submodule ℂ (Matrix (Fin 8) (Fin 8) ℂ) :=
  LinearMap.range controlCoefficientMap

/-- The right coefficient space contains no unitary operator. Source: the rank-three
obstruction in Section 2 of
`docs/audits/2026-10-02_mpu_schmidt_unitary_obstruction.tex`. -/
theorem controlCoefficientSpace_not_mem_unitaryGroup
    {A : Matrix (Fin 8) (Fin 8) ℂ} (hA : A ∈ controlCoefficientSpace) :
    A ∉ Matrix.unitaryGroup (Fin 8) ℂ := by
  obtain ⟨v, rfl⟩ := hA
  exact controlDiagonal_not_mem_unitaryGroup v

/-- The first three diagonal entries recover the three coefficient coordinates. -/
theorem controlCoefficientMap_injective : Function.Injective controlCoefficientMap := by
  intro v w hvw
  change controlDiagonal v = controlDiagonal w at hvw
  have h₀ := congrArg (fun A : Matrix (Fin 8) (Fin 8) ℂ => A 0 0) hvw
  have h₁ := congrArg (fun A : Matrix (Fin 8) (Fin 8) ℂ => A 1 1) hvw
  have h₂ := congrArg (fun A : Matrix (Fin 8) (Fin 8) ℂ => A 2 2) hvw
  norm_num [controlDiagonal, controlLinearCombination, coordinateInt,
    Fin.sum_univ_three] at h₀ h₁ h₂
  funext i
  fin_cases i <;> assumption

/-- The right coefficient space has complex dimension three. -/
theorem finrank_controlCoefficientSpace : Module.finrank ℂ controlCoefficientSpace = 3 := by
  rw [controlCoefficientSpace, LinearMap.finrank_range_of_inj controlCoefficientMap_injective]
  simp

/-- The diagonal control coefficient paired with one Pauli matrix. -/
def coefficient (k : Fin 3) : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.diagonal (fun j => (coordinateInt j k : ℂ) / 15)

/-- The coefficient map is the linear combination of the three displayed diagonal coefficients. -/
theorem controlCoefficientMap_apply (v : Fin 3 → ℂ) :
    controlCoefficientMap v = ∑ k, v k • coefficient k := by
  ext i j
  by_cases hij : i = j <;>
    simp [controlCoefficientMap, controlDiagonal, coefficient, hij,
      controlLinearCombination, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_comm]

/-- The controlled Pauli witness has a three-term tensor expansion. Source: the
first-cut expansion in Section 2 of
`docs/audits/2026-10-02_mpu_schmidt_unitary_obstruction.tex`. -/
theorem witness_eq_sum_pauli_kronecker :
    witness = ∑ k, SpinCover.pauli k ⊗ₖ coefficient k := by
  ext ⟨i, a⟩ ⟨j, b⟩
  by_cases hab : a = b
  · subst b
    simp [witness, Matrix.blockDiagonal_apply, oneSite, pauliCombination, coefficient,
      Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.kroneckerMap_apply,
      mul_comm]
  · simp [witness, Matrix.blockDiagonal_apply, hab, coefficient,
      Matrix.sum_apply, Matrix.kroneckerMap_apply]

/-- The three right coefficients in the Pauli expansion are linearly independent. -/
theorem coefficient_linearIndependent : LinearIndependent ℂ coefficient := by
  rw [Fintype.linearIndependent_iff]
  intro v hv k
  have h : controlCoefficientMap v = controlCoefficientMap 0 := by
    simpa only [controlCoefficientMap_apply, map_zero] using hv
  exact congrFun (controlCoefficientMap_injective h) k

/-- Each right coefficient belongs to the specified coefficient space. -/
theorem coefficient_mem_controlCoefficientSpace (k : Fin 3) :
    coefficient k ∈ controlCoefficientSpace := by
  refine ⟨Pi.single k 1, ?_⟩
  simp [controlCoefficientMap_apply]

/-- The specified coefficient space is exactly the span of the three right coefficients. -/
theorem controlCoefficientSpace_eq_span :
    controlCoefficientSpace = Submodule.span ℂ (Set.range coefficient) := by
  apply le_antisymm
  · rintro A ⟨v, rfl⟩
    rw [controlCoefficientMap_apply]
    exact Submodule.sum_mem _ (fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
  · apply Submodule.span_le.mpr
    rintro A ⟨k, rfl⟩
    exact coefficient_mem_controlCoefficientSpace k

end MPUPauliControl
