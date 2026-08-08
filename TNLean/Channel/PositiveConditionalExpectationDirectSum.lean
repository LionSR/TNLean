/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ScalarCommutant
import TNLean.Algebra.StarSubalgebraBlockForm
import TNLean.Analysis.MatrixSqrt
import TNLean.Channel.KrausCPTP
import TNLean.Channel.PositiveConditionalExpectation
import TNLean.Channel.Schwarz.PositiveMapProperties

/-!
# Positive conditional expectations onto finite sums of matrix factors

This file determines the form of a positive linear retraction onto the coordinate
star-subalgebra
\[
  \bigoplus_k \bigl(1_{m_k}\otimes M_{d_k}(\mathbb C)\bigr).
\]

## Main result

* `Matrix.exists_density_of_positive_retraction_onto_direct_sum_right_factors`: the
  coordinate direct-sum classification.
* `StarSubalgebra.exists_block_densities_of_positive_retraction`: the classification for
  an arbitrary star-subalgebra.
* `Matrix.trace_unitaryReindexLinearEquiv_symm_mul`: the trace-pairing identity
  for unitary block coordinates.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Proposition 1.5 and
  Equation (1.40)][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder Kronecker
open Matrix

namespace Matrix

variable {K : ℕ} {m d : Fin K → ℕ}

/-- Change from an original matrix basis to unitary block coordinates.

For an equivalence `e : H ≃ n`, this sends $A$ to
$\operatorname{reindex}_{e^{-1}}(U^*AU)$. Its inverse sends $X$ to
$U\operatorname{reindex}_e(X)U^*$. These are the coordinate changes in Wolf,
Equation (1.39). -/
noncomputable def unitaryReindexLinearEquiv
    {n H : Type*} [Fintype n] [DecidableEq n] [Fintype H] [DecidableEq H]
    (e : H ≃ n) (U : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    Matrix n n ℂ ≃ₗ[ℂ] Matrix H H ℂ :=
  ((((Unitary.toUnits (⟨U, hU⟩ : unitary (Matrix n n ℂ)))⁻¹).mulLeftLinearEquiv
    ℂ (Matrix n n ℂ)).trans
    ((Unitary.toUnits (⟨U, hU⟩ : unitary (Matrix n n ℂ))).mulRightLinearEquiv ℂ)) |>.trans
      (Matrix.reindexLinearEquiv ℂ ℂ e.symm e.symm)

@[simp]
theorem unitaryReindexLinearEquiv_apply
    {n H : Type*} [Fintype n] [DecidableEq n] [Fintype H] [DecidableEq H]
    (e : H ≃ n) (U : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (A : Matrix n n ℂ) :
    unitaryReindexLinearEquiv e U hU A =
      Matrix.reindex e.symm e.symm (star U * A * U) := by
  rfl

@[simp]
theorem unitaryReindexLinearEquiv_symm_apply
    {n H : Type*} [Fintype n] [DecidableEq n] [Fintype H] [DecidableEq H]
    (e : H ≃ n) (U : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (A : Matrix H H ℂ) :
    (unitaryReindexLinearEquiv e U hU).symm A =
      U * Matrix.reindex e e A * star U := by
  simp [unitaryReindexLinearEquiv, Unitary.toUnits,
    Matrix.symm_reindexLinearEquiv, Matrix.coe_reindexLinearEquiv, Matrix.mul_assoc]

@[simp]
theorem unitaryReindexLinearEquiv_one
    {n H : Type*} [Fintype n] [DecidableEq n] [Fintype H] [DecidableEq H]
    (e : H ≃ n) (U : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    unitaryReindexLinearEquiv e U hU 1 = 1 := by
  rw [unitaryReindexLinearEquiv_apply, Matrix.mul_one,
    Matrix.mem_unitaryGroup_iff'.mp hU]
  exact Matrix.reindexLinearEquiv_one ℂ ℂ e.symm

theorem unitaryReindexLinearEquiv_mul
    {n H : Type*} [Fintype n] [DecidableEq n] [Fintype H] [DecidableEq H]
    (e : H ≃ n) (U : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (A B : Matrix n n ℂ) :
    unitaryReindexLinearEquiv e U hU (A * B) =
      unitaryReindexLinearEquiv e U hU A *
        unitaryReindexLinearEquiv e U hU B := by
  rw [unitaryReindexLinearEquiv_apply, unitaryReindexLinearEquiv_apply,
    unitaryReindexLinearEquiv_apply]
  have hUright : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have hconj : star U * (A * B) * U =
      (star U * A * U) * (star U * B * U) := by
    calc
      star U * (A * B) * U = star U * A * (U * star U) * B * U := by
        rw [hUright]
        simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = (star U * A * U) * (star U * B * U) := by
        simp only [Matrix.mul_assoc]
  calc
    Matrix.reindex e.symm e.symm (star U * (A * B) * U) =
        Matrix.reindex e.symm e.symm
          ((star U * A * U) * (star U * B * U)) := congrArg _ hconj
    _ = Matrix.reindex e.symm e.symm (star U * A * U) *
        Matrix.reindex e.symm e.symm (star U * B * U) :=
      (Matrix.reindexLinearEquiv_mul ℂ ℂ e.symm e.symm e.symm _ _).symm

@[simp]
theorem unitaryReindexLinearEquiv_star
    {n H : Type*} [Fintype n] [DecidableEq n] [Fintype H] [DecidableEq H]
    (e : H ≃ n) (U : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (A : Matrix n n ℂ) :
    unitaryReindexLinearEquiv e U hU (star A) =
      star (unitaryReindexLinearEquiv e U hU A) := by
  rw [unitaryReindexLinearEquiv_apply, unitaryReindexLinearEquiv_apply]
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- The inverse unitary block-coordinate change is adjoint to the forward
change under the bilinear trace pairing:
$\operatorname{tr}(\Phi^{-1}(X)A)=\operatorname{tr}(X\Phi(A))$. -/
theorem trace_unitaryReindexLinearEquiv_symm_mul
    {n H : Type*} [Fintype n] [DecidableEq n] [Fintype H] [DecidableEq H]
    (e : H ≃ n) (U : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (X : Matrix H H ℂ) (A : Matrix n n ℂ) :
    Matrix.trace ((unitaryReindexLinearEquiv e U hU).symm X * A) =
      Matrix.trace (X * unitaryReindexLinearEquiv e U hU A) := by
  classical
  rw [unitaryReindexLinearEquiv_symm_apply, unitaryReindexLinearEquiv_apply]
  let Ahat := Matrix.reindex e.symm e.symm (star U * A * U)
  have hreindex : Matrix.reindex e e Ahat = star U * A * U := by
    ext i j
    simp [Ahat]
  calc
    Matrix.trace ((U * Matrix.reindex e e X * star U) * A) =
        Matrix.trace (U * (Matrix.reindex e e X * star U * A)) := by
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((Matrix.reindex e e X * star U * A) * U) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace (Matrix.reindex e e X * (star U * A * U)) := by
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace
        (Matrix.reindex e e X * Matrix.reindex e e Ahat) := by rw [hreindex]
    _ = Matrix.trace (Matrix.reindex e e (X * Ahat)) := by
      exact congrArg Matrix.trace
        (Matrix.reindexLinearEquiv_mul ℂ ℂ e e e X Ahat)
    _ = Matrix.trace (X * Ahat) := Matrix.trace_submatrix_equiv e.symm (X * Ahat)

/-- Unitary change of basis and reindexing preserve positive semidefiniteness. -/
theorem unitaryReindexLinearEquiv_posSemidef
    {n H : Type*} [Fintype n] [DecidableEq n] [Fintype H] [DecidableEq H]
    (e : H ≃ n) (U : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ)
    {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    (unitaryReindexLinearEquiv e U hU A).PosSemidef := by
  rw [unitaryReindexLinearEquiv_apply]
  have hConj : (star U * A * U).PosSemidef := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] using
      hA.mul_mul_conjTranspose_same (B := star U)
  exact hConj.submatrix e

/-- The inverse unitary change of basis and reindexing preserve positive
semidefiniteness. -/
theorem unitaryReindexLinearEquiv_symm_posSemidef
    {n H : Type*} [Fintype n] [DecidableEq n] [Fintype H] [DecidableEq H]
    (e : H ≃ n) (U : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ)
    {A : Matrix H H ℂ} (hA : A.PosSemidef) :
    ((unitaryReindexLinearEquiv e U hU).symm A).PosSemidef := by
  rw [unitaryReindexLinearEquiv_symm_apply]
  exact (hA.submatrix e.symm).mul_mul_conjTranspose_same (B := U)

/-- Changing to unitary block coordinates is trace-preserving and completely positive. -/
theorem unitaryReindexLinearEquiv_toLinearMap_isKrausCPTP
    {n H : Type*} [Fintype n] [DecidableEq n] [Fintype H] [DecidableEq H]
    (e : H ≃ n) (U : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    IsKrausCPTP (unitaryReindexLinearEquiv e U hU).toLinearMap := by
  rw [show (unitaryReindexLinearEquiv e U hU).toLinearMap =
      equivReindexMap e.symm ∘ₗ singleKrausMap (star U) by
    apply LinearMap.ext
    intro A
    simp [unitaryReindexLinearEquiv_apply, equivReindexMap,
      Matrix.coe_reindexLinearEquiv, Matrix.star_eq_conjTranspose]]
  apply isKrausCPTP_comp
  · apply singleKrausMap_isKrausCPTP
    simpa only [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hU
  · exact equivReindexMap_isKrausCPTP e.symm

/-- Returning from unitary block coordinates is trace-preserving and completely positive. -/
theorem unitaryReindexLinearEquiv_symm_toLinearMap_isKrausCPTP
    {n H : Type*} [Fintype n] [DecidableEq n] [Fintype H] [DecidableEq H]
    (e : H ≃ n) (U : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    IsKrausCPTP (unitaryReindexLinearEquiv e U hU).symm.toLinearMap := by
  rw [show (unitaryReindexLinearEquiv e U hU).symm.toLinearMap =
      singleKrausMap U ∘ₗ equivReindexMap e by
    apply LinearMap.ext
    intro A
    simp [unitaryReindexLinearEquiv_symm_apply, equivReindexMap,
      Matrix.coe_reindexLinearEquiv, Matrix.star_eq_conjTranspose]]
  apply isKrausCPTP_comp
  · exact equivReindexMap_isKrausCPTP e
  · apply singleKrausMap_isKrausCPTP
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hU

/-- A matrix acting on the traced factor may be moved across an input before taking the
partial trace.

This is the finite-dimensional cyclicity used to pass between the two orders in Wolf,
Equation (1.40): the displayed equation uses $A_{kk}(\rho_k\otimes 1)$, while the
one-factor functional representation naturally gives $(\rho_k\otimes 1)A_{kk}$. -/
private theorem partialTraceLeft_kronecker_one_mul_eq_mul_kronecker_one
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (ρ : Matrix α α ℂ) (A : Matrix (α × β) (α × β) ℂ) :
    Matrix.partialTraceLeft ((ρ ⊗ₖ (1 : Matrix β β ℂ)) * A) =
      Matrix.partialTraceLeft (A * (ρ ⊗ₖ (1 : Matrix β β ℂ))) := by
  classical
  ext i j
  simp only [Matrix.partialTraceLeft_apply, Matrix.mul_apply]
  simp_rw [Fintype.sum_prod_type]
  simp only [Matrix.kroneckerMap_apply, Matrix.one_apply]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Finset.sum_ite_eq']
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The diagonal block of a matrix on a finite dependent direct sum.

This is the block restriction used in Wolf, Proposition 1.5 and Equation (1.40). -/
noncomputable def directSumBlockCompression (k : Fin K) :
    Matrix ((j : Fin K) × (Fin (m j) × Fin (d j)))
        ((j : Fin K) × (Fin (m j) × Fin (d j))) ℂ →ₗ[ℂ]
      Matrix (Fin (m k) × Fin (d k)) (Fin (m k) × Fin (d k)) ℂ where
  toFun A := A.submatrix (fun i ↦ ⟨k, i⟩) (fun i ↦ ⟨k, i⟩)
  map_add' A B := by
    ext i j
    rfl
  map_smul' c A := by
    ext i j
    rfl

@[simp]
theorem directSumBlockCompression_apply (k : Fin K)
    (A : Matrix ((j : Fin K) × (Fin (m j) × Fin (d j)))
      ((j : Fin K) × (Fin (m j) × Fin (d j))) ℂ)
    (i j : Fin (m k) × Fin (d k)) :
    directSumBlockCompression (m := m) (d := d) k A i j = A ⟨k, i⟩ ⟨k, j⟩ :=
  rfl

@[simp]
theorem directSumBlockCompression_blockDiagonal'
    (B : ∀ j, Matrix (Fin (m j) × Fin (d j))
      (Fin (m j) × Fin (d j)) ℂ) (k : Fin K) :
    directSumBlockCompression (m := m) (d := d) k
        (Matrix.blockDiagonal' B) = B k := by
  classical
  ext i j
  exact Matrix.blockDiagonal'_apply_eq B k i j

@[simp]
theorem directSumBlockCompression_one (k : Fin K) :
    directSumBlockCompression (m := m) (d := d) k 1 = 1 := by
  classical
  ext i j
  rcases i with ⟨a, b⟩
  rcases j with ⟨c, f⟩
  simp [directSumBlockCompression, Matrix.one_apply]

/-- Embed a matrix as one diagonal block of a finite dependent direct sum.

This is the inclusion of a single summand in Wolf, Proposition 1.5 and
Equation (1.40). -/
noncomputable def directSumBlockEmbedding (k : Fin K) :
    Matrix (Fin (m k) × Fin (d k)) (Fin (m k) × Fin (d k)) ℂ →ₗ[ℂ]
      Matrix ((j : Fin K) × (Fin (m j) × Fin (d j)))
        ((j : Fin K) × (Fin (m j) × Fin (d j))) ℂ where
  toFun A := Matrix.blockDiagonal' (Pi.single k A)
  map_add' A B := by
    rw [Pi.single_add, Matrix.blockDiagonal'_add]
  map_smul' c A := by
    rw [Pi.single_smul, Matrix.blockDiagonal'_smul]
    rfl

@[simp]
theorem directSumBlockCompression_embedding (k : Fin K)
    (A : Matrix (Fin (m k) × Fin (d k)) (Fin (m k) × Fin (d k)) ℂ) :
    directSumBlockCompression (m := m) (d := d) k
      (directSumBlockEmbedding (m := m) (d := d) k A) = A := by
  ext i j
  simp [directSumBlockCompression, directSumBlockEmbedding,
    Matrix.blockDiagonal'_apply_eq]

/-- Multiplication by block-diagonal matrices restricts on an embedded
summand to multiplication by the corresponding diagonal blocks. -/
theorem blockDiagonal'_mul_directSumBlockEmbedding_mul_blockDiagonal'
    (P Q : ∀ j, Matrix (Fin (m j) × Fin (d j))
      (Fin (m j) × Fin (d j)) ℂ)
    (k : Fin K)
    (A : Matrix (Fin (m k) × Fin (d k))
      (Fin (m k) × Fin (d k)) ℂ) :
    Matrix.blockDiagonal' P *
        directSumBlockEmbedding (m := m) (d := d) k A *
        Matrix.blockDiagonal' Q =
      directSumBlockEmbedding (m := m) (d := d) k (P k * A * Q k) := by
  classical
  change Matrix.blockDiagonal' P * Matrix.blockDiagonal' (Pi.single k A) *
      Matrix.blockDiagonal' Q =
    Matrix.blockDiagonal' (Pi.single k (P k * A * Q k))
  rw [← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
  congr 1
  funext j
  by_cases hjk : j = k
  · subst j
    simp
  · simp [hjk]

/-- A dependent block-diagonal matrix is the sum of its embedded diagonal
blocks. -/
theorem sum_directSumBlockEmbedding_eq_blockDiagonal'
    (B : ∀ j, Matrix (Fin (m j) × Fin (d j))
      (Fin (m j) × Fin (d j)) ℂ) :
    ∑ j, directSumBlockEmbedding (m := m) (d := d) j (B j) =
      Matrix.blockDiagonal' B := by
  classical
  ext ⟨k, a⟩ ⟨l, b⟩
  change (∑ j, Matrix.blockDiagonal' (Pi.single j (B j))) ⟨k, a⟩ ⟨l, b⟩ =
    Matrix.blockDiagonal' B ⟨k, a⟩ ⟨l, b⟩
  by_cases hkl : k = l
  · subst l
    rw [Matrix.sum_apply]
    simp only [Matrix.blockDiagonal'_apply_eq]
    rw [Finset.sum_eq_single k]
    · simp
    · intro i _ hik
      rw [Pi.single_eq_of_ne (Ne.symm hik)]
      rfl
    · simp
  · rw [Matrix.blockDiagonal'_apply_ne B a b hkl, Matrix.sum_apply]
    apply Finset.sum_eq_zero
    intro j _
    exact Matrix.blockDiagonal'_apply_ne
      (Pi.single j (B j) : ∀ i, Matrix (Fin (m i) × Fin (d i))
        (Fin (m i) × Fin (d i)) ℂ) a b hkl

/-- Compression to a diagonal summand preserves positive semidefiniteness. -/
theorem directSumBlockCompression_isPositiveMap (k : Fin K) :
    IsPositiveMap (directSumBlockCompression (m := m) (d := d) k) := by
  intro A hA
  exact hA.submatrix (fun i ↦ ⟨k, i⟩)

/-- Embedding in a diagonal summand preserves positive semidefiniteness. -/
theorem directSumBlockEmbedding_isPositiveMap (k : Fin K) :
    IsPositiveMap (directSumBlockEmbedding (m := m) (d := d) k) := by
  intro A hA
  apply Matrix.PosSemidef.blockDiagonal'
  intro j
  by_cases hjk : j = k
  · subst j
    simpa using hA
  · simpa [hjk] using
      (Matrix.PosSemidef.zero :
        (0 : Matrix (Fin (m j) × Fin (d j)) (Fin (m j) × Fin (d j)) ℂ).PosSemidef)

/-- The image of a map, restricted to one diagonal output block. -/
noncomputable def directSumOutputBlockMap
    (E : Matrix ((j : Fin K) × (Fin (m j) × Fin (d j)))
        ((j : Fin K) × (Fin (m j) × Fin (d j))) ℂ →ₗ[ℂ]
      Matrix ((j : Fin K) × (Fin (m j) × Fin (d j)))
        ((j : Fin K) × (Fin (m j) × Fin (d j))) ℂ)
    (k : Fin K) :
    Matrix ((j : Fin K) × (Fin (m j) × Fin (d j)))
        ((j : Fin K) × (Fin (m j) × Fin (d j))) ℂ →ₗ[ℂ]
      Matrix (Fin (m k) × Fin (d k)) (Fin (m k) × Fin (d k)) ℂ :=
  (directSumBlockCompression (m := m) (d := d) k).comp E

/-- Restrict a map to one diagonal input block and one diagonal output block. -/
noncomputable def directSumDiagonalBlockMap
    (E : Matrix ((j : Fin K) × (Fin (m j) × Fin (d j)))
        ((j : Fin K) × (Fin (m j) × Fin (d j))) ℂ →ₗ[ℂ]
      Matrix ((j : Fin K) × (Fin (m j) × Fin (d j)))
        ((j : Fin K) × (Fin (m j) × Fin (d j))) ℂ)
    (k : Fin K) :
    Matrix (Fin (m k) × Fin (d k)) (Fin (m k) × Fin (d k)) ℂ →ₗ[ℂ]
      Matrix (Fin (m k) × Fin (d k)) (Fin (m k) × Fin (d k)) ℂ :=
  (directSumOutputBlockMap E k).comp
    (directSumBlockEmbedding (m := m) (d := d) k)

/-- Restricting a positive map to one diagonal output block preserves positivity. -/
theorem directSumOutputBlockMap_isPositiveMap
    (E : Matrix ((j : Fin K) × (Fin (m j) × Fin (d j)))
        ((j : Fin K) × (Fin (m j) × Fin (d j))) ℂ →ₗ[ℂ]
      Matrix ((j : Fin K) × (Fin (m j) × Fin (d j)))
        ((j : Fin K) × (Fin (m j) × Fin (d j))) ℂ)
    (hE : IsPositiveMap E) (k : Fin K) :
    IsPositiveMap (directSumOutputBlockMap E k) := by
  intro A hA
  exact directSumBlockCompression_isPositiveMap k (E A) (hE A hA)

/-- Restricting a positive map to one diagonal input and output block preserves
positivity. -/
theorem directSumDiagonalBlockMap_isPositiveMap
    (E : Matrix ((j : Fin K) × (Fin (m j) × Fin (d j)))
        ((j : Fin K) × (Fin (m j) × Fin (d j))) ℂ →ₗ[ℂ]
      Matrix ((j : Fin K) × (Fin (m j) × Fin (d j)))
        ((j : Fin K) × (Fin (m j) × Fin (d j))) ℂ)
    (hE : IsPositiveMap E) (k : Fin K) :
    IsPositiveMap (directSumDiagonalBlockMap E k) := by
  intro A hA
  exact directSumOutputBlockMap_isPositiveMap E hE k _
    (directSumBlockEmbedding_isPositiveMap k A hA)

/-- The identity embedded in one summand is its central block projection. -/
theorem directSumBlockEmbedding_one (k : Fin K) :
    directSumBlockEmbedding (m := m) (d := d) k 1 =
      Matrix.blockProjection
        (n := fun j : Fin K ↦ Fin (m j) × Fin (d j)) (R := ℂ) k := by
  classical
  change Matrix.blockDiagonal' (Pi.single k 1) =
    Matrix.blockDiagonal' (fun i => if i = k then 1 else 0)
  congr 1
  funext i
  by_cases hik : i = k
  · subst i
    simp
  · simp [hik]

/-- Embedding a right-factor matrix in one summand agrees with its coordinate factor
family. -/
theorem directSumBlockEmbedding_one_kronecker (k : Fin K)
    (X : Matrix (Fin (d k)) (Fin (d k)) ℂ) :
    directSumBlockEmbedding (m := m) (d := d) k
        ((1 : Matrix (Fin (m k)) (Fin (m k)) ℂ) ⊗ₖ X) =
      Matrix.blockDiagonal' fun j =>
        (1 : Matrix (Fin (m j)) (Fin (m j)) ℂ) ⊗ₖ
          (Pi.single k X : ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) j := by
  classical
  change Matrix.blockDiagonal'
      (Pi.single k ((1 : Matrix (Fin (m k)) (Fin (m k)) ℂ) ⊗ₖ X) :
        ∀ i, Matrix (Fin (m i) × Fin (d i)) (Fin (m i) × Fin (d i)) ℂ) = _
  congr 1
  funext j
  by_cases hjk : j = k
  · subst j
    simp
  · simp [hjk]

/-- The identity matrix is the coordinate factor family of identity matrices. -/
theorem blockDiagonal_one_kronecker_one :
    Matrix.blockDiagonal' (fun j : Fin K =>
        (1 : Matrix (Fin (m j)) (Fin (m j)) ℂ) ⊗ₖ
          (1 : Matrix (Fin (d j)) (Fin (d j)) ℂ)) =
      (1 : Matrix ((j : Fin K) × (Fin (m j) × Fin (d j)))
        ((j : Fin K) × (Fin (m j) × Fin (d j))) ℂ) := by
  rw [← Matrix.blockDiagonal'_one]
  congr 1
  funext j
  simp

/-- Compressing a coordinate factor decomposition selects the corresponding factor. -/
@[simp]
theorem directSumBlockCompression_blockDiagonal_one_kronecker
    (B : ∀ j, Matrix (Fin (d j)) (Fin (d j)) ℂ) (k : Fin K) :
    directSumBlockCompression (m := m) (d := d) k
        (Matrix.blockDiagonal' fun j =>
          (1 : Matrix (Fin (m j)) (Fin (m j)) ℂ) ⊗ₖ B j) =
      (1 : Matrix (Fin (m k)) (Fin (m k)) ℂ) ⊗ₖ B k := by
  ext i j
  simp [directSumBlockCompression, Matrix.blockDiagonal'_apply_eq]

/-- Compression by a central block projection retains exactly one diagonal block. -/
theorem blockProjection_mul_mul_eq_directSumBlockEmbedding
    (A : Matrix ((j : Fin K) × (Fin (m j) × Fin (d j)))
      ((j : Fin K) × (Fin (m j) × Fin (d j))) ℂ)
    (k : Fin K) :
    Matrix.blockProjection
          (n := fun j : Fin K ↦ Fin (m j) × Fin (d j)) (R := ℂ) k * A *
        Matrix.blockProjection
          (n := fun j : Fin K ↦ Fin (m j) × Fin (d j)) (R := ℂ) k =
      directSumBlockEmbedding (m := m) (d := d) k
        (directSumBlockCompression (m := m) (d := d) k A) := by
  classical
  ext ⟨i, a⟩ ⟨j, b⟩
  by_cases hik : i = k
  · subst i
    by_cases hjk : j = k
    · subst j
      simp [directSumBlockEmbedding, directSumBlockCompression]
    · rw [Matrix.mul_blockProjection_apply_ne _ k hjk]
      have hkj : k ≠ j := Ne.symm hjk
      simp [directSumBlockEmbedding, Matrix.blockDiagonal'_apply, hkj]
  · have hright :
        directSumBlockEmbedding (m := m) (d := d) k
            (directSumBlockCompression (m := m) (d := d) k A) ⟨i, a⟩ ⟨j, b⟩ = 0 := by
      simp [directSumBlockEmbedding, Matrix.blockDiagonal'_apply, hik]
    rw [hright, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    rintro x _
    rw [Matrix.blockProjection_mul_apply_ne A k hik, zero_mul]

/-- A coordinate positive retraction sees only the corresponding diagonal input block
when one restricts its output to a fixed summand.

The complementary central projection is annihilated by the restricted output map, so
positivity annihilates both its left and right corners. This is the cross-block removal
in Wolf, Proposition 1.5, lines 548--560. -/
theorem directSumOutputBlockMap_eq_diagonalBlockMap_compression
    (E : Matrix ((j : Fin K) × (Fin (m j) × Fin (d j)))
        ((j : Fin K) × (Fin (m j) × Fin (d j))) ℂ →ₗ[ℂ]
      Matrix ((j : Fin K) × (Fin (m j) × Fin (d j)))
        ((j : Fin K) × (Fin (m j) × Fin (d j))) ℂ)
    (hE : IsPositiveMap E)
    (hFix : ∀ B : ∀ j, Matrix (Fin (d j)) (Fin (d j)) ℂ,
      E (Matrix.blockDiagonal' fun j =>
          (1 : Matrix (Fin (m j)) (Fin (m j)) ℂ) ⊗ₖ B j) =
        Matrix.blockDiagonal' fun j =>
          (1 : Matrix (Fin (m j)) (Fin (m j)) ℂ) ⊗ₖ B j)
    (A : Matrix ((j : Fin K) × (Fin (m j) × Fin (d j)))
      ((j : Fin K) × (Fin (m j) × Fin (d j))) ℂ)
    (k : Fin K) :
    directSumOutputBlockMap E k A =
      directSumDiagonalBlockMap E k
        (directSumBlockCompression (m := m) (d := d) k A) := by
  let P := Matrix.blockProjection
    (n := fun j : Fin K ↦ Fin (m j) × Fin (d j)) (R := ℂ) k
  let T := directSumOutputBlockMap E k
  have hTP : T P = 1 := by
    dsimp only [T, P]
    rw [← directSumBlockEmbedding_one (m := m) (d := d) k]
    have hOneKron :
        (1 : Matrix (Fin (m k) × Fin (d k)) (Fin (m k) × Fin (d k)) ℂ) =
          (1 : Matrix (Fin (m k)) (Fin (m k)) ℂ) ⊗ₖ
            (1 : Matrix (Fin (d k)) (Fin (d k)) ℂ) := by
      simp
    conv_lhs => rw [hOneKron, directSumBlockEmbedding_one_kronecker]
    change directSumBlockCompression (m := m) (d := d) k
      (E (Matrix.blockDiagonal' fun j =>
        (1 : Matrix (Fin (m j)) (Fin (m j)) ℂ) ⊗ₖ
          (Pi.single k (1 : Matrix (Fin (d k)) (Fin (d k)) ℂ) :
            ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) j)) = 1
    rw [hFix]
    simp
  have hTOne : T 1 = 1 := by
    dsimp only [T]
    rw [← blockDiagonal_one_kronecker_one (m := m) (d := d)]
    change directSumBlockCompression (m := m) (d := d) k
      (E (Matrix.blockDiagonal' fun j =>
        (1 : Matrix (Fin (m j)) (Fin (m j)) ℂ) ⊗ₖ
          (1 : Matrix (Fin (d j)) (Fin (d j)) ℂ))) = 1
    rw [hFix]
    exact directSumBlockCompression_blockDiagonal_one_kronecker
      (m := m) (d := d) (fun j => 1) k |>.trans (by simp)
  have hTComplement : T (1 - P) = 0 := by
    rw [map_sub, hTOne, hTP, sub_self]
  have hPherm : P.IsHermitian := by
    exact Matrix.blockProjection_isHermitian k
  have hPidem : IsIdempotentElem P := by
    exact Matrix.blockProjection_isIdempotentElem k
  have hQherm : (1 - P).IsHermitian := Matrix.isHermitian_one.sub hPherm
  have hQidem : IsIdempotentElem (1 - P) := hPidem.one_sub
  have hCorners :=
    (directSumOutputBlockMap_isPositiveMap E hE k).map_mul_eq_zero_of_map_projection_eq_zero
      hQherm hQidem hTComplement
  have hLeft : T A = T (P * A) := by
    have hDecomp : A = P * A + (1 - P) * A := by
      rw [Matrix.sub_mul, Matrix.one_mul]
      abel
    calc
      T A = T (P * A + (1 - P) * A) := congrArg T hDecomp
      _ = T (P * A) := by rw [map_add, (hCorners A).1, add_zero]
  have hRight : T (P * A) = T (P * A * P) := by
    have hDecomp : P * A = P * A * P + P * A * (1 - P) := by
      rw [Matrix.mul_sub, Matrix.mul_one]
      abel
    calc
      T (P * A) = T (P * A * P + P * A * (1 - P)) := congrArg T hDecomp
      _ = T (P * A * P) := by
        rw [map_add, (hCorners (P * A)).2, add_zero]
  rw [hLeft, hRight,
    blockProjection_mul_mul_eq_directSumBlockEmbedding (m := m) (d := d)]
  rfl

/-- A positive linear retraction onto
$\bigoplus_k(1_{m_k}\otimes M_{d_k}(\mathbb C))$ is a weighted partial trace on each
diagonal summand.

More precisely, there are positive semidefinite matrices $\rho_k$ of trace one such that
\[
  E(A)=\bigoplus_k\left[1_{m_k}\otimes
    \operatorname{tr}_{m_k}\bigl((\rho_k\otimes 1_{d_k})A_{kk}\bigr)\right].
\]
This is the coordinate direct-sum form of Wolf, Proposition 1.5 and Equation (1.40),
lines 536--570. The theorem assumes a given positive retraction; it does not construct
such a retraction from a fixed-point space. -/
theorem exists_density_of_positive_retraction_onto_direct_sum_right_factors
    [∀ k, NeZero (m k)] [∀ k, NeZero (d k)]
    (E : Matrix ((j : Fin K) × (Fin (m j) × Fin (d j)))
        ((j : Fin K) × (Fin (m j) × Fin (d j))) ℂ →ₗ[ℂ]
      Matrix ((j : Fin K) × (Fin (m j) × Fin (d j)))
        ((j : Fin K) × (Fin (m j) × Fin (d j))) ℂ)
    (hE : IsPositiveMap E)
    (hRange : ∀ A, ∃ B : ∀ j, Matrix (Fin (d j)) (Fin (d j)) ℂ,
      E A = Matrix.blockDiagonal' fun j =>
        (1 : Matrix (Fin (m j)) (Fin (m j)) ℂ) ⊗ₖ B j)
    (hFix : ∀ B : ∀ j, Matrix (Fin (d j)) (Fin (d j)) ℂ,
      E (Matrix.blockDiagonal' fun j =>
          (1 : Matrix (Fin (m j)) (Fin (m j)) ℂ) ⊗ₖ B j) =
        Matrix.blockDiagonal' fun j =>
          (1 : Matrix (Fin (m j)) (Fin (m j)) ℂ) ⊗ₖ B j) :
    ∃ ρ : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ,
      (∀ k, (ρ k).PosSemidef) ∧ (∀ k, (ρ k).trace = 1) ∧
        ∀ A, E A = Matrix.blockDiagonal' fun k =>
          (1 : Matrix (Fin (m k)) (Fin (m k)) ℂ) ⊗ₖ
            Matrix.partialTraceLeft
              (((ρ k) ⊗ₖ (1 : Matrix (Fin (d k)) (Fin (d k)) ℂ)) *
                directSumBlockCompression (m := m) (d := d) k A) := by
  have hLocalRange (k : Fin K)
      (A : Matrix (Fin (m k) × Fin (d k)) (Fin (m k) × Fin (d k)) ℂ) :
      ∃ B : Matrix (Fin (d k)) (Fin (d k)) ℂ,
        directSumDiagonalBlockMap E k A =
          (1 : Matrix (Fin (m k)) (Fin (m k)) ℂ) ⊗ₖ B := by
    obtain ⟨B, hB⟩ := hRange (directSumBlockEmbedding (m := m) (d := d) k A)
    refine ⟨B k, ?_⟩
    change directSumBlockCompression (m := m) (d := d) k
      (E (directSumBlockEmbedding (m := m) (d := d) k A)) = _
    rw [hB]
    exact directSumBlockCompression_blockDiagonal_one_kronecker B k
  have hLocalFix (k : Fin K) (X : Matrix (Fin (d k)) (Fin (d k)) ℂ) :
      directSumDiagonalBlockMap E k
          ((1 : Matrix (Fin (m k)) (Fin (m k)) ℂ) ⊗ₖ X) =
        (1 : Matrix (Fin (m k)) (Fin (m k)) ℂ) ⊗ₖ X := by
    change directSumBlockCompression (m := m) (d := d) k
      (E (directSumBlockEmbedding (m := m) (d := d) k
        ((1 : Matrix (Fin (m k)) (Fin (m k)) ℂ) ⊗ₖ X))) = _
    rw [directSumBlockEmbedding_one_kronecker, hFix]
    exact (directSumBlockCompression_blockDiagonal_one_kronecker
      (m := m) (d := d)
      (Pi.single k X : ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) k).trans (by simp)
  have hLocal (k : Fin K) :
      ∃ ρ : Matrix (Fin (m k)) (Fin (m k)) ℂ,
        ρ.PosSemidef ∧ ρ.trace = 1 ∧
          ∀ A : Matrix (Fin (m k) × Fin (d k)) (Fin (m k) × Fin (d k)) ℂ,
            directSumDiagonalBlockMap E k A =
              (1 : Matrix (Fin (m k)) (Fin (m k)) ℂ) ⊗ₖ
                Matrix.partialTraceLeft
                  (A * (ρ ⊗ₖ (1 : Matrix (Fin (d k)) (Fin (d k)) ℂ))) := by
    obtain ⟨ρ, hρpos, hρtrace, hρformula⟩ :=
      Matrix.exists_density_of_positive_retraction_onto_right_factor
      (directSumDiagonalBlockMap E k)
      (directSumDiagonalBlockMap_isPositiveMap E hE k) (hLocalRange k) (hLocalFix k)
    refine ⟨ρ, hρpos, hρtrace, fun A ↦ ?_⟩
    rw [hρformula]
    congr 1
    exact partialTraceLeft_kronecker_one_mul_eq_mul_kronecker_one ρ A
  choose ρ hρpos hρtrace hρformula using hLocal
  refine ⟨ρ, hρpos, hρtrace, fun A ↦ ?_⟩
  obtain ⟨B, hB⟩ := hRange A
  rw [hB]
  congr 1
  funext k
  calc
    (1 : Matrix (Fin (m k)) (Fin (m k)) ℂ) ⊗ₖ B k =
        directSumOutputBlockMap E k A := by
      change _ = directSumBlockCompression (m := m) (d := d) k (E A)
      rw [hB]
      exact (directSumBlockCompression_blockDiagonal_one_kronecker B k).symm
    _ = directSumDiagonalBlockMap E k
          (directSumBlockCompression (m := m) (d := d) k A) :=
      directSumOutputBlockMap_eq_diagonalBlockMap_compression E hE hFix A k
    _ = (1 : Matrix (Fin (m k)) (Fin (m k)) ℂ) ⊗ₖ
          Matrix.partialTraceLeft
            (directSumBlockCompression (m := m) (d := d) k A *
              ((ρ k) ⊗ₖ (1 : Matrix (Fin (d k)) (Fin (d k)) ℂ))) := hρformula k _
    _ = _ := by
      congr 1
      exact (partialTraceLeft_kronecker_one_mul_eq_mul_kronecker_one
        (ρ k) (directSumBlockCompression (m := m) (d := d) k A)).symm

end Matrix

namespace StarSubalgebra

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A positive linear retraction onto a star-subalgebra of a full complex matrix algebra
has the blockwise weighted-partial-trace form.

Thus, after the unitary and index change of Wolf, Equation (1.39), there are positive
semidefinite matrices $\rho_k$ of trace one such that
\[
 E(A)=U\left(\bigoplus_k 1_{m_k}\otimes
   \operatorname{tr}_{m_k}\bigl((\rho_k\otimes1_{d_k})
     (U^*AU)_{kk}\bigr)\right)U^*.
\]
This is Wolf, Proposition 1.5 and Equation (1.40), lines 536--570.

Proposition 1.5 itself assumes the positive retraction. The separate construction of a
fixed-point projection required for Wolf, Theorem 6.14 is documented in
`docs/paper-gaps/wolf_theorem6_14_fixed_point_projection_gap.tex`. -/
theorem exists_block_densities_of_positive_retraction
    (S : StarSubalgebra ℂ (Matrix n n ℂ))
    (E : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
    (hE : IsPositiveMap E) (hRange : ∀ A, E A ∈ S)
    (hFix : ∀ A ∈ S, E A = A) :
    ∃ (K : ℕ) (d m : Fin K → ℕ)
      (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ n)
      (U : Matrix n n ℂ) (ρ : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ),
      U ∈ Matrix.unitaryGroup n ℂ ∧ (∀ k, 0 < d k) ∧ (∀ k, 0 < m k) ∧
        (∀ A : Matrix n n ℂ,
          A ∈ S ↔ ∃ B : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ,
            star U * A * U = Matrix.reindex e e
              (Matrix.blockDiagonal' fun k =>
                (1 : Matrix (Fin (m k)) (Fin (m k)) ℂ) ⊗ₖ B k)) ∧
        (∀ k, (ρ k).PosSemidef) ∧ (∀ k, (ρ k).trace = 1) ∧
          ∀ A, E A = U * Matrix.reindex e e
            (Matrix.blockDiagonal' fun k =>
              (1 : Matrix (Fin (m k)) (Fin (m k)) ℂ) ⊗ₖ
                Matrix.partialTraceLeft
                  (((ρ k) ⊗ₖ (1 : Matrix (Fin (d k)) (Fin (d k)) ℂ)) *
                    Matrix.directSumBlockCompression (m := m) (d := d) k
                      (Matrix.reindex e.symm e.symm (star U * A * U)))) * star U := by
  classical
  obtain ⟨K, d, m, e, U, hU, hd, hm, hBlock⟩ :=
    S.exists_unitary_conj_blockDiagonal_iff
  letI : ∀ k, NeZero (m k) := fun k => ⟨Nat.ne_of_gt (hm k)⟩
  letI : ∀ k, NeZero (d k) := fun k => ⟨Nat.ne_of_gt (hd k)⟩
  let Φ := Matrix.unitaryReindexLinearEquiv e U hU
  let Ehat : Matrix ((k : Fin K) × (Fin (m k) × Fin (d k)))
      ((k : Fin K) × (Fin (m k) × Fin (d k))) ℂ →ₗ[ℂ]
        Matrix ((k : Fin K) × (Fin (m k) × Fin (d k)))
          ((k : Fin K) × (Fin (m k) × Fin (d k))) ℂ := Φ.conj E
  have hEhat : IsPositiveMap Ehat := by
    intro A hA
    exact Matrix.unitaryReindexLinearEquiv_posSemidef e U hU
      (hE _ (Matrix.unitaryReindexLinearEquiv_symm_posSemidef e U hU hA))
  have hRangeHat (A : Matrix ((k : Fin K) × (Fin (m k) × Fin (d k)))
      ((k : Fin K) × (Fin (m k) × Fin (d k))) ℂ) :
      ∃ B : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ,
        Ehat A = Matrix.blockDiagonal' fun k =>
          (1 : Matrix (Fin (m k)) (Fin (m k)) ℂ) ⊗ₖ B k := by
    obtain ⟨B, hB⟩ := (hBlock (E (Φ.symm A))).mp (hRange (Φ.symm A))
    refine ⟨B, ?_⟩
    change Φ (E (Φ.symm A)) = _
    rw [Matrix.unitaryReindexLinearEquiv_apply, hB]
    simpa only [Matrix.symm_reindexLinearEquiv, Matrix.coe_reindexLinearEquiv] using
      (Matrix.reindexLinearEquiv ℂ ℂ e e).symm_apply_apply
        (Matrix.blockDiagonal' fun k =>
          (1 : Matrix (Fin (m k)) (Fin (m k)) ℂ) ⊗ₖ B k)
  have hFixHat (B : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ) :
      Ehat (Matrix.blockDiagonal' fun k =>
          (1 : Matrix (Fin (m k)) (Fin (m k)) ℂ) ⊗ₖ B k) =
        Matrix.blockDiagonal' fun k =>
          (1 : Matrix (Fin (m k)) (Fin (m k)) ℂ) ⊗ₖ B k := by
    let X := Matrix.blockDiagonal' fun k =>
      (1 : Matrix (Fin (m k)) (Fin (m k)) ℂ) ⊗ₖ B k
    have hXmem : Φ.symm X ∈ S := by
      apply (hBlock (Φ.symm X)).mpr
      refine ⟨B, ?_⟩
      rw [show star U * Φ.symm X * U = Matrix.reindex e e X by
        rw [Matrix.unitaryReindexLinearEquiv_symm_apply]
        have hUstarU : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
        calc
          star U * (U * Matrix.reindex e e X * star U) * U =
              (star U * U) * Matrix.reindex e e X * (star U * U) := by
            simp only [Matrix.mul_assoc]
          _ = Matrix.reindex e e X := by rw [hUstarU, Matrix.one_mul, Matrix.mul_one]]
    change Φ (E (Φ.symm X)) = X
    rw [hFix _ hXmem, Φ.apply_symm_apply]
  obtain ⟨ρ, hρpos, hρtrace, hEhatFormula⟩ :=
    Matrix.exists_density_of_positive_retraction_onto_direct_sum_right_factors
      Ehat hEhat hRangeHat hFixHat
  refine ⟨K, d, m, e, U, ρ, hU, hd, hm, hBlock, hρpos, hρtrace, fun A ↦ ?_⟩
  have hFormula :
      Φ (E A) = Matrix.blockDiagonal' fun k =>
        (1 : Matrix (Fin (m k)) (Fin (m k)) ℂ) ⊗ₖ
          Matrix.partialTraceLeft
            (((ρ k) ⊗ₖ (1 : Matrix (Fin (d k)) (Fin (d k)) ℂ)) *
              Matrix.directSumBlockCompression (m := m) (d := d) k (Φ A)) := by
    simpa only [Ehat, LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply] using
      hEhatFormula (Φ A)
  have hFormulaBack := congrArg Φ.symm hFormula
  calc
    E A = Φ.symm (Φ (E A)) := (Φ.symm_apply_apply (E A)).symm
    _ = Φ.symm (Matrix.blockDiagonal' fun k =>
          (1 : Matrix (Fin (m k)) (Fin (m k)) ℂ) ⊗ₖ
            Matrix.partialTraceLeft
              (((ρ k) ⊗ₖ (1 : Matrix (Fin (d k)) (Fin (d k)) ℂ)) *
                Matrix.directSumBlockCompression (m := m) (d := d) k (Φ A))) := hFormulaBack
    _ = _ := by
      rw [show Φ.symm = (Matrix.unitaryReindexLinearEquiv e U hU).symm from rfl]
      simp only [Matrix.unitaryReindexLinearEquiv_symm_apply,
        Φ, Matrix.unitaryReindexLinearEquiv_apply]

end StarSubalgebra
