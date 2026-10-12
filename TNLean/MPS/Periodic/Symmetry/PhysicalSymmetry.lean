/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.PeriodExistence
import TNLean.MPS.Periodic.PhaseClassGrouping
import TNLean.MPS.Periodic.Symmetry.Theorem41Forward

/-!
# Physical symmetries of a block tensor in irreducible form

Let `A = ⊕_j μ_j A_j` be a weighted direct sum of periodic blocks, and let `u`
be a local unitary with `|V_N(A)⟩ = u^{⊗N} |V_N(A)⟩` for all `N`. The symmetry
corollary of arXiv:1708.00029 (lines 834--845) asserts a diagonal unitary `Z`
commuting with every `A^i` and generating the same vectors as `A`, and a
unitary `U`, such that
`∑_i u^{i',i} A^i = Z U A^{i'} U†` for every `i'` (equation `eq:symm`).

The proof applies the equal-case fundamental theorem (`thm:bdequal`,
lines 643--693) to `A` and its physical rotation. The blocks of both tensors
are first grouped into bases of periodic tensors without repetition; the
multiplicity gauge of the theorem is then transported back to the original
blocks, where it acts on each block by a root of unity whose order divides the
period of that block.

Repeated blocks are allowed: the corollary is stated for the block tensor
itself, not for a chosen basis of periodic tensors.

## Main declarations

* `MPSTensor.exists_unitary_matching_of_periodic_block_families`: two weighted
  periodic block sums with the same vectors agree up to a unitary similarity
  after multiplying the weights of the first by roots of unity.
* `MPSTensor.exists_diagonal_unitary_of_irreducibleForm_physical_symmetry`: the
  symmetry corollary, equation `eq:symm`.

## References

* De las Cuevas, Cirac, Schuch, Pérez-García, *Irreducible forms of Matrix
  Product States: Theory and Applications*, arXiv:1708.00029, irreducible
  form II, lines 313--332; `thm:bdequal`, lines 643--693; Section 4.2,
  lines 828--845.
-/

open scoped Matrix BigOperators Matrix.Norms.Operator

namespace MPSTensor

/-- Physical mixing commutes with a weighted direct sum, letter by letter.
Source: arXiv:1708.00029, Section 4.2, lines 834--845. -/
theorem toTensorFromBlocks_sum_smul {d m r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (B : (k : Fin r) → MPSTensor d (dim k))
    (W : Matrix (Fin m) (Fin d) ℂ) (τ : Fin m) :
    ∑ σ, W τ σ • toTensorFromBlocks μ B σ =
      toTensorFromBlocks μ (fun k τ ↦ ∑ σ, W τ σ • B k σ) τ := by
  classical
  ext x y
  simp only [toTensorFromBlocks, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.blockDiagonal'_apply]
  split_ifs with h
  · rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun σ _ ↦ smul_comm _ _ _
  · simp

/-- A block-scalar matrix is diagonal in the flattened bond coordinates.
Source: arXiv:1708.00029, `thm:bdequal`, line 653. -/
theorem blockScalarMatrix_eq_diagonal {r : ℕ} {dim : Fin r → ℕ} (z : Fin r → ℂ) :
    blockScalarMatrix dim z =
      Matrix.diagonal (fun x ↦ z (finSigmaFinEquiv.symm x).1) := by
  classical
  have hblock :
      (fun k : Fin r ↦ z k • (1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) =
        fun k ↦ Matrix.diagonal (fun _ : Fin (dim k) ↦ z k) := by
    funext k
    exact Matrix.smul_one_eq_diagonal (z k)
  rw [blockScalarMatrix, hblock, Matrix.blockDiagonal'_diagonal, Matrix.reindex_apply]
  exact Matrix.submatrix_diagonal _ _ (Equiv.injective _)

/-- Unit-modulus block scalars define a unitary on the flattened bond space.
Source: arXiv:1708.00029, Section 4.2, lines 834--845. -/
theorem blockScalarMatrix_mem_unitaryGroup {r : ℕ} {dim : Fin r → ℕ}
    (z : Fin r → ℂ) (hz : ∀ k, ‖z k‖ = 1) :
    blockScalarMatrix dim z ∈ Matrix.unitaryGroup (Fin (∑ k, dim k)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, blockScalarMatrix_eq_diagonal, Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  refine Matrix.diagonal_eq_one.mpr (funext fun x ↦ ?_)
  rw [Pi.star_apply, Complex.star_def, Complex.mul_conj', hz]
  norm_num

/-- Two weighted sums of left-canonical periodic blocks with the same vectors at
every positive length agree up to a unitary similarity, after multiplying each
weight of the first sum by a root of unity whose order divides the period of its
block. Repeated blocks are allowed in both sums.

The roots of unity are the multiplicity gauge `Z` of the equal-case
fundamental theorem, transported from a basis of periodic tensors back to the
original blocks. Source: arXiv:1708.00029, `thm:bdequal`, lines 643--693, with
the grouping `eq:bdnr`, lines 286--305, and the unitary gauge of line 625. -/
theorem exists_unitary_matching_of_periodic_block_families
    {d r s : ℕ} {dim : Fin r → ℕ} {dim' : Fin s → ℕ}
    (A : (j : Fin r) → MPSTensor d (dim j)) (μ : Fin r → ℂ) (hμ : ∀ j, μ j ≠ 0)
    (B : (k : Fin s) → MPSTensor d (dim' k)) (ν : Fin s → ℂ) (hν : ∀ k, ν k ≠ 0)
    (periodA : Fin r → ℕ) (periodB : Fin s → ℕ)
    (hPerA : ∀ j, IsPeriodic (periodA j) (A j))
    (hPerB : ∀ k, IsPeriodic (periodB k) (B k))
    (hSame : SameMPV₂Pos (toTensorFromBlocks μ A) (toTensorFromBlocks ν B)) :
    ∃ (c : Fin r → ℂ) (W : Matrix (Fin (∑ j, dim j)) (Fin (∑ k, dim' k)) ℂ),
      (∀ j, c j ^ periodA j = 1) ∧ W * Wᴴ = 1 ∧ Wᴴ * W = 1 ∧
      ∀ i, toTensorFromBlocks (fun j ↦ c j * μ j) A i =
        W * toTensorFromBlocks ν B i * Wᴴ := by
  classical
  let cA := mpvPhaseClassData A
  let cB := mpvPhaseClassData B
  obtain ⟨ξA, hξA, _, hPerP, hNonRepP, _, hSameP, YA, hYA, hYA', _, hAz⟩ :=
    cA.exists_unitary_sectorDecomposition μ hμ periodA hPerA
  obtain ⟨ξB, hξB, _, hPerQ, hNonRepQ, _, hSameQ, YB, hYB, hYB', hBQ, _⟩ :=
    cB.exists_unitary_sectorDecomposition ν hν periodB hPerB
  let P := cA.toSectorDecomposition μ ξA hμ hξA
  let Q := cB.toSectorDecomposition ν ξB hν hξB
  have hPQ : SameMPV₂Pos P.toTensor Q.toTensor :=
    hSameP.symm.trans (hSame.trans hSameQ)
  obtain ⟨_, _, z, _, _, _, _, hzpow, _, Y, Y', hYY', hY'Y, hY', _, _, hZY, _⟩ :=
    fundamentalTheorem_periodic_equalCase_sectorDecomposition P Q
      (fun j ↦ periodA (cA.repr j)) (fun k ↦ periodB (cB.repr k))
      hPerP hPerQ hNonRepP hNonRepQ hPQ
  subst hY'
  let c : Fin r → ℂ := fun k ↦ z (cA.enumEquiv.symm k).1 (cA.enumEquiv.symm k).2
  refine ⟨c, YA * Y * YBᴴ, ?_, ?_, ?_, ?_⟩
  · intro k
    obtain ⟨⟨j, q⟩, rfl⟩ := cA.enumEquiv.surjective k
    have hper : periodA (cA.enumEquiv ⟨j, q⟩) = periodA (cA.repr j) :=
      (cA.periodic_unitary_match periodA hPerA j q).1
    have hentry {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) (n : ℕ)
        (h : Matrix.diagonal v ^ n = 1) (q : ι) : v q ^ n = 1 := by
      have h' := congrFun₂ h q q
      rwa [Matrix.diagonal_pow, Matrix.diagonal_apply_eq, Matrix.one_apply_eq,
        Pi.pow_apply] at h'
    have hz : z j q ^ periodA (cA.repr j) = 1 := hentry (z j) _ (hzpow j) q
    rw [hper]
    exact (congrArg (fun x ↦ z x.1 x.2 ^ periodA (cA.repr j))
      (cA.enumEquiv.symm_apply_apply ⟨j, q⟩)).trans hz
  · simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc YBᴴ, hYB', Matrix.one_mul, ← Matrix.mul_assoc Y, hYY',
      Matrix.one_mul, hYA]
  · simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc YAᴴ, hYA', Matrix.one_mul, ← Matrix.mul_assoc Yᴴ, hY'Y,
      Matrix.one_mul, hYB]
  · intro i
    have hQ : Q.toTensor i = YBᴴ * toTensorFromBlocks ν B i * YB := by
      rw [hBQ i]
      simp only [← Matrix.mul_assoc, hYB', Matrix.one_mul]
      rw [Matrix.mul_assoc, hYB', Matrix.mul_one]
    rw [hAz z i, hZY i, hQ]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- Phases whose orders divide the block periods leave the vectors of a weighted
direct sum of periodic blocks unchanged, including the empty word.
Source: arXiv:1708.00029, `thm:bdequal`, lines 655 and 661--663. -/
theorem sameMPV₂_toTensorFromBlocks_of_periodic_phases
    {d r : ℕ} {dim : Fin r → ℕ}
    (A : (j : Fin r) → MPSTensor d (dim j)) (μ c : Fin r → ℂ)
    (period : Fin r → ℕ) (hPer : ∀ j, IsPeriodic (period j) (A j))
    (hc : ∀ j, c j ^ period j = 1) :
    SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks (fun j ↦ c j * μ j) A) := by
  classical
  intro N σ
  rw [mpv_toTensorFromBlocks_eq_sum, mpv_toTensorFromBlocks_eq_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  by_cases hdiv : period j ∣ N
  · obtain ⟨k, rfl⟩ := hdiv
    rw [mul_pow, pow_mul (c j), hc, one_pow, one_mul]
  · rw [pgvwc07_stateVector_eq_zero_of_not_dvd (A j) (hPer j) hdiv σ]
    simp

/-- **Physical symmetries of a periodic block tensor.** If a local unitary `u`
preserves the vectors of `A = ⊕_j μ_j A_j` at every positive length, then there
are roots of unity `z_j`, of order dividing the period of `A_j`, and a unitary
`U` with `∑_i u^{i',i} A^i = Z U A^{i'} U†` for `Z = ⊕_j z_j 1`. The matrix `Z`
commutes with every `A^i` and leaves the vectors of `A` unchanged.
Source: arXiv:1708.00029, Section 4.2, lines 834--845, equation `eq:symm`. -/
theorem exists_blockScalar_unitary_of_periodic_physical_symmetry
    {d r : ℕ} {dim : Fin r → ℕ}
    (A : (j : Fin r) → MPSTensor d (dim j)) (μ : Fin r → ℂ) (hμ : ∀ j, μ j ≠ 0)
    (period : Fin r → ℕ) (hPer : ∀ j, IsPeriodic (period j) (A j))
    (u : Matrix (Fin d) (Fin d) ℂ) (hu : u ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSym : SameMPV₂Pos (toTensorFromBlocks μ A)
      (fun i ↦ ∑ j, u i j • toTensorFromBlocks μ A j)) :
    ∃ (z : Fin r → ℂ) (U : Matrix (Fin (∑ j, dim j)) (Fin (∑ j, dim j)) ℂ),
      (∀ j, z j ^ period j = 1) ∧ U ∈ Matrix.unitaryGroup (Fin (∑ j, dim j)) ℂ ∧
      (∀ i, blockScalarMatrix dim z * toTensorFromBlocks μ A i =
        toTensorFromBlocks μ A i * blockScalarMatrix dim z) ∧
      SameMPV₂ (toTensorFromBlocks μ A)
        (fun i ↦ blockScalarMatrix dim z * toTensorFromBlocks μ A i) ∧
      ∀ i, ∑ j, u i j • toTensorFromBlocks μ A j =
        blockScalarMatrix dim z * U * toTensorFromBlocks μ A i * Uᴴ := by
  classical
  let C : (k : Fin r) → MPSTensor d (dim k) := fun k i ↦ ∑ j, u i j • A k j
  have hLetters (i : Fin d) : ∑ j, u i j • toTensorFromBlocks μ A j = toTensorFromBlocks μ C i :=
    toTensorFromBlocks_sum_smul μ A u i
  have hIso : uᴴ * u = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hu
  have hSame : SameMPV₂Pos (toTensorFromBlocks μ C) (toTensorFromBlocks μ A) := by
    have h := hSym.symm
    simp only [hLetters] at h
    exact h
  obtain ⟨c, U, hc, hUU, hU, hMatch⟩ :=
    exists_unitary_matching_of_periodic_block_families C μ hμ A μ hμ period period
      (fun j ↦ isPeriodic_kraus_isometry (A j) u hIso (hPer j)) hPer hSame
  have hcne (j : Fin r) : c j ≠ 0 := by
    rintro h
    have := hc j
    rw [h, zero_pow (hPer j).period_pos.ne'] at this
    exact zero_ne_one this
  let z : Fin r → ℂ := fun j ↦ (c j)⁻¹
  have hz (j : Fin r) : z j ^ period j = 1 := by
    simp only [z, inv_pow, hc, inv_one]
  refine ⟨z, U, hz, Matrix.mem_unitaryGroup_iff.mpr ?_, fun i ↦ ?_, ?_, fun i ↦ ?_⟩
  · simpa only [Matrix.star_eq_conjTranspose] using hUU
  · rw [blockScalarMatrix_mul_toTensorFromBlocks, toTensorFromBlocks_mul_blockScalarMatrix]
  · rw [show (fun i ↦ blockScalarMatrix dim z * toTensorFromBlocks μ A i) =
        toTensorFromBlocks (fun j ↦ z j * μ j) A from
      funext (blockScalarMatrix_mul_toTensorFromBlocks z μ A)]
    exact sameMPV₂_toTensorFromBlocks_of_periodic_phases A μ z period hPer hz
  · have h := congrArg (blockScalarMatrix dim z * ·) (hMatch i)
    simp only [blockScalarMatrix_mul_toTensorFromBlocks] at h
    have hw : (fun j ↦ z j * (c j * μ j)) = μ := by
      funext j
      simp only [z, ← mul_assoc, inv_mul_cancel₀ (hcne j), one_mul]
    rw [hw] at h
    rw [hLetters, h]
    simp only [Matrix.mul_assoc]

/-- **Corollary (symmetries) of arXiv:1708.00029.** Let `A = ⊕_j μ_j A_j` be
a weighted direct sum of irreducible blocks with spectral radius one and
trace-preserving transfer maps, as in irreducible form II. If a local unitary
`u` satisfies `|V_N(A)⟩ = u^{⊗N} |V_N(A)⟩` for every positive `N`, then there
are a diagonal unitary `Z` with `[A^i, Z] = 0` and `V(A) = V(ZA)`, and a unitary
`U` such that `∑_i u^{i',i} A^i = Z U A^{i'} U†` for every `i'`.

The periods of the blocks are derived, not assumed, and repeated blocks are
allowed. The diagonality of the fixed points in irreducible form II is not used.
Source: arXiv:1708.00029, Section 4.2, lines 834--845, equation `eq:symm`;
irreducible form II, lines 313--332. -/
theorem exists_diagonal_unitary_of_irreducibleForm_physical_symmetry
    {d r : ℕ} {dim : Fin r → ℕ}
    (A : (j : Fin r) → MPSTensor d (dim j)) (μ : Fin r → ℂ) (hμ : ∀ j, μ j ≠ 0)
    (hIrr : ∀ j, Kraus.IsIrreducibleFamily (A j))
    (hRad : ∀ j, spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin (dim j)) (Fin (dim j)) ℂ))
        (Kraus.transferMap (A j))) = 1)
    (hTP : ∀ j, IsLeftCanonical (A j))
    (u : Matrix (Fin d) (Fin d) ℂ) (hu : u ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hSym : SameMPV₂Pos (toTensorFromBlocks μ A)
      (fun i ↦ ∑ j, u i j • toTensorFromBlocks μ A j)) :
    ∃ (z : Fin (∑ j, dim j) → ℂ) (U : Matrix (Fin (∑ j, dim j)) (Fin (∑ j, dim j)) ℂ),
      Matrix.diagonal z ∈ Matrix.unitaryGroup (Fin (∑ j, dim j)) ℂ ∧
      U ∈ Matrix.unitaryGroup (Fin (∑ j, dim j)) ℂ ∧
      (∀ i, Matrix.diagonal z * toTensorFromBlocks μ A i =
        toTensorFromBlocks μ A i * Matrix.diagonal z) ∧
      SameMPV₂ (toTensorFromBlocks μ A)
        (fun i ↦ Matrix.diagonal z * toTensorFromBlocks μ A i) ∧
      ∀ i, ∑ j, u i j • toTensorFromBlocks μ A j =
        Matrix.diagonal z * U * toTensorFromBlocks μ A i * Uᴴ := by
  choose period hPer using fun j ↦
    exists_isSpectrallyPeriodic_of_irreducible_of_spectralRadius_one (hIrr j) (hRad j)
  have hPeriodic (j : Fin r) : IsPeriodic (period j) (A j) :=
    ⟨hIrr j, hTP j, (hPer j).period_pos, (hPer j).peripheral_eq⟩
  obtain ⟨z, U, hz, hU, hComm, hSame, hEq⟩ :=
    exists_blockScalar_unitary_of_periodic_physical_symmetry A μ hμ period hPeriodic u hu hSym
  have hZ := blockScalarMatrix_eq_diagonal (dim := dim) z
  refine ⟨_, U, hZ ▸ blockScalarMatrix_mem_unitaryGroup z fun j ↦
    Complex.norm_eq_one_of_pow_eq_one (hz j) (hPer j).period_pos.ne', hU, ?_, ?_, ?_⟩
  · simpa only [hZ] using hComm
  · simpa only [hZ] using hSame
  · simpa only [hZ] using hEq

end MPSTensor
