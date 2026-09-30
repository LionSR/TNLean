/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.Symmetry.LiteralRefinementForward
import TNLean.MPS.Periodic.BlockScalarUnitary

/-!
# Physical symmetry of a literal periodic block tensor

The finite-order copy phases of the equal-case theorem give the diagonal
unitary in the symmetry corollary. Each phase has order dividing its block's
period, so it leaves every periodic vector unchanged.

Source: arXiv:1708.00029, Section 4.2, lines 834--845.
-/

open scoped Matrix BigOperators Matrix.Norms.Operator

namespace MPSTensor

/-- Phases whose orders divide the block periods preserve the vectors of a
weighted direct sum, including the empty word.
Source: arXiv:1708.00029, Theorem 3.8 and Section 4.2, lines 643--690 and 834--845. -/
theorem sameMPV₂_toTensorFromBlocks_of_periodic_phases
    {d r : ℕ} {dim : Fin r → ℕ}
    (A : (j : Fin r) → MPSTensor d (dim j)) (μ c : Fin r → ℂ)
    (period : Fin r → ℕ) (hPer : ∀ j, IsPeriodic (period j) (A j))
    (hc : ∀ j, c j ^ period j = 1) :
    SameMPV₂ (toTensorFromBlocks μ A)
      (toTensorFromBlocks (fun j => c j * μ j) A) := by
  classical
  intro N σ
  rw [mpv_toTensorFromBlocks_eq_sum, mpv_toTensorFromBlocks_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hdiv : period j ∣ N
  · obtain ⟨k, rfl⟩ := hdiv
    have hcpow : c j ^ (period j * k) = 1 := by
      rw [pow_mul, hc, one_pow]
    rw [mul_pow, hcpow, one_mul]
  · rw [pgvwc07_stateVector_eq_zero_of_not_dvd (A j) (hPer j) hdiv σ]
    simp

/-- The physical rotation of a symmetric literal periodic direct sum equals
a unitary bond conjugation multiplied by a block-scalar phase. Those phases
have orders dividing the block periods. Source: arXiv:1708.00029, Section 4.2,
lines 834--845, equation `eq:symm`. -/
theorem exists_blockPhase_unitary_of_periodic_physical_symmetry
    {d r : ℕ} {dim : Fin r → ℕ}
    (A : (j : Fin r) → MPSTensor d (dim j))
    (μ : Fin r → ℂ) (hμ : ∀ j, μ j ≠ 0)
    (period : Fin r → ℕ) (hPer : ∀ j, IsPeriodic (period j) (A j))
    (u : Matrix (Fin d) (Fin d) ℂ) (hu : uᴴ * u = 1)
    (hSym : SameMPV₂Pos (toTensorFromBlocks μ A)
      (fun i => ∑ j, u i j • toTensorFromBlocks μ A j)) :
    ∃ (z : Fin r → ℂ) (U : Matrix (Fin (∑ j, dim j)) (Fin (∑ j, dim j)) ℂ),
      (∀ j, z j ^ period j = 1) ∧ U * Uᴴ = 1 ∧ Uᴴ * U = 1 ∧
      (∀ i, blockScalarMatrix dim z * toTensorFromBlocks μ A i =
        toTensorFromBlocks μ A i * blockScalarMatrix dim z) ∧
      SameMPV₂ (toTensorFromBlocks μ A)
        (fun i => blockScalarMatrix dim z * toTensorFromBlocks μ A i) ∧
      ∀ i, (∑ j, u i j • toTensorFromBlocks μ A j) =
        blockScalarMatrix dim z * U * toTensorFromBlocks μ A i * Uᴴ := by
  classical
  let C := fun k i => ∑ j, u i j • A k j
  have hLiteral : (fun i => ∑ j, u i j • toTensorFromBlocks μ A j) =
      toTensorFromBlocks μ C := funext (toTensorFromBlocks_sum_smul μ A u)
  have hSame : SameMPV₂Pos (toTensorFromBlocks μ C) (toTensorFromBlocks μ A) := by
    rw [← hLiteral]
    exact hSym.symm
  obtain ⟨c, U, hc, hUU, hU, hMatch⟩ :=
    exists_unitary_matching_of_periodic_block_families_sameMPV₂Pos
      C μ hμ A μ hμ period period
      (fun j => isPeriodic_kraus_isometry (A j) u hu (hPer j)) hPer hSame
  let z := fun j => (c j)⁻¹
  have hz : ∀ j, z j ^ period j = 1 := by
    intro j
    simp only [z, inv_pow, hc, inv_one]
  have hcne : ∀ j, c j ≠ 0 := fun j =>
    Complex.ne_zero_of_norm_eq_one
      (Complex.norm_eq_one_of_pow_eq_one (hc j) (hPer j).period_pos.ne')
  refine ⟨z, U, hz, hUU, hU, ?_, ?_, ?_⟩
  · intro i
    rw [blockScalarMatrix_mul_toTensorFromBlocks, toTensorFromBlocks_mul_blockScalarMatrix]
  · have h := sameMPV₂_toTensorFromBlocks_of_periodic_phases A μ z period hPer hz
    have hletters : (fun i => blockScalarMatrix dim z * toTensorFromBlocks μ A i) =
        toTensorFromBlocks (fun j => z j * μ j) A :=
      funext (blockScalarMatrix_mul_toTensorFromBlocks z μ A)
    rw [hletters]
    exact h
  · intro i
    change (fun i => ∑ j, u i j • toTensorFromBlocks μ A j) i = _
    rw [hLiteral]
    have h := congrArg (fun M => blockScalarMatrix dim z * M) (hMatch i)
    rw [blockScalarMatrix_mul_toTensorFromBlocks] at h
    have hweights : (fun j => z j * (c j * μ j)) = μ := by
      funext j
      simp only [z, ← mul_assoc, inv_mul_cancel₀ (hcne j), one_mul]
    rw [hweights] at h
    simpa only [Matrix.mul_assoc] using h

/-- The symmetry corollary for the literal irreducible form II: a physical
unitary preserving the vector family is implemented by a diagonal unitary
commuting with the tensor and a unitary bond conjugation. The diagonal
unitary itself preserves the vector family. Periods are derived from the
irreducible blocks rather than supplied as additional hypotheses.
Source: arXiv:1708.00029, Section 4.2, lines 834--845, equation `eq:symm`;
irreducible form II at lines 313--332. -/
theorem exists_diagonal_unitary_of_irreducibleForm_physical_symmetry
    {d r : ℕ} {dim : Fin r → ℕ}
    (A : (j : Fin r) → MPSTensor d (dim j))
    (μ : Fin r → ℂ) (hμ : ∀ j, μ j ≠ 0)
    (hIrr : ∀ j, Kraus.IsIrreducibleFamily (A j))
    (hRad : ∀ j, spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin (dim j)) (Fin (dim j)) ℂ))
        (Kraus.transferMap (A j))) = 1)
    (hTP : ∀ j, IsLeftCanonical (A j))
    (u : Matrix (Fin d) (Fin d) ℂ) (hu : uᴴ * u = 1)
    (hSym : SameMPV₂Pos (toTensorFromBlocks μ A)
      (fun i => ∑ j, u i j • toTensorFromBlocks μ A j)) :
    ∃ Z U : Matrix (Fin (∑ j, dim j)) (Fin (∑ j, dim j)) ℂ,
      (∃ z, Z = Matrix.diagonal z) ∧ Matrix.IsUnitaryBetween Z ∧
      Matrix.IsUnitaryBetween U ∧
      (∀ i, Z * toTensorFromBlocks μ A i = toTensorFromBlocks μ A i * Z) ∧
      SameMPV₂ (toTensorFromBlocks μ A) (fun i => Z * toTensorFromBlocks μ A i) ∧
      ∀ i, (∑ j, u i j • toTensorFromBlocks μ A j) =
        Z * U * toTensorFromBlocks μ A i * Uᴴ := by
  choose period hPer using fun j =>
    exists_isSpectrallyPeriodic_of_irreducible_of_spectralRadius_one (hIrr j) (hRad j)
  have hPeriodic : ∀ j, IsPeriodic (period j) (A j) := fun j =>
    ⟨hIrr j, hTP j, (hPer j).period_pos, (hPer j).peripheral_eq⟩
  obtain ⟨z, U, hz, hUU, hU, hComm, hSame, hEq⟩ :=
    exists_blockPhase_unitary_of_periodic_physical_symmetry A μ hμ
      period hPeriodic u hu hSym
  refine ⟨blockScalarMatrix dim z, U,
    ⟨_, blockScalarMatrix_eq_diagonal z⟩, ?_, ⟨hU, hUU⟩, hComm, hSame, hEq⟩
  exact blockScalarMatrix_isUnitaryBetween z (fun j =>
    Complex.norm_eq_one_of_pow_eq_one (hz j) (hPer j).period_pos.ne')

end MPSTensor
