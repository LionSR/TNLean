/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.UncleBoundaryProduct
import QICLean.Algebra.ScalarCommutant
import QICLean.Algebra.TraceReindex

/-!
# Boundary trace coefficients in the uncle closure argument

The cyclic pairing of two arbitrary single-wall coefficient products forces
their two boundary matrices to agree. A boundary matrix whose pairing is
cyclic has zero off-diagonal blocks and scalar diagonal blocks. Thus it
retains only the two periodic sector traces.

This is the coefficient-uniqueness step in arXiv:1210.6613, Appendix
"intersection-closure", the closure proof at source lines 1943–1984.
Applying this classification to the actual shifted open-chain boundary
spaces gives the source's periodic closure.
-/

noncomputable section

open scoped Matrix

namespace MPSTensor

variable {a b : ℕ}

/-- The ordinary trace pairing reads the four uncle boundary blocks in the
opposite order. Source: arXiv:1210.6613, Appendix closure proof, lines 1943–1984. -/
theorem trace_uncleBlockMatrix_mul
    (A C : Matrix (Fin a) (Fin a) ℂ) (R S : Matrix (Fin a) (Fin b) ℂ)
    (L T : Matrix (Fin b) (Fin a) ℂ) (B E : Matrix (Fin b) (Fin b) ℂ) :
    Matrix.trace (uncleBlockMatrix A R L B * uncleBlockMatrix C S T E) =
      Matrix.trace (A * C + R * T) + Matrix.trace (L * S + B * E) := by
  change Matrix.trace
    (Matrix.reindexAlgEquiv ℂ ℂ finSumFinEquiv (Matrix.fromBlocks A R L B) *
      Matrix.reindexAlgEquiv ℂ ℂ finSumFinEquiv (Matrix.fromBlocks C S T E)) = _
  rw [← map_mul, Matrix.fromBlocks_multiply]
  change Matrix.trace (Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (A * C + R * T) (A * S + R * E)
      (L * C + B * T) (L * S + B * E))) = _
  rw [Matrix.trace_reindex]
  simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_sum_type,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂]

/-- The two boundary matrices in a cyclic coefficient pairing coincide.
Source: arXiv:1210.6613, Appendix closure proof, lines 1943–1984. -/
theorem eq_of_uncleBoundary_cyclic_pairing
    (X Y : Matrix (Fin (a + b)) (Fin (a + b)) ℂ)
    (h : ∀ M N : Matrix (Fin (a + b)) (Fin (a + b)) ℂ,
      Matrix.trace (uncleBoundaryMul M N * X) =
        Matrix.trace (uncleBoundaryMul N M * Y)) : X = Y := by
  apply Matrix.ext_iff_trace_mul_left.mpr
  intro M
  simpa only [one_uncleBoundaryMul, uncleBoundaryMul_one] using h 1 M

private theorem scalar_of_cyclic_trace {k : ℕ} (C : Matrix (Fin k) (Fin k) ℂ)
    (h : ∀ P Q : Matrix (Fin k) (Fin k) ℂ,
      Matrix.trace (P * Q * C) = Matrix.trace (Q * P * C)) :
    ∃ c : ℂ, C = Matrix.scalar (Fin k) c := by
  apply Matrix.isScalar_of_commute_span_eq_top C (S := Set.univ) (by simp)
  intro P _
  apply Matrix.ext_iff_trace_mul_left.mpr
  intro Q
  calc
    Matrix.trace (Q * (C * P)) = Matrix.trace (P * Q * C) := by
      simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle Q C P
    _ = Matrix.trace (Q * P * C) := h P Q
    _ = Matrix.trace (Q * (P * C)) := by rw [Matrix.mul_assoc]

/-- A cyclic trace pairing for the actual single-wall coefficient product
leaves only scalar diagonal sector boundaries. Source: arXiv:1210.6613,
Appendix closure proof, lines 1943–1984. This is a derived coefficient lemma,
not a periodic-closure statement with closure supplied as a hypothesis. -/
theorem exists_scalar_blocks_of_uncleBoundary_trace_cyclic
    (X : Matrix (Fin (a + b)) (Fin (a + b)) ℂ)
    (h : ∀ M N : Matrix (Fin (a + b)) (Fin (a + b)) ℂ,
      Matrix.trace (uncleBoundaryMul M N * X) =
        Matrix.trace (uncleBoundaryMul N M * X)) :
    ∃ α β : ℂ, X = uncleBlockMatrix (Matrix.scalar (Fin a) α) 0 0
      (Matrix.scalar (Fin b) β) := by
  obtain ⟨C, S, T, E, rfl⟩ := exists_eq_uncleBlockMatrix X
  have hT : T = 0 := by
    apply Matrix.ext_iff_trace_mul_left.mpr
    intro R
    have hc := h
      (uncleBlockMatrix (1 : Matrix (Fin a) (Fin a) ℂ) 0 0
        (0 : Matrix (Fin b) (Fin b) ℂ))
      (uncleBlockMatrix (0 : Matrix (Fin a) (Fin a) ℂ) R 0
        (0 : Matrix (Fin b) (Fin b) ℂ))
    simpa [uncleBoundaryMul_block, trace_uncleBlockMatrix_mul] using hc
  have hS : S = 0 := by
    apply Matrix.ext_iff_trace_mul_left.mpr
    intro L
    have hc := h
      (uncleBlockMatrix (0 : Matrix (Fin a) (Fin a) ℂ) 0 0
        (1 : Matrix (Fin b) (Fin b) ℂ))
      (uncleBlockMatrix (0 : Matrix (Fin a) (Fin a) ℂ) 0 L
        (0 : Matrix (Fin b) (Fin b) ℂ))
    simpa [uncleBoundaryMul_block, trace_uncleBlockMatrix_mul] using hc
  obtain ⟨α, hC⟩ := scalar_of_cyclic_trace C fun P Q ↦ by
    have hc := h
      (uncleBlockMatrix P 0 0 (0 : Matrix (Fin b) (Fin b) ℂ))
      (uncleBlockMatrix Q 0 0 (0 : Matrix (Fin b) (Fin b) ℂ))
    simpa [uncleBoundaryMul_block, trace_uncleBlockMatrix_mul] using hc
  obtain ⟨β, hE⟩ := scalar_of_cyclic_trace E fun P Q ↦ by
    have hc := h
      (uncleBlockMatrix (0 : Matrix (Fin a) (Fin a) ℂ) 0 0 P)
      (uncleBlockMatrix (0 : Matrix (Fin a) (Fin a) ℂ) 0 0 Q)
    simpa [uncleBoundaryMul_block, trace_uncleBlockMatrix_mul] using hc
  exact ⟨α, β, by rw [hC, hS, hT, hE]⟩

end MPSTensor
