/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Circuit.Party.Compression.PartialExpansion.Evaluation
import QICLean.Algebra.Matrix.MatrixDensitySum
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Density coefficients of the chronological partial expansion

The exact chronological operator identity gives an exact ket–bra expansion in
the configuration coordinates of the grouped memories. Its scalar weights are the
original ket coefficients times the conjugates of the bra coefficients. The
identity holds for arbitrary input matrices.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 342–381.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

noncomputable section
open scoped ComplexConjugate Matrix
open Matrix ManyBody

namespace QuantumCircuit.Party.SourceCircuit

variable {P : Type} [Fintype P] [DecidableEq P] {X Y : P → Type} [∀ p, Fintype (X p)]
  [∀ p, DecidableEq (X p)]

/-- The density calculation has independent partial choices on its ket and bra
sides, weighted by the original coefficient and the conjugate bra coefficient.
Untouched gates remain aggregate operators in every summand. No positivity or
normalization assumption on the input matrix is required.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–381. -/
theorem density_eval_eq_sum_partialWord (A : P → Bool) (w : SourceCircuit X Y)
    (ρ : Matrix (Config (blockSystem (affectedOwner A) X))
      (Config (blockSystem (affectedOwner A) X)) ℂ) :
    let M := reindex (blockConfigEquiv (affectedOwner A) Y).symm
      (blockConfigEquiv (affectedOwner A) X).symm w.op
    let K := fun ξ ↦ Word.op (partialWord A w ξ)
    M * ρ * Mᴴ = ∑ ξ, ∑ ζ,
      (coefficient A w ξ * conj (coefficient A w ζ)) • (K ξ * ρ * (K ζ)ᴴ) := by
  dsimp only
  rw [← expandedEval_eq_reindex_op A w, expandedEval]
  exact Matrix.sum_smul_mul_mul_conjTranspose _ _ _ _ _

end QuantumCircuit.Party.SourceCircuit
