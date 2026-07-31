/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FrobeniusHilbert
import TNLean.Channel.KrausCPTP

import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Weighted Hilbert--Schmidt channel maps

This file begins the finite-dimensional Hilbert-space infrastructure needed
for the direct `p = 2` specialization of Beigi's weighted Schatten-norm
contraction.  In particular, it identifies the trace-pairing adjoint of a
rectangular Kraus map with its Hilbert-space adjoint after Frobenius
vectorization.

## Main result

* `Matrix.adjoint_frobeniusEuclideanMap_eq`: the Hilbert-space adjoint of a
  Kraus map is its trace-pairing adjoint.

## References

* S. Beigi, *Sandwiched Rényi Divergence Satisfies Data Processing
  Inequality*, J. Math. Phys. 54 (2013), 122202, arXiv:1306.5920,
  Theorem 6 and equation (18).
-/

open scoped Matrix Matrix.Norms.Frobenius

namespace Matrix

/-- After Frobenius vectorization, the Hilbert-space adjoint of a rectangular
Kraus map is its trace-pairing adjoint.

This is the adjoint identity used in the direct `p = 2` proof of Beigi,
arXiv:1306.5920, Theorem 6, equation (18). -/
theorem adjoint_frobeniusEuclideanMap_eq
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (E : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ) (hE : IsKrausCP E) :
    (frobeniusEuclideanMap E).adjoint =
      frobeniusEuclideanMap (traceAdjointMap E) := by
  symm
  apply (LinearMap.eq_adjoint_iff _ _).2
  intro X Y
  rw [← (frobeniusEquivEuclidean β β).apply_symm_apply X,
    ← (frobeniusEquivEuclidean α α).apply_symm_apply Y]
  simp only [frobeniusEuclideanMap_apply, inner_frobeniusEquivEuclidean]
  have hstar (Z : Matrix β β ℂ) :
      (traceAdjointMap E Z)ᴴ = traceAdjointMap E Zᴴ := by
    obtain ⟨r, A, hA⟩ := hE.traceAdjointMap
    rw [hA, hA]
    simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [hstar, trace_traceAdjointMap_mul]

end Matrix
