/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import TNLean.Circuit.LocalCircuit

/-!
# Functional calculus preserves finite quantum-circuit support

The supported operator algebra is a closed finite-dimensional star
subalgebra. Real functional calculus therefore preserves its support.
This shared fact is used by spectral windows and regional ground spaces.

Source: Hastings, arXiv:cond-mat/0508554v3, grouping and spectral windows,
lines 609–628; AKLV, arXiv:1301.1162v1, Section 6.1 normalization.
-/

open scoped Matrix.Norms.L2Operator

namespace QuantumCircuit

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Real functional calculus preserves the support of a finite operator.
Source context: Hastings, arXiv:cond-mat/0508554v3, lines 609–628;
AKLV, arXiv:1301.1162v1, Section 6.1. -/
theorem cfc_mem_supportedOperators (f : ℝ → ℝ) {S : Set ι}
    {A : Matrix (ι → Fin d) (ι → Fin d) ℂ} (hA : A ∈ supportedOperators d S) :
    cfc f A ∈ supportedOperators d S := by
  let s : StarSubalgebra ℂ (Matrix (ι → Fin d) (ι → Fin d) ℂ) :=
    { (supportedOperators d S).toSubalgebra (one_mem_supportedOperators S)
        fun _ _ ↦ mul_mem_supportedOperators with
      star_mem' := star_mem_supportedOperators }
  have : IsClosed (s : Set (Matrix (ι → Fin d) (ι → Fin d) ℂ)) :=
    Submodule.closed_of_finiteDimensional (supportedOperators d S)
  exact cfc_mem (𝕜 := ℝ) (𝕜' := ℂ) (s := s) f hA

end QuantumCircuit
