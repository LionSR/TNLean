/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.IntervalSamplingChoices
import TNLean.MPS.AreaLaw.IndependentIntervalOperation
import TNLean.MPS.AreaLaw.CanonicalSampledIntervalInterleaved

/-!
# The sampled operation for the existing balanced recursion

A single family of independent interval choices determines an operation
for the existing balanced interval recursion. Every valid long parent uses
its own coordinate, the actual adjacent child merge, and the specified
family's literal interleaved iteration. Supporting ALVV,
arXiv:1602.08828v2, Figure `fig:algo1` and lines 1777–1817.
-/

namespace TNLean.MPS.AreaLaw

/-- One realization of the independent interval choices fixes the actual
sampled operation. The targets and families precede these choices. Short
or out-of-range parents are set to the full space; they are never used as
internal nodes of a valid balanced root. Supporting ALVV,
arXiv:1602.08828v2, Figure `fig:algo1`, lines 1777–1817. -/
noncomputable def canonicalIntervalSamplingOperation {L q width : ℕ}
    (D s : ℕ) (N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (xi : ℝ) (U : IntervalSamplingChoices L q) : IntervalMergeOperation L q :=
  independentIntervalOperation
    (fun J W v ↦ canonicalSampledIntervalInterleavedTrim L q J.val.1 J.val.2 D s
      (F J) xi W v) U

end TNLean.MPS.AreaLaw
