/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Kraus.Wielandt.RankOne.Element
import TNLean.Wielandt.SpanGrowth.VectorToMatrixSpan

/-!
# Bounded word powers for MPS tensors

This file restates the word-power results of
`Kraus.Wielandt.RankOne.Element` for an MPS tensor's evaluated words.
-/

open scoped Matrix
open Module

namespace MPSTensor

variable {d D : ℕ}

/-- A power of an evaluated word belongs to the word span at the multiplied length. -/
theorem evalWord_pow_mem_wordSpan (A : MPSTensor d D) (w : List (Fin d)) (k : ℕ) :
    (evalWord A w) ^ k ∈ wordSpan A (k * w.length) := by
  change (evalWord A w) ^ k ∈ Kraus.wordSpan A (k * w.length)
  exact Kraus.evalWord_pow_mem_wordSpan A w k

/-- A word matrix with a nonzero eigenvalue has a nonzero bounded power whose range lies
in the sum of its generalized eigenspaces for nonzero eigenvalues.

This is only the intermediate Fitting-projector-power step
$A_1^r = A_1^r P$ in arXiv:0909.5347, Lemma 2(b). It is weaker than the
rank-one-element conclusion of that lemma. -/
theorem exists_nonzero_pow_evalWord_mem_wordSpan_range_le
    (A : MPSTensor d D) (w₀ : List (Fin d))
    (μ : ℂ) (φ : Fin D → ℂ)
    (hμ : μ ≠ 0) (hφ : φ ≠ 0)
    (heig : evalWord A w₀ *ᵥ φ = μ • φ) :
    ∃ P : Matrix (Fin D) (Fin D) ℂ,
      P ∈ wordSpan A (D * w₀.length) ∧
      P ≠ 0 ∧
      LinearMap.range (Matrix.toLin' P) ≤
        ⨆ (ν : ℂ) (_ : ν ≠ 0),
          End.maxGenEigenspace (Matrix.toLin' (evalWord A w₀)) ν := by
  simpa only [wordSpan] using
    Kraus.exists_nonzero_pow_evalWord_mem_wordSpan_range_le A w₀ μ φ hμ hφ heig

end MPSTensor
