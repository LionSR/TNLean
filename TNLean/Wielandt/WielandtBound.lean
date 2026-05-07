/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Authors]
-/

import TNLean.Wielandt.RankOne.Products
import TNLean.Wielandt.SpanGrowth.EigenvectorSpreading

/-!
# Wielandt cumulative chain

This file records the **cumulative** Wielandt chain: the four standard
consequences of normality that feed into the fixed-length Wielandt bound
(Theorem 1 of arXiv:0909.5347).

The paper-facing Theorem 1 statements (case (1), (2), (3) bounds on the
Kraus-rank index $i(A)$) are in `PaperResults/WielandtInequality.lean`.
This file only provides the cumulative-span and eigenvector-spreading
inputs needed by the primitivity/normality bridge and the blueprint.

## Main result

* `wielandt_chain`: under `IsNormal A`, simultaneously:
  1. `cumulativeSpan A (D ^ 2) = ⊤`
  2. $\exists w_0,\ |w_0| \le D^2 \land \operatorname{tr}(A^{w_0}) \ne 0$
  3. $\exists w_0, \mu \ne 0, \varphi \ne 0$ with
     $|w_0| \le D^2$ and $A^{w_0}\varphi = \mu\varphi$
  4. $\forall \varphi \ne 0,\ \operatorname{cumulativeVectorSpan} A \varphi (D^2) = \top$

## References

- [Sanz, Pérez-García, Wolf, Cirac, *A quantum version of Wielandt's
  inequality*, arXiv:0909.5347](https://arxiv.org/abs/0909.5347)
-/

open scoped Matrix
open MPSTensor Module

namespace MPSTensor

variable {d D : ℕ}

/-! ## The cumulative Wielandt chain

The four standard consequences of normality.  These are combined below
in one theorem so that callers (e.g. the primitivity/normality bridge
in `Primitivity/Normal.lean`) get all outputs at once. -/

/-- **The cumulative Wielandt chain**: under `IsNormal A`,
the four standard cumulative consequences hold simultaneously.

1. Cumulative span `T_{D²}(A) = M_D(ℂ)` (Lemma 1, cumulative version)
2. A word `w₀` of length `≤ D²` with nonzero trace
3. A nonzero eigenvalue `μ ≠ 0` and eigenvector `φ ≠ 0` for `evalWord A w₀`
4. For any nonzero `φ`, the cumulative vector span reaches ⊤ in `D²` steps

**Paper**: arXiv:0909.5347, proof of Theorem 1, before the fixed-length
upgrade in Lemma 2(b).

The fixed-length paper-facing bounds on `i(A)` (cases (1), (2), (3)) are
assembled in `PaperResults/WielandtInequality.lean`.
-/
theorem wielandt_chain [NeZero D]
    (A : MPSTensor d D) (hN : IsNormal A) :
    -- Step 1: Cumulative span = ⊤
    cumulativeSpan A (D ^ 2) = ⊤ ∧
    -- Step 2: Nonzero trace word exists
    (∃ (w₀ : List (Fin d)),
      w₀.length ≤ D ^ 2 ∧ Matrix.trace (evalWord A w₀) ≠ 0) ∧
    -- Step 3: Eigenvalue and eigenvector exist
    (∃ (w₀ : List (Fin d)) (μ : ℂ) (φ : Fin D → ℂ),
      w₀.length ≤ D ^ 2 ∧ μ ≠ 0 ∧ φ ≠ 0 ∧
      evalWord A w₀ *ᵥ φ = μ • φ) ∧
    -- Step 4: Vector spanning
    (∀ (φ : Fin D → ℂ), φ ≠ 0 →
      cumulativeVectorSpan A φ (D ^ 2) = ⊤) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact cumulativeSpan_eq_top A hN
  · exact exists_nonzero_trace_word A hN
  · exact exists_word_eigenvector A hN
  · intro φ hφ
    exact cumulativeVectorSpan_eq_top_of_cumulativeSpan_eq_top A φ hφ
      (cumulativeSpan_eq_top A hN)

end MPSTensor
