/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.PiAlgebra.CanonicalFormSep
import TNLean.MPS.Structure.PrimitivityBridge

/-!
# Canonical form from primitive blocks

This file is a downstream builder: it combines blockwise injectivity, left-canonical
normalization, strict weight ordering, and blockwise primitivity into `IsCanonicalForm`.
It does not prove such data from arbitrary input tensors.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-- Build `IsCanonicalForm` once the normalized self-overlap hypothesis has been derived from
blockwise primitivity.

This theorem proves the final implication after the blockwise injectivity, normalization, weight
ordering, and primitivity hypotheses have already been established.

Source context: Perez-Garcia--Verstraete--Wolf--Cirac 2007,
Theorem `Th:TIcanonical`, lines 742--763, starts from an arbitrary
translation-invariant MPS representation.

**Scope restriction (primitive block hypotheses):** this theorem assumes
injectivity, strict ordering of the weight moduli, nonzero weights, and a primitive fixed point
for every block. Those hypotheses are not assumptions of PGVWC07
Theorem `Th:TIcanonical`. See
`docs/paper-gaps/pgvwc07_ti_canonical_form_scope.tex`. -/
theorem isCanonicalForm_of_primitive
    {d : ℕ} {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    {μ : Fin r → ℂ} {A : (k : Fin r) → MPSTensor d (dim k)}
    (hInj : ∀ k, IsInjective (A k))
    (hDS : ∀ k, ∑ i : Fin d, (A k i)ᴴ * (A k i) = 1)
    (hμanti : StrictAnti (fun k : Fin r => ‖μ k‖))
    (hμne : ∀ k, μ k ≠ 0)
    (hPrim : ∀ k, MPSTensor.HasPrimitiveFixedPoint (A k)) :
    MPSTensor.IsCanonicalForm (d := d) (μ := μ) A := by
  refine MPSTensor.IsCanonicalForm.ofStrictSeparatedData ?_ ?_ ?_ ?_
  · exact ⟨hInj⟩
  · exact ⟨hDS⟩
  · exact ⟨hμanti, hμne⟩
  · refine ⟨?_⟩
    intro k
    simpa using
      (HasPrimitiveFixedPoint.overlap_tendsto_one (d := d) (A := A k) (hPrim k))

end MPSTensor
