/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.PiAlgebra.CanonicalFormSep
import TNLean.MPS.Structure.PrimitivityBridge

/-!
# Canonical form from primitive blocks

This file is a downstream builder: it packages blockwise injectivity, left-canonical
normalization, strict weight ordering, and blockwise primitivity into `IsCanonicalForm`.
It does not prove such data from arbitrary input tensors.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-- Build `IsCanonicalForm` once the normalized self-overlap hypothesis has been derived from
blockwise primitivity.

This is a late-stage builder theorem: all blockwise injectivity / normalization / ordering data are
assumed as inputs. -/
theorem isCanonicalForm_of_primitive
    {d : ℕ} {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    {μ : Fin r → ℂ} {A : (k : Fin r) → MPSTensor d (dim k)}
    (hInj : ∀ k, IsInjective (A k))
    (hDS : ∀ k, ∑ i : Fin d, (A k i)ᴴ * (A k i) = 1)
    (hμanti : StrictAnti (fun k : Fin r => ‖μ k‖))
    (hμne : ∀ k, μ k ≠ 0)
    (hPrim : ∀ k, MPSTensor.HasPrimitiveFixedPoint (A k)) :
    MPSTensor.IsCanonicalForm (d := d) (μ := μ) A := by
  refine MPSTensor.IsCanonicalForm.ofSeparatedData ?_ ?_ ?_ ?_
  · exact ⟨hInj⟩
  · exact ⟨hDS⟩
  · exact ⟨hμanti, hμne⟩
  · refine ⟨?_⟩
    intro k
    simpa using
      (HasPrimitiveFixedPoint.overlap_tendsto_one (d := d) (A := A k) (hPrim k))

end MPSTensor
