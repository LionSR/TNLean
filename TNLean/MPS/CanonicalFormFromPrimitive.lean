/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.PiAlgebra.CanonicalFormSep
import TNLean.MPS.PrimitivityBridge

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false

open scoped Matrix BigOperators
open Filter

namespace MPSTensor

/-- Builder lemma: construct `IsCanonicalForm` once the overlap hypothesis is derived from
primitivity. -/
theorem isCanonicalForm_of_primitive
    {d : ℕ} {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    {μ : Fin r → ℂ} {A : (k : Fin r) → MPSTensor d (dim k)}
    (hInj : ∀ k, IsInjective (A k))
    (hDS : ∀ k, ∑ i : Fin d, (A k i)ᴴ * (A k i) = 1)
    (hμanti : StrictAnti (fun k : Fin r => ‖μ k‖))
    (hμne : ∀ k, μ k ≠ 0)
    (hPrim : ∀ k, MPSTensor.IsPrimitive (A k)) :
    MPSTensor.IsCanonicalForm (d := d) (μ := μ) A := by
  refine
    { block_injective := hInj
      ds_gauge := hDS
      mu_strict_anti := hμanti
      mu_ne_zero := hμne
      overlap_tendsto_one := ?_ }
  intro k
  simpa using (IsPrimitive.overlap_tendsto_one (d := d) (A := A k) (hPrim k))

end MPSTensor
