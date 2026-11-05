/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.Reduction.GaugeWordModule
import TNLean.MPS.FundamentalTheorem.Reduction.UniquenessBlocks

/-!
# Gauge equivalence is isomorphism of word modules

Two tensors `A`, `A'` with `d` letters are gauge equivalent, `A i * X = X * A' i` for an invertible
`X`, exactly when their word modules are isomorphic modules over the free algebra on the letters.
One direction is `nonempty_linearEquiv_wordModule_of_isGaugeRelated`, the other
`isGaugeRelated_of_linearEquiv`; reflexivity, symmetry and transitivity of gauge equivalence are
`IsGaugeRelated.refl`, `IsGaugeRelated.symm` and `IsGaugeRelated.trans`.

## Main results

* `MPSTensor.isGaugeRelated_iff_nonempty_linearEquiv_wordModule`.
-/

namespace MPSTensor

variable {d : ℕ}

/-- **Word modules and gauges**. Two tensors are gauge equivalent if and only
if their word modules are isomorphic modules over the free algebra on the letters. -/
theorem isGaugeRelated_iff_nonempty_linearEquiv_wordModule {D₁ D₂ : ℕ} {A : MPSTensor d D₁}
    {A' : MPSTensor d D₂} :
    IsGaugeRelated A A' ↔ Nonempty (A.WordModule ≃ₗ[WordAlgebra d] A'.WordModule) :=
  ⟨nonempty_linearEquiv_wordModule_of_isGaugeRelated, fun ⟨e⟩ => isGaugeRelated_of_linearEquiv e⟩

end MPSTensor
