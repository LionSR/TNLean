/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TNLean.Algebra.BurnsideTheorem
import TNLean.Algebra.IrreducibleTensorAction
import TNLean.Wielandt.SpanGrowth.CumulativeToWordSpan
import TNLean.Wielandt.Primitivity.ImpliesIrreducible

/-!
# Quantum Wielandt assembly under `PosDef` and aperiodicity

This file assembles the current conditional primitive-to-normal bridge,
chaining together results from across the library:

```
  IsPrimitiveMPS A ρ + ρ.PosDef + aperiodicity
    → IsIrreducibleTensor
    → IsIrreducibleAction
    → algSpan A = ⊤
    → IsNormal A
```

with the steps implemented in `PrimitiveImpliesIrreducible.lean`,
`IrreducibleTensorAction.lean`, `BurnsideTheorem.lean`, and
`CumulativeToWordSpan.lean`.

## The aperiodicity hypothesis

The assembly requires `1 ∈ wordSpan A 1`, i.e., the identity matrix lies in the
linear span of the Kraus operators `{A 0, …, A (d-1)}`. This is **not** automatic
from left-canonical / trace-preserving normalization (`∑ᵢ Aᵢᴴ Aᵢ = I`), which only gives
a quadratic identity and at best places `I` in a length-2 span.
Without aperiodicity, `IsNormal` can fail even when `algSpan = ⊤`. The standard
counterexample is `A₁ = e₁₂, A₂ = e₂₁` in `M₂(ℂ)`: these generate the full matrix
algebra but have period 2, so no single word-length spans `M₂(ℂ)`.

For the paper-style primitive notion — peripheral-spectrum primitivity together
with a positive-definite fixed point — the aperiodicity condition should follow
from spectral analysis of the transfer map. Formalizing that bridge from the
current hypotheses is left as future work.

Within TNLean this conditional assembly is currently standalone: the
normal/canonical-form pipeline in `TNLean.MPS.*` does not import it directly.

This module is intentionally auxiliary rather than the default paper-facing
endpoint. Downstream users who only need Proposition 3 / Theorem 1 wrappers
should prefer `Primitivity/Equivalence.lean` and `PaperResults/WielandtInequality.lean`.

## References

- Sanz, Pérez-García, Wolf, Cirac, *A quantum version of Wielandt's inequality*,
  arXiv:0909.5347, Proposition 3
- Cirac, Pérez-García, Schuch, Verstraete, *Matrix product unitaries: structure,
  symmetries, and topological invariants*, arXiv:1606.00608, §2.3
-/

open scoped Matrix ComplexOrder BigOperators
open Matrix MPSTensor

namespace MPSTensor

variable {d D : ℕ} [NeZero D]

/-! ## Main assembly theorem -/

/-- **Quantum Wielandt theorem (conditional on aperiodicity).**

If `A` satisfies the spectral-gap predicate `IsPrimitiveMPS A ρ`, the fixed
point `ρ` is positive definite, and the identity matrix lies in the span of the
Kraus operators (aperiodicity), then `A` is normal: word products of some fixed
length span the full matrix algebra.

The proof chains four results:
1. `isIrreducibleTensor_of_isPrimitiveMPS_of_posDef`:
   primitivity + PosDef → no invariant projections
2. `isIrreducibleAction_of_isIrreducibleTensor`: no invariant projections → no invariant subspaces
3. `burnside_matrix`: irreducible action → algebra span = ⊤ (Burnside's theorem)
4. `isNormal_of_algSpan_eq_top_of_aperiodic`: full algebra + aperiodicity → word span = ⊤ -/
theorem isNormal_of_isPrimitiveMPS_of_posDef
    {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hPrim : IsPrimitiveMPS A ρ)
    (hPD : ρ.PosDef)
    (hAper : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ wordSpan A 1) :
    IsNormal A := by
  -- Step 1: IsPrimitiveMPS + PosDef → IsIrreducibleTensor
  have hIrr := isIrreducibleTensor_of_isPrimitiveMPS_of_posDef hPrim hPD
  -- Step 2: IsIrreducibleTensor → IsIrreducibleAction
  have hAct := isIrreducibleAction_of_isIrreducibleTensor A hIrr
  -- Step 3: IsIrreducibleAction → algSpan = ⊤ (Burnside)
  have hAlg := burnside_matrix A hAct
  -- Step 4: algSpan = ⊤ + aperiodicity → IsNormal
  exact isNormal_of_algSpan_eq_top_of_aperiodic A hAlg hAper

/-- Under `IsPrimitiveMPS`, `PosDef`, and aperiodicity, exact word spans are eventually `⊤`.

This is the witness form of `isNormal_of_isPrimitiveMPS_of_posDef`: there is a
threshold `N` after which every exact-length word span equals the full matrix
algebra. -/
theorem wordSpan_eq_top_eventually_of_isPrimitiveMPS_of_posDef_of_aperiodic
    {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hPrim : IsPrimitiveMPS A ρ)
    (hPD : ρ.PosDef)
    (hAper : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ wordSpan A 1) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → wordSpan A n = ⊤ := by
  obtain ⟨N, hN⟩ := isNormal_of_isPrimitiveMPS_of_posDef hPrim hPD hAper
  rw [← wordSpan_eq_top_iff_isNBlkInjective] at hN
  refine ⟨N, fun n hn => ?_⟩
  exact eq_top_iff.mpr <| by
    simpa [hN] using wordSpan_mono'_of_one_mem_wordSpan_one A hAper hn

/-- Legacy compatibility alias for
`wordSpan_eq_top_eventually_of_isPrimitiveMPS_of_posDef_of_aperiodic`.

The historical name suggests the existential predicate `MPSTensor.IsPrimitive`,
but the theorem still takes the fixed-point witness `ρ` explicitly through
`IsPrimitiveMPS A ρ`. Prefer the more honest theorem name above, or
`isNormal_of_isPrimitiveMPS_of_posDef` when the `IsNormal` conclusion itself is
the desired API. -/
theorem isNormal_of_isPrimitive_of_posDef
    {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hPrim : IsPrimitiveMPS A ρ)
    (hPD : ρ.PosDef)
    (hAper : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ wordSpan A 1) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → wordSpan A n = ⊤ :=
  wordSpan_eq_top_eventually_of_isPrimitiveMPS_of_posDef_of_aperiodic hPrim hPD hAper

end MPSTensor
