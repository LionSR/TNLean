/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TNLean.Wielandt.PrimitiveImpliesIrreducible
import TNLean.Wielandt.CumulativeToWordSpan
import TNLean.Algebra.BurnsideTheorem
import TNLean.Algebra.IrreducibleTensorAction

/-!
# Quantum Wielandt theorem: IsPrimitive → IsNormal

This file assembles the complete quantum Wielandt theorem, chaining together results
from across the library:

```
  IsPrimitiveMPS A ρ  +  ρ.PosDef  +  aperiodicity
  ──────────────────────────────────────────────────
  Step 1: IsPrimitiveMPS + PosDef → IsIrreducibleTensor
          (PrimitiveImpliesIrreducible.lean)
  Step 2: IsIrreducibleTensor → IsIrreducibleAction
          (IrreducibleTensorAction.lean)
  Step 3: IsIrreducibleAction → algSpan A = ⊤
          (BurnsideTheorem.lean — Burnside/Jacobson density)
  Step 4: algSpan A = ⊤ + aperiodicity → IsNormal A
          (CumulativeToWordSpan.lean)
```

## The aperiodicity hypothesis

The assembly requires `1 ∈ wordSpan A 1`, i.e., the identity matrix lies in the
linear span of the Kraus operators `{A 0, …, A (d-1)}`. This is **not** automatic
from left-canonical / trace-preserving normalization (`∑ᵢ Aᵢᴴ Aᵢ = I`), which only gives
a quadratic identity and at best places `I` in a length-2 span.
Without aperiodicity, `IsNormal` can fail even when `algSpan = ⊤`. The standard
counterexample is `A₁ = e₁₂, A₂ = e₂₁` in `M₂(ℂ)`: these generate the full matrix
algebra but have period 2, so no single word-length spans `M₂(ℂ)`.

For truly primitive tensors (peripheral spectrum = {1}), the aperiodicity condition
follows from spectral analysis of the transfer map; formalizing this derivation is
left as future work.

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

If the transfer map of `A` has a spectral gap with positive-definite fixed point, and the
identity matrix lies in the span of the Kraus operators (aperiodicity), then `A` is normal:
word products of some fixed length span the full matrix algebra.

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

/-- **Quantum Wielandt theorem (existential version).**

The existential wrapper: if `A` is primitive (∃ ρ with spectral gap), the fixed point
is positive definite, and the aperiodicity condition holds, then `A` is normal. -/
theorem isNormal_of_isPrimitive_of_posDef
    {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hPrim : IsPrimitiveMPS A ρ)
    (hPD : ρ.PosDef)
    (hAper : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ wordSpan A 1) :
    ∃ N : ℕ, ∀ (n : ℕ), N ≤ n → wordSpan A n = ⊤ := by
  obtain ⟨N, hN⟩ := isNormal_of_isPrimitiveMPS_of_posDef hPrim hPD hAper
  refine ⟨N, fun n hn => ?_⟩
  rw [← wordSpan_eq_top_iff_isNBlkInjective] at hN
  exact le_antisymm le_top (hN ▸ wordSpan_mono'_of_one_mem_wordSpan_one A hAper hn)

/-- **Full pipeline (short form).**

One-line combination: `IsIrreducibleTensor + aperiodicity → IsNormal`.
This is the composition of Steps 2–4 above, useful when Step 1 has already been applied. -/
theorem isNormal_of_isIrreducibleTensor_aperiodic
    (A : MPSTensor d D)
    (hIrr : IsIrreducibleTensor A)
    (hAper : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ wordSpan A 1) :
    IsNormal A :=
  isNormal_of_isIrreducibleTensor_of_aperiodic A hIrr hAper

end MPSTensor
