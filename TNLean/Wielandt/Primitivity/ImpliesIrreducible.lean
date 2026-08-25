/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.InvariantProjection
import TNLean.Wielandt.Primitivity.PrimitiveBridge

/-!
# Primitive tensors with a positive-definite fixed point are irreducible

The `IsPrimitiveMPS A ρ` hypothesis, together with positive definiteness of
`ρ`, implies irreducibility of the transfer map. The corresponding finite
matrix family is therefore irreducible by the transfer-map comparison theorem.

## Main result

* `isIrreducibleTensor_of_isPrimitiveMPS_of_posDef`:
  `IsPrimitiveMPS A ρ → ρ.PosDef → Kraus.IsIrreducibleFamily A`.

This is the irreducibility half of the later primitive-to-normal implication.
The complementary aperiodicity input is recovered from strong irreducibility
in `ImpliesStronglyIrreducible.lean` and
`StronglyIrreducibleToFullRank.lean`.

## References

- Sanz, Pérez-García, Wolf, Cirac, arXiv:0909.5347, Proposition 3.
- Cirac, Pérez-García, Schuch, Verstraete, arXiv:1606.00608, Section 2.3.
-/

open scoped ComplexOrder

namespace MPSTensor

variable {d D : ℕ} [NeZero D]

/-- A primitive MPS tensor with a positive-definite fixed point is irreducible.

This is the irreducibility implication in Proposition 3 of Sanz,
Pérez-García, Wolf, and Cirac, arXiv:0909.5347. -/
theorem isIrreducibleTensor_of_isPrimitiveMPS_of_posDef
    {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hPrim : IsPrimitiveMPS A ρ)
    (hPD : ρ.PosDef) :
    Kraus.IsIrreducibleFamily A :=
  Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM A
    (isIrreducibleMap_of_isPrimitiveMPS_of_posDef hPrim hPD)

end MPSTensor
