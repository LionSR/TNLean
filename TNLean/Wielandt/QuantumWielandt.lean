/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TNLean.Algebra.BurnsideTheorem
import TNLean.Algebra.IrreducibleTensorAction
import TNLean.Wielandt.Primitivity.ImpliesIrreducible
import TNLean.Wielandt.Primitivity.StronglyIrreducibleToFullRank

/-!
# Quantum Wielandt: primitivity implies normality under `PosDef`

This file contains the primitive-to-normal implication:
`isNormal_of_isPrimitiveMPS_of_posDef`.

## Proof route for normality

```
  IsPrimitiveMPS A ρ + ρ.PosDef
    → IsStronglyIrreduciblePaper A
    → HasEventuallyFullKrausRank A
    → IsNormal A
```

The `(a)→(c)` part is provided by `ImpliesStronglyIrreducible.lean`, while the
`(c)→(b)` part is provided by `Primitivity/StronglyIrreducibleToFullRank.lean`.

The main theorem requires only `IsPrimitiveMPS A ρ` and `ρ.PosDef` —
no aperiodicity assumption. Strong irreducibility already yields peripheral
spectrum `{1}`.

This module is intentionally auxiliary. Downstream users who only need
Proposition 3 / Theorem 1 statements should prefer
`Primitivity/Equivalence.lean` and `SourceTheorems/WielandtInequality.lean`.

## References

- Sanz, Pérez-García, Wolf, Cirac, *A quantum version of Wielandt's inequality*,
  arXiv:0909.5347, Proposition 3
- Cirac, Pérez-García, Schuch, Verstraete, *Matrix product unitaries: structure,
  symmetries, and topological invariants*, arXiv:1606.00608, Section 2.3
-/

open scoped Matrix ComplexOrder BigOperators
open Matrix MPSTensor

namespace MPSTensor

variable {d D : ℕ} [NeZero D]

/-! ## Main primitive-to-normal theorem -/

/-- **Quantum Wielandt theorem.**

If `A` satisfies the spectral-gap predicate `IsPrimitiveMPS A ρ` and the fixed
point `ρ` is positive definite, then `A` is normal.

The proof factors through strong irreducibility: from `IsPrimitiveMPS + ρ.PosDef`
one gets `IsStronglyIrreduciblePaper A` (i.e., primitive in Wolf's sense), and
Wolf's primitivity equivalence (`wolf_theorem_6_8_conjunction`) identifies this
directly with eventual full Kraus rank, hence normality.

No aperiodicity hypothesis is needed. -/
theorem isNormal_of_isPrimitiveMPS_of_posDef
    {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hPrim : IsPrimitiveMPS A ρ)
    (hPD : ρ.PosDef) :
    IsNormal A := by
  exact isNormal_of_isPrimitiveMPS_with_posDef hPrim hPD

end MPSTensor
