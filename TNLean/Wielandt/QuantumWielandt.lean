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
`Primitivity/Equivalence.lean` and `PaperResults/WielandtInequality.lean`.

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

No aperiodicity hypothesis is needed.

## Hypothesis boundary

The conjunction `IsPrimitiveMPS A ρ ∧ ρ.PosDef` is the formal counterpart of the
strongly-irreducible characterisation in arXiv:0909.5347, Proposition 3(c):
peripheral spectrum `{1}`, irreducibility of the transfer map, and a positive
*definite* fixed point. Proposition 3 of that paper makes this equivalent to
both primitivity in the uniform-spreading sense (3(a)) and to eventual full
Kraus rank `IsNormal A` (3(b)), so the hypothesis used here is mathematically
equivalent to the conclusion under the paper's normalisation.

The formal proof chain consumes `ρ.PosDef` in two places: the call to
`isStronglyIrreduciblePaper_of_isPrimitiveMPS_of_posDef` upgrades the
spectral-gap predicate to Proposition 3(c), and the trace-pairing positivity
lemma `trace_conjTranspose_posDef_mul_lower` inside the `(c) → (b)` argument
extracts a uniform constant `c > 0` with `c · ‖B‖² ≤ Re tr(Bᴴ ρ B)`, which is
unavailable from positive semidefiniteness alone. The peripheral-spectrum
predicate `IsPrimitiveMPS A ρ` records `ρ` as PSD only, so the formal
upgrade to PosDef is an explicit hypothesis rather than an automatic
consequence; in the paper, the upgrade is supplied by Perron–Frobenius for
irreducible quantum channels.

The fundamental-theorem application of this lemma (arXiv:1606.00608, §2.3)
also takes Proposition 3(c) as the input characterisation, so passing through
the `IsPrimitiveMPS + ρ.PosDef` form does not weaken the downstream usage.
The current formal boundary is recorded in
`docs/paper-gaps/quantum_wielandt_deviation.tex`. -/
theorem isNormal_of_isPrimitiveMPS_of_posDef
    {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hPrim : IsPrimitiveMPS A ρ)
    (hPD : ρ.PosDef) :
    IsNormal A := by
  exact isNormal_of_isPrimitiveMPS_with_posDef hPrim hPD

end MPSTensor
