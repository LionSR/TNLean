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

No aperiodicity hypothesis is needed.

## Spreading-primitivity equivalence and the `PosDef` hypothesis

Proposition 3 of arXiv:0909.5347 establishes the equivalence of three
properties of a quantum channel `ℰ_A` on `M_D(ℂ)`:

* (a) primitivity in the spreading sense: `ℰ_A^n(ρ) > 0` for some `n` and every
  density matrix `ρ`;
* (b) eventual full Kraus rank: `S_n(A) = M_D(ℂ)` for some `n`, where
  `S_n(A) = span {A_{i_1} ⋯ A_{i_n}}`;
* (c) strong irreducibility: `ℰ_A` has a unique peripheral eigenvalue `λ = 1`,
  whose corresponding eigenvector `ρ` is positive **definite** (`ρ > 0`).

Property (b) is the predicate `IsNormal A`. The hypothesis used here,
`IsPrimitiveMPS A ρ ∧ ρ.PosDef`, is precisely (c): the spectral-gap data inside
`IsPrimitiveMPS` gives the unique peripheral eigenvalue `λ = 1` with fixed
point `ρ`, and `ρ.PosDef` strengthens the eigenvector from positive semidefinite
to positive definite. Under Proposition 3, (c) is equivalent to (b), so the
conclusion `IsNormal A` follows.

The hypothesis `ρ.PosDef`, rather than the weaker `ρ.PosSemidef` carried by
`IsPrimitiveMPS`, is essential for two distinct steps of the proof. First,
strong irreducibility in the sense of (c) requires positive definiteness of
the fixed point by the very statement of the paper. Second, the Perron–Frobenius
direction `(c) ⇒ (b)` proceeds through the trace pairing
`B ↦ Re tr(Bᴴ ρ B)`: only when `ρ > 0` does this pairing satisfy a uniform
lower bound `c · ‖B‖² ≤ Re tr(Bᴴ ρ B)` for some `c > 0`, which controls the
growth of the cumulative span and forces it to fill `M_D(ℂ)`. From `ρ ≥ 0`
alone, the bound degenerates on the kernel of `ρ`. In the paper, positive
definiteness is obtained from Perron–Frobenius for irreducible quantum
channels; here it is taken as an explicit hypothesis, which is why the
statement names both `IsPrimitiveMPS A ρ` and `ρ.PosDef`. -/
theorem isNormal_of_isPrimitiveMPS_of_posDef
    {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hPrim : IsPrimitiveMPS A ρ)
    (hPD : ρ.PosDef) :
    IsNormal A := by
  exact isNormal_of_isPrimitiveMPS_with_posDef hPrim hPD

end MPSTensor
