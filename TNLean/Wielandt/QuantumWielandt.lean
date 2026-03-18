/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TNLean.Algebra.BurnsideTheorem
import TNLean.Algebra.IrreducibleTensorAction
import TNLean.Wielandt.SpanGrowth.CumulativeToWordSpan
import TNLean.Wielandt.Primitivity.ImpliesIrreducible
import TNLean.Wielandt.Primitivity.StronglyIrreducibleToFullRank

/-!
# Quantum Wielandt primitive-to-normal packaging under `PosDef`

This file packages the current primitive-to-normal bridge around
`isNormal_of_isPrimitiveMPS_of_posDef`, together with a legacy exact-word-span
witness theorem whose public statement still carries an explicit aperiodicity
argument.

## Proof route for normality

```
  IsPrimitiveMPS A ρ + ρ.PosDef
    → IsStronglyIrreduciblePaper A
    → HasEventuallyFullKrausRank A
    → IsNormal A
```

The `(a)→(c)` part is provided by `ImpliesStronglyIrreducible.lean`, while the
`(c)→(b)` part is provided by `Primitivity/StronglyIrreducibleToFullRank.lean`.

## The aperiodicity hypothesis

The theorem `isNormal_of_isPrimitiveMPS_of_posDef` itself no longer uses an
aperiodicity assumption. The extra argument `hAper : 1 ∈ wordSpan A 1` survives
only in the legacy witness theorem
`wordSpan_eq_top_eventually_of_isPrimitiveMPS_of_posDef_of_aperiodic`, where it
upgrades `IsNormal A` to monotone exact-length word spans.

Conceptually, this matches Proposition 3: strong irreducibility packages
irreducibility together with peripheral spectrum `{1}`. That peripheral
condition is the source of the aperiodicity used by the
`CumulativeToWordSpan.lean` endpoint.

Within TNLean this auxiliary packaging is currently standalone: the
normal/canonical-form reduction in `TNLean.MPS.*` does not import it directly.

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

/-! ## Main primitive-to-normal theorem -/

/-- **Quantum Wielandt theorem.**

If `A` satisfies the spectral-gap predicate `IsPrimitiveMPS A ρ` and the fixed
point `ρ` is positive definite, then `A` is normal.

Conceptually, the proof factors through strong irreducibility. From
`IsPrimitiveMPS + ρ.PosDef` one gets `IsStronglyIrreduciblePaper A`; this gives
peripheral spectrum `{1}` (hence aperiodicity) together with irreducibility, and
the Proposition 3(c)→(b) backend then yields eventual full Kraus rank. The
extra aperiodicity argument `hAper` is kept only for backward compatibility with
the older API of this file and is not used by the proof term. -/
theorem isNormal_of_isPrimitiveMPS_of_posDef
    {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hPrim : IsPrimitiveMPS A ρ)
    (hPD : ρ.PosDef)
    (_hAper : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ wordSpan A 1) :
    IsNormal A := by
  exact isNormal_of_isPrimitiveMPS_with_posDef hPrim hPD

/-- Under `IsPrimitiveMPS`, `PosDef`, and aperiodicity, exact word spans are eventually `⊤`.

This is the witness form of `isNormal_of_isPrimitiveMPS_of_posDef`: once
`IsNormal A` is known, the extra aperiodicity hypothesis makes exact word spans
monotone, so from one full span one gets `wordSpan A n = ⊤` for all sufficiently
large `n`. -/
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

The historical name suggests the existential spectral-gap wrapper from
`PrimitivityBridge.lean`, but the theorem still takes the fixed-point witness `ρ`
explicitly through `IsPrimitiveMPS A ρ`. Prefer the more precise theorem name
above, or `isNormal_of_isPrimitiveMPS_of_posDef` when the `IsNormal` conclusion
itself is the desired API. -/
theorem isNormal_of_isPrimitive_of_posDef
    {A : MPSTensor d D} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hPrim : IsPrimitiveMPS A ρ)
    (hPD : ρ.PosDef)
    (hAper : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ wordSpan A 1) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → wordSpan A n = ⊤ :=
  wordSpan_eq_top_eventually_of_isPrimitiveMPS_of_posDef_of_aperiodic hPrim hPD hAper

end MPSTensor
