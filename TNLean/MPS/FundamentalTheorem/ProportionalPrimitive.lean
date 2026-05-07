/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.Proportional
import TNLean.MPS.Structure.PrimitivityBridge
import TNLean.Wielandt.Primitivity.ImpliesIrreducible

/-!
# Proportional Fundamental Theorem — Primitive convenience formulations

This file provides strengthened versions of the proportional single-block
Fundamental Theorem that take `IsPrimitiveMPS` hypotheses directly, eliminating
the need to separately supply normalization and overlap-convergence conditions.

## Main results

* `gaugePhaseEquiv_of_proportionalMPV₂_of_isPrimitiveMPS`: if both tensors
  have primitive transfer maps with positive-definite fixed points and their MPV
  families are proportional, then the tensors are gauge-phase equivalent.

## Strengthening over the literature

The standard statement (arXiv:2011.12127, Theorem 4.4) requires the user to
separately verify left-canonicality, self-overlap convergence, and
irreducibility.  Since `IsPrimitiveMPS` comprises all of these (primitivity
implies irreducibility, left-canonicality is built in, and the spectral gap
gives overlap convergence), the formulation here reduces the hypothesis count from
7 to 4.

## External input — Quantum Wielandt primitivity ⇒ irreducibility

This file imports `TNLean.Wielandt.Primitivity.ImpliesIrreducible`, which
supplies the Quantum Wielandt theorem that a primitive (aperiodic) transfer
map yields irreducible Kraus operators:

> **Quantum Wielandt, primitivity-to-irreducibility direction**
> (arXiv:0909.5347, Proposition 3 / Wolf Theorem 6.7).
> If `E_A` is primitive (has a unique peripheral eigenvalue `1`), then the
> Kraus operators `{A_i}` are **irreducible**: their word products span the
> full matrix algebra `M_D(ℂ)`.

In MPS notation: `IsPrimitiveMPS A ρ` (primitive transfer map with PD fixed
point `ρ`) implies `IsIrreducible A` (the Kraus operators `{A_i}` generate
`M_D(ℂ)` as an algebra).  This implication is used here to eliminate the
separate irreducibility hypothesis from the proportional FT statement.

The formal Lean declaration that supplies this external input is:

> `Wielandt.Primitivity.ImpliesIrreducible` provides the bridge from the
> peripheral-spectrum primitivity predicate (`_root_.IsPrimitive`) to the
> irreducibility conclusion.

## References

- Cirac, Pérez-García, Schuch, Verstraete, *Matrix Product States and Projected
  Entangled Pair States*, arXiv:2011.12127, Theorem 4.4
- Sanz, Pérez-García, Wolf, Cirac, *A quantum version of Wielandt's inequality*,
  arXiv:0909.5347, Proposition 3
- Wolf, *Quantum Channels & Operations*, Theorem 6.7
-/

open scoped Matrix BigOperators ComplexOrder
open Filter

namespace MPSTensor

variable {d D : ℕ} [NeZero D]

/-- **Proportional Fundamental Theorem (primitive convenience form).**

If `A` and `B` both have primitive transfer maps with positive-definite fixed
points and their MPV families are proportional, then they are gauge-phase
equivalent: `B i = ζ • X * A i * X⁻¹` for some nonzero `ζ` and invertible `X`.

This eliminates the separate normalization, overlap-convergence, and
irreducibility hypotheses by extracting them from `IsPrimitiveMPS`. -/
theorem gaugePhaseEquiv_of_proportionalMPV₂_of_isPrimitiveMPS
    (A B : MPSTensor d D)
    {ρA ρB : Matrix (Fin D) (Fin D) ℂ}
    (hA : IsPrimitiveMPS A ρA) (hA_pd : ρA.PosDef)
    (hB : IsPrimitiveMPS B ρB) (hB_pd : ρB.PosDef)
    (hProp : ProportionalMPV₂ (d := d) A B) :
    GaugePhaseEquiv A B :=
  gaugePhaseEquiv_of_proportionalMPV₂_of_overlap_tendsto_one_of_irreducible_TP A B
    (isIrreducibleTensor_of_isPrimitiveMPS_of_posDef hA hA_pd)
    (isIrreducibleTensor_of_isPrimitiveMPS_of_posDef hB hB_pd)
    hA.norm hB.norm
    hA.overlap_tendsto_one hB.overlap_tendsto_one
    hProp

end MPSTensor
