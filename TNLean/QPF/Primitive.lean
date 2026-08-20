/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Irreducible.FixedPointUniqueness
import TNLean.MPS.Core.CPPrimitive

/-!
# Quantum Perron–Frobenius for irreducible transfer maps

This file weakens the hypothesis of the quantum Perron–Frobenius theorem from
`IsInjective A` (Kraus operators span the full algebra) to
`IsIrreducibleMap (transferMap A)` (the transfer map has no nontrivial
invariant projections).

## Main results

* `quantum_perron_frobenius_irreducible` — QPF under irreducibility of the
  transfer map (weaker than injectivity)

## Mathematical content

The standard QPF theorem in Wolf (Theorem 6.3) is stated for **irreducible**
positive maps, not specifically for injective MPS tensors. The existing
`quantum_perron_frobenius` in `Assembly.lean` uses `IsInjective A` because
that implies `IsIrreducibleMap (transferMap A)` via
`injective_implies_irreducibleCP`. This file provides the direct
irreducibility-based version.

**Hierarchy of hypotheses** (each implies the next):
  `IsInjective A` → `IsPrimitive (transferMap A)` → `IsIrreducibleMap (transferMap A)`

Note: Injectivity implies primitivity (by Wolf Corollary 6.5 / the Wielandt bound),
and primitivity (1 is the only peripheral eigenvalue) implies irreducibility.
The converse fails: an irreducible channel can have period > 1.

## Strengthening relative to the literature

The existing formalization only provides QPF at the `IsInjective` level.
This file exposes the natural generality of Wolf's theorem at the
`IsIrreducibleMap` level, which applies to tensors that are not injective
but whose transfer maps are still irreducible (e.g., after blocking).

## References

* [Wolf2012] M. Wolf, *Quantum Channels & Operations: Guided Tour*,
  Section 6.2, Theorem 6.3 (quantum Perron–Frobenius for irreducible positive maps).
* [EH78] Evans, Høegh-Krohn, *Spectral properties of positive maps*, 1978.
-/

open scoped Matrix ComplexOrder BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- **Quantum Perron–Frobenius under irreducibility** (Wolf Theorem 6.3).

If the transfer map `E_A` is irreducible and trace-preserving (`∑ Aᵢ† Aᵢ = I`),
then it has a unique positive definite fixed point.

This is strictly more general than `quantum_perron_frobenius`, which requires
`IsInjective A`. The generalization matters for blocked tensors: after blocking
`n` sites, the resulting tensor may not be injective (the Kraus operators
may not span), but the transfer map can still be irreducible.

**Proof**: The normalization makes the transfer map a channel, so channel fixed-point
existence and uniqueness under irreducibility applies directly. -/
theorem quantum_perron_frobenius_irreducible [DecidableEq (Fin D)]
    (A : MPSTensor d D)
    (hIrr : IsIrreducibleMap (transferMap (d := d) (D := D) A))
    (hNorm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hD : 0 < D) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ,
      HasUniqueFixedPoint (transferMap (d := d) (D := D) A) ρ := by
  exact (transferMap_isChannel A (by convert hNorm)).exists_hasUniqueFixedPoint_of_irreducible
    hIrr hD

end MPSTensor
