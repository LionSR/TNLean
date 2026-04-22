/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Peripheral.CyclicDecomposition.Basic
import TNLean.Channel.Peripheral.CyclicDecomposition.PeripheralUnitary
import TNLean.Channel.Peripheral.CyclicDecomposition.CyclicProjections
import TNLean.Channel.Peripheral.CyclicDecomposition.Decomposition
import TNLean.Channel.Peripheral.CyclicDecomposition.Primitivity

/-!
# Cyclic decomposition of periodic irreducible channels

This module keeps the historical import path
`TNLean.Channel.Peripheral.CyclicDecomposition` while the development is split
across five focused submodules.

The supporting modules are:

* `TNLean.Channel.Peripheral.CyclicDecomposition.Basic` — corner algebras,
  compression linear equivalences, and the corner-rank API.
* `TNLean.Channel.Peripheral.CyclicDecomposition.PeripheralUnitary` — scalar
  fixed points and peripheral-unitary normalization.
* `TNLean.Channel.Peripheral.CyclicDecomposition.CyclicProjections` — Fourier
  spectral projections of a finite-order peripheral unitary.
* `TNLean.Channel.Peripheral.CyclicDecomposition.Decomposition` — the main
  cyclic decomposition theorem for irreducible unital Schwarz maps.
* `TNLean.Channel.Peripheral.CyclicDecomposition.Primitivity` — corner
  preservation, sector irreducibility, sector primitivity, and the permutation
  variant.

## Main statements

* `exists_cyclic_decomposition_of_irreducible_schwarz`
* `preserves_corner_pow_of_cyclic_decomp`
* `isIrreducible_restriction_of_cyclic_decomp`
* `isPrimitive_restriction_of_cyclic_decomp`
* `preserves_corner_pow_orderOf_of_perm_decomp`

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Thm. 6.6, Thm. 6.16]
-/
