/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.BiCFDerivation.Counterexample

/-!
# Finite-length sufficient conditions and obstructions for MPDO biCF

This module is the public entry point for the MPDO biCF derivation layer. It
keeps the historical import path `TNLean.MPS.MPDO.BiCFDerivation` available
while the development is split into focused submodules.

The supporting modules are:

* `TNLean.MPS.MPDO.BiCFDerivation.Basic` — historical re-export path for the
  finite-length biCF criteria.
* `TNLean.MPS.MPDO.BiCFDerivation.Core` — tuple-span, linear-independence, and
  finite/cumulative pair trace-separation criteria.
* `TNLean.MPS.MPDO.BiCFDerivation.PairHomogenization` — homogeneous pair-span
  padding and Burnside-Jacobson pair-algebra placeholders.
* `TNLean.MPS.MPDO.BiCFDerivation.Selectors` — selector data and constructors
  for `HorizontalCFData`.
* `TNLean.MPS.MPDO.BiCFDerivation.Counterexample` — the duplicate scalar-block
  obstruction showing that blockwise injectivity, left-canonicality, and
  nonzero weights do not imply the biCF property.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608, Proposition IV.3]

## Tags

matrix product states, matrix product density operators, canonical form, block separation
-/
