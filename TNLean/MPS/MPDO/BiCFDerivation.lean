/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.BiCFDerivation.Counterexample
import TNLean.MPS.MPDO.BiCFDerivation.DirectSumGroundSpace
import TNLean.MPS.MPDO.BiCFDerivation.DirectSumInput

/-!
# Finite-length sufficient conditions and obstructions for MPDO biCF

This module retains the historical import path for the MPDO biCF derivation
layer while the finite-length criteria are organized by their mathematical
role.

The supporting modules are:

* `TNLean.MPS.MPDO.BiCFDerivation.Basic` — historical import path for the
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
* `TNLean.MPS.MPDO.BiCFDerivation.DirectSumInput` — the trace-dual algebraic
  input from David--Perez-Garcia--Schuch--Wolf Lemma `lem:direct-sum` that
  follows from the two-sided nonzero span lemma.
* `TNLean.MPS.MPDO.BiCFDerivation.DirectSumGroundSpace` — the corresponding
  inclusion/equality of finite-chain image spaces.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608, Proposition IV.3]
* [David--Perez-Garcia--Schuch--Wolf 2006, Lemmas `lem1` and `lem:direct-sum`]

## Tags

matrix product states, matrix product density operators, canonical form, block separation
-/
