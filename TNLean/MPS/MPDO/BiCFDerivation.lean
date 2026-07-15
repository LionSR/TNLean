/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.BiCFDerivation.Counterexample
import TNLean.MPS.MPDO.BiCFDerivation.DiagonalRestrictionCounterexample

/-!
# Finite-length sufficient conditions and obstructions for MPDO biCF

This module retains the historical import path for the MPDO biCF derivation
layer while the finite-length criteria are organized by their mathematical
role. It imports the proof-complete obstruction and criterion layer. The
direct-sum uniqueness and sharp BNT block-separation theorems remain available
from their own files; they are not imported here because this historical path
is intended to retain the lighter criterion layer.

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
* `TNLean.MPS.MPDO.BiCFDerivation.DiagonalRestrictionCounterexample` — an
  injective, left-canonical single block whose restriction from physical pairs
  (i,j) to (i,i) is not normal at any blocking length.
* `TNLean.MPS.MPDO.BiCFDerivation.DirectSumInput` — the trace-dual algebraic
  input from the direct-sum decomposition lemma of
  David--Perez-Garcia--Schuch--Wolf that follows from the two-sided nonzero
  span lemma.
* `TNLean.MPS.MPDO.BiCFDerivation.DirectSumGroundSpace` — the corresponding
  inclusion/equality of finite-chain image spaces.
* `TNLean.MPS.MPDO.BiCFDerivation.DirectSumUniqueness` — the parent-Hamiltonian
  uniqueness input that rules out the equal-size direct-sum collapse once the
  two injective block states have distinct MPV lines.
* `TNLean.MPS.MPDO.BiCFDerivation.BNTDirectSum` — the BNT-facing direct-sum
  form that supplies that distinctness input from separated same-dimension
  blocks, gives the fixed three-block pair separation for all ordered pairs,
  and proves the sharp \(3D^5\) simultaneous representative span. This heavier
  theorem is imported directly by users who need the BNT conclusion.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608, lines 340--345]
* [David--Perez-Garcia--Schuch--Wolf 2006, two-sided nonzero span and direct-sum
  decomposition lemmas]

## Tags

matrix product states, matrix product density operators, canonical form, block separation
-/
