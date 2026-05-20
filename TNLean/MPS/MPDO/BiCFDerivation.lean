/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.BiCFDerivation.Counterexample

/-!
# Finite-length sufficient conditions and obstructions for MPDO biCF

This module retains the historical import path for the MPDO biCF derivation
layer while the finite-length criteria are organized by their mathematical
role. It imports the proof-complete obstruction and criterion layer. The
direct-sum uniqueness capstone remains available from its own files, but is not
imported here while it depends on the unfinished parent-Hamiltonian uniqueness
argument.

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
* `TNLean.MPS.MPDO.BiCFDerivation.DirectSumUniqueness` — the parent-Hamiltonian
  uniqueness input that rules out the equal-size direct-sum collapse once the
  two injective block states have distinct MPV lines.
* `TNLean.MPS.MPDO.BiCFDerivation.BNTDirectSum` — the BNT-facing direct-sum
  form that supplies that distinctness input from separated same-dimension
  blocks and gives the fixed three-block pair separation for all ordered pairs,
  while keeping the direct-sum injectivity hypotheses explicit. This capstone
  is imported directly by users who need the unfinished uniqueness route.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Proposition `propblockinj`, lines 340--345]
* [David--Perez-Garcia--Schuch--Wolf 2006, Lemmas `lem1` and `lem:direct-sum`]

## Tags

matrix product states, matrix product density operators, canonical form, block separation
-/
