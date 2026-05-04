/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.BiCFDerivation.Selectors

/-!
# Finite-length sufficient conditions for MPDO biCF

This module is the public entry point for the finite-length MPDO biCF
derivation layer.  The implementation is split into focused submodules:

* `TNLean.MPS.MPDO.BiCFDerivation.Core` contains the tuple-span,
  linear-independence, and finite/cumulative pair trace-separation criteria.
* `TNLean.MPS.MPDO.BiCFDerivation.PairHomogenization` contains the
  homogeneous pair-span padding and Burnside-Jacobson pair-algebra placeholders.
* `TNLean.MPS.MPDO.BiCFDerivation.Selectors` contains the selector constructors
  and `HorizontalCFData` packaging theorems.

The original import path is retained as a thin re-export wrapper.
-/
