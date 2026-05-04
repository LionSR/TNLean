/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.BiCFDerivation.Selectors

/-!
# Finite-length sufficient conditions for MPDO biCF

This module retains the historical import path for the finite-length MPDO biCF
derivation layer. The criteria are organized into focused mathematical
submodules:

* `TNLean.MPS.MPDO.BiCFDerivation.Core` contains the tuple-span,
  linear-independence, and finite/cumulative pair trace-separation criteria.
* `TNLean.MPS.MPDO.BiCFDerivation.PairHomogenization` contains the
  homogeneous pair-span padding and Burnside-Jacobson pair-algebra placeholders.
* `TNLean.MPS.MPDO.BiCFDerivation.Selectors` contains the selector constructors
  and theorems assembling `HorizontalCFData`.

The original import path continues to provide these declarations.
-/
