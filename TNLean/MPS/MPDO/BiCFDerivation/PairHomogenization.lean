/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.BiCFDerivation.PairHomogenization.Algebra
import TNLean.MPS.MPDO.BiCFDerivation.PairHomogenization.Span
import TNLean.MPS.MPDO.BiCFDerivation.PairHomogenization.BurnsideJacobson

/-!
# Pair-span homogenization for MPDO biCF

This module re-exports the homogeneous pair-span padding criteria and the
Burnside-Jacobson pair-algebra placeholders used to turn all-length pair trace
separation into a fixed homogeneous word length.

The content is organized across three submodules:

* `Algebra` — subdirect product algebra density, Skolem–Noether gauge-equivalence
  detection, two-sided axis ideals, `subdirect_matrix_pair_eq_top_or_eq_graph_algEquiv`.
* `Span` — homogeneous word-tuple multiplication, identity padding,
  cumulative-to-homogeneous conversion lemmas.
* `BurnsideJacobson` — finite-family separation and Burnside–Jacobson bridge to
  `PairTraceSeparatingAt`.
-/
