/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Periodic.FundamentalTheorem
import TNLean.MPS.Periodic.Applications
import TNLean.MPS.Symmetry.Defs
import TNLean.MPS.Core.Blocking
import TNLean.MPS.Core.BlockingTransfer
import TNLean.MPS.Core.CPPrimitive
import TNLean.Channel.Basic
import TNLean.Channel.KrausRepresentation
import TNLean.Channel.KrausUnitaryFreedom
import TNLean.Channel.Peripheral.CyclicDecomposition

/-!
# Periodic equal-case Fundamental Theorem hypothesis

This module isolates the explicit equal-case Fundamental Theorem hypothesis used
in the periodic symmetry and Theorem 4.1 developments.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-! ## Periodic equal-case Fundamental Theorem stated as a hypothesis -/

section PeriodicEqualCaseFTHyp

variable {d D : ℕ}

/-- Coarse abstract form of the periodic equal-case Fundamental Theorem of MPS,
motivated by Theorem 3.8 of arXiv:1708.00029 and stated as a Prop for use as
an explicit hypothesis.

Given two tensors of the same physical/bond dimensions in irreducible form that
generate the same matrix-product-vector family, this hypothesis asserts the existence
of a positive period `m` and a `Z_m`-gauge equivalence between the two tensors.

The source theorem has finer blockwise multiplicity data: after matching bases of
periodic tensors, each block has its own period `m_j` and a diagonal matrix `Z_j`
on the multiplicity space with `Z_j R_j = S_j`. The present hypothesis forgets
that blockwise structure and records only the resulting global finite-order
intertwining relation.

Note that the Lean theorem `fundamentalTheorem_periodic_equalCase` in
`MPS/Periodic/FundamentalTheorem.lean` requires four extra hypotheses beyond
irreducibility and `SameMPV` (non-repetition of blocks for both tensors, the periodic
overlap dichotomy, and a per-block weight-power equality). The Prop introduced here
asserts an unconditional abstract equal-case hypothesis, so it is strictly stronger
than the current repository theorem; callers committing to it are committing to the
hypotheses recorded in `docs/paper-gaps/1708_periodic_overlap_route_alignment.tex`.
The convention follows the analogous
hypothesis in `MPS/Periodic/Applications.lean`. -/
def PeriodicEqualCaseFT (d D : ℕ) : Prop :=
  ∀ {X Y : MPSTensor d D},
    IsIrreducibleForm X → IsIrreducibleForm Y →
    SameMPV X Y →
    ∃ m : ℕ, 0 < m ∧ ZGaugeEquiv m X Y

end PeriodicEqualCaseFTHyp

end MPSTensor
