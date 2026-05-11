/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Defs

/-!
# BNT block matching support

This module contains the witness type used for BNT block matching in
arXiv:1606.00608.

It deliberately contains no equal- or proportional-MPV Fundamental Theorem
formulation: statements with common block structure or explicit coefficient
arrays as hypotheses are stricter than arXiv:1606.00608, Theorem II.1 and
Corollary II.2.

## Main results

### Block matching witness

`BlockPermutationGaugeWitness` records the block-count, permutation,
bond-dimension, and gauge-phase data produced by the heterogeneous equal-MPV
block-matching theorem.

## References

- Pérez-García, Verstraete, Wolf, Cirac, *Matrix Product State Representations*,
  Quantum Inf. Comput. 7 (2007), arXiv:quant-ph/0608197.
- Cirac, Pérez-García, Schuch, Verstraete, *Matrix product states and projected entangled pair
  states: Concepts, symmetries, theorems*, Rev. Mod. Phys. 93 (2021), arXiv:2011.12127.

-/

namespace MPSTensor

/-- Conclusion type for BNT block-matching statements.

Source: arXiv:1606.00608, Theorem II.1, lines 349--352 and 1165--1192.  This is
the permutation, dimension-equality, and gauge-phase part of the conclusion; it
does not assert the hypotheses from which that conclusion follows. -/
abbrev BlockPermutationGaugeWitness
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k)) : Prop :=
  ∃ _h : rA = rB,
    ∃ perm : Fin rA ≃ Fin rB,
      ∀ j : Fin rA,
        ∃ hdim : dimA j = dimB (perm j),
          GaugePhaseEquiv (d := d)
            (cast (congr_arg (MPSTensor d) hdim) (A j))
            (B (perm j))

end MPSTensor
