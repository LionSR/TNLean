import TNLean.MPS.SharedInfra.GaugePhase

/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# BNT separation predicate

This module contains the basic separation predicate for finite block families:
distinct equal-dimension blocks are not gauge-phase equivalent.

The predicate is used both by the older separated one-representative BNT
surface and by canonical-form phase-class constructions. It is kept independent
of the heavier BNT construction theorems so modules that only need the
separation hypothesis do not import the whole construction layer.
-/

namespace MPSTensor

variable {d : ℕ}

/-- Distinct equal-dimension blocks in a family are not gauge-phase equivalent. -/
abbrev BlocksNotGaugePhaseEquiv {r : ℕ} {dim : Fin r → ℕ}
    (A : (k : Fin r) → MPSTensor d (dim k)) : Prop :=
  ∀ j k : Fin r, j ≠ k →
    ∀ h : dim j = dim k,
      ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (A j)) (A k)

/-- Block-permutation gauge-phase matching between two block families.

Source: arXiv:1606.00608, Theorem `thm1`, statement lines 1167--1170 and proof
line 1182. The source proves this block-matching conclusion from canonical-form
BNT data and proportional MPV families. This abbreviation records only the
conclusion, not a theorem asserting it from extra coefficient-array hypotheses;
the copy-weight comparison and global gauge in lines 1184--1192 belong to the
equal-MPV corollary. -/
abbrev BlockPermutationGaugePhaseConclusion
    {rA rB : ℕ}
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
