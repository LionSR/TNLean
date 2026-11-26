/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Transfer.Spectrum.GaugePhase

/-!
# BNT separation predicate

This module contains the basic separation predicate for finite block families:
distinct equal-dimension blocks are not gauge-phase equivalent.

The predicate is used both by the older separated one-representative BNT
surface and by canonical-form phase-class constructions. It is kept independent
of the heavier BNT construction theorems so modules that only need the
separation hypothesis do not import the whole construction layer.

It also contains the following results.

* `MPSTensor.BlocksNotGaugePhaseEquiv.forall_ne_transport`: bond-dimension transport in sector
  separation.
-/

open MPTensor

namespace MPSTensor

section Separation

variable {d : ℕ}

/-- Distinct equal-dimension blocks in a family are not gauge-phase equivalent. -/
abbrev BlocksNotGaugePhaseEquiv {r : ℕ} {dim : Fin r → ℕ}
    (A : (k : Fin r) → MPSTensor d (dim k)) : Prop :=
  ∀ j k : Fin r, j ≠ k →
    ∀ h : dim j = dim k,
      ¬ GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) (A j)) (A k)

/-- Separation of a block family passes to the subfamily along an injective reindexing. -/
theorem BlocksNotGaugePhaseEquiv.comp {r s : ℕ} {dim : Fin r → ℕ}
    {A : (k : Fin r) → MPSTensor d (dim k)} (hA : BlocksNotGaugePhaseEquiv (d := d) A)
    {f : Fin s → Fin r} (hf : Function.Injective f) :
    BlocksNotGaugePhaseEquiv (d := d) (fun j => A (f j)) :=
  fun j k hjk h => hA (f j) (f k) (hf.ne hjk) h

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
          GaugePhaseEquiv (α := Fin d)
            (cast (congr_arg (MPSTensor d) hdim) (A j))
            (B (perm j))

end Separation

section GaugePhaseSeparationTransport

/-!
## Bond-dimension transport in sector separation

Pairwise gauge-phase inequivalence can be expressed by transporting the second
labelled tensor to the first tensor's bond dimension. This form of the existing
separation condition is used by the primitive-sector support and gap theorems.

Source: Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
Proposition prop:char-BNT and Theorem thm1; Nachtergaele,
arXiv:cond-mat/9410110, Section 3 and Lemma disjoint.
-/

/-- Read sector separation with the second tensor transported to the first
bond space. Source: CPSV16, arXiv:1606.00608, Proposition prop:char-BNT.
This is a reformulation of the existing condition, with no added assumption. -/
theorem BlocksNotGaugePhaseEquiv.forall_ne_transport {d r : ℕ} {dim : Fin r → ℕ}
    {A : ∀ j, MPSTensor d (dim j)} (hA : BlocksNotGaugePhaseEquiv A) :
    ∀ i j, i ≠ j → ∀ e : dim j = dim i, ¬ GaugePhaseEquiv (e ▸ A j) (A i) := by
  intro i j hij e
  simpa only [eqRec_eq_cast] using hA j i hij.symm e

end GaugePhaseSeparationTransport

end MPSTensor
