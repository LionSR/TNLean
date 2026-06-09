/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.BlockIntersectionProperty
import TNLean.MPS.MPDO.BiCFDerivation.BNTDirectSum

/-!
# BNT direct-sum input for block intersections

This file connects the already-injective BNT direct-sum selector span to the
PGVWC07 one-step block-intersection identity.

## References

* [Perez-Garcia--Verstraete--Wolf--Cirac 2007], Theorem 12 and Lemma
  `lem:direct-sum`.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d L : ℕ}

/-- Already-injective BNT direct-sum data give the PGVWC one-step
block-intersection identity at the selector length.

The internal word length is
\[
  n=L+(r-1)(L+(L+L)).
\]
At this length the direct-sum selector theorem supplies the common blockwise
word span required in the PGVWC07 restriction-intersection argument. -/
theorem pgvwc07_iSup_restriction_intersection_of_bnt_directSum_selectors
    {r : ℕ} {dim : Fin r → ℕ} [∀ k, NeZero (dim k)]
    (A : (k : Fin r) → MPSTensor d (dim k))
    (hIrr : HasIrreducibleBlocks (d := d) A)
    (hLeft : IsLeftCanonicalBlockFamily (d := d) A)
    (hOverlap : HasNormalizedSelfOverlap (d := d) A)
    (hBlocks : BlocksNotGaugePhaseEquiv (d := d) A)
    (hBlk : ∀ k : Fin r, IsNBlkInjective (A k) L)
    (hBlk3 : ∀ k : Fin r, IsNBlkInjective (A k) (L + (L + L)))
    (hInj : ∀ k : Fin r, IsInjective (A k))
    (hL : 1 < L)
    {n : ℕ} (hn : n = L + (r - 1) * (L + (L + L)))
    (hUnital : ∀ j : Fin r, ∑ a : Fin d, A j a * (A j a)ᴴ = 1) :
    ((⨅ b : Fin d,
        (⨆ j : Fin r, groundSpace (A j) (n + 1)).comap (restrictLastₗ b)) ⊓
      (⨅ a : Fin d,
        (⨆ j : Fin r, groundSpace (A j) (n + 1)).comap (restrictFirstₗ a))) =
      ⨆ j : Fin r, groundSpace (A j) (n + 2) := by
  subst n
  exact pgvwc07_iSup_groundSpace_eq_restriction_intersection A
    (wordTupleSpanTop_of_blocksNotGaugePhaseEquiv_directSum_selectors
      A hIrr hLeft hOverlap hBlocks hBlk hBlk3 hInj hL)
    hUnital

end MPSTensor
