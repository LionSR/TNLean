/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PostBlockedRepresentativeSpan
import TNLean.MPS.Overlap.PeripheralToTransferMapGap
import TNLean.Wielandt.Primitivity.StronglyIrreducibleToFullRank

/-!
# Simultaneous word spans of primitive blocks

A finite family of normalized primitive tensors, pairwise inequivalent up to
similarity and phase, has full simultaneous word span at every sufficiently
large length. Individual normality gives a common injective length; the
three-block separation argument supplies a fixed family of block selectors.
This is the block-separation input to PGVWC07, arXiv:quant-ph/0608197,
the direct-sum lemma (lines 1346--1408) and Theorem 12 (lines
1424--1456).
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ} [∀ j, NeZero (dim j)]

/-- Pairwise inequivalent normalized primitive blocks span their full product
matrix algebra at all sufficiently large word lengths. This is the eventual
form of the direct-sum separation argument in PGVWC07,
arXiv:quant-ph/0608197, the direct-sum lemma, lines 1346--1408. -/
theorem exists_eventually_wordTupleSpanTop_of_isPrimitiveMPS
    (A : (j : Fin r) → MPSTensor d (dim j))
    (ρ : ∀ j, Matrix (Fin (dim j)) (Fin (dim j)) ℂ)
    (hP : ∀ j, IsPrimitiveMPS (A j) (ρ j)) (hρ : ∀ j, (ρ j).PosDef)
    (hDistinct : ∀ i j, i ≠ j → ∀ h : dim j = dim i,
      ¬ GaugePhaseEquiv (h ▸ A j) (A i)) :
    ∃ L₀ : ℕ, ∀ L ≥ L₀, WordTupleSpanTop A L := by
  have hNormal : ∀ j, Kraus.IsNormal (A j) :=
    fun j ↦ isNormal_of_isPrimitiveMPS_with_posDef (hP j) (hρ j)
  obtain ⟨p, hp, hAtP⟩ := exists_common_isNBlkInjective_of_isNormal_leftCanonical
    A (fun j ↦ (hP j).norm) (fun j ↦ NeZero.ne (dim j)) hNormal
  have hPair := hasPairBlockSeparatingWords_threeBlock_of_blocksNotGaugePhaseEquiv_c1
    A (HasIrreducibleBlocks.ofForall fun j ↦ (hP j).isIrreducibleFamily_of_posDef (hρ j))
    (IsLeftCanonicalBlockFamily.ofForall fun j ↦ (hP j).norm)
    (HasNormalizedSelfOverlap.ofForall fun j ↦
      overlap_tendsto_one_of_peripheralPrimitive_of_irreducible (A j)
        ((hP j).isIrreducibleFamily_of_posDef (hρ j)) (hP j).norm (hP j).isPrimitive)
    (show BlocksNotGaugePhaseEquiv A from fun i j hij hdim ↦ by
      simpa only [eqRec_eq_cast] using hDistinct j i hij.symm hdim)
    hAtP (fun j ↦ isNBlkInjective_of_le hp (hAtP j) (Nat.le_succ p))
    (fun j ↦ isNBlkInjective_of_le hp (hAtP j) (by omega)) hp
  exact eventually_wordTupleSpanTop_of_blockSelectorWords_of_isNBlkInjective
    A (hasBlockSelectorWords_of_pairBlockSeparatingWords A hPair) hp hAtP

end MPSTensor
